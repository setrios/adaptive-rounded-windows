/**
 * extension.js – Rounded Window Corners
 *
 * Applies GLSL-based rounded corners (and an optional custom shadow) to every
 * window that is not already drawn with libadwaita / libhandy.
 *
 * Signal / lifecycle flow
 * ──────────────────────
 * enable()
 *   └─ wait for shell startup → enableEffect()
 *        ├─ connect global signals   (window-created, minimize, unminimize,
 *        │                            destroy, restacked, settings changed)
 *        └─ applyEffectTo() every existing window actor
 *
 * applyEffectTo(actor)
 *   ├─ connect per-window signals  (actor size, texture size, win size /
 *   │                               position, fullscreen, focus,
 *   │                               workspace-changed)
 *   └─ onAddEffect(actor)
 *        ├─ add RoundedCornersEffect to the actor / surface
 *        ├─ create custom shadow St.Bin (below the actor in windowGroup)
 *        └─ refreshRoundedCorners()
 *
 * Geometry triggers coalesce through queueRefresh() into one
 * refreshRoundedCorners() per frame (Meta BEFORE_REDRAW later).  Skipped
 * windows (maximized/fullscreen/blacklisted) are soft-removed: effect and
 * shadow are destroyed but signals + ActorData stay, so the next geometry
 * change can re-add the effect (unmaximize, fullscreen exit).
 *
 * Shadow visibility is owned by syncShadowVisibility(): hidden whenever the
 * WindowActor is transformed (animations), shown - repositioned - in the
 * same frame the actor returns to identity.  The actor's transforms are
 * deliberately NOT mirrored onto the shadow (see shadowShouldBeVisible).
 *
 * disable()
 *   ├─ disableEffect()    → removeEffectFrom() every actor
 *   └─ uninitPrefs()
 */

import Gio from 'gi://Gio';
import GLib from 'gi://GLib';
import Meta from 'gi://Meta';
import Shell from 'gi://Shell';
import St from 'gi://St';

import { Extension } from 'resource:///org/gnome/shell/extensions/extension.js';
import * as Main from 'resource:///org/gnome/shell/ui/main.js';

import { RoundedCornersEffect, ClipShadowEffect } from './effect.js';

// ─────────────────────────────────────────────────────────────────────────────
// Constants
// ─────────────────────────────────────────────────────────────────────────────
const ROUNDED_CORNERS_EFFECT = 'rwc-rounded-corners';
const CLIP_SHADOW_EFFECT      = 'rwc-clip-shadow';
const SHADOW_PADDING          = 80;   // extra pixels around the shadow actor

// ─────────────────────────────────────────────────────────────────────────────
// Module-level state
//   _settings  – Gio.Settings instance (populated by enable())
//   _connections – list of { object, id } for global signal connections
//   _actorMap    – WeakMap<Meta.WindowActor, ActorData>
//
// ActorData = {
//   shadow         : St.Bin | null,
//   signalsAttached : boolean,
//   laterId        : number,            // pending BEFORE_REDRAW refresh (0 = none)
//   lastScale      : number,            // scaleFactor at last shadow placement
//   lastShadowRect : {x,y,w,h} | null,  // last applied shadow geometry
//   lastShadowStyle: string | null,     // style-string caches (skip identical
//   lastInnerStyle : string | null,     //   inline-CSS reassignment)
// }
// ─────────────────────────────────────────────────────────────────────────────
let _settings       = null;
let _connections    = [];   // global connections
const _actorMap     = new WeakMap();
let _mutterSettings = null;
let _mutterSettingsConn = 0;
let _fractionalScaling = null;
let _settingsTimeoutId = 0;

// ─────────────────────────────────────────────────────────────────────────────
// Settings helpers
// ─────────────────────────────────────────────────────────────────────────────
function getS(key)   { return _settings.get_value(key).recursiveUnpack(); }
function getB(key)   { return _settings.get_boolean(key); }
function getI(key)   { return _settings.get_int(key); }
function getD(key)   { return _settings.get_double(key); }

/** Build the per-window config object from GSettings. */
function buildConfig() {
    // Theme-aware border: border-* is the light-theme (and only) colour;
    // dark-border-* applies while the system Appearance style prefers dark.
    // Read the scheme live like every other input - a cached module value
    // here went stale across the disable/enable cycle that screen lock
    // triggers, painting light borders on every unlock.
    const dark = St.Settings.get().color_scheme ===
        St.SystemColorScheme.PREFER_DARK;
    const border = (dark && getB('theme-aware-border'))
        ? 'dark-border' : 'border';

    return {
        cornerRadius: getI('corner-radius'),
        smoothing:    getD('smoothing'),
        padding: {
            top:    getI('padding-top'),
            bottom: getI('padding-bottom'),
            left:   getI('padding-left'),
            right:  getI('padding-right'),
        },
        borderWidth: getI('border-width'),
        borderColor: [
            getD(`${border}-red`),
            getD(`${border}-green`),
            getD(`${border}-blue`),
            getD(`${border}-alpha`),
        ],
        keepRoundedMaximized:  getB('keep-rounded-maximized'),
        keepRoundedFullscreen: getB('keep-rounded-fullscreen'),
    };
}

/** Return the shadow settings for the focused or unfocused state. */
function shadowConfig(focused) {
    const prefix = focused ? 'focused-shadow' : 'unfocused-shadow';
    return {
        opacity:         getI(`${prefix}-opacity`),
        blur:            getI(`${prefix}-blur`),
        spread:          getI(`${prefix}-spread`),
        xOffset:         getI(`${prefix}-x-offset`),
        yOffset:         getI(`${prefix}-y-offset`),
    };
}

// ─────────────────────────────────────────────────────────────────────────────
// Logging
// ─────────────────────────────────────────────────────────────────────────────
function logDbg(msg) {
    if (_settings && getB('debug-mode'))
        console.log(`[RoundedWindows] ${msg}`);
}

// ─────────────────────────────────────────────────────────────────────────────
// Application type detection  (libadwaita / libhandy)
// ─────────────────────────────────────────────────────────────────────────────
const _appTypeCache = new Map();   // pid ↦ 'LibAdwaita' | 'LibHandy' | 'Other'
const ROUNDABLE_WINDOW_TYPES = [
    Meta.WindowType.NORMAL,
    Meta.WindowType.DIALOG,
    Meta.WindowType.MODAL_DIALOG,
    Meta.WindowType.UTILITY,
    Meta.WindowType.SPLASHSCREEN,
    Meta.WindowType.TOOLBAR,
].filter(type => type !== undefined);

function normalizeAppId(value) {
    if (typeof value !== 'string')
        return '';
    return value.trim().replace(/\.desktop$/i, '');
}

function getWindowIdentifiers(win) {
    const identifiers = new Set();
    const add = value => {
        if (typeof value !== 'string')
            return;

        const trimmed = value.trim();
        if (!trimmed)
            return;

        identifiers.add(trimmed);

        const normalized = normalizeAppId(trimmed);
        if (normalized)
            identifiers.add(normalized);
    };

    try {
        add(win.get_wm_class_instance?.());
        add(win.get_wm_class?.());
    } catch (_) {}

    try {
        add(win.gtkApplicationId ?? win.get_gtk_application_id?.());
    } catch (_) {}

    try {
        add(win.get_sandboxed_app_id?.());
    } catch (_) {}

    try {
        const tracker = Shell.WindowTracker.get_default();
        const app = tracker?.get_window_app(win) ?? null;
        add(app?.get_id?.());
        add(app?.get_name?.());
    } catch (_) {}

    return [...identifiers];
}

// Normalized exception list, cached between settings changes: shouldSkip()
// runs once per coalesced refresh (per frame during resizes), so rebuilding
// the Set from GSettings on every call is wasted work.
let _blacklistCache = null;

function getBlacklist() {
    if (!_blacklistCache) {
        _blacklistCache = new Set(
            getS('blacklist').map(normalizeAppId).filter(Boolean));
    }
    return _blacklistCache;
}

function isListedWindow(identifiers, listSet) {
    return identifiers.some(id => listSet.has(normalizeAppId(id)));
}

function getAppType(win) {
    const pid = win.get_pid();

    // Prevent infinite growth of the PID cache
    if (_appTypeCache.size > 200)
        _appTypeCache.clear();

    if (_appTypeCache.has(pid))
        return _appTypeCache.get(pid);

    let type = 'Other';
    try {
        const decoder = new TextDecoder();
        const [, bytes] = GLib.file_get_contents(`/proc/${pid}/maps`);
        const maps = decoder.decode(bytes);
        if (maps.includes('libadwaita-1.so'))
            type = 'LibAdwaita';
        else if (maps.includes('libhandy-1.so'))
            type = 'LibHandy';
    } catch (_) {
        // /proc may not be readable for all pids – treat as 'Other'
    }

    _appTypeCache.set(pid, type);
    return type;
}

/** True when this window should NOT get rounded corners. */
function shouldSkip(win, cfg = null) {
    const identifiers = getWindowIdentifiers(win);
    if (identifiers.some(id => ['com.rastersoft.ding', 'ding'].includes(normalizeAppId(id))))
        return true;

    const windowType = win.windowType ?? win.get_window_type?.();
    if (!ROUNDABLE_WINDOW_TYPES.includes(windowType))
        return true;

    // Blacklist / whitelist logic:
    //   Normal mode (whitelist-mode = false):
    //     listed windows are EXCLUDED (blacklist)
    //   Whitelist mode (whitelist-mode = true):
    //     only listed windows are INCLUDED, all others are excluded
    const whitelistMode = getB('whitelist-mode');
    const isListed      = isListedWindow(identifiers, getBlacklist());

    if (whitelistMode && !isListed)
        return true;   // whitelist mode: skip apps not in the list
    if (!whitelistMode && isListed)
        return true;   // blacklist mode: skip apps in the list

    // Optionally skip libadwaita / libhandy apps (unless explicitly listed)
    const appType = getAppType(win);
    if (getB('skip-libadwaita-app') && appType === 'LibAdwaita' && !isListed)
        return true;
    if (getB('skip-libhandy-app')   && appType === 'LibHandy'   && !isListed)
        return true;

    // Skip maximised / fullscreen windows unless the user explicitly wants
    // rounded corners in those states.
    // NOTE: skipping destroys the shadow along with the effect, so the
    // 'keep-shadow-maximized' setting only has an effect when
    // 'keep-rounded-maximized' is also enabled (see refreshShadowStyle).
    cfg = cfg ?? buildConfig();
    const isMax  = win.maximizedHorizontally || win.maximizedVertically;
    const isFull = win.fullscreen;

    if (isMax  && !cfg.keepRoundedMaximized)  return true;
    if (isFull && !cfg.keepRoundedFullscreen) return true;

    return false;
}

// ─────────────────────────────────────────────────────────────────────────────
// Actor helpers
// ─────────────────────────────────────────────────────────────────────────────

function findTextureActor(actor) {
    if (!actor)
        return null;

    if (actor.get_texture?.())
        return actor;

    let child = actor.get_first_child?.() ?? null;
    while (child) {
        const textured = findTextureActor(child);
        if (textured)
            return textured;

        child = child.get_next_sibling?.() ?? null;
    }

    return null;
}

/**
 * Get the Clutter.Actor to which the rounded-corners effect should be applied.
 *
 * On GNOME 50 both Wayland-native and X11/XWayland windows render through a
 * texture-bearing descendant actor. Applying the effect to that actor keeps
 * the shader aligned with the actual painted content instead of the outer
 * WindowActor container.
 */
function targetActor(actor) {
    return findTextureActor(actor) ?? actor;
}

function getWindowTexture(actor) {
    const target = targetActor(actor);
    return target?.get_texture?.() ?? actor?.get_texture?.() ?? null;
}

/** Get the RoundedCornersEffect attached to a window actor (or null). */
function getEffect(actor) {
    const target = targetActor(actor);
    return target ? target.get_effect(ROUNDED_CORNERS_EFFECT) : null;
}

/**
 * Check whether fractional scaling is enabled.
 * When `scale-monitor-framebuffer` is active (default on GNOME 46+ Wayland),
 * the compositor handles scaling at the buffer level and the actor/FBO
 * dimensions already account for the scale.  Returning the raw monitor
 * scale in that case would double-scale all shader values.
 */
function isFractionalScalingEnabled() {
    if (_fractionalScaling !== null)
        return _fractionalScaling;

    try {
        if (!_mutterSettings) {
            _mutterSettings = new Gio.Settings({ schema_id: 'org.gnome.mutter' });
            _mutterSettingsConn = _mutterSettings.connect('changed::experimental-features', () => {
                _fractionalScaling = null;
                refreshAll();
            });
        }

        const features = _mutterSettings.get_strv('experimental-features');
        const isWayland = !Meta.is_wayland_compositor || Meta.is_wayland_compositor();
        _fractionalScaling = isWayland && features.includes('scale-monitor-framebuffer');
    } catch (_) {
        _fractionalScaling = false;
    }
    return _fractionalScaling;
}

/** Get the monitor scale factor for a window (respects fractional scaling). */
function scaleFactor(win) {
    // When fractional scaling is enabled the actor dimensions already
    // incorporate the scale, so the shader must use scale = 1.
    if (isFractionalScalingEnabled())
        return 1;

    const idx = win.get_monitor();
    return global.display.get_monitor_scale(idx);
}

/**
 * Compute the offset between the window's buffer rect and its frame rect.
 * CSD windows have invisible resize grips outside the visible frame; this
 * delta lets us clip only the visible part.
 *
 * Returns [dx, dy, dw, dh] (all ≤ 0 for the width/height components).
 */
function contentOffset(win) {
    const buf   = win.get_buffer_rect();
    const frame = win.get_frame_rect();
    return [
        frame.x - buf.x,
        frame.y - buf.y,
        frame.width  - buf.width,
        frame.height - buf.height,
    ];
}

/**
 * Compute the shader bounds (x1, y1, x2, y2) in *target-actor-local* pixel
 * coords.  The target actor is determined by targetActor().
 *
 * The target actor is the texture-bearing descendant returned by targetActor().
 * Its allocation tracks the actual window buffer, so contentOffset() can be
 * applied uniformly for Wayland and X11/XWayland windows.
 */
function computeBounds(actor) {
    const win = actor.metaWindow;
    const sc  = scaleFactor(win);
    const target = targetActor(actor) ?? actor;
    const targetW = target.width;
    const targetH = target.height;

    const [dx, dy, dw, dh] = contentOffset(win);
    // The frame area starts at (dx, dy) inside the buffer actor, because dx/dy
    // is the difference between the visible frame and the underlying buffer.
    let x1 = dx;
    let y1 = dy;
    let x2 = dx + targetW + dw;
    let y2 = dy + targetH + dh;

    // Apply a 1px anti-aliasing inset if the window has no buffer padding
    // in that direction to avoid drawing semitransparent texture edge pixels.
    if (x1 === 0) x1 += sc;
    if (y1 === 0) y1 += sc;
    if (x2 === targetW) x2 -= sc;
    if (y2 === targetH) y2 -= sc;

    return { x1, y1, x2, y2 };
}

// ─────────────────────────────────────────────────────────────────────────────
// Shadow helpers
// ─────────────────────────────────────────────────────────────────────────────

/** Build the CSS box-shadow string from a shadow config object. */
function boxShadowCss(sc, scale) {
    const alpha  = (sc.opacity / 255).toFixed(3);
    const blur   = (sc.blur   * scale).toFixed(1);
    const spread = (sc.spread * scale).toFixed(1);
    const x      = (sc.xOffset * scale).toFixed(1);
    const y      = (sc.yOffset * scale).toFixed(1);
    return `box-shadow: ${x}px ${y}px ${blur}px ${spread}px rgba(0,0,0,${alpha})`;
}

/**
 * Shared per-pass geometry for the shadow helpers.  Computed once in
 * refreshRoundedCorners() and passed down so positionShadow() and
 * refreshShadowClip() can never disagree on pad/frame (the clip's
 * [pad, pad] origin is only valid if both use identical values).
 */
function shadowGeometry(win) {
    const sc = scaleFactor(win);
    return { sc, pad: SHADOW_PADDING * sc, frame: win.get_frame_rect() };
}

/**
 * Squircle corner radius + exponent in scaled pixels, with the max-radius
 * clamp, for a window whose content area is (frameW − padding) × (frameH −
 * padding).  Shared by refreshShadowClip() (the shader clip) and
 * refreshShadowStyle() (the CSS border-radius) so the shadow's transparent
 * corners always trace exactly the clipped contour - the coupling CLAUDE.md
 * requires.  RoundedCornersEffect.updateUniforms() keeps its own copy because
 * it derives bounds from the target-actor allocation, not the frame rect.
 */
function squircleRadius(cfg, sc, frameW, frameH) {
    let exponent = cfg.smoothing * 10 + 2;
    let radius   = cfg.cornerRadius * sc * 0.5 * exponent;

    const contentW = frameW - (cfg.padding.left + cfg.padding.right) * sc;
    const contentH = frameH - (cfg.padding.top  + cfg.padding.bottom) * sc;
    const maxR = Math.min(contentW, contentH) / 2;
    if (maxR > 0 && radius > maxR) {
        exponent *= maxR / radius;
        radius    = maxR;
    }
    return { radius, exponent };
}

/**
 * Coalesce refresh triggers into one refreshRoundedCorners() run per frame,
 * executed just before the next paint.  A single geometry change fires
 * several signals (actor notify::size, texture size-changed, win
 * size-changed); running the refresh once and late keeps shadow position,
 * clip uniforms and style atomic within the frame and avoids duplicate
 * GSettings/uniform work on the compositor thread.
 */
function queueRefresh(actor) {
    const data = _actorMap.get(actor);
    if (!data) {
        refreshRoundedCorners(actor);
        return;
    }
    if (data.laterId) return;

    data.laterId = global.compositor.get_laters().add(
        Meta.LaterType.BEFORE_REDRAW, () => {
            data.laterId = 0;
            if (actor.metaWindow)
                refreshRoundedCorners(actor);
            return GLib.SOURCE_REMOVE;
        });
}

/**
 * Anchor the shadow actor to the window's frame rect in global (stage)
 * coordinates, padded by SHADOW_PADDING on every side.
 *
 * The frame rect is authoritative from Mutter and independent of how the
 * WindowActor lays out its children.  Anchoring to the WindowActor with
 * BindConstraint + contentOffset() breaks for clients whose buffer rect
 * differs from their frame rect (Chromium/Electron on Wayland draw their
 * own CSD shadow margins), because the WindowActor origin does not follow
 * the buffer-rect convention those offsets assume.
 */
function positionShadow(actor, shadow, geom = null) {
    const win = actor.metaWindow;
    if (!win || !shadow) return;

    const { sc, pad, frame } = geom ?? shadowGeometry(win);
    const x = frame.x - pad;
    const y = frame.y - pad;
    const w = frame.width  + 2 * pad;
    const h = frame.height + 2 * pad;

    // Skip redundant calls: position-changed fires every frame during a
    // drag, and Clutter does not short-circuit identical set_size values.
    const data = _actorMap.get(actor);
    const last = data?.lastShadowRect;
    if (!last || last.x !== x || last.y !== y)
        shadow.set_position(x, y);
    if (!last || last.w !== w || last.h !== h)
        shadow.set_size(w, h);

    if (data) {
        data.lastShadowRect = { x, y, w, h };
        data.lastScale = sc;
    }
}

/**
 * The shadow is only correct when the window actor is at rest.  During
 * animated transitions (minimize/unminimize, maximize size-change, …) the
 * shell eases the actor's position/scale/translation; the shadow is anchored
 * to the static frame rect and cannot follow those transforms - mirroring
 * them via property bindings is geometrically wrong because shadow and actor
 * have different sizes and origins (that mirroring caused the "shadow drifts
 * in from the top-left" artifact).  So: hidden while transformed, shown at
 * identity.
 */
// Tolerances for "the actor is at rest": interrupted transitions or other
// extensions can leave tiny residual transforms (e.g. scale 0.999999); with
// strict equality the shadow would then stay hidden forever.
const SCALE_EPSILON       = 1e-3;
const TRANSLATION_EPSILON = 0.5;   // half a logical pixel

function shadowShouldBeVisible(actor) {
    return actor.visible &&
        !actor.metaWindow?.minimized &&
        Math.abs(actor.scale_x - 1) < SCALE_EPSILON &&
        Math.abs(actor.scale_y - 1) < SCALE_EPSILON &&
        Math.abs(actor.translation_x) < TRANSLATION_EPSILON &&
        Math.abs(actor.translation_y) < TRANSLATION_EPSILON;
}

/**
 * Single authority for shadow visibility, driven by the actor's
 * transform/visibility notify signals.  The reveal happens synchronously in
 * the same tick the animation lands on identity, before that frame is
 * painted - the shadow pops in together with the window's resting frame.
 *
 * Exceptions that may force-hide outside this function: the 'minimize'
 * handler (magic-lamp minimize deforms the actor without touching
 * scale/translation) and the magic-lamp unminimize path, whose timer also
 * force-shows when the lamp finishes.
 */
function syncShadowVisibility(actor) {
    const data = _actorMap.get(actor);
    if (!data?.shadow) return;

    const show = shadowShouldBeVisible(actor);
    if (show === data.shadow.visible) return;

    if (show) {
        // The monitor scale may have changed while hidden (e.g. revealed on
        // a different-scale monitor): queue a full refresh - it runs before
        // this frame paints, so clip and style land coherent with the scale.
        const win = actor.metaWindow;
        if (win && data.lastScale && data.lastScale !== scaleFactor(win))
            queueRefresh(actor);

        // Geometry and opacity may have changed while hidden
        positionShadow(actor, data.shadow);
        data.shadow.opacity = actor.opacity;
        data.shadow.show();
    } else {
        data.shadow.hide();
    }
}

/** Reset the per-window shadow caches (forces the next refresh to reapply). */
function resetShadowCaches(data) {
    data.lastScale = 0;
    data.lastShadowRect = null;
    data.lastShadowStyle = null;
    data.lastInnerStyle = null;
}

/** Remove and destroy a window's shadow actor, if any. */
function destroyShadow(data) {
    if (!data.shadow) return;
    try {
        if (data.shadow.get_parent())
            global.windowGroup.remove_child(data.shadow);
        data.shadow.clear_effects();
        data.shadow.destroy();
    } catch (_) {
        // Shadow actor may already be destroyed
    }
    data.shadow = null;
    resetShadowCaches(data);
}

/** Create and insert a custom shadow St.Bin below the window actor. */
function createShadow(actor) {
    // Outer bin: provides extra padding so the shadow can extend outside
    const shadow = new St.Bin({
        name: 'RWC Shadow',
        style: 'background: transparent;',
    });

    // Inner bin: the actual CSS shadow is applied here
    const inner = new St.Bin({ x_expand: true, y_expand: true });
    inner.add_style_class_name('rwc-shadow');
    shadow.set_child(inner);

    // Clip-shadow effect prevents shadow from showing inside the window
    shadow.add_effect_with_name(CLIP_SHADOW_EFFECT, new ClipShadowEffect());

    // Match the window's current opacity (kept in sync by the watcher)
    shadow.opacity = actor.opacity;

    global.windowGroup.insert_child_below(shadow, actor);

    // Position, style, clip and visibility are applied by the caller's
    // refreshRoundedCorners()/syncShadowVisibility() pass in the same tick
    // (no paint happens in between), where the ActorData caches exist.
    return shadow;
}

/** Update the CSS style of an existing shadow actor. */
function refreshShadowStyle(actor, shadowActor, geom = null, cfg = null) {
    if (!shadowActor) return;

    const win = actor.metaWindow;
    geom = geom ?? shadowGeometry(win);
    cfg  = cfg  ?? buildConfig();

    const origScale  = St.ThemeContext.get_for_stage(global.stage).scale_factor;
    const cssScale   = geom.sc / origScale;

    const pad    = SHADOW_PADDING * cssScale;
    const scfg   = shadowConfig(win.appears_focused);

    // Compute the CSS border-radius to match the shader's squircle.
    // The shader uses:  exponent = smoothing*10+2,  radius = outerR * 0.5 * exponent
    // CSS border-radius only supports circular arcs (exponent=2).
    // A squircle extends further along diagonals than a circle of the same radius,
    // so using the shader's radius for the CSS guarantees the transparent background
    // never shows through the shader's transparent corners.
    //
    // The clamp MUST mirror refreshShadowClip()/updateUniforms() exactly, so
    // compute it in the same scaled-pixel space (radius and bounds inset by
    // padding*sc) and only then convert to CSS px.  Doing the clamp in logical
    // px here would use a different threshold when sc≠1 (integer HiDPI) and the
    // CSS corner would no longer coincide with the clipped corner.  The
    // squircle exponent does not enter the CSS (border-radius is circular).
    const { radius: radiusScaled } =
        squircleRadius(cfg, geom.sc, geom.frame.width, geom.frame.height);
    // scaled px → CSS px (rendered size = radius * origScale = radiusScaled)
    const radius = radiusScaled / origScale;

    const inner = shadowActor.get_first_child();
    if (!inner) return;

    // Hide shadow when maximised/fullscreened (unless keep-shadow-maximized)
    const isMax  = win.maximizedHorizontally || win.maximizedVertically;
    const isFull = win.fullscreen;
    const hide   = (isMax || isFull) && !getB('keep-shadow-maximized');

    const shadowStyle = `padding: ${pad}px;`;

    // Use transparent background - NEVER white.  The box-shadow alone provides
    // the visual shadow.  A white background would bleed through the shader's
    // transparent squircle corners because CSS border-radius is circular.
    const innerStyle = hide
        ? 'opacity: 0;'
        : `background: transparent;
           border-radius: ${radius}px;
           ${boxShadowCss(scfg, cssScale)};
           margin: ${cfg.padding.top    * cssScale}px
                   ${cfg.padding.right  * cssScale}px
                   ${cfg.padding.bottom * cssScale}px
                   ${cfg.padding.left   * cssScale}px;`;

    // The style strings only depend on config/focus/maximize/scale - not on
    // the frame geometry - so during resizes and drags they are identical
    // every frame.  Skip the assignment then: setting inline style forces a
    // CSS re-parse and relayout even when the string is unchanged.
    const data = _actorMap.get(actor);
    if (data?.lastShadowStyle !== shadowStyle) {
        shadowActor.style = shadowStyle;
        if (data) data.lastShadowStyle = shadowStyle;
    }
    if (data?.lastInnerStyle !== innerStyle) {
        inner.style = innerStyle;
        if (data) data.lastInnerStyle = innerStyle;
    }
}

/** Update the ClipShadowEffect bounds for a shadow actor.
 *
 * The clip now uses the same squircle parameters as the RoundedCornersEffect
 * so the shadow is transparent exactly where the rounded corners are, with
 * pixel-perfect anti-aliasing along the curved edge.
 */
function refreshShadowClip(actor, shadowActor, geom = null, cfg = null) {
    if (!shadowActor) return;

    const effect = shadowActor.get_effect(CLIP_SHADOW_EFFECT);
    if (!effect) return;

    // Window content rect within the shadow actor in pixel coordinates.
    // positionShadow() places the shadow at (frame - pad) sized
    // (frame + 2*pad), so the window frame maps exactly to [pad, pad] in
    // shadow-actor-local coordinates.  Compute sw/sh from the frame rect
    // rather than reading shadowActor.width / shadowActor.height: the
    // allocation is resolved on the next Clutter layout pass and can still
    // be 0 on the very first call (deferred applyEffectTo path for
    // Qt / OpenGL X11 windows such as VirtualBox).
    const win = actor.metaWindow;
    const { sc, pad, frame } = geom ?? shadowGeometry(win);
    cfg = cfg ?? buildConfig();

    // A momentarily 0-sized frame (window mapped before its first allocation)
    // would produce inverted clip bounds - skip until real geometry arrives.
    if (frame.width <= 0 || frame.height <= 0) return;

    const sw = frame.width  + 2 * pad;
    const sh = frame.height + 2 * pad;

    // Squircle radius/exponent (clamped) shared with refreshShadowStyle().
    const { radius, exponent } =
        squircleRadius(cfg, sc, frame.width, frame.height);

    // Window content rect within the shadow actor: the frame maps to
    // [pad, pad], inset by the padding (same basis as squircleRadius).
    const bx1 = pad + cfg.padding.left   * sc;
    const by1 = pad + cfg.padding.top    * sc;
    const bx2 = pad + frame.width  - cfg.padding.right  * sc;
    const by2 = pad + frame.height - cfg.padding.bottom * sc;

    // Pass sw/sh explicitly so the shader step uniform is correct even when
    // the shadow actor's allocation hasn't been resolved yet.
    effect.setClip([bx1, by1, bx2, by2], radius, exponent, sw, sh);
}

// ─────────────────────────────────────────────────────────────────────────────
// Effect application / removal
// ─────────────────────────────────────────────────────────────────────────────

/** Get or create the ActorData entry for a window actor. */
function ensureActorData(actor) {
    let data = _actorMap.get(actor);
    if (!data) {
        data = {
            shadow: null,
            connections: [],
            signalsAttached: false,
            laterId: 0,
            lastScale: 0,
            lastShadowRect: null,
            lastShadowStyle: null,
            lastInnerStyle: null,
        };
        _actorMap.set(actor, data);
    }
    return data;
}

/** Attach the RoundedCornersEffect (the shadow is created by the refresh). */
function onAddEffect(actor) {
    logDbg(`Adding effect to "${actor.metaWindow?.title}"`);

    const win = actor.metaWindow;
    if (!win) return;

    if (shouldSkip(win)) {
        logDbg(`  → skipped`);
        // Track the window anyway: with signals attached, a later geometry
        // change (e.g. the window opened maximized and gets unmaximized)
        // re-evaluates shouldSkip() and adds the effect then.
        ensureActorData(actor);
        attachWindowSignals(actor);
        return;
    }

    // Never attach while the texture hasn't arrived: findTextureActor()
    // would fall back to the outer WindowActor, and once the real texture
    // actor appears the effect would have to be added again there, orphaning
    // the first copy (and its uniforms) on the WindowActor.  Track the
    // window instead - the texture's arrival changes the actor size, so the
    // per-window signals retry via queueRefresh (same deferral idea as
    // applyEffectTo).
    if (!getWindowTexture(actor)) {
        ensureActorData(actor);
        attachWindowSignals(actor);
        return;
    }

    const target = targetActor(actor);
    if (!target) return;

    if (_settings && getB('debug-mode')) {
        const buf   = win.get_buffer_rect();
        const frame = win.get_frame_rect();
        logDbg(`  geometry: buffer=${buf.x},${buf.y} ${buf.width}x${buf.height}` +
            ` frame=${frame.x},${frame.y} ${frame.width}x${frame.height}` +
            ` actor=${actor.x},${actor.y} ${actor.width}x${actor.height}` +
            ` target=${target.x},${target.y} ${target.width}x${target.height}`);
    }

    if (target.get_effect(ROUNDED_CORNERS_EFFECT)) {
        refreshRoundedCorners(actor);
        return;
    }

    target.add_effect_with_name(ROUNDED_CORNERS_EFFECT, new RoundedCornersEffect());

    // Reuse the entry on re-add after a soft removal (unmaximize etc.) so
    // the still-connected per-window signals are preserved.  The shadow is
    // created (or reused) by refreshRoundedCorners' reconcile step.
    const data = ensureActorData(actor);
    resetShadowCaches(data);

    // Attach signals here (idempotent) so windows added later via
    // refreshAll() - e.g. removed from the blacklist - also get their
    // per-window triggers, not only those that went through applyEffectTo().
    attachWindowSignals(actor);
    refreshRoundedCorners(actor);
}

/**
 * Remove effects and shadow from a window actor.
 *
 * keepSignals=true is the "skip removal" (window became maximized /
 * fullscreen / blacklisted): the per-window signal connections and the
 * ActorData entry stay alive so a later geometry change (unmaximize,
 * fullscreen exit) can re-add the effect.  Without this, maximizing a
 * window once would disconnect everything and it would never get rounded
 * corners back.  Hard removal (window destroyed, extension disabled)
 * tears everything down.
 */
function onRemoveEffect(actor, keepSignals = false) {
    try {
        logDbg(`Removing effect from "${actor.metaWindow?.title}"`);
    } catch (_) {}

    try {
        const target = targetActor(actor);
        if (target)
            target.remove_effect_by_name(ROUNDED_CORNERS_EFFECT);
    } catch (_) {
        // Actor may already be destroyed
    }

    const data = _actorMap.get(actor);
    if (!data) return;

    // Disconnect per-window signals (hard removal only)
    if (!keepSignals && data.connections) {
        for (const c of data.connections) {
            try { c.obj.disconnect(c.id); } catch (_) {}
        }
        data.connections = [];
    }

    destroyShadow(data);

    if (data.laterId) {
        global.compositor.get_laters().remove(data.laterId);
        data.laterId = 0;
    }

    if (keepSignals)
        resetShadowCaches(data);
    else
        _actorMap.delete(actor);
}

/** Recompute and push all shader uniforms for a single window. */
function refreshRoundedCorners(actor) {
    const win = actor.metaWindow;
    if (!win) return;

    const data = _actorMap.get(actor);
    const fx   = getEffect(actor);

    // One config read per pass: shouldSkip, uniforms, style and clip all
    // consume it (this runs once per frame during interactive resizes).
    const cfg = buildConfig();

    if (shouldSkip(win, cfg)) {
        // Soft removal: keep signals + ActorData so unmaximize / fullscreen
        // exit / list changes can bring the effect back via the next trigger.
        if (data) onRemoveEffect(actor, true);
        return;
    }

    // Not skipped but no effect attached: either a fresh window or one that
    // was soft-removed.  onAddEffect() (re)creates the effect and ends by
    // calling refreshRoundedCorners() again with fx present, so there is no
    // recursion.
    if (!fx) {
        onAddEffect(actor);
        return;
    }
    // Restore the effect unless the minimize handler disabled it - the
    // unminimize paths own re-enabling in that case (a settings change while
    // minimized must not reactivate the shader mid-lamp).
    if (!fx.enabled && !win.minimized)
        fx.enabled = true;

    const geom = shadowGeometry(win);
    fx.updateUniforms(geom.sc, cfg, computeBounds(actor));

    if (data) {
        data.lastScale = geom.sc;

        // Reconcile with the custom-shadow setting (toggleable at runtime)
        const wantShadow = getB('custom-shadow');
        if (wantShadow && !data.shadow) {
            data.shadow = createShadow(actor);
            syncShadowVisibility(actor);
        } else if (!wantShadow && data.shadow) {
            destroyShadow(data);
        }

        // One shared geometry so pad/frame can never diverge between the
        // clip's [pad, pad] origin and the shadow actor's position.
        if (data.shadow) {
            refreshShadowStyle(actor, data.shadow, geom, cfg);
            refreshShadowClip(actor, data.shadow, geom, cfg);
            positionShadow(actor, data.shadow, geom);
        }
    }
}

/** Refresh the shadow style / position for a single actor. */
function refreshFocus(actor) {
    const data = _actorMap.get(actor);
    if (data?.shadow)
        refreshShadowStyle(actor, data.shadow);
}

/** Remove and re-add the effect for a window actor. */
function refreshAll() {
    for (const actor of global.get_window_actors())
        refreshRoundedCorners(actor);
}

/** When windows are re-stacked, keep shadow actors sorted below their windows. */
function onRestacked() {
    for (const actor of global.get_window_actors()) {
        const data = _actorMap.get(actor);
        if (actor.visible && data?.shadow)
            global.windowGroup.set_child_below_sibling(data.shadow, actor);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Global signal management
// ─────────────────────────────────────────────────────────────────────────────

function addConnection(obj, signal, cb) {
    _connections.push({ object: obj, id: obj.connect(signal, cb) });
}

function removeConnections(obj) {
    let i = _connections.length;
    while (i--) {
        const c = _connections[i];
        if (!obj || c.object === obj) {
            try { c.object.disconnect(c.id); } catch (_) {}
            _connections.splice(i, 1);
        }
    }
}

function disconnectAll() {
    for (const c of _connections) {
        try { c.object.disconnect(c.id); } catch (_) {}
    }
    _connections = [];
}

/**
 * One-shot deferred connection, tracked in the global connection list so
 * disable() tears it down if it never fires.  The object must not carry any
 * other tracked global connection (true for the deferral targets: a fresh
 * WindowActor or Meta.Window that has not been wired up yet).
 */
function connectOnce(obj, signal, cb) {
    addConnection(obj, signal, (...args) => {
        removeConnections(obj);
        cb(...args);
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-window signal setup / teardown
// ─────────────────────────────────────────────────────────────────────────────

function attachWindowSignals(actor) {
    const data = _actorMap.get(actor);
    if (data?.signalsAttached)
        return;

    if (!data) return;

    const addWinConn = (obj, sig, cb) => {
        if (obj) data.connections.push({ obj, id: obj.connect(sig, cb) });
    };

    const win     = actor.metaWindow;
    const texture = getWindowTexture(actor);

    // Geometry triggers all funnel through queueRefresh(): one geometry
    // change fires several of these in the same frame (actor notify::size,
    // texture size-changed, win size-changed for frame-only changes such as
    // Chromium/Electron CSD margin updates), and the coalesced BEFORE_REDRAW
    // refresh runs once with position, clip and style updated atomically.
    const queue = () => { if (actor.metaWindow) queueRefresh(actor); };
    addWinConn(actor, 'notify::size', queue);
    if (texture)
        addWinConn(texture, 'size-changed', queue);
    addWinConn(win, 'size-changed', queue);

    // Fires every frame during a drag: cheap path (move the shadow only -
    // the clip depends on frame size, not position).  If the window crossed
    // to a monitor with a different scale, pad/clip/style are all stale →
    // full refresh.
    addWinConn(win, 'position-changed', () => {
        if (!actor.metaWindow) return;
        const data = _actorMap.get(actor);
        if (!data) return;
        if (data.lastScale && scaleFactor(actor.metaWindow) !== data.lastScale)
            queueRefresh(actor);
        else
            positionShadow(actor, data.shadow);
    });

    // Fullscreen state changed (may not cause a size change)
    addWinConn(win, 'notify::fullscreen', queue);
    // Focus changed → update shadow style (style caching makes this cheap)
    addWinConn(win, 'notify::appears-focused',() => { if (actor.metaWindow) refreshFocus(actor); });
    // Monitor / workspace change → scale may have changed, full refresh
    addWinConn(win, 'workspace-changed', queue);

    // Transform / visibility watcher: hide the shadow while the actor is
    // animated (minimize, unminimize, maximize size-change, extension
    // effects) and reveal it - repositioned - the moment it is at rest.
    // These fire per animation frame; syncShadowVisibility early-outs when
    // the state is unchanged, so the steady cost is a few property reads.
    const sync = () => { if (actor.metaWindow) syncShadowVisibility(actor); };
    for (const prop of ['scale-x', 'scale-y',
                        'translation-x', 'translation-y', 'visible'])
        addWinConn(actor, `notify::${prop}`, sync);

    // Mirror opacity so fade animations (opacity-only map/close effects)
    // don't show a full-strength shadow around a translucent window.
    // Opacity mirroring is safe - unlike scale/translation it cannot desync
    // shadow and window geometry.
    addWinConn(actor, 'notify::opacity', () => {
        const d = _actorMap.get(actor);
        // Only when shown and actually changed: a hidden shadow needs no
        // redraw, and syncShadowVisibility re-syncs opacity on reveal.
        if (d?.shadow?.visible && d.shadow.opacity !== actor.opacity)
            d.shadow.opacity = actor.opacity;
    });

    if (data)
        data.signalsAttached = true;
}

function applyEffectTo(actor) {
    if (!actor?.metaWindow)
        return;

    if (_actorMap.has(actor) || getEffect(actor)) {
        refreshRoundedCorners(actor);
        attachWindowSignals(actor);
        return;
    }

    // Wayland / XWayland windows may not have a surface child yet.
    if (!actor.get_first_child?.()) {
        connectOnce(actor, 'notify::first-child', () => applyEffectTo(actor));
        return;
    }

    if (!getWindowTexture(actor)) {
        // The compositor texture is not ready yet.  This happens with Qt /
        // OpenGL-accelerated X11 apps (VirtualBox, Qt-GL, some Chromium builds)
        // where the window is mapped before its first paint arrives.
        // Wait for the actor's size to change (first paint / resize), then retry.
        connectOnce(actor, 'notify::size', () => applyEffectTo(actor));
        return;
    }

    // Add the effect FIRST, then connect signals. If signals were connected
    // before the effect, adding the effect could trigger notify::size
    // synchronously, causing re-entrant calls to refreshRoundedCorners
    // before _actorMap has been populated.
    onAddEffect(actor);
    attachWindowSignals(actor);
}

function applyEffectToWindow(win) {
    if (!win)
        return;

    const actor = win.get_compositor_private?.();
    if (actor) {
        applyEffectTo(actor);
        return;
    }

    // Tracked like the actor deferrals so disable() cleans it up; keeps
    // waiting if the property notifies with a null value.
    addConnection(win, 'notify::compositor-private', () => {
        const nextActor = win.get_compositor_private?.();
        if (!nextActor)
            return;

        removeConnections(win);
        applyEffectTo(nextActor);
    });
}

function removeEffectFrom(actor) {
    // Clear any pending one-shot deferrals for this window so they don't
    // fire after the window is gone.
    removeConnections(actor);
    if (actor.metaWindow)
        removeConnections(actor.metaWindow);
    onRemoveEffect(actor);
}

// ─────────────────────────────────────────────────────────────────────────────
// Global enable / disable
// ─────────────────────────────────────────────────────────────────────────────

function enableEffect() {
    // Apply to all existing windows
    for (const actor of global.get_window_actors())
        applyEffectTo(actor);

    // New window created
    addConnection(global.display, 'window-created',
        (_, win) => {
            applyEffectToWindow(win);
        });

    // Window closed
    addConnection(global.windowManager, 'destroy',
        (_, actor) => removeEffectFrom(actor));

    // Minimise: hide the shadow up front (covers magic-lamp minimize, which
    // deforms the actor without touching scale/translation, so the transform
    // watcher cannot see it) and disable the corner effect for the animation.
    addConnection(global.windowManager, 'minimize',
        (_, actor) => {
            const data = _actorMap.get(actor);
            if (data?.shadow)
                data.shadow.visible = false;
            const fx = getEffect(actor);
            if (fx) fx.enabled = false;
        });

    // Unminimise: restore the corner effect.  The shadow is NOT shown here -
    // the transform watcher (syncShadowVisibility) reveals it in the same
    // frame the unminimize animation lands, avoiding the drift artifact of a
    // shadow visible mid-animation.  For the Magic-Lamp extension the actor
    // is deformed with scale/translation untouched, so wait until the lamp
    // animation is nearly finished before showing the shadow.
    addConnection(global.windowManager, 'unminimize',
        (_, actor) => {
            const data = _actorMap.get(actor);
            const fx   = getEffect(actor);

            const lamp = actor.get_effect('unminimize-magic-lamp-effect');
            if (lamp && data?.shadow && fx) {
                data.shadow.visible = false;
                const timer = lamp.timerId;
                if (timer) {
                    // Track the connection in data.connections so a destroy
                    // or extension disable mid-lamp disconnects it (clean
                    // teardown); re-check the window state when it fires -
                    // the shadow/effect may be gone by then.
                    const conn = { obj: timer, id: 0 };
                    conn.id = timer.connect('new-frame', src => {
                        if (src.get_progress() <= 0.98)
                            return;
                        src.disconnect(conn.id);
                        const idx = data.connections.indexOf(conn);
                        if (idx !== -1)
                            data.connections.splice(idx, 1);

                        const d = _actorMap.get(actor);
                        if (d?.shadow)
                            d.shadow.visible = true;
                        const effect = getEffect(actor);
                        if (effect)
                            effect.enabled = true;
                    });
                    data.connections.push(conn);
                }
                return;
            }

            // Standard unminimise: the watcher shows the shadow at rest
            if (fx) fx.enabled = true;
        });

    // Window re-stack → reorder shadow actors
    addConnection(global.display, 'restacked', onRestacked);

    // Monitor layout / scale changed → every scale-dependent value (pad,
    // clip, style, shader uniforms) may be stale, and a scale change alone
    // fires none of the per-window geometry signals.
    addConnection(Main.layoutManager, 'monitors-changed', () => refreshAll());

    // System light/dark style changed → repaint so buildConfig() picks the
    // other border colour.  buildConfig() reads the scheme live, so this is
    // purely a repaint trigger; skip it while theme-aware borders are off
    // (the colour cannot change then, and enabling the toggle later repaints
    // via the settings 'changed' debounce below).
    addConnection(St.Settings.get(), 'notify::color-scheme', () => {
        if (getB('theme-aware-border'))
            refreshAll();
    });

    // Settings changed → reapply all with debounce to prevent slider lag
    addConnection(_settings, 'changed', () => {
        if (_settingsTimeoutId) {
            GLib.source_remove(_settingsTimeoutId);
            _settingsTimeoutId = 0;
        }
        _settingsTimeoutId = GLib.timeout_add(GLib.PRIORITY_DEFAULT, 100, () => {
            _appTypeCache.clear();
            _blacklistCache = null;
            refreshAll();
            _settingsTimeoutId = 0;
            return GLib.SOURCE_REMOVE;
        });
    });
}

function disableEffect() {
    for (const actor of global.get_window_actors())
        removeEffectFrom(actor);
    disconnectAll();

    if (_settingsTimeoutId) {
        GLib.source_remove(_settingsTimeoutId);
        _settingsTimeoutId = 0;
    }

    _appTypeCache.clear();
    _blacklistCache = null;
    if (_mutterSettings && _mutterSettingsConn) {
        _mutterSettings.disconnect(_mutterSettingsConn);
        _mutterSettingsConn = 0;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Extension class
// ─────────────────────────────────────────────────────────────────────────────

export default class RoundedWindowCornersExtension extends Extension {

    #startupConnection = null;

    enable() {
        _settings = this.getSettings();
        logDbg('Enabling…');

        if (Main.layoutManager._startingUp) {
            // GNOME Shell is still starting up – wait until it is ready
            this.#startupConnection = Main.layoutManager.connect(
                'startup-complete', () => {
                    enableEffect();
                    Main.layoutManager.disconnect(this.#startupConnection);
                    this.#startupConnection = null;
                },
            );
        } else {
            enableEffect();
        }
    }

    disable() {
        logDbg('Disabling…');

        if (this.#startupConnection !== null) {
            Main.layoutManager.disconnect(this.#startupConnection);
            this.#startupConnection = null;
        }

        disableEffect();
        _settings = null;
        _mutterSettings = null;
        _fractionalScaling = null;
    }
}
