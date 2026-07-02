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
 * disable()
 *   ├─ disableEffect()    → removeEffectFrom() every actor
 *   └─ uninitPrefs()
 */

import Gio from 'gi://Gio';
import GLib from 'gi://GLib';
import GObject from 'gi://GObject';
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
//   propertyBindings: GObject.Binding[],
//   signalsAttached : boolean,
//   timeoutId      : GLib.Source | 0,
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
            getD('border-red'),
            getD('border-green'),
            getD('border-blue'),
            getD('border-alpha'),
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

function isListedWindow(identifiers, list) {
    const lookup = new Set(
        identifiers
            .map(id => normalizeAppId(id))
            .filter(Boolean),
    );

    for (const item of list) {
        const normalized = normalizeAppId(item);
        if (normalized && lookup.has(normalized))
            return true;
    }

    return false;
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
function shouldSkip(win) {
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
    const blacklist     = getS('blacklist');
    const whitelistMode = getB('whitelist-mode');
    const isListed      = isListedWindow(identifiers, blacklist);

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
    // rounded corners in those states
    const cfg = buildConfig();
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

    positionShadow(actor, shadow);

    // Clip-shadow effect prevents shadow from showing inside the window
    shadow.add_effect_with_name(CLIP_SHADOW_EFFECT, new ClipShadowEffect());

    global.windowGroup.insert_child_below(shadow, actor);

    refreshShadowStyle(actor, shadow);
    return shadow;
}

/** Update the CSS style of an existing shadow actor. */
function refreshShadowStyle(actor, shadowActor, geom = null) {
    if (!shadowActor) return;

    const win        = actor.metaWindow;
    const sc         = geom?.sc ?? scaleFactor(win);
    const origScale  = St.ThemeContext.get_for_stage(global.stage).scale_factor;
    const cssScale   = sc / origScale;

    const pad    = SHADOW_PADDING * cssScale;
    const cfg    = buildConfig();
    const scfg   = shadowConfig(win.appears_focused);

    // Compute the CSS border-radius to match the shader's squircle.
    // The shader uses:  exponent = smoothing*10+2,  radius = outerR * 0.5 * exponent
    // CSS border-radius only supports circular arcs (exponent=2).
    // A squircle extends further along diagonals than a circle of the same radius,
    // so using the shader's radius for the CSS guarantees the transparent background
    // never shows through the shader's transparent corners.
    const exponent    = cfg.smoothing * 10 + 2;
    const shaderR     = cfg.cornerRadius * 0.5 * exponent;
    const radius      = shaderR * cssScale;

    const inner = shadowActor.get_first_child();
    if (!inner) return;

    // Hide shadow when maximised/fullscreened (unless keep-shadow-maximized)
    const isMax  = win.maximizedHorizontally || win.maximizedVertically;
    const isFull = win.fullscreen;
    const hide   = (isMax || isFull) && !getB('keep-shadow-maximized');

    const shadowStyle = `padding: ${pad}px;`;

    // Use transparent background — NEVER white.  The box-shadow alone provides
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

    // The style strings only depend on config/focus/maximize/scale — not on
    // the frame geometry — so during resizes and drags they are identical
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
function refreshShadowClip(actor, shadowActor, geom = null) {
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

    const sw = frame.width  + 2 * pad;
    const sh = frame.height + 2 * pad;
    if (sw <= 0 || sh <= 0) return;

    const cfg    = buildConfig();
    const outerR = cfg.cornerRadius * sc;

    // Use the same exponent / radius formulae as RoundedCornersEffect
    // so the clip contour is identical to the rounded corners shader.
    let exponent = cfg.smoothing * 10 + 2;
    let radius   = outerR * 0.5 * exponent;

    const rawX1 = pad;
    const rawY1 = pad;
    const rawX2 = pad + frame.width;
    const rawY2 = pad + frame.height;

    // Account for padding inset (same as RoundedCornersEffect)
    const bx1 = rawX1 + cfg.padding.left   * sc;
    const by1 = rawY1 + cfg.padding.top    * sc;
    const bx2 = rawX2 - cfg.padding.right  * sc;
    const by2 = rawY2 - cfg.padding.bottom * sc;

    const maxR = Math.min(bx2 - bx1, by2 - by1) / 2;
    if (maxR > 0 && radius > maxR) {
        exponent *= maxR / radius;
        radius    = maxR;
    }

    // Pass sw/sh explicitly so the shader step uniform is correct even when
    // the shadow actor's BindConstraints haven't been resolved yet.
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
            bindings: [],
            connections: [],
            signalsAttached: false,
            timeoutId: 0,
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

/** Attach the RoundedCornersEffect and a custom shadow to a window actor. */
function onAddEffect(actor) {
    logDbg(`Adding effect to "${actor.metaWindow.title}"`);

    const win = actor.metaWindow;
    if (shouldSkip(win)) {
        logDbg(`  → skipped`);
        // Track the window anyway: with signals attached, a later geometry
        // change (e.g. the window opened maximized and gets unmaximized)
        // re-evaluates shouldSkip() and adds the effect then.
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

    let shadow = null;
    let bindings = [];

    if (getB('custom-shadow')) {
        shadow = createShadow(actor);

        // Mirror visibility / transform from window to shadow.
        // NOTE: never add 'x'/'y' here — the shadow's position is owned by
        // positionShadow() (frame-rect anchoring).  Binding position to the
        // WindowActor would silently override it and resurrect the
        // Chromium/Electron shadow-offset bug.
        for (const prop of ['pivot-point', 'translation-x', 'translation-y',
                             'scale-x', 'scale-y', 'visible']) {
            bindings.push(actor.bind_property(prop, shadow, prop,
                GObject.BindingFlags.SYNC_CREATE));
        }
    }

    // Reuses the entry on re-add after a soft removal (unmaximize etc.) so
    // the still-connected per-window signals are preserved.
    const data = ensureActorData(actor);
    data.shadow = shadow;
    data.bindings = bindings;
    data.lastScale = 0;
    data.lastShadowRect = null;
    data.lastShadowStyle = null;
    data.lastInnerStyle = null;

    // Attach signals here (idempotent) so windows added later via
    // refreshAll() — e.g. removed from the blacklist — also get their
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

    // Unbind property mirrors (they target the shadow, which is destroyed)
    for (const b of data.bindings)
        b.unbind();
    data.bindings = [];

    // Remove and destroy the custom shadow actor
    if (data.shadow) {
        try {
            if (data.shadow.get_parent())
                global.windowGroup.remove_child(data.shadow);
            data.shadow.clear_effects();
            data.shadow.destroy();
        } catch (_) {
            // Shadow actor may already be destroyed
        }
        data.shadow = null;
    }

    if (data.timeoutId) {
        GLib.source_remove(data.timeoutId);
        data.timeoutId = 0;
    }

    if (data.laterId) {
        global.compositor.get_laters().remove(data.laterId);
        data.laterId = 0;
    }

    if (keepSignals) {
        data.lastScale = 0;
        data.lastShadowRect = null;
        data.lastShadowStyle = null;
        data.lastInnerStyle = null;
    } else {
        _actorMap.delete(actor);
    }
}

/** Recompute and push all shader uniforms for a single window. */
function refreshRoundedCorners(actor) {
    const win = actor.metaWindow;
    if (!win) return;

    const data = _actorMap.get(actor);
    const fx   = getEffect(actor);

    if (shouldSkip(win)) {
        // Soft removal: keep signals + ActorData so unmaximize / fullscreen
        // exit / list changes can bring the effect back via the next trigger.
        if (data) onRemoveEffect(actor, true);
        return;
    }

    // Not skipped but no effect attached: either a fresh window or one that
    // was soft-removed.  onAddEffect() (re)creates the effect + shadow and
    // ends by calling refreshRoundedCorners() again with fx present, so
    // there is no recursion.
    if (!fx) {
        onAddEffect(actor);
        return;
    }
    if (!fx.enabled) fx.enabled = true;

    const cfg = buildConfig();
    fx.updateUniforms(scaleFactor(win), cfg, computeBounds(actor));

    // Update shadow (one shared geometry so pad/frame can never diverge
    // between the clip's [pad, pad] origin and the actor's position)
    if (data) {
        const geom = shadowGeometry(win);
        refreshShadowStyle(actor, data.shadow, geom);
        refreshShadowClip(actor, data.shadow, geom);
        positionShadow(actor, data.shadow, geom);
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
            c.object.disconnect(c.id);
            _connections.splice(i, 1);
        }
    }
}

function disconnectAll() {
    for (const c of _connections)
        c.object.disconnect(c.id);
    _connections = [];
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

    // Fires every frame during a drag: cheap path (move the shadow only —
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
        const connId = actor.connect('notify::first-child', () => {
            actor.disconnect(connId);
            applyEffectTo(actor);
        });
        return;
    }

    if (!getWindowTexture(actor)) {
        // The compositor texture is not ready yet.  This happens with Qt /
        // OpenGL-accelerated X11 apps (VirtualBox, Qt-GL, some Chromium builds)
        // where the window is mapped before its first paint arrives.
        // Wait for the actor's size to change (first paint / resize), then retry.
        // We disconnect before retrying to avoid double-applying the effect.
        let connId;
        connId = actor.connect('notify::size', () => {
            actor.disconnect(connId);
            applyEffectTo(actor);
        });
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

    let connId;
    connId = win.connect('notify::compositor-private', () => {
        const nextActor = win.get_compositor_private?.();
        if (!nextActor)
            return;

        win.disconnect(connId);
        applyEffectTo(nextActor);
    });
}

function removeEffectFrom(actor) {
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

    // Minimise: always hide shadow + disable effect to prevent the white
    // background of the shadow actor from showing during the animation.
    addConnection(global.windowManager, 'minimize',
        (_, actor) => {
            const data = _actorMap.get(actor);
            if (data?.shadow)
                data.shadow.visible = false;
            const fx = getEffect(actor);
            if (fx) fx.enabled = false;
        });

    // Unminimise: restore shadow + effect.  For the Magic-Lamp extension,
    // wait until the animation is nearly finished before showing the shadow.
    addConnection(global.windowManager, 'unminimize',
        (_, actor) => {
            const data = _actorMap.get(actor);
            const fx   = getEffect(actor);

            const lamp = actor.get_effect('unminimize-magic-lamp-effect');
            if (lamp && data?.shadow && fx) {
                data.shadow.visible = false;
                const timer = lamp.timerId;
                if (timer) {
                    const tid = timer.connect('new-frame', src => {
                        if (src.get_progress() > 0.98) {
                            data.shadow.visible = true;
                            fx.enabled = true;
                            src.disconnect(tid);
                        }
                    });
                }
                return;
            }

            // Standard unminimise (no magic lamp)
            if (data?.shadow)
                data.shadow.visible = true;
            if (fx) fx.enabled = true;
        });

    // Window re-stack → reorder shadow actors
    addConnection(global.display, 'restacked', onRestacked);

    // Settings changed → reapply all with debounce to prevent slider lag
    addConnection(_settings, 'changed', () => {
        if (_settingsTimeoutId) {
            GLib.source_remove(_settingsTimeoutId);
            _settingsTimeoutId = 0;
        }
        _settingsTimeoutId = GLib.timeout_add(GLib.PRIORITY_DEFAULT, 100, () => {
            _appTypeCache.clear();
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
