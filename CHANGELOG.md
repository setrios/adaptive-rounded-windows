# Changelog

## v2.3.0

- Add optional separate border colours for light and dark system themes (toggle in Corners → Border; follows the system Appearance style live).
- Fix the custom shadow being drawn offset on Chromium/Electron windows (Wayland CSD shadow margins) - the shadow is now anchored to the window frame.
- Fix the shadow drifting in from the top-left during minimize/unminimize/maximize animations - it now hides while the window animates and appears the moment it lands.
- Fix windows permanently losing rounded corners after being maximized or fullscreened.
- Apply the custom-shadow toggle and exception-list changes live to already-open windows.
- Fix stale shadow scale when a window moves between monitors with different scales; refresh on monitor layout changes.
- Fix teardown leaks and errors (Magic Lamp minimize interplay, windows still setting up, extension disable).
- Performance: coalesce refreshes to one per frame, cache settings and exception-list reads, and skip redundant CSS and geometry work during resizes and drags.

## v2.2.0

- Add GNOME 50 compatibility fixes for the rounded-corners shader path.
- Round Wayland-native, X11/XWayland, Qt, Electron, Firefox, VS Code, Thunderbird, and LibreOffice top-level windows more reliably.
- Match windows using WM_CLASS, Wayland app IDs, and desktop IDs.
- Avoid duplicate effect and shadow attachment during complex window startup.
- Clarify installation and Wayland limitations in the documentation.