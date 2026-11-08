# Component CSS Reference

Copy-paste CSS for all Cyber Garage components.

## Nav Bar

```css
.nav {
  position: fixed; top: 2px; left: 0; right: 0; z-index: 100;
  backdrop-filter: blur(16px); background: rgba(3,7,16,0.85);
  border-bottom: 1px solid rgba(127,200,255,0.06);
  padding: 0 24px; height: 56px;
  display: flex; align-items: center; justify-content: space-between;
}
.nav-brand {
  font-family: 'JetBrains Mono', monospace; font-weight: 700;
  font-size: 18px; color: #7fc8ff; letter-spacing: 2px; text-decoration: none;
}
.nav-links { display: flex; gap: 16px; }
.nav-links a { font-size: 14px; color: #6b8299; text-decoration: none; transition: color 0.2s; }
.nav-links a:hover, .nav-links a.active { color: #7fc8ff; }
```

## Page Title (Gradient)

```css
.page-title {
  font-family: 'JetBrains Mono', monospace; font-size: clamp(24px, 4vw, 36px);
  font-weight: 700; margin-bottom: 8px;
  background: linear-gradient(135deg, #7fc8ff, #a78bfa);
  -webkit-background-clip: text; -webkit-text-fill-color: transparent;
}
/* Admin gold: linear-gradient(135deg, #facc15, #eab308) */
.page-subtitle { color: #6b8299; font-size: 14px; margin-bottom: 24px; }
```

## Summary Card

```css
.summary-card {
  background: rgba(127,200,255,0.02); border: 1px solid rgba(127,200,255,0.06);
  border-radius: 12px; padding: 20px; transition: border-color 0.3s;
}
.summary-card:hover { border-color: rgba(127,200,255,0.15); }
.summary-label {
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  text-transform: uppercase; letter-spacing: 0.1em; color: #6b8299; margin-bottom: 8px;
}
.summary-value {
  font-family: 'JetBrains Mono', monospace; font-size: 32px; font-weight: 700;
  color: #7fc8ff; text-shadow: 0 0 30px rgba(127,200,255,0.15);
}
.summary-value.green { color: #4ade80; text-shadow: 0 0 30px rgba(74,222,128,0.15); }
.summary-value.red { color: #f87171; }
```

## Chart Section (Content Card)

```css
.chart-section {
  background: rgba(127,200,255,0.02); border: 1px solid rgba(127,200,255,0.06);
  border-radius: 12px; padding: 24px; margin-bottom: 32px;
}
.section-title {
  font-family: 'JetBrains Mono', monospace; font-size: 12px;
  text-transform: uppercase; letter-spacing: 0.1em; color: #7fc8ff; margin-bottom: 16px;
}
```

## Data Table

```css
.data-table { width: 100%; border-collapse: collapse; }
.data-table th {
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  text-transform: uppercase; letter-spacing: 0.05em; color: #6b8299;
  padding: 12px 8px; text-align: left; border-bottom: 1px solid rgba(127,200,255,0.08);
}
.data-table td {
  font-family: 'JetBrains Mono', monospace; font-size: 13px;
  padding: 12px 8px; color: #c8d6e5; border-bottom: 1px solid rgba(127,200,255,0.04);
}
.data-table tr:hover td { background: rgba(127,200,255,0.02); }
```

## Badges

```css
.badge {
  display: inline-block; padding: 3px 10px; border-radius: 6px;
  font-size: 11px; font-weight: 600; font-family: 'JetBrains Mono', monospace;
}
.badge-success { background: rgba(34,197,94,0.15);  color: #4ade80; }
.badge-danger  { background: rgba(239,68,68,0.15);  color: #f87171; }
.badge-warning { background: rgba(234,179,8,0.15);  color: #facc15; }
.badge-info    { background: rgba(127,200,255,0.1);  color: #7fc8ff; }
.badge-muted   { background: rgba(107,130,153,0.15); color: #6b8299; }
.badge-admin   { background: #facc15; color: #030710; font-weight: 700; }
```

## Buttons — Tab Switcher

```css
.tab-btn {
  background: rgba(127,200,255,0.04); border: 1px solid rgba(127,200,255,0.08);
  color: #6b8299; padding: 7px 16px; border-radius: 6px;
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  cursor: pointer; transition: all 0.2s;
}
.tab-btn:hover { border-color: rgba(127,200,255,0.2); color: #e2e8f0; }
.tab-btn.active { background: rgba(127,200,255,0.1); border-color: #7fc8ff; color: #7fc8ff; }
```

## Buttons — Color-Coded Action

Replace `COLOR_RGB` and `COLOR_HEX`:

```css
.action-btn {
  background: rgba(COLOR_RGB, 0.1); border: 1px solid rgba(COLOR_RGB, 0.25);
  color: COLOR_HEX; padding: 6px 16px; border-radius: 6px;
  font-size: 12px; font-family: 'JetBrains Mono', monospace;
  cursor: pointer; transition: all 0.15s;
}
.action-btn:hover { background: rgba(COLOR_RGB, 0.2); }
```

## Buttons — Toggle (ON/OFF)

```css
.toggle-btn {
  padding: 4px 14px; border-radius: 6px; font-size: 11px; font-weight: 700;
  font-family: 'JetBrains Mono', monospace; border: 1px solid rgba(127,200,255,0.15);
  cursor: pointer; transition: all 0.15s; min-width: 50px; text-align: center;
}
.toggle-btn.on  { background: rgba(74,222,128,0.15); color: #4ade80; border-color: rgba(74,222,128,0.3); }
.toggle-btn.off { background: rgba(248,113,113,0.1);  color: #f87171; border-color: rgba(248,113,113,0.2); }
```

## Buttons — CTA

```css
.btn-cta {
  padding: 10px 24px; border-radius: 10px; border: none;
  background: linear-gradient(135deg, #3b82f6, #6366f1);
  color: #fff; font-size: 14px; font-weight: 500; cursor: pointer;
}
.btn-outline {
  padding: 10px 24px; border-radius: 10px;
  background: rgba(127,200,255,0.08); color: #7fc8ff;
  border: 1px solid rgba(127,200,255,0.15);
  font-family: 'JetBrains Mono', monospace; font-size: 13px; font-weight: 600;
  cursor: pointer; transition: all 0.2s;
}
.btn-outline:hover { background: rgba(127,200,255,0.15); }
```

## Buttons — Config (small)

```css
.cfg-btn {
  padding: 4px 12px; border-radius: 6px; font-size: 11px;
  font-family: 'JetBrains Mono', monospace;
  border: 1px solid rgba(127,200,255,0.15); cursor: pointer;
  background: rgba(127,200,255,0.06); color: #6b8299; transition: all 0.15s;
}
.cfg-btn:hover { border-color: rgba(127,200,255,0.3); color: #e2e8f0; }
.cfg-btn.active { background: rgba(250,204,21,0.15); color: #facc15; border-color: rgba(250,204,21,0.3); }
```

## Modal

```css
.modal-overlay {
  display: none; position: fixed; inset: 0; z-index: 10000;
  background: rgba(0,0,0,0.75); backdrop-filter: blur(6px);
  align-items: flex-start; justify-content: center;
  padding: 40px 20px; overflow-y: auto;
}
.modal-overlay.open { display: flex; }
.modal-body {
  background: #0d1117; border: 1px solid rgba(ACCENT_RGB, 0.15);
  border-radius: 14px; max-width: 640px; width: 100%;
  padding: 24px; position: relative;
  box-shadow: 0 20px 60px rgba(0,0,0,0.5);
}
.modal-close {
  position: absolute; top: 14px; right: 14px;
  background: none; border: none; color: #6b8299;
  font-size: 22px; cursor: pointer; padding: 4px 8px; line-height: 1;
}
.modal-title {
  font-family: 'JetBrains Mono', monospace; font-size: 16px;
  font-weight: 700; color: ACCENT_HEX;
}
```

## Form Inputs

```css
.form-input {
  background: rgba(ACCENT_RGB, 0.06); border: 1px solid rgba(ACCENT_RGB, 0.15);
  color: #e2e8f0; padding: 6px 10px; border-radius: 8px;
  font-size: 12px; font-family: 'JetBrains Mono', monospace; outline: none;
}
.form-select {
  background: #0a0e1a; color: #e2e8f0;
  border: 1px solid rgba(127,200,255,0.15); border-radius: 8px;
  padding: 6px 12px; font-family: 'JetBrains Mono', monospace; font-size: 12px;
}
input[type="range"] { width: 100%; accent-color: ACCENT_HEX; }
```

## Auth Bar

```css
.auth-bar {
  display: flex; align-items: center; gap: 12px; padding: 8px 16px;
  border-radius: 10px; background: rgba(127,200,255,0.04);
  border: 1px solid rgba(127,200,255,0.06); margin-bottom: 16px;
}
.auth-bar-name { font-family: 'JetBrains Mono', monospace; font-size: 13px; color: #7fc8ff; }
```

## Status Dots

```css
.status-dot { display: inline-block; width: 8px; height: 8px; border-radius: 50%; margin-right: 6px; }
.status-dot.ok   { background: #4ade80; box-shadow: 0 0 8px rgba(74,222,128,0.5); }
.status-dot.fail { background: #f87171; }
```

## Alert Banners

```css
.banner-error {
  padding: 14px 18px; border-radius: 10px;
  background: rgba(248,113,113,0.12); border: 1px solid rgba(248,113,113,0.4);
  color: #f87171;
}
.banner-warn {
  padding: 14px 18px; border-radius: 12px;
  background: rgba(255,152,0,0.1); border: 1px solid rgba(255,152,0,0.25);
  color: #ffb74d;
}
.banner-info {
  padding: 14px 18px; border-radius: 10px;
  background: rgba(250,204,21,0.06); border: 1px solid rgba(250,204,21,0.15);
}
```

## Icon Container

```css
.icon-box {
  width: 42px; height: 42px; border-radius: 12px;
  background: linear-gradient(135deg, rgba(127,200,255,0.15), rgba(99,102,241,0.15));
  display: flex; align-items: center; justify-content: center; font-size: 20px;
}
.icon-box-lg { width: 56px; height: 56px; border-radius: 16px; font-size: 28px; }
```
