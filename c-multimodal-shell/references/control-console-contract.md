# Control Console Contract

Use this contract when replacing the template stubs with platform-specific C code.

## Frame Packet

Each model tick should produce a packet with these fields:

- `tick_id`: monotonically increasing unsigned integer for the active process.
- `screenshot_path`: path to a model-facing screenshot that may include a grid.
- `mouse_x`, `mouse_y`: current pointer coordinates in screen pixels.
- `buttons`: ordered controls with `placeholder`, `label`, `x`, `y`, `width`, and `height`.
- `overlay_message`: optional state update shown while generation continues.

## Placeholder Rules

- Use `BTN_01`, `BTN_02`, etc. for detected buttons.
- Use `MOUSE_CURRENT` for the current pointer location.
- Use `GRID_A1`, `GRID_B1`, etc. only for coarse regions in the temporary grid image.
- Never ask the model to memorize raw coordinates when a placeholder is available.

## Streaming Rule

The GGUF adapter should stream tokens or partial responses. If a new one-second screenshot arrives while the model is responding, send an overlay/frame update to the stream rather than killing the current request.

## Safety Gate

Keep actual mouse and keyboard operations behind one C function that receives a reviewed action struct. This keeps OS-specific APIs isolated and lets a caller add confirmation, allowlists, or dry-run behavior.
