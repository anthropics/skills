// GLTF Calibration Helpers (Three.js)
// Purpose: make the "reference frame contract" visible and provable in ~60 seconds.
//
// Usage (in your project):
//   import { attachGltfCalibrationHelpers } from './gltf-calibration-helpers.mjs';
//   attachGltfCalibrationHelpers({ scene, root: modelRoot, label: 'Hero' });
//
// Notes:
// - In Three.js, Object3D "forward" is local -Z.
// - getWorldDirection() returns the object's -Z axis in world space.

import * as THREE from 'three';

const DEFAULTS = Object.freeze({
  axisSize: 0.6,
  forwardArrowLength: 1.2,
  forwardArrowColor: 0xff00ff,
  boundsColor: 0xff00ff,
  labelColor: '#ff00ff',
  labelFont: '12px ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, sans-serif',
  // Local position on the model root where we place the arrow + label.
  anchorLocal: new THREE.Vector3(0, 1.2, 0),
});

function ensureLayer(root) {
  const layer = new THREE.Group();
  layer.name = '__gltf_calibration_helpers__';
  root.add(layer);
  return layer;
}

function removeExisting(root) {
  const existing = root.getObjectByName('__gltf_calibration_helpers__');
  if (existing) root.remove(existing);
}

function makeLabelSprite(text, { color, font }) {
  const canvas = document.createElement('canvas');
  const ctx = canvas.getContext('2d');
  ctx.font = font;
  const paddingX = 10;
  const paddingY = 6;
  const metrics = ctx.measureText(text);
  const w = Math.ceil(metrics.width + paddingX * 2);
  const h = Math.ceil(20 + paddingY * 2);
  canvas.width = Math.max(1, w);
  canvas.height = Math.max(1, h);

  // background
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  // text
  ctx.font = font;
  ctx.fillStyle = color;
  ctx.textBaseline = 'middle';
  ctx.fillText(text, paddingX, canvas.height / 2);

  const tex = new THREE.CanvasTexture(canvas);
  tex.colorSpace = THREE.SRGBColorSpace;
  tex.needsUpdate = true;
  const mat = new THREE.SpriteMaterial({ map: tex, transparent: true });
  const sprite = new THREE.Sprite(mat);
  sprite.scale.set(1.2, 0.3, 1);
  sprite.renderOrder = 999;
  return sprite;
}

export function attachGltfCalibrationHelpers({
  scene = null,
  root,
  label = 'model',
  axisSize = DEFAULTS.axisSize,
  forwardArrowLength = DEFAULTS.forwardArrowLength,
  forwardArrowColor = DEFAULTS.forwardArrowColor,
  boundsColor = DEFAULTS.boundsColor,
  anchorLocal = DEFAULTS.anchorLocal,
  showGrid = false,
  gridSize = 10,
  gridDivisions = 10,
  log = true,
  replaceExisting = true,
} = {}) {
  if (!root) throw new Error('attachGltfCalibrationHelpers: missing { root }');
  if (replaceExisting) removeExisting(root);

  const layer = ensureLayer(root);

  // Helpers: axes at the root origin, bounds in world space, and a forward arrow (local -Z).
  const axes = new THREE.AxesHelper(axisSize);
  layer.add(axes);

  const box = new THREE.Box3().setFromObject(root);
  const boxHelper = new THREE.Box3Helper(box, boundsColor);
  layer.add(boxHelper);

  const localForward = new THREE.Vector3(0, 0, -1);
  const arrow = new THREE.ArrowHelper(localForward, anchorLocal.clone(), forwardArrowLength, forwardArrowColor);
  layer.add(arrow);

  const labelSprite = makeLabelSprite(label, { color: DEFAULTS.labelColor, font: DEFAULTS.labelFont });
  labelSprite.position.copy(anchorLocal).add(new THREE.Vector3(0, 0.45, 0));
  layer.add(labelSprite);

  if (showGrid && scene) {
    const grid = new THREE.GridHelper(gridSize, gridDivisions, 0xffffff, 0xffffff);
    grid.material.opacity = 0.18;
    grid.material.transparent = true;
    grid.position.y = 0.001;
    grid.name = '__gltf_calibration_grid__';
    scene.add(grid);
  }

  // One-shot diagnostics.
  root.updateMatrixWorld(true);
  const worldForward = new THREE.Vector3();
  root.getWorldDirection(worldForward);
  const worldPos = new THREE.Vector3();
  root.getWorldPosition(worldPos);
  const size = box.getSize(new THREE.Vector3());

  if (log) {
    // Note: getWorldDirection is root's -Z axis.
    // If gameplay forward is +Z, and the mesh runs backward, a common fix is yawOffset = Math.PI.
    console.log(`[calibrate] ${label}`);
    console.log('  worldPos:', worldPos.toArray());
    console.log('  bboxSize:', size.toArray());
    console.log('  worldForward(-Z):', worldForward.toArray());
  }

  return {
    layer,
    axes,
    boxHelper,
    arrow,
    labelSprite,
    recomputeBounds() {
      box.setFromObject(root);
      return box;
    },
  };
}
