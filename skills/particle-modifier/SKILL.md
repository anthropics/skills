---
name: particle-modifier
description: Cocos Creator 2.4.x 粒子系统修饰器开发框架。用于创建、使用和调试自定义粒子修饰器，支持修改粒子位置、颜色、大小、旋转、速度等属性。当需要在 Cocos Creator 中实现复杂的粒子效果控制时使用此技能。
version: "1.0"
usage: 当用户请求创建、修改或调试 Cocos Creator 粒子系统修饰器时调用
keywords: [粒子系统, 粒子修饰器, Cocos Creator, 2.4.x, 粒子效果]
---

# 粒子修饰器系统开发指南

## 概述

本技能提供 Cocos Creator 2.4.x 粒子系统的自定义修饰器开发框架。通过编写修饰器类，可以精确控制每个粒子的行为，实现复杂的视觉效果。

## 核心文件结构

```
项目根目录/
├── ParticleModifier.ts           # 粒子修饰器胶水组件（拦截粒子系统更新）
├── ParticleModifierBase.ts       # 修饰器基类（提供钩子方法）
├── SKILL.md                      # 本技能文档
├── js/                           # 引擎核心源码（Cocos Creator 2.4.13）
│   ├── CCParticleAsset.js        # 粒子资源类
│   ├── CCParticleSystem.js       # 粒子系统组件（主组件）
│   ├── particle-simulator.js     # 粒子模拟器（核心逻辑）
│   └── particle-system-assembler.js  # 渲染汇编器
└── examples/
    ├── ColorFadeModifier.ts      # 颜色渐变修饰器示例
    ├── GravityModifier.ts        # 重力修饰器示例
    └── LeafRotationModifier.ts   # 叶子旋转修饰器示例
```

## 快速开始

### 步骤 1：复制核心文件
将 `ParticleModifier.ts` 和 `ParticleModifierBase.ts` 复制到项目的任意目录（建议放在 `assets/scripts/` 下）

### 步骤 2：创建自定义修饰器
创建继承自 `ParticleModifierBase` 的新类，实现 `onParticleUpdate` 方法

### 步骤 3：在编辑器中配置
1. 在粒子系统节点上添加 `ParticleModifier` 组件
2. 添加自定义修饰器组件
3. 配置参数并运行

## 修饰器开发模板

### 基础模板

```typescript
import { IParticle } from "./ParticleModifier";
import ParticleModifierBase from "./ParticleModifierBase";

const { ccclass, property } = cc._decorator;

@ccclass
export class MyCustomModifier extends ParticleModifierBase {
    @property({ tooltip: '执行优先级（数值越小越先执行）' })
    priority: number = 0;

    @property({ tooltip: '属性说明' })
    myProperty: number = 1.0;

    onParticleEmit(particle: IParticle, system: cc.ParticleSystem): void {
        // 粒子发射时调用（可选）
        // 初始化粒子自定义数据
    }

    onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
        // 粒子每帧更新时调用（必需）
        // 更新粒子状态
    }
}
```

### IParticle 接口

```typescript
interface IParticle {
    // 位置
    pos: cc.Vec2;                    // 当前位置（相对于发射器）
    startPos: cc.Vec2;               // 起始位置
    drawPos: cc.Vec2;                // 绘制位置

    // 颜色
    color: cc.Color;                 // 当前颜色
    deltaColor: { r, g, b, a };      // 颜色变化率
    preciseColor: { r, g, b, a };    // 精确颜色（浮点）

    // 大小
    size: number;                    // 当前大小
    deltaSize: number;               // 大小变化率
    aspectRatio: number;             // 宽高比

    // 旋转
    rotation: number;                // 当前旋转角度（度）
    deltaRotation: number;           // 旋转变化率（度/秒）

    // 生命周期
    timeToLive: number;              // 剩余生命周期（秒）

    // Mode A: 重力模式
    dir: cc.Vec2;                    // 速度向量
    radialAccel: number;             // 径向加速度
    tangentialAccel: number;         // 切向加速度

    // Mode B: 半径模式
    angle: number;                   // 当前角度（弧度）
    degreesPerSecond: number;        // 角速度
    radius: number;                  // 当前半径
    deltaRadius: number;             // 半径变化率
}
```

**注意**：IParticle 接口可以被扩展以存储自定义数据，但必须在 `onParticleEmit` 中初始化。

## 技术原理

### 粒子修饰器拦截机制

粒子修饰器系统通过以下方式拦截粒子更新：

1. **获取粒子系统引用**
   ```typescript
   const simulator = (system as any)._simulator;
   ```

2. **保存原始函数**
   ```typescript
   this._originalEmitParticle = simulator.emitParticle;
   this._originalStep = simulator.step;
   ```

3. **覆盖关键函数**
   ```typescript
   simulator.emitParticle = (pos: cc.Vec2) => {
       this._originalEmitParticle.call(simulator, pos);
       this._onParticleEmit(particle);
   };

   simulator.step = (dt: number) => {
       this._originalStep.call(simulator, dt);
       this._onParticleUpdate(particle, dt);
   };
   ```

### aspectRatio 处理逻辑

引擎底层的 `updateParticleBuffer` 函数（`js/particle-simulator.js:257`）：
```javascript
let aspectRatio = particle.aspectRatio;
aspectRatio > 1 ? (height = width / aspectRatio) : (width = height * aspectRatio);
```

这就是长方形图片旋转跳变的根本原因！当 `aspectRatio` 从 >1 变到 <1 时，引擎会切换锚点。

## 常见修饰器模式

### 1. 位置修改

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // X 轴摆动
    particle.pos.x += Math.sin(Date.now() / 1000) * 10 * dt;
}
```

### 2. 颜色渐变

```typescript
// 需要先定义扩展接口
interface IColorFadeOptions extends IParticle {
    maxTimeToLive: number;  // 记录初始生命周期
}

onParticleEmit(particle: IColorFadeOptions, system: cc.ParticleSystem): void {
    particle.maxTimeToLive = particle.timeToLive;
}

onParticleUpdate(particle: IColorFadeOptions, dt: number, system: cc.ParticleSystem): void {
    const lifeRatio = 1 - (particle.timeToLive / particle.maxTimeToLive);
    particle.color.r = Math.floor(255 * lifeRatio);
    particle.color.g = Math.floor(255 * (1 - lifeRatio));
}
```

### 3. 大小呼吸

```typescript
// 基于粒子生命周期计算呼吸效果
interface IBreathingSizeOptions extends IParticle {
    maxTimeToLive: number;  // 记录初始生命周期
    baseSize: number;       // 记录初始大小
}

onParticleEmit(particle: IBreathingSizeOptions, system: cc.ParticleSystem): void {
    particle.maxTimeToLive = particle.timeToLive;
    particle.baseSize = particle.size;
}

onParticleUpdate(particle: IBreathingSizeOptions, dt: number, system: cc.ParticleSystem): void {
    const lifeRatio = 1 - (particle.timeToLive / particle.maxTimeToLive);
    // 基于生命周期的呼吸效果，每个粒子有独立相位
    particle.size = particle.baseSize + Math.sin(lifeRatio * Math.PI * 4) * 20;
}
```

### 4. 3D 旋转（关键）

**⚠️ 重要：aspectRatio 跳变问题**

长方形图片旋转时会出现视觉跳变，因为引擎底层硬切换锚点：
- `aspectRatio > 1`：宽度固定为 `particle.size`
- `aspectRatio < 1`：高度固定为 `particle.size`

**解决方案：长方形图片（AR > 1）只使用 X 轴旋转**

```typescript
interface ILeafRotationOptions extends IParticle {
    maxTimeToLive: number;           // 自定义：记录初始生命周期
    originalAspectRatio: number;     // 自定义：记录初始宽高比
    rotationAngle: number;           // 自定义：当前旋转角度
    rotationSpeed: number;           // 自定义：旋转速度
    randomOffset: number;            // 自定义：随机偏移
}

@ccclass
export class LeafRotationModifier extends ParticleModifierBase {
    @property({ tooltip: '最小旋转速度（圈/秒）' })
    minRotationSpeed: number = 0.5;

    @property({ tooltip: '最大旋转速度（圈/秒）' })
    maxRotationSpeed: number = 2.0;

    @property({ tooltip: '旋转轴（X=上下翻转，Y=左右翻转）' })
    rotationAxis: 'X' | 'Y' = 'X';

    onParticleEmit(particle: ILeafRotationOptions, system: cc.ParticleSystem): void {
        // ⚠️ 重要：必须在 onParticleEmit 中初始化自定义数据
        particle.maxTimeToLive = particle.timeToLive;
        particle.originalAspectRatio = particle.aspectRatio || 1.0;
        particle.rotationAngle = 0;

        const randomSpeed = this.minRotationSpeed + Math.random() * (this.maxRotationSpeed - this.minRotationSpeed);
        particle.rotationSpeed = Math.PI * 2 * randomSpeed;
        particle.randomOffset = Math.random() * Math.PI * 2;
    }

    onParticleUpdate(particle: ILeafRotationOptions, dt: number, system: cc.ParticleSystem): void {
        particle.rotationAngle += particle.rotationSpeed * dt;
        const currentAngle = particle.rotationAngle + particle.randomOffset;
        const cosValue = Math.abs(Math.cos(currentAngle));
        const safeCos = Math.max(0.01, cosValue);

        if (this.rotationAxis === 'X') {
            // X 轴旋转：宽度不变，高度缩放
            particle.aspectRatio = particle.originalAspectRatio / safeCos;
        } else {
            // Y 轴旋转：⚠️ 长方形图片会跳变
            particle.aspectRatio = particle.originalAspectRatio * safeCos;
        }
    }
}
```

**使用建议：**
- 长方形图片（AR > 1）：使用 `rotationAxis = 'X'`
- 正方形图片（AR ≈ 1）：可以使用任意轴
- 配合粒子 Z 轴旋转：只做 X 轴 3D 翻转 + 粒子 `rotation` 属性

## 高级功能

### 访问顶点缓冲区

**⚠️ 警告**：此功能需要深入了解引擎顶点格式，仅用于高级场景

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    const simulator = (system as any)._simulator;
    const buffer = system._assembler.getBuffer();
    const vbuf = buffer._vData;

    const particleIndex = simulator.particles.indexOf(particle);
    // vfmtPosUvColor 格式：每顶点 8 floats (pos:2 + uv:2 + color:4)，每粒子 4 顶点 = 32 floats
    const FLOAT_PER_PARTICLE = 32;
    const offset = particleIndex * FLOAT_PER_PARTICLE;

    // 修改第一个顶点的 UV 坐标（offset + 8, offset + 9）
    // 第二个顶点：offset + 16, offset + 17
    // 第三个顶点：offset + 24, offset + 25
    // 第四个顶点：offset + 32, offset + 33
    vbuf[offset + 8] = 0.0;
    vbuf[offset + 9] = 0.0;

    // step 函数会自动上传数据，无需手动调用 uploadData
}
```

### 多修饰器协同

在编辑器中添加多个修饰器，按 `priority` 顺序执行（数值越小越先执行）：

```
ParticleSystem
├── ParticleModifier (胶水组件，自动收集并排序子修饰器)
├── GravityModifier (priority: 0)       # 先应用重力
├── LeafRotationModifier (priority: 1) # 再应用 3D 旋转
└── ColorFadeModifier (priority: 2)    # 最后应用颜色渐变
```

**执行顺序影响**：
- 如果先应用颜色渐变，再应用 3D 旋转，旋转不会影响颜色
- 优先级决定了修饰器的应用顺序，可能影响最终效果

## 调试技巧

### 查看粒子系统状态

**⚠️ 性能警告**：以下调试方法会产生大量日志，仅在开发环境使用，生产环境务必移除

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 仅在每 100 帧输出一次，避免日志爆炸
    if (Date.now() % 100 < 16) {  // 约 6fps
        const simulator = (system as any)._simulator;
        console.log('粒子数量:', simulator.particles.length);
        console.log('激活状态:', simulator.active);
    }
}
```

### 监控 aspectRatio

```typescript
if (particle.aspectRatio > 1.1 || particle.aspectRatio < 0.9) {
    console.log('aspectRatio 异常:', particle.aspectRatio);
}
```

### 性能分析

```typescript
const startTime = Date.now();
// ... 修饰器逻辑
const endTime = Date.now();
if (endTime - startTime > 1) {
    console.warn('执行时间过长:', endTime - startTime, 'ms');
}
```

## 质量校验清单

在创建修饰器时，请确保满足以下标准：

- [ ] **性能检查**：避免在 `onParticleUpdate` 中创建新对象
- [ ] **初始化检查**：粒子自定义数据在 `onParticleEmit` 中初始化
- [ ] **生命周期检查**：不修改粒子数组，只修改单个粒子属性
- [ ] **兼容性检查**：确认粒子系统模式（Gravity 或 Radius）
- [ ] **aspectRatio 检查**：长方形图片使用 X 轴旋转避免跳变
- [ ] **priority 设置**：合理设置优先级控制执行顺序

## 常见问题与解决方案

### 问题 1：修饰器未生效

**检查清单：**
- [ ] 是否添加了 `ParticleModifier` 组件？
- [ ] 修饰器是否已添加到粒子系统节点？
- [ ] `priority` 是否正确（按顺序执行）？

### 问题 2：性能问题

**优化建议：**
- 减少粒子数量（建议 < 1000）
- 简化修饰器逻辑
- 避免复杂的数学运算

### 问题 3：长方形图片旋转跳变

**解决方案：**
- 使用 `rotationAxis = 'X'`
- 公式：`aspectRatio = originalAspectRatio / cos`

### 问题 4：粒子间交互需求

**实现方法：**
- 在修饰器中维护粒子列表
- 在 `onParticleUpdate` 中遍历计算

### 问题 5：自定义数据丢失

**解决方案：**
- 必须在 `onParticleEmit` 中初始化自定义数据
- 使用 TypeScript 接口扩展 IParticle

## 参考资源

### 示例文件（位于本技能包的 `examples/` 目录）
- `examples/ColorFadeModifier.ts` - 颜色渐变
- `examples/GravityModifier.ts` - 重力修改
- `examples/LeafRotationModifier.ts` - 3D 旋转

**注意**：这些示例文件位于粒子修饰器技能包中，可参考实现方式

### 引擎源码（位于本技能包的 `js/` 目录，供理解原理使用）

#### `js/particle-simulator.js` - 粒子模拟器
- **Particle 类定义**：粒子对象结构，包含位置、颜色、大小、旋转、生命周期等属性
- **emitParticle 函数**：发射新粒子，初始化粒子属性
- **step 函数**：每帧更新所有粒子，包括发射、更新、回收
- **updateParticleBuffer 函数**：更新顶点缓冲区，包含 **aspectRatio 处理的关键逻辑**（根据 aspectRatio 切换宽高锚点）
- **对象池**：粒子对象池管理，避免频繁创建销毁

#### `js/CCParticleSystem.js` - 粒子系统组件
- **属性定义**：粒子系统所有可配置属性（totalParticles、duration、emissionRate、life、startColor、endColor、gravity、speed 等）
- **_simulator 初始化**：创建粒子模拟器实例
- **lateUpdate 函数**：每帧调用模拟器的 step 方法
- **emitterMode**：GRAVITY（重力模式）和 RADIUS（半径模式）
- **positionType**：FREE（自由模式）、RELATIVE（相对模式）、GROUPED（整组模式）

#### `js/particle-system-assembler.js` - 渲染汇编器
- **getBuffer 函数**：获取顶点缓冲区（QuadBuffer）
- **fillBuffers 函数**：提交渲染数据到 GPU
- **顶点格式**：vfmtPosUvColor（位置 + UV + 颜色）
- **每粒子顶点数**：4 个顶点，6 个索引（2 个三角形）

#### `js/CCParticleAsset.js` - 粒子资源
- **spriteFrame 属性**：粒子贴图资源
- **支持格式**：plist 格式的粒子配置文件

**注意**：这些是 Cocos Creator 引擎源码，位于技能包中供理解原理使用

## 最佳实践

1. **优先使用 X 轴旋转**：长方形图片避免跳变
2. **避免对象创建**：在 `onParticleUpdate` 中不创建新对象
3. **合理控制粒子数**：建议 < 1000 个粒子
4. **使用 priority 控制顺序**：修饰器按 `priority` 从小到大执行
5. **在 onParticleEmit 初始化**：粒子自定义数据在发射时初始化
6. **扩展 IParticle 接口**：使用 TypeScript 接口扩展自定义数据类型