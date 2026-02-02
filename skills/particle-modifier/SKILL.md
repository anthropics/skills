# 粒子修饰器系统使用指南

## 📋 概述

这是一个基于 Cocos Creator 2.4.x 的粒子修饰器系统，允许你通过编写修饰器类来自定义控制粒子系统的行为。

## 🚀 快速开始

### 步骤 1：复制核心文件到项目

将以下两个文件复制到你的项目中：

```
你的项目/assets/script/game/particle/
├── ParticleModifier.ts          # 粒子修饰器胶水组件
└── ParticleModifierBase.ts      # 粒子修饰器基类
```

### 步骤 2：创建自定义修饰器

创建一个继承自 `ParticleModifierBase` 的新类：

```typescript
import { IParticle } from "./ParticleModifier";
import ParticleModifierBase from "./ParticleModifierBase";

const { ccclass, property } = cc._decorator;

@ccclass
export class MyCustomModifier extends ParticleModifierBase {
    // 在这里添加你的可配置属性
    @property({
        tooltip: '你的属性说明'
    })
    myProperty: number = 1.0;

    /**
     * 粒子发射时调用（可选）
     */
    onParticleEmit(particle: IParticle, system: cc.ParticleSystem): void {
        // 粒子出生时的初始化逻辑
    }

    /**
     * 粒子每帧更新时调用（必需）
     */
    onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
        // 粒子每帧的更新逻辑
    }
}
```

### 步骤 3：在编辑器中使用

1. 创建一个粒子系统节点
2. 添加 `ParticleModifier` 组件
3. 添加你的自定义修饰器组件（如 `MyCustomModifier`）
4. 配置参数并运行

## 📚 IParticle 接口说明

```typescript
interface IParticle {
    // 位置相关
    pos: cc.Vec2;                    // 当前位置（相对于发射器）
    startPos: cc.Vec2;               // 发射时的起始位置
    drawPos: cc.Vec2;                // 绘制位置

    // 颜色相关
    color: cc.Color;                 // 当前颜色
    deltaColor: {                    // 颜色变化率
        r: number;
        g: number;
        b: number;
        a: number;
    };
    preciseColor: {                  // 精确颜色（浮点数）
        r: number;
        g: number;
        b: number;
        a: number;
    };

    // 大小相关
    size: number;                    // 当前大小
    deltaSize: number;               // 大小变化率
    aspectRatio: number;             // 宽高比

    // 旋转相关
    rotation: number;                // 当前旋转角度（度）
    deltaRotation: number;           // 旋转变化率（度/秒）

    // 生命周期
    timeToLive: number;              // 剩余生命周期（秒）

    // Mode A: 重力模式相关
    dir: cc.Vec2;                    // 速度向量（包含方向和大小）
    radialAccel: number;             // 径向加速度
    tangentialAccel: number;         // 切向加速度

    // Mode B: 半径模式相关
    angle: number;                   // 当前角度（弧度）
    degreesPerSecond: number;        // 角速度（弧度/秒）
    radius: number;                  // 当前半径
    deltaRadius: number;             // 半径变化率
}
```

## 💡 常见使用场景

### 场景 1：修改粒子位置

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 让粒子在 X 轴上摆动
    particle.pos.x += Math.sin(Date.now() / 1000) * 10 * dt;
}
```

### 场景 2：修改粒子颜色

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 根据生命周期改变颜色
    const lifeRatio = 1 - (particle.timeToLive / particle.maxTimeToLive);
    particle.color.r = Math.floor(255 * lifeRatio);
    particle.color.g = Math.floor(255 * (1 - lifeRatio));
}
```

### 场景 3：修改粒子大小

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 呼吸效果
    particle.size = 50 + Math.sin(Date.now() / 500) * 20;
}
```

### 场景 4：修改粒子旋转

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 持续旋转
    particle.rotation += 180 * dt;
}
```

### 场景 5：修改粒子速度

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    // 施加额外的力
    particle.dir.x += this.force.x * dt;
    particle.dir.y += this.force.y * dt;
}
```

### 场景 6：修改宽高比（实现 3D 旋转效果）⚠️ 重要

**⚠️ 关键问题：长方形图片旋转时的跳变问题**

如果粒子图片是长方形（如 `originalAspectRatio = 1.8`），简单的 `aspectRatio * cos` 会导致视觉跳变。

**原因**：Cocos 引擎底层逻辑（`Simulator.js`）有一个硬切换：
```javascript
aspectRatio > 1 ? (height = width / aspectRatio) : (width = height * aspectRatio);
```
- 当 `AR > 1` 时，**宽度**被固定为 `particle.size`
- 当 `AR < 1` 时，**高度**被固定为 `particle.size`

**解决方案**：根据图片比例，只旋转某个轴以避免跳变。

```typescript
interface ILeafRotationOptions extends IParticle {
    maxTimeToLive: number;
    originalAspectRatio: number;
    rotationAngle: number;
    rotationSpeed: number;
    randomOffset: number;
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
        const safeCos = Math.max(0.01, cosValue); // 防止除以0

        if (this.rotationAxis === 'X') {
            // --- 绕 X 轴转：宽度不变，高度缩放 ---
            // 适用于 originalAspectRatio > 1 的长方形图片
            // 公式：aspectRatio = originalAspectRatio / cos
            // 当 cos 从 1 变到 0，AR 从 1.8 变到无穷大
            // 根据引擎公式 height = size / AR，高度会从 size/1.8 缩向 0
            particle.aspectRatio = particle.originalAspectRatio / safeCos;
        } else {
            // --- 绕 Y 轴转：高度不变，宽度缩放 ---
            // ⚠️ 受限于引擎逻辑，如果 originalAspectRatio > 1，Y轴旋转会导致高度跳变
            // 建议长方形图片使用 X 轴旋转
            particle.aspectRatio = particle.originalAspectRatio * safeCos;
        }
    }
}
```

**使用建议**：
- **长方形图片（AR > 1）**：使用 `rotationAxis = 'X'`，避免跳变
- **正方形图片（AR ≈ 1）**：可以使用任意轴
- **配合粒子 Z 轴旋转**：只做 X 轴的 3D 翻转，配合粒子本身的 `rotation` 属性，效果已经很真实

## 🎯 完整示例：叶子旋转修饰器

```typescript
import { IParticle } from "./ParticleModifier";
import ParticleModifierBase from "./ParticleModifierBase";

const { ccclass, property } = cc._decorator;

interface ILeafRotationOptions extends IParticle {
    maxTimeToLive: number;
    originalAspectRatio: number;
    rotationAngle: number;
    rotationSpeed: number;
    randomOffset: number;
}

@ccclass
export class LeafRotationModifier extends ParticleModifierBase {
    @property({ tooltip: '最小旋转速度（圈/秒）' })
    minRotationSpeed: number = 0.5;

    @property({ tooltip: '最大旋转速度（圈/秒）' })
    maxRotationSpeed: number = 2.0;

    onParticleEmit(particle: ILeafRotationOptions, system: cc.ParticleSystem): void {
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
        const visibleRatio = Math.abs(Math.cos(currentAngle));
        particle.aspectRatio = particle.originalAspectRatio * visibleRatio;
    }
}
```

## 🔧 高级用法

### 访问顶点缓冲区（直接修改 UV）

```typescript
onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
    const simulator = (system as any)._simulator;
    const buffer = system._assembler.getBuffer();
    const vbuf = buffer._vData;
    
    const particleIndex = simulator.particles.indexOf(particle);
    const FLOAT_PER_PARTICLE = 20;
    const offset = particleIndex * FLOAT_PER_PARTICLE;
    
    // 修改 UV 坐标
    vbuf[offset + 2] = 0.0;  // 左下 U
    vbuf[offset + 3] = 0.0;  // 左下 V
    // ... 其他顶点
    
    buffer._dirty = true;
}
```

### 多个修饰器协同工作

```typescript
// 在编辑器中添加多个修饰器
ParticleSystem
├── ParticleModifier (胶水组件)
├── GravityModifier (重力修改器)
├── LeafRotationModifier (旋转修改器)
└── ColorFadeModifier (颜色渐变修改器)

// 修饰器按 priority 顺序执行
// priority 越小越先执行
```

## ⚠️ 注意事项

1. **性能考虑**：
   - 避免在 `onParticleUpdate` 中创建新对象
   - 尽量减少复杂的数学运算
   - 粒子数量建议控制在 1000 以内

2. **生命周期管理**：
   - 在 `onParticleEmit` 中初始化粒子数据
   - 在 `onParticleUpdate` 中更新粒子状态
   - 不要在 `onParticleUpdate` 中修改粒子数组

3. **兼容性**：
   - 确保粒子系统使用 Gravity 模式或 Radius 模式
   - 不同模式下的粒子属性可能不同

4. **调试技巧**：
   - 使用 `cc.log()` 输出粒子状态
   - 在编辑器中实时调整参数
   - 使用优先级控制修饰器执行顺序

5. **aspectRatio 旋转的坑**：
   - **长方形图片（AR > 1）**：使用 X 轴旋转（`aspectRatio = originalAspectRatio / cos`），避免跳变
   - **正方形图片（AR ≈ 1）**：可以使用任意轴
   - **Y 轴旋转限制**：受限于引擎底层逻辑，长方形图片使用 Y 轴旋转会导致高度跳变
   - **推荐做法**：长方形图片只使用 X 轴旋转

## 📖 参考资料

- Cocos Creator 2.4.x 粒子系统文档
- 粒子系统源码：`engine/cocos2d/particle/`
- 顶点格式定义：`engine/cocos2d/core/renderer/webgl/vertex-format.js`

## 🆘 常见问题

### Q: 为什么我的修饰器没有生效？
A: 检查是否添加了 `ParticleModifier` 组件，以及修饰器的 `priority` 是否正确。

### Q: 如何让修饰器只影响部分粒子？
A: 在 `onParticleEmit` 中给粒子打标记，在 `onParticleUpdate` 中根据标记决定是否处理。

### Q: 如何实现粒子之间的交互？
A: 可以在修饰器中维护一个粒子列表，在 `onParticleUpdate` 中遍历计算粒子间的距离和力。

### Q: 性能太慢怎么办？
A: 减少粒子数量，简化修饰器逻辑，或者使用对象池优化。

### Q: 长方形图片旋转时为什么会跳变？
A: 这是 Cocos 引擎底层逻辑的限制。当 `aspectRatio` 从 >1 变到 <1 时，引擎会切换锚点（从宽度固定变为高度固定），导致视觉跳变。**解决方案**：长方形图片（AR > 1）只使用 X 轴旋转（`aspectRatio = originalAspectRatio / cos`），避免跳变。

### Q: 如何选择旋转轴？
A: 
- **长方形图片（AR > 1）**：使用 X 轴旋转
- **正方形图片（AR ≈ 1）**：可以使用任意轴
- **配合 Z 轴旋转**：只做 X 轴的 3D 翻转，配合粒子本身的 `rotation` 属性，效果已经很真实
