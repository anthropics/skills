# 粒子修饰器系统

一个强大的 Cocos Creator 2.4.13 粒子系统扩展框架，允许你通过编写修饰器类来自定义控制粒子行为。

## 📁 文件结构

```
particle-modifier/
├── SKILL.md                      # 完整使用指南
├── README.md                     # 本文件
├── ParticleModifier.ts           # 粒子修饰器胶水组件（核心）
├── ParticleModifierBase.ts       # 粒子修饰器基类（核心）
└── examples/                     # 示例修饰器
    ├── LeafRotationModifier.ts   # 叶子旋转效果
    ├── GravityModifier.ts        # 重力效果
    └── ColorFadeModifier.ts      # 颜色渐变效果
```

## 🚀 快速开始

### 1. 复制核心文件

将以下两个文件复制到你的项目中：

```
你的项目/assets/script/game/particle/
├── ParticleModifier.ts
└── ParticleModifierBase.ts
```

### 2. 创建自定义修饰器

```typescript
import { IParticle } from "./ParticleModifier";
import ParticleModifierBase from "./ParticleModifierBase";

const { ccclass, property } = cc._decorator;

@ccclass
export class MyModifier extends ParticleModifierBase {
    @property({ tooltip: '我的属性' })
    myProperty: number = 1.0;

    onParticleEmit(particle: IParticle, system: cc.ParticleSystem): void {
        // 粒子出生时的初始化
    }

    onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
        // 粒子每帧的更新
    }
}
```

### 3. 在编辑器中使用

1. 创建粒子系统节点
2. 添加 `ParticleModifier` 组件
3. 添加你的修饰器组件
4. 配置参数并运行

## 📚 详细文档

查看 [SKILL.md](./SKILL.md) 获取完整的使用指南，包括：

- IParticle 接口详细说明
- 常见使用场景
- 完整示例代码
- 高级用法
- 性能优化建议
- 常见问题解答

## 🎯 示例修饰器

### LeafRotationModifier
模拟叶子在 3D 空间中旋转的效果，通过改变宽高比实现。

**⚠️ 重要提示**：
- 长方形图片（AR > 1）建议使用 X 轴旋转，避免跳变
- 正方形图片（AR ≈ 1）可以使用任意轴
- 配合粒子 Z 轴旋转，效果更真实

### GravityModifier
在粒子生命周期中应用额外的重力。

### ColorFadeModifier
根据粒子生命周期实现颜色渐变。

## 💡 核心特性

- ✅ 简单易用的 API
- ✅ 支持多个修饰器协同工作
- ✅ 可配置的优先级系统
- ✅ 完整的类型定义
- ✅ 丰富的示例代码

## ⚠️ 兼容性

- Cocos Creator 2.4.13
- TypeScript

## 📞 获取帮助

查看 [SKILL.md](./SKILL.md) 获取详细文档和常见问题解答。