import ParticleModifierBase from "./ParticleModifierBase";

const { ccclass, property } = cc._decorator;

/**
 * 粒子对象接口
 * 定义粒子系统中粒子的数据结构
 */
export interface IParticle {
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

/**
 * 粒子修饰器胶水组件
 * 负责拦截粒子更新，并调用所有子修饰器
 */
@ccclass
export default class ParticleModifier extends cc.Component {
    // 粒子系统引用
    protected _particleSystem: cc.ParticleSystem = null;

    // 原始函数引用
    private _originalEmitParticle: Function = null;
    private _originalStep: Function = null;
    private _isPatched: boolean = false;

    // 存储所有子修饰器
    private _modifiers: ParticleModifierBase[] = [];

    onLoad() {
        // 获取同节点的粒子系统
        this._particleSystem = this.node.getComponent(cc.ParticleSystem);
        if (!this._particleSystem) {
            cc.warn('ParticleModifier: 未找到 cc.ParticleSystem 组件');
            return;
        }

        // 收集所有子修饰器
        this._collectModifiers();

        // 应用补丁
        this._patchSimulator();
    }

    onDestroy() {
        // 恢复原始函数
        this._unpatchSimulator();
    }

    onEnable() {
        // 重新应用补丁
        if (this._particleSystem && !this._isPatched) {
            this._patchSimulator();
        }
    }

    onDisable() {
        // 恢复原始函数
        this._unpatchSimulator();
    }

    /**
     * 收集所有子修饰器组件
     */
    private _collectModifiers() {
        this._modifiers = this.node.getComponentsInChildren(ParticleModifierBase);

        // 按优先级排序
        this._modifiers.sort((a, b) => a.priority - b.priority);
    }

    /**
     * 覆盖 ParticleSimulator 的函数
     */
    private _patchSimulator() {
        if (this._isPatched || !this._particleSystem) {
            return;
        }

        const simulator = (this._particleSystem as any)._simulator;
        if (!simulator) {
            cc.error('ParticleModifier: 无法获取 simulator 实例');
            return;
        }

        // 保存原始函数
        this._originalEmitParticle = simulator.emitParticle;
        this._originalStep = simulator.step;

        // 覆盖 emitParticle 函数
        simulator.emitParticle = (pos: cc.Vec2) => {
            // 调用原函数
            this._originalEmitParticle.call(simulator, pos);

            // 获取新创建的粒子（最后一个）
            const particles = simulator.particles;
            const particle = particles[particles.length - 1] as IParticle;

            // 调用所有修饰器的发射钩子
            this._onParticleEmit(particle);
        };

        // 覆盖 step 函数
        simulator.step = (dt: number) => {
            // 调用原函数
            this._originalStep.call(simulator, dt);

            // 在原函数执行后，遍历所有粒子调用更新钩子
            const particles = simulator.particles;
            for (let i = 0; i < particles.length; i++) {
                this._onParticleUpdate(particles[i] as IParticle, dt);
            }
        };

        this._isPatched = true;
    }

    /**
     * 恢复原始函数
     */
    private _unpatchSimulator() {
        if (!this._isPatched || !this._particleSystem) {
            return;
        }

        const simulator = (this._particleSystem as any)._simulator;
        if (!simulator) {
            return;
        }

        // 恢复原始函数
        if (this._originalEmitParticle) {
            simulator.emitParticle = this._originalEmitParticle;
        }
        if (this._originalStep) {
            simulator.step = this._originalStep;
        }

        this._isPatched = false;
    }

    /**
     * 粒子发射时调用所有修饰器
     */
    private _onParticleEmit(particle: IParticle) {
        for (let i = 0; i < this._modifiers.length; i++) {
            const modifier = this._modifiers[i];
            modifier.onParticleEmit(particle, this._particleSystem);
        }
    }

    /**
     * 粒子每帧更新时调用所有修饰器
     */
    private _onParticleUpdate(particle: IParticle, dt: number) {
        for (let i = 0; i < this._modifiers.length; i++) {
            const modifier = this._modifiers[i];
            modifier.onParticleUpdate(particle, dt, this._particleSystem);
        }
    }
}