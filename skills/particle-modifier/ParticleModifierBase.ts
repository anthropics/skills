import ParticleModifier, { IParticle } from "./ParticleModifier";

const { ccclass, property } = cc._decorator;

/**
 * 粒子修饰器基类
 * 所有具体修饰器都继承此类
 */
@ccclass
export default class ParticleModifierBase extends cc.Component {

    // 优先级（数值越小越先执行）
    @property({
        tooltip: '执行优先级，数值越小越先执行'
    })
    priority: number = 0;

    /**
     * 粒子发射时调用（子类重写）
     * @param particle 粒子对象
     * @param system 粒子系统
     */
    onParticleEmit(particle: IParticle, system: cc.ParticleSystem): void {
        // 子类实现
    }

    /**
     * 粒子每帧更新时调用（子类重写）
     * @param particle 粒子对象
     * @param dt 时间增量
     * @param system 粒子系统
     */
    onParticleUpdate(particle: IParticle, dt: number, system: cc.ParticleSystem): void {
        // 子类实现
    }
}