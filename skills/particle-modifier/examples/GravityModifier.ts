import { IParticle } from "../ParticleModifier";
import ParticleModifierBase from "../ParticleModifierBase";

const { ccclass, property } = cc._decorator;

/**
 * 重力修改器示例
 * 在粒子生命周期中应用额外的重力
 */
interface IGravityModifierOptions extends IParticle {
    maxTimeToLive: number;
}

@ccclass
export class GravityModifier extends ParticleModifierBase {
    @property(cc.Vec2)
    force: cc.Vec2 = cc.v2(0, 0);

    onParticleEmit(particle: IGravityModifierOptions, system: cc.ParticleSystem): void {
        particle.maxTimeToLive = particle.timeToLive;
    }

    onParticleUpdate(particle: IGravityModifierOptions, dt: number, system: cc.ParticleSystem): void {
        let lifeRatio = 1 - (particle.timeToLive / particle.maxTimeToLive);
        if (lifeRatio < 0.5) {
            particle.pos.y += this.force.y * dt;
        } else {
            particle.pos.y -= this.force.y * dt;
        }
    }
}