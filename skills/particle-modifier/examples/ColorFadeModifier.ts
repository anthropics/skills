import { IParticle } from "../ParticleModifier";
import ParticleModifierBase from "../ParticleModifierBase";

const { ccclass, property } = cc._decorator;

/**
 * 颜色渐变修饰器示例
 * 根据粒子生命周期改变颜色
 */
interface IColorFadeOptions extends IParticle {
    maxTimeToLive: number;
    startColor: cc.Color;
    endColor: cc.Color;
}

@ccclass
export class ColorFadeModifier extends ParticleModifierBase {
    @property(cc.Color)
    startColor: cc.Color = cc.color(255, 255, 255, 255);

    @property(cc.Color)
    endColor: cc.Color = cc.color(255, 0, 0, 0);

    onParticleEmit(particle: IColorFadeOptions, system: cc.ParticleSystem): void {
        particle.maxTimeToLive = particle.timeToLive;
        particle.startColor = this.startColor.clone();
        particle.endColor = this.endColor.clone();
    }

    onParticleUpdate(particle: IColorFadeOptions, dt: number, system: cc.ParticleSystem): void {
        if (!particle.maxTimeToLive) return;
        
        const lifeRatio = 1 - (particle.timeToLive / particle.maxTimeToLive);
        
        particle.color.r = Math.floor(particle.startColor.r + (particle.endColor.r - particle.startColor.r) * lifeRatio);
        particle.color.g = Math.floor(particle.startColor.g + (particle.endColor.g - particle.startColor.g) * lifeRatio);
        particle.color.b = Math.floor(particle.startColor.b + (particle.endColor.b - particle.startColor.b) * lifeRatio);
        particle.color.a = Math.floor(particle.startColor.a + (particle.endColor.a - particle.startColor.a) * lifeRatio);
    }
}