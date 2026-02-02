import { IParticle } from "../ParticleModifier";
import ParticleModifierBase from "../ParticleModifierBase";

const { ccclass, property } = cc._decorator;

/**
 * 叶子旋转修饰器示例
 * 通过改变 aspectRatio 模拟叶子在 3D 空间中旋转的效果
 * 
 * ⚠️ 重要：长方形图片（AR > 1）建议使用 X 轴旋转，避免跳变
 */
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

    @property({
        tooltip: '旋转轴（X=上下翻转，Y=左右翻转）⚠️ 长方形图片建议使用 X 轴',
        type: cc.Enum({ 'X': 0, 'Y': 1 })
    })
    rotationAxis: number = 0; // 0 = X, 1 = Y

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

        if (this.rotationAxis === 0) {
            // --- 绕 X 轴转：宽度不变，高度缩放 ---
            // 适用于 originalAspectRatio > 1 的长方形图片
            // 公式：aspectRatio = originalAspectRatio / cos
            particle.aspectRatio = particle.originalAspectRatio / safeCos;
        } else {
            // --- 绕 Y 轴转：高度不变，宽度缩放 ---
            // ⚠️ 受限于引擎逻辑，长方形图片使用 Y 轴旋转会导致高度跳变
            particle.aspectRatio = particle.originalAspectRatio * safeCos;
        }
    }
}