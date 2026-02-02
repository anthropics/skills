/****************************************************************************
 Copyright (c) 2013-2016 Chukong Technologies Inc.
 Copyright (c) 2017-2018 Xiamen Yaji Software Co., Ltd.

 https://www.cocos.com/

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated engine source code (the "Software"), a limited,
  worldwide, royalty-free, non-assignable, revocable and non-exclusive license
 to use Cocos Creator solely to develop games on your target platforms. You shall
  not use Cocos Creator software for developing other software or tools that's
  used for developing games. You are not granted to publish, distribute,
  sublicense, and/or sell copies of Cocos Creator.

 The software or tools in this License Agreement are licensed, not sold.
 Xiamen Yaji Software Co., Ltd. reserves all rights not expressly granted to you.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 ****************************************************************************/

const macro = require('../core/platform/CCMacro');
const ParticleAsset = require('./CCParticleAsset');
const RenderComponent = require('../core/components/CCRenderComponent');
const codec = require('../compression/ZipUtils');
const PNGReader = require('./CCPNGReader');
const tiffReader = require('./CCTIFFReader');
const textureUtil = require('../core/utils/texture-util');
const RenderFlow = require('../core/renderer/render-flow');
const ParticleSimulator = require('./particle-simulator');
const Material = require('../core/assets/material/CCMaterial');
const BlendFunc = require('../core/utils/blend-func');

function getImageFormatByData (imgData) {
    // if it is a png file buffer.
    if (imgData.length > 8 && imgData[0] === 0x89
        && imgData[1] === 0x50
        && imgData[2] === 0x4E
        && imgData[3] === 0x47
        && imgData[4] === 0x0D
        && imgData[5] === 0x0A
        && imgData[6] === 0x1A
        && imgData[7] === 0x0A) {
        return macro.ImageFormat.PNG;
    }

    // if it is a tiff file buffer.
    if (imgData.length > 2 && ((imgData[0] === 0x49 && imgData[1] === 0x49)
        || (imgData[0] === 0x4d && imgData[1] === 0x4d)
        || (imgData[0] === 0xff && imgData[1] === 0xd8))) {
        return macro.ImageFormat.TIFF;
    }
    return macro.ImageFormat.UNKNOWN;
}

//
function getParticleComponents (node) {
    let parent = node.parent, comp = node.getComponent(cc.ParticleSystem);
    if (!parent || !comp) {
        return node.getComponentsInChildren(cc.ParticleSystem);
    }
    return getParticleComponents(parent);
}


/**
 * !#en Enum for emitter modes
 * !#zh 发射模式
 * @enum ParticleSystem.EmitterMode
 */
var EmitterMode = cc.Enum({
    /**
     * !#en Uses gravity, speed, radial and tangential acceleration.
     * !#zh 重力模式，模拟重力，可让粒子围绕一个中心点移近或移远。
     * @property {Number} GRAVITY
     */
    GRAVITY: 0,
    /**
     * !#en Uses radius movement + rotation.
     * !#zh 半径模式，可以使粒子以圆圈方式旋转，它也可以创造螺旋效果让粒子急速前进或后退。
     * @property {Number} RADIUS - Uses radius movement + rotation.
     */
    RADIUS: 1
});

/**
 * !#en Enum for particles movement type.
 * !#zh 粒子位置类型
 * @enum ParticleSystem.PositionType
 */
var PositionType = cc.Enum({
    /**
     * !#en
     * Living particles are attached to the world and are unaffected by emitter repositioning.
     * !#zh
     * 自由模式，相对于世界坐标，不会随粒子节点移动而移动。（可产生火焰、蒸汽等效果）
     * @property {Number} FREE
     */
    FREE: 0,

    /**
     * !#en
     * In the relative mode, the particle will move with the parent node, but not with the node where the particle is. 
     * For example, the coffee in the cup is steaming. Then the steam moves (forward) with the train, rather than moves with the cup.
     * !#zh
     * 相对模式，粒子会跟随父节点移动，但不跟随粒子所在节点移动，例如在一列行进火车中，杯中的咖啡飘起雾气，
     * 杯子移动，雾气整体并不会随着杯子移动，但从火车整体的角度来看，雾气整体会随着火车移动。
     * @property {Number} RELATIVE
     */
    RELATIVE: 1,

    /**
     * !#en
     * Living particles are attached to the emitter and are translated along with it.
     * !#zh
     * 整组模式，粒子跟随发射器移动。（不会发生拖尾）
     * @property {Number} GROUPED
     */
    GROUPED: 2
});

/**
 * @class ParticleSystem
 */

var properties = {
    /**
     * !#en Play particle in edit mode.
     * !#zh 在编辑器模式下预览粒子，启用后选中粒子时，粒子将自动播放。
     * @property {Boolean} preview
     * @default false
     */
    preview: {
        default: true,
        editorOnly: true,
        notify: CC_EDITOR && function () {
            this.resetSystem();
            if ( !this.preview ) {
                this.stopSystem();
                this.disableRender();
            }
            cc.engine.repaintInEditMode();
        },
        animatable: false,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.preview'
    },

    /**
     * !#en
     * If set custom to true, then use custom properties insteadof read particle file.
     * !#zh 是否自定义粒子属性。
     * @property {Boolean} custom
     * @default false
     */
    _custom: false,
    custom: {
        get: function () {
            return this._custom;
        },
        set: function (value) {
            if (CC_EDITOR && !value && !this._file) {
                return cc.warnID(6000);
            }
            if (this._custom !== value) {
                this._custom = value;
                this._applyFile();
                if (CC_EDITOR) {
                    cc.engine.repaintInEditMode();
                }
            }
        },
        animatable: false,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.custom'
    },

    /**
     * !#en The plist file.
     * !#zh plist 格式的粒子配置文件。
     * @property {ParticleAsset} file
     * @default null
     */
    _file: {
        default: null,
        type: ParticleAsset
    },
    file: {
        get: function () {
            return this._file;
        },
        set: function (value, force) {
            if (this._file !== value || (CC_EDITOR && force)) {
                this._file = value;
                if (value) {
                    this._applyFile();
                    if (CC_EDITOR) {
                        cc.engine.repaintInEditMode();
                    }
                }
                else {
                    this.custom = true;
                }
            }
        },
        animatable: false,
        type: ParticleAsset,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.file'
    },

    /**
     * !#en SpriteFrame used for particles display
     * !#zh 用于粒子呈现的 SpriteFrame
     * @property spriteFrame
     * @type {SpriteFrame}
     */
    _spriteFrame: {
        default: null,
        type: cc.SpriteFrame
    },
    spriteFrame: {
        get: function () {
            return this._spriteFrame;
        },
        set: function (value, force) {
            var lastSprite = this._renderSpriteFrame;
            if (CC_EDITOR) {
                if (!force && lastSprite === value) {
                    return;
                }
            }
            else {
                if (lastSprite === value) {
                    return;
                }
            }
            this._renderSpriteFrame = value;

            if (!value || value._uuid) {
                this._spriteFrame = value;
            }

            this._applySpriteFrame(lastSprite);
            if (CC_EDITOR) {
                this.node.emit('spriteframe-changed', this);
            }
        },
        type: cc.SpriteFrame,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.spriteFrame'
    },


    // just used to read data from 1.x
    _texture: {
        default: null,
        type: cc.Texture2D,
        editorOnly: true,
    },

    /**
     * !#en Texture of Particle System, readonly, please use spriteFrame to setup new texture。
     * !#zh 粒子贴图，只读属性，请使用 spriteFrame 属性来替换贴图。
     * @property texture
     * @type {String}
     * @readonly
     */
    texture: {
        get: function () {
            return this._getTexture();
        },
        set: function (value) {
            if (value) {
                cc.warnID(6017);
            }
        },
        type: cc.Texture2D,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.texture',
        readonly: true,
        visible: false,
        animatable: false
    },

    /**
     * !#en Current quantity of particles that are being simulated.
     * !#zh 当前播放的粒子数量。
     * @property {Number} particleCount
     * @readonly
     */
    particleCount: {
        visible: false,
        get () {
            return this._simulator.particles.length;
        },
        readonly: true
    },

    /**
     * !#en Indicate whether the system simulation have stopped.
     * !#zh 指示粒子播放是否完毕。
     * @property {Boolean} stopped
     */
    _stopped: true,
    stopped: {
        get () {
            return this._stopped;
        },
        animatable: false,
        visible: false
    },

    /**
     * !#en If set to true, the particle system will automatically start playing on onLoad.
     * !#zh 如果设置为 true 运行时会自动发射粒子。
     * @property playOnLoad
     * @type {boolean}
     * @default true
     */
    playOnLoad: true,

    /**
     * !#en Indicate whether the owner node will be auto-removed when it has no particles left.
     * !#zh 粒子播放完毕后自动销毁所在的节点。
     * @property {Boolean} autoRemoveOnFinish
     */
    autoRemoveOnFinish: {
        default: false,
        animatable: false,
        tooltip: CC_DEV && 'i18n:COMPONENT.particle_system.autoRemoveOnFinish'
    },

    /**
     * !#en Indicate whether the particle system is activated.
     * !#zh 是否激活粒子。
     * @property {Boolean} active
     * @readonly
     */
    active: {
        get: function () {
            return this._simulator.active;
        },
        visible: false
    },

    /**
     * !#en Maximum particles of the system.
     * !#zh 粒子最大数量。
     * @property {Number} totalParticles
     * @default 150
     */
    totalParticles: 150,
    /**
     * !#en How many seconds the emitter wil run. -1 means 'forever'.
     * !#zh 发射器生存时间，单位秒，-1表示持续发射。
     * @property {Number} duration
     * @default ParticleSystem.DURATION_INFINITY
     */
    duration: -1,
    /**
     * !#en Emission rate of the particles.
     * !#zh 每秒发射的粒子数目。
     * @property {Number} emissionRate
     * @default 10
     */
    emissionRate: 10,
    /**
     * !#en Life of each particle setter.
     * !#zh 粒子的运行时间。
     * @property {Number} life
     * @default 1
     */
    life: 1,
    /**
     * !#en Variation of life.
     * !#zh 粒子的运行时间变化范围。
     * @property {Number} lifeVar
     * @default 0
     */
    lifeVar: 0,

    /**
     * !#en Start color of each particle.
     * !#zh 粒子初始颜色。
     * @property {cc.Color} startColor
     * @default {r: 255, g: 255, b: 255, a: 255}
     */
    _startColor: null,
    startColor: {
        type: cc.Color,
        get () {
            return this._startColor;
        },
        set (val) {
            this._startColor.r = val.r;
            this._startColor.g = val.g;
            this._startColor.b = val.b;
            this._startColor.a = val.a;
        }
    },
    /**
     * !#en Variation of the start color.
     * !#zh 粒子初始颜色变化范围。
     * @property {cc.Color} startColorVar
     * @default {r: 0, g: 0, b: 0, a: 0}
     */
    _startColorVar: null,
    startColorVar: {
        type: cc.Color,
        get () {
            return this._startColorVar;
        },
        set (val) {
            this._startColorVar.r = val.r;
            this._startColorVar.g = val.g;
            this._startColorVar.b = val.b;
            this._startColorVar.a = val.a;
        }
    },
    /**
     * !#en Ending color of each particle.
     * !#zh 粒子结束颜色。
     * @property {cc.Color} endColor
     * @default {r: 255, g: 255, b: 255, a: 0}
     */
    _endColor: null,
    endColor: {
        type: cc.Color,
        get () {
            return this._endColor;
        },
        set (val) {
            this._endColor.r = val.r;
            this._endColor.g = val.g;
            this._endColor.b = val.b;
            this._endColor.a = val.a;
        }
    },
    /**
     * !#en Variation of the end color.
     * !#zh 粒子结束颜色变化范围。
     * @property {cc.Color} endColorVar
     * @default {r: 0, g: 0, b: 0, a: 0}
     */
    _endColorVar: null,
    endColorVar: {
        type: cc.Color,
        get () {
            return this._endColorVar;
        },
        set (val) {
            this._endColorVar.r = val.r;
            this._endColorVar.g = val.g;
            this._endColorVar.b = val.b;
            this._endColorVar.a = val.a;
        }
    },

    /**
     * !#en Angle of each particle setter.
     * !#zh 粒子角度。
     * @property {Number} angle
     * @default 90
     */
    angle: 90,
    /**
     * !#en Variation of angle of each particle setter.
     * !#zh 粒子角度变化范围。
     * @property {Number} angleVar
     * @default 20
     */
    angleVar: 20,
    /**
     * !#en Start size in pixels of each particle.
     * !#zh 粒子的初始大小。
     * @property {Number} startSize
     * @default 50
     */
    startSize: 50,
    /**
     * !#en Variation of start size in pixels.
     * !#zh 粒子初始大小的变化范围。
     * @property {Number} startSizeVar
     * @default 0
     */
    startSizeVar: 0,
    /**
     * !#en End size in pixels of each particle.
     * !#zh 粒子结束时的大小。
     * @property {Number} endSize
     * @default 0
     */
    endSize: 0,
    /**
     * !#en Variation of end size in pixels.
     * !#zh 粒子结束大小的变化范围。
     * @property {Number} endSizeVar
     * @default 0
     */
    endSizeVar: 0,
    /**
     * !#en Start angle of each particle.
     * !#zh 粒子开始自旋角度。
     * @property {Number} startSpin
     * @default 0
     */
    startSpin: 0,
    /**
     * !#en Variation of start angle.
     * !#zh 粒子开始自旋角度变化范围。
     * @property {Number} startSpinVar
     * @default 0
     */
    startSpinVar: 0,
    /**
     * !#en End angle of each particle.
     * !#zh 粒子结束自旋角度。
     * @property {Number} endSpin
     * @default 0
     */
    endSpin: 0,
    /**
     * !#en Variation of end angle.
     * !#zh 粒子结束自旋角度变化范围。
     * @property {Number} endSpinVar
     * @default 0
     */
    endSpinVar: 0,

    /**
     * !#en Source position of the emitter.
     * !#zh 发射器位置。
     * @property {Vec2} sourcePos
     * @default cc.Vec2.ZERO
     */
    sourcePos: cc.Vec2.ZERO,

    /**
     * !#en Variation of source position.
     * !#zh 发射器位置的变化范围。（横向和纵向）
     * @property {Vec2} posVar
     * @default cc.Vec2.ZERO
     */
    posVar: cc.Vec2.ZERO,

    /**
     * !#en Particles movement type.
     * !#zh 粒子位置类型。
     * @property {ParticleSystem.PositionType} positionType
     * @default ParticleSystem.PositionType.FREE
     */
    _positionType: {
        default: PositionType.FREE,
        formerlySerializedAs: "positionType"
    },

    positionType: {
        type: PositionType,
        get () {
            return this._positionType;
        },
        set (val) {
            this._positionType = val;
            this._updateMaterial();
        }
    },

    /**
     * !#en Particles emitter modes.
     * !#zh 发射器类型。
     * @property {ParticleSystem.EmitterMode} emitterMode
     * @default ParticleSystem.EmitterMode.GRAVITY
     */
    emitterMode: {
        default: EmitterMode.GRAVITY,
        type: EmitterMode
    },

    // GRAVITY MODE

    /**
     * !#en Gravity of the emitter.
     * !#zh 重力。
     * @property {Vec2} gravity
     * @default cc.Vec2.ZERO
     */
    gravity: cc.Vec2.ZERO,
    /**
     * !#en Speed of the emitter.
     * !#zh 速度。
     * @property {Number} speed
     * @default 180
     */
    speed: 180,
    /**
     * !#en Variation of the speed.
     * !#zh 速度变化范围。
     * @property {Number} speedVar
     * @default 50
     */
    speedVar: 50,
    /**
     * !#en Tangential acceleration of each particle. Only available in 'Gravity' mode.
     * !#zh 每个粒子的切向加速度，即垂直于重力方向的加速度，只有在重力模式下可用。
     * @property {Number} tangentialAccel
     * @default 80
     */
    tangentialAccel: 80,
    /**
     * !#en Variation of the tangential acceleration.
     * !#zh 每个粒子的切向加速度变化范围。
     * @property {Number} tangentialAccelVar
     * @default 0
     */
    tangentialAccelVar: 0,
    /**
     * !#en Acceleration of each particle. Only available in 'Gravity' mode.
     * !#zh 粒子径向加速度，即平行于重力方向的加速度，只有在重力模式下可用。
     * @property {Number} radialAccel
     * @default 0
     */
    radialAccel: 0,
    /**
     * !#en Variation of the radial acceleration.
     * !#zh 粒子径向加速度变化范围。
     * @property {Number} radialAccelVar
     * @default 0
     */
    radialAccelVar: 0,

    /**
     * !#en Indicate whether the rotation of each particle equals to its direction. Only available in 'Gravity' mode.
     * !#zh 每个粒子的旋转是否等于其方向，只有在重力模式下可用。
     * @property {Boolean} rotationIsDir
     * @default false
     */
    rotationIsDir: false,

    // RADIUS MODE

    /**
     * !#en Starting radius of the particles. Only available in 'Radius' mode.
     * !#zh 初始半径，表示粒子出生时相对发射器的距离，只有在半径模式下可用。
     * @property {Number} startRadius
     * @default 0
     */
    startRadius: 0,
    /**
     * !#en Variation of the starting radius.
     * !#zh 初始半径变化范围。
     * @property {Number} startRadiusVar
     * @default 0
     */
    startRadiusVar: 0,
    /**
     * !#en Ending radius of the particles. Only available in 'Radius' mode.
     * !#zh 结束半径，只有在半径模式下可用。
     * @property {Number} endRadius
     * @default 0
     */
    endRadius: 0,
    /**
     * !#en Variation of the ending radius.
     * !#zh 结束半径变化范围。
     * @property {Number} endRadiusVar
     * @default 0
     */
    endRadiusVar: 0,
    /**
     * !#en Number of degress to rotate a particle around the source pos per second. Only available in 'Radius' mode.
     * !#zh 粒子每秒围绕起始点的旋转角度，只有在半径模式下可用。
     * @property {Number} rotatePerS
     * @default 0
     */
    rotatePerS: 0,
    /**
     * !#en Variation of the degress to rotate a particle around the source pos per second.
     * !#zh 粒子每秒围绕起始点的旋转角度变化范围。
     * @property {Number} rotatePerSVar
     * @default 0
     */
    rotatePerSVar: 0

};

/**
 * Particle System base class. <br/>
 * Attributes of a Particle System:<br/>
 *  - emmision rate of the particles<br/>
 *  - Gravity Mode (Mode A): <br/>
 *  - gravity <br/>
 *  - direction <br/>
 *  - speed +-  variance <br/>
 *  - tangential acceleration +- variance<br/>
 *  - radial acceleration +- variance<br/>
 *  - Radius Mode (Mode B):      <br/>
 *  - startRadius +- variance    <br/>
 *  - endRadius +- variance      <br/>
 *  - rotate +- variance         <br/>
 *  - Properties common to all modes: <br/>
 *  - life +- life variance      <br/>
 *  - start spin +- variance     <br/>
 *  - end spin +- variance       <br/>
 *  - start size +- variance     <br/>
 *  - end size +- variance       <br/>
 *  - start color +- variance    <br/>
 *  - end color +- variance      <br/>
 *  - life +- variance           <br/>
 *  - blending function          <br/>
 *  - texture                    <br/>
 * <br/>
 * cocos2d also supports particles generated by Particle Designer (http://particledesigner.71squared.com/).<br/>
 * 'Radius Mode' in Particle Designer uses a fixed emit rate of 30 hz. Since that can't be guarateed in cocos2d,  <br/>
 * cocos2d uses a another approach, but the results are almost identical.<br/>
 * cocos2d supports all the variables used by Particle Designer plus a bit more:  <br/>
 *  - spinning particles (supported when using ParticleSystem)       <br/>
 *  - tangential acceleration (Gravity mode)                               <br/>
 *  - radial acceleration (Gravity mode)                                   <br/>
 *  - radius direction (Radius mode) (Particle Designer supports outwards to inwards direction only) <br/>
 * It is possible to customize any of the above mentioned properties in runtime. Example:   <br/>
 *
 * @example
 * emitter.radialAccel = 15;
 * emitter.startSpin = 0;
 *
 * @class ParticleSystem
 * @extends RenderComponent
 * @uses BlendFunc
 */
var ParticleSystem = cc.Class({
    name: 'cc.ParticleSystem',
    extends: RenderComponent,
    mixins: [BlendFunc],
    editor: CC_EDITOR && {
        menu: 'i18n:MAIN_MENU.component.renderers/ParticleSystem',
        inspector: 'packages://inspector/inspectors/comps/particle-system.js',
        help: 'i18n:COMPONENT.help_url.particle-system',
        playOnFocus: true,
        executeInEditMode: true
    },

    ctor () {
        this.initProperties();
    },

    initProperties () {
        this._previewTimer = null;
        this._focused = false;
        this._aspectRatio = 1;

        this._simulator = new ParticleSimulator(this);

        // colors
        this._startColor = cc.color(255, 255, 255, 255);
        this._startColorVar = cc.color(0, 0, 0, 0);
        this._endColor = cc.color(255, 255, 255, 0);
        this._endColorVar = cc.color(0, 0, 0, 0);

        // The temporary SpriteFrame object used for the renderer. Because there is no corresponding asset, it can't be serialized.
        this._renderSpriteFrame = null;
    },

    properties: properties,

    statics: {

        /**
         * !#en The Particle emitter lives forever.
         * !#zh 表示发射器永久存在
         * @property {Number} DURATION_INFINITY
         * @default -1
         * @static
         * @readonly
         */
        DURATION_INFINITY: -1,

        /**
         * !#en The starting size of the particle is equal to the ending size.
         * !#zh 表示粒子的起始大小等于结束大小。
         * @property {Number} START_SIZE_EQUAL_TO_END_SIZE
         * @default -1
         * @static
         * @readonly
         */
        START_SIZE_EQUAL_TO_END_SIZE: -1,

        /**
         * !#en The starting radius of the particle is equal to the ending radius.
         * !#zh 表示粒子的起始半径等于结束半径。
         * @property {Number} START_RADIUS_EQUAL_TO_END_RADIUS
         * @default -1
         * @static
         * @readonly
         */
        START_RADIUS_EQUAL_TO_END_RADIUS: -1,

        EmitterMode: EmitterMode,
        PositionType: PositionType,


        _PNGReader: PNGReader,
        _TIFFReader: tiffReader,
    },

    // EDITOR RELATED METHODS

    onFocusInEditor: CC_EDITOR && function () {
        this._focused = true;
        let components = getParticleComponents(this.node);
        for (let i = 0; i < components.length; ++i) {
            components[i]._startPreview();
        }
    },

    onLostFocusInEditor: CC_EDITOR && function () {
        this._focused = false;
        let components = getParticleComponents(this.node);
        for (let i = 0; i < components.length; ++i) {
            components[i]._stopPreview();
        }
    },

    onRestore: CC_EDITOR && function () {
        // Because undo/redo will not call onEnable/onDisable,
        // we need call onEnable/onDisable manually to active/disactive children nodes.
        if (this.enabledInHierarchy) {
            this.node._renderComponent = null;
            this.onEnable();
        }
        else {
            this.onDisable();
        }
    },

    _startPreview: CC_EDITOR && function () {
        if (this.preview) {
            this.resetSystem();
        }
    },

    _stopPreview: CC_EDITOR && function () {
        if (this.preview) {
            this.resetSystem();
            this.stopSystem();
            this.disableRender();
            cc.engine.repaintInEditMode();
        }
        if (this._previewTimer) {
            clearInterval(this._previewTimer);
        }
    },

    // LIFE-CYCLE METHODS

    // just used to read data from 1.x
    _convertTextureToSpriteFrame: CC_EDITOR && function () {
        if (this._spriteFrame) {
            return;
        }
        let texture = this.texture;
        if (!texture || !texture._uuid) {
            return;
        }

        let _this = this;
        Editor.assetdb.queryMetaInfoByUuid(texture._uuid, function (err, metaInfo) {
            if (err) return Editor.error(err);
            let meta = JSON.parse(metaInfo.json);
            if (meta.type === 'raw') {
                const NodeUtils = Editor.require('app://editor/page/scene-utils/utils/node');
                let nodePath = NodeUtils.getNodePath(_this.node);
                return Editor.warn(`The texture ${metaInfo.assetUrl} used by particle ${nodePath} does not contain any SpriteFrame, please set the texture type to Sprite and reassign the SpriteFrame to the particle component.`);
            }
            else {
                let Url = require('fire-url');
                let name = Url.basenameNoExt(metaInfo.assetPath);
                let uuid = meta.subMetas[name].uuid;
                cc.assetManager.loadAny(uuid, function (err, sp) {
                    if (err) return Editor.error(err);
                    _this.spriteFrame = sp;
                });
            }
        });
    },

    __preload () {
        this._super();

        if (CC_EDITOR) {
            this._convertTextureToSpriteFrame();
        }

        if (this._custom && this.spriteFrame && !this._renderSpriteFrame) {
            this._applySpriteFrame(this.spriteFrame);
        }
        else if (this._file) {
            if (this._custom) {
                let missCustomTexture = !this._getTexture();
                if (missCustomTexture) { 
                    this._applyFile();
                }
            }
            else {
                this._applyFile();
            }
        }
        // auto play
        if (!CC_EDITOR || cc.engine.isPlaying) {
            if (this.playOnLoad) {
                this.resetSystem();
            }
        }
        // Upgrade color type from v2.0.0
        if (CC_EDITOR && !(this._startColor instanceof cc.Color)) {
            this._startColor = cc.color(this._startColor);
            this._startColorVar = cc.color(this._startColorVar);
            this._endColor = cc.color(this._endColor);
            this._endColorVar = cc.color(this._endColorVar);
        }
    },

    onDestroy () {
        if (this.autoRemoveOnFinish) {
            this.autoRemoveOnFinish = false;    // already removed
        }
        if (this._buffer) {
            this._buffer.destroy();
            this._buffer = null;
        }
        // reset uv data so next time simulator will refill buffer uv info when exit edit mode from prefab.
        this._simulator._uvFilled = 0;
        this._super();
    },
    
    lateUpdate (dt) {
        if (!this._simulator.finished) {
            this._simulator.step(dt);
        }
    },

    // APIS

    /*
     * !#en Add a particle to the emitter.
     * !#zh 添加一个粒子到发射器中。
     * @method addParticle
     * @return {Boolean}
     */
    addParticle: function () {
        // Not implemented
    },

    /**
     * !#en Stop emitting particles. Running particles will continue to run until they die.
     * !#zh 停止发射器发射粒子，发射出去的粒子将继续运行，直至粒子生命结束。
     * @method stopSystem
     * @example
     * // stop particle system.
     * myParticleSystem.stopSystem();
     */
    stopSystem: function () {
        this._stopped = true;
        this._simulator.stop();
    },

    /**
     * !#en Kill all living particles.
     * !#zh 杀死所有存在的粒子，然后重新启动粒子发射器。
     * @method resetSystem
     * @example
     * // play particle system.
     * myParticleSystem.resetSystem();
     */
    resetSystem: function () {
        this._stopped = false;
        this._simulator.reset();
        this.markForRender(true);
    },

    /**
     * !#en Whether or not the system is full.
     * !#zh 发射器中粒子是否大于等于设置的总粒子数量。
     * @method isFull
     * @return {Boolean}
     */
    isFull: function () {
        return (this.particleCount >= this.totalParticles);
    },

    /**
     * !#en Sets a new texture with a rect. The rect is in texture position and size.
     * Please use spriteFrame property instead, this function is deprecated since v1.9
     * !#zh 设置一张新贴图和关联的矩形。
     * 请直接设置 spriteFrame 属性，这个函数从 v1.9 版本开始已经被废弃
     * @method setTextureWithRect
     * @param {Texture2D} texture
     * @param {Rect} rect
     * @deprecated since v1.9
     */
    setTextureWithRect: function (texture, rect) {
        if (texture instanceof cc.Texture2D) {
            this.spriteFrame = new cc.SpriteFrame(texture, rect);
        }
    },

    // PRIVATE METHODS

    _applyFile: function () {
        let file = this._file;
        if (file) {
            var self = this;
            cc.assetManager.postLoadNative(file, function (err) {
                if (err || !file._nativeAsset) {
                    cc.errorID(6029);
                    return;
                }
                if (!self.isValid) {
                    return;
                }

                self._plistFile = file.nativeUrl;
                
                if (!self._custom) {
                    var isDiffFrame = self._spriteFrame !== file.spriteFrame;
                    if (isDiffFrame) self.spriteFrame = file.spriteFrame;
                    self._initWithDictionary(file._nativeAsset);
                }
                
                if (!self._spriteFrame) {
                    if (file.spriteFrame) {
                        self.spriteFrame = file.spriteFrame;
                    }
                    else if (self._custom) {
                        self._initTextureWithDictionary(file._nativeAsset);
                    }
                }
                else if (!self._renderSpriteFrame && self._spriteFrame) {
                    self._applySpriteFrame(self.spriteFrame);
                }
            });
        }
    },

    _initTextureWithDictionary: function (dict) {
        let imgPath = cc.path.changeBasename(this._plistFile, dict["textureFileName"] || '');
        // texture
        if (dict["textureFileName"]) {
            // Try to get the texture from the cache
            textureUtil.loadImage(imgPath, function (error, texture) {
                if (error) {
                    dict["textureFileName"] = undefined;
                    this._initTextureWithDictionary(dict);
                }
                else {
                    cc.assetManager.assets.add(imgPath, texture);
                    this.spriteFrame = new cc.SpriteFrame(texture);
                }
            }, this);
        } else if (dict["textureImageData"]) {
            let textureData = dict["textureImageData"];

            if (textureData && textureData.length > 0) {
                let tex = cc.assetManager.assets.get(imgPath);
                
                if (!tex) {
                    let buffer = codec.unzipBase64AsArray(textureData, 1);
                    if (!buffer) {
                        cc.warnID(6030, this._file.name);
                        return false;
                    }

                    let imageFormat = getImageFormatByData(buffer);
                    if (imageFormat !== macro.ImageFormat.TIFF && imageFormat !== macro.ImageFormat.PNG) {
                        cc.warnID(6031, this._file.name);
                        return false;
                    }

                    let canvasObj = document.createElement("canvas");
                    if(imageFormat === macro.ImageFormat.PNG){
                        let myPngObj = new PNGReader(buffer);
                        myPngObj.render(canvasObj);
                    } else {
                        tiffReader.parseTIFF(buffer,canvasObj);
                    }
                    tex = textureUtil.cacheImage(imgPath, canvasObj);
                }
                
                if (!tex)
                    cc.warnID(6032, this._file.name);
                // TODO: Use cc.assetManager to load asynchronously the SpriteFrame object, avoid using textureUtil
                this.spriteFrame = new cc.SpriteFrame(tex);
            }
            else {
                return false;
            }
        }
        return true;
    },

    // parsing process
    _initWithDictionary: function (dict) {
        this.totalParticles = parseInt(dict["maxParticles"] || 0);

        // life span
        this.life = parseFloat(dict["particleLifespan"] || 0);
        this.lifeVar = parseFloat(dict["particleLifespanVariance"] || 0);

        // emission Rate
        let _tempEmissionRate = dict["emissionRate"];
        if (_tempEmissionRate) {
            this.emissionRate = _tempEmissionRate;
        }
        else {
            this.emissionRate = Math.min(this.totalParticles / this.life, Number.MAX_VALUE);
        }

        // duration
        this.duration = parseFloat(dict["duration"] || 0);

        // blend function
        this.srcBlendFactor = parseInt(dict["blendFuncSource"] || macro.SRC_ALPHA);
        this.dstBlendFactor = parseInt(dict["blendFuncDestination"] || macro.ONE_MINUS_SRC_ALPHA);

        // color
        let locStartColor = this._startColor;
        locStartColor.r = parseFloat(dict["startColorRed"] || 0) * 255;
        locStartColor.g = parseFloat(dict["startColorGreen"] || 0) * 255;
        locStartColor.b = parseFloat(dict["startColorBlue"] || 0) * 255;
        locStartColor.a = parseFloat(dict["startColorAlpha"] || 0) * 255;

        let locStartColorVar = this._startColorVar;
        locStartColorVar.r = parseFloat(dict["startColorVarianceRed"] || 0) * 255;
        locStartColorVar.g = parseFloat(dict["startColorVarianceGreen"] || 0) * 255;
        locStartColorVar.b = parseFloat(dict["startColorVarianceBlue"] || 0) * 255;
        locStartColorVar.a = parseFloat(dict["startColorVarianceAlpha"] || 0) * 255;

        let locEndColor = this._endColor;
        locEndColor.r = parseFloat(dict["finishColorRed"] || 0) * 255;
        locEndColor.g = parseFloat(dict["finishColorGreen"] || 0) * 255;
        locEndColor.b = parseFloat(dict["finishColorBlue"] || 0) * 255;
        locEndColor.a = parseFloat(dict["finishColorAlpha"] || 0) * 255;

        let locEndColorVar = this._endColorVar;
        locEndColorVar.r = parseFloat(dict["finishColorVarianceRed"] || 0) * 255;
        locEndColorVar.g = parseFloat(dict["finishColorVarianceGreen"] || 0) * 255;
        locEndColorVar.b = parseFloat(dict["finishColorVarianceBlue"] || 0) * 255;
        locEndColorVar.a = parseFloat(dict["finishColorVarianceAlpha"] || 0) * 255;

        // particle size
        this.startSize = parseFloat(dict["startParticleSize"] || 0);
        this.startSizeVar = parseFloat(dict["startParticleSizeVariance"] || 0);
        this.endSize = parseFloat(dict["finishParticleSize"] || 0);
        this.endSizeVar = parseFloat(dict["finishParticleSizeVariance"] || 0);

        // position
        // Make empty positionType value and old version compatible
        this.positionType = parseFloat(dict['positionType'] !== undefined ? dict['positionType'] : PositionType.RELATIVE);
        // for
        this.sourcePos.x = 0;
        this.sourcePos.y = 0;
        this.posVar.x = parseFloat(dict["sourcePositionVariancex"] || 0);
        this.posVar.y = parseFloat(dict["sourcePositionVariancey"] || 0);

        // angle
        this.angle = parseFloat(dict["angle"] || 0);
        this.angleVar = parseFloat(dict["angleVariance"] || 0);

        // Spinning
        this.startSpin = parseFloat(dict["rotationStart"] || 0);
        this.startSpinVar = parseFloat(dict["rotationStartVariance"] || 0);
        this.endSpin = parseFloat(dict["rotationEnd"] || 0);
        this.endSpinVar = parseFloat(dict["rotationEndVariance"] || 0);

        this.emitterMode = parseInt(dict["emitterType"] || EmitterMode.GRAVITY);

        // Mode A: Gravity + tangential accel + radial accel
        if (this.emitterMode === EmitterMode.GRAVITY) {
            // gravity
            this.gravity.x = parseFloat(dict["gravityx"] || 0);
            this.gravity.y = parseFloat(dict["gravityy"] || 0);

            // speed
            this.speed = parseFloat(dict["speed"] || 0);
            this.speedVar = parseFloat(dict["speedVariance"] || 0);

            // radial acceleration
            this.radialAccel = parseFloat(dict["radialAcceleration"] || 0);
            this.radialAccelVar = parseFloat(dict["radialAccelVariance"] || 0);

            // tangential acceleration
            this.tangentialAccel = parseFloat(dict["tangentialAcceleration"] || 0);
            this.tangentialAccelVar = parseFloat(dict["tangentialAccelVariance"] || 0);

            // rotation is dir
            let locRotationIsDir = dict["rotationIsDir"] || "";
            if (locRotationIsDir !== null) {
                locRotationIsDir = locRotationIsDir.toString().toLowerCase();
                this.rotationIsDir = (locRotationIsDir === "true" || locRotationIsDir === "1");
            }
            else {
                this.rotationIsDir = false;
            }
        } else if (this.emitterMode === EmitterMode.RADIUS) {
            // or Mode B: radius movement
            this.startRadius = parseFloat(dict["maxRadius"] || 0);
            this.startRadiusVar = parseFloat(dict["maxRadiusVariance"] || 0);
            this.endRadius = parseFloat(dict["minRadius"] || 0);
            this.endRadiusVar = parseFloat(dict["minRadiusVariance"] || 0);
            this.rotatePerS = parseFloat(dict["rotatePerSecond"] || 0);
            this.rotatePerSVar = parseFloat(dict["rotatePerSecondVariance"] || 0);
        } else {
            cc.warnID(6009);
            return false;
        }

        this._initTextureWithDictionary(dict);
        return true;
    },

    _validateRender () {
        let texture = this._getTexture();
        if (!texture || !texture.loaded) {
            this.disableRender();
            return;
        }
        this._super();
    },

    _onTextureLoaded () {
        this._simulator.updateUVs(true);
        this._syncAspect();
        this._updateMaterial();
        this.markForRender(true);
    },

    _syncAspect () {
        let frameRect = this._renderSpriteFrame._rect;
        this._aspectRatio = frameRect.width / frameRect.height;
    },

    _applySpriteFrame () {
        this._renderSpriteFrame = this._renderSpriteFrame || this._spriteFrame;
        if (this._renderSpriteFrame) {
            if (this._renderSpriteFrame.textureLoaded()) {
                this._onTextureLoaded();
            }
            else {
                this._renderSpriteFrame.onTextureLoaded(this._onTextureLoaded, this);
            }
        }
    },

    _getTexture () {
        return (this._renderSpriteFrame && this._renderSpriteFrame.getTexture()) || this._texture;
    },

    _updateMaterial () {
        let material = this.getMaterial(0);
        if (!material) return;

        material.define('CC_USE_MODEL', this._positionType !== PositionType.FREE);
        material.setProperty('texture', this._getTexture());

        BlendFunc.prototype._updateMaterial.call(this);
    },

    _finishedSimulation: function () {
        if (CC_EDITOR) {
            if (this.preview && this._focused && !this.active && !cc.engine.isPlaying) {
                this.resetSystem();
            }
            return;
        }
        this.resetSystem();
        this.stopSystem();
        this.disableRender();
        if (this.autoRemoveOnFinish && this._stopped) {
            this.node.destroy();
        }
    }
});

cc.ParticleSystem = module.exports = ParticleSystem;

