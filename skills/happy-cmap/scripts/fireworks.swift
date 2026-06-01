#!/usr/bin/env swift
import Cocoa

// MARK: - Particle / Rocket

final class Particle {
    var x: CGFloat, y: CGFloat
    var vx: CGFloat, vy: CGFloat
    var life: CGFloat
    let maxLife: CGFloat
    let hue: CGFloat
    let size: CGFloat
    var trail: [(CGFloat, CGFloat, CGFloat)] = []

    init(x: CGFloat, y: CGFloat, hue: CGFloat) {
        self.x = x; self.y = y
        let angle = CGFloat.random(in: 0 ..< (2 * .pi))
        let speed = CGFloat.random(in: 70 ... 320)
        self.vx = cos(angle) * speed
        self.vy = sin(angle) * speed
        let l = CGFloat.random(in: 1.1 ... 2.2)
        self.life = l; self.maxLife = l
        var h = hue + CGFloat.random(in: -0.04 ... 0.04)
        if h < 0 { h += 1 }; if h >= 1 { h -= 1 }
        self.hue = h
        self.size = CGFloat.random(in: 2.2 ... 4.2)
    }

    func step(_ dt: CGFloat) -> Bool {
        trail.append((x, y, alpha))
        if trail.count > 6 { trail.removeFirst() }
        x += vx * dt
        y += vy * dt
        vy -= 230 * dt          // gravity (NSView y-up)
        let drag = pow(0.55, dt)
        vx *= drag; vy *= drag
        life -= dt
        return life > 0
    }

    var alpha: CGFloat { max(0, life / maxLife) }
}

final class Rocket {
    var x: CGFloat, y: CGFloat
    var vx: CGFloat, vy: CGFloat
    let hue: CGFloat
    let explodeY: CGFloat
    var trail: [(CGFloat, CGFloat)] = []

    init(width: CGFloat, height: CGFloat) {
        x = CGFloat.random(in: width * 0.15 ... width * 0.85)
        y = 0
        let target = CGFloat.random(in: height * 0.55 ... height * 0.85)
        explodeY = target
        let g: CGFloat = 380
        vy = sqrt(2 * g * target) * 0.95
        vx = CGFloat.random(in: -40 ... 40)
        hue = CGFloat.random(in: 0 ... 1)
    }

    func step(_ dt: CGFloat) -> Bool {
        trail.append((x, y))
        if trail.count > 10 { trail.removeFirst() }
        x += vx * dt
        y += vy * dt
        vy -= 380 * dt
        return vy > 0 && y < explodeY
    }
}

// MARK: - View

final class FireworksView: NSView {
    private var rockets: [Rocket] = []
    private var particles: [Particle] = []
    private var lastTick = CACurrentMediaTime()
    private var spawnTimer: CGFloat = 0
    private var timer: Timer?

    override var isFlipped: Bool { false }

    func start() {
        lastTick = CACurrentMediaTime()
        timer = Timer.scheduledTimer(withTimeInterval: 1.0 / 60.0, repeats: true) { [weak self] _ in
            self?.tick()
        }
        if let t = timer { RunLoop.main.add(t, forMode: .common) }
    }

    func stop() { timer?.invalidate(); timer = nil }

    private func tick() {
        let now = CACurrentMediaTime()
        var dt = CGFloat(now - lastTick); lastTick = now
        if dt > 0.1 { dt = 0.1 }

        let w = bounds.width, h = bounds.height
        spawnTimer -= dt
        if spawnTimer <= 0 {
            rockets.append(Rocket(width: w, height: h))
            spawnTimer = CGFloat.random(in: 0.20 ... 0.75)
        }

        var aliveR: [Rocket] = []
        aliveR.reserveCapacity(rockets.count)
        for r in rockets {
            if r.step(dt) {
                aliveR.append(r)
            } else {
                let count = Int.random(in: 90 ... 160)
                for _ in 0 ..< count {
                    particles.append(Particle(x: r.x, y: r.y, hue: r.hue))
                }
            }
        }
        rockets = aliveR
        particles = particles.filter { $0.step(dt) }
        needsDisplay = true
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let ctx = NSGraphicsContext.current?.cgContext else { return }
        ctx.clear(bounds)

        // rocket trails & heads (normal blend)
        for r in rockets {
            for (i, p) in r.trail.enumerated() {
                let a = CGFloat(i) / CGFloat(max(r.trail.count, 1)) * 0.55
                ctx.setFillColor(NSColor(hue: r.hue, saturation: 0.4, brightness: 1.0, alpha: a).cgColor)
                ctx.fillEllipse(in: CGRect(x: p.0 - 1.5, y: p.1 - 1.5, width: 3, height: 3))
            }
            ctx.setFillColor(NSColor(hue: r.hue, saturation: 0.5, brightness: 1.0, alpha: 1).cgColor)
            ctx.fillEllipse(in: CGRect(x: r.x - 2.5, y: r.y - 2.5, width: 5, height: 5))
        }

        // particles with additive blend for glow
        ctx.setBlendMode(.plusLighter)
        for p in particles {
            for (i, t) in p.trail.enumerated() {
                let f = CGFloat(i) / CGFloat(max(p.trail.count, 1))
                let a = t.2 * f * 0.35
                let s = p.size * f
                ctx.setFillColor(NSColor(hue: p.hue, saturation: 0.9, brightness: 1.0, alpha: a).cgColor)
                ctx.fillEllipse(in: CGRect(x: t.0 - s/2, y: t.1 - s/2, width: s, height: s))
            }
            let glow = p.size * 4.5
            ctx.setFillColor(NSColor(hue: p.hue, saturation: 0.75, brightness: 1.0, alpha: p.alpha * 0.20).cgColor)
            ctx.fillEllipse(in: CGRect(x: p.x - glow/2, y: p.y - glow/2, width: glow, height: glow))
            ctx.setFillColor(NSColor(hue: p.hue, saturation: 0.6, brightness: 1.0, alpha: p.alpha).cgColor)
            ctx.fillEllipse(in: CGRect(x: p.x - p.size/2, y: p.y - p.size/2, width: p.size, height: p.size))
        }
        ctx.setBlendMode(.normal)
    }
}

// MARK: - App bootstrap

let app = NSApplication.shared
app.setActivationPolicy(.accessory)

let duration: TimeInterval = {
    if CommandLine.arguments.count >= 2, let d = Double(CommandLine.arguments[1]) { return d }
    return 8.0
}()

var windows: [NSWindow] = []
var views: [FireworksView] = []
for screen in NSScreen.screens {
    let rect = screen.frame
    let w = NSWindow(contentRect: rect, styleMask: [.borderless], backing: .buffered, defer: false)
    w.isOpaque = false
    w.backgroundColor = .clear
    w.level = NSWindow.Level(rawValue: Int(CGWindowLevelForKey(.maximumWindow)))
    w.ignoresMouseEvents = true
    w.collectionBehavior = [.canJoinAllSpaces, .stationary, .fullScreenAuxiliary, .ignoresCycle]
    w.hasShadow = false
    w.alphaValue = 0
    let v = FireworksView(frame: NSRect(origin: .zero, size: rect.size))
    v.wantsLayer = true
    w.contentView = v
    w.orderFrontRegardless()
    v.start()
    windows.append(w); views.append(v)
}

// fade in
NSAnimationContext.runAnimationGroup { ctx in
    ctx.duration = 0.35
    for w in windows { w.animator().alphaValue = 1 }
}

// fade out + quit
DispatchQueue.main.asyncAfter(deadline: .now() + duration - 1.0) {
    NSAnimationContext.runAnimationGroup({ ctx in
        ctx.duration = 1.0
        for w in windows { w.animator().alphaValue = 0 }
    }, completionHandler: {
        for v in views { v.stop() }
        NSApp.terminate(nil)
    })
}

// Ctrl+C / SIGTERM clean exit
signal(SIGINT) { _ in NSApp.terminate(nil) }
signal(SIGTERM) { _ in NSApp.terminate(nil) }

app.run()
