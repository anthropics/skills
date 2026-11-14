-- ============================================================
-- AdFlow 数据库 Schema (SQLite)
-- ============================================================

-- 素材库主表
CREATE TABLE IF NOT EXISTS materials (
    material_id         TEXT PRIMARY KEY,
    file_path           TEXT NOT NULL,
    original_filename   TEXT NOT NULL DEFAULT '',
    duration_ms         INTEGER NOT NULL DEFAULT 0,
    fps                 REAL NOT NULL DEFAULT 30.0,
    width               INTEGER NOT NULL DEFAULT 1080,
    height              INTEGER NOT NULL DEFAULT 1920,
    file_size_bytes     INTEGER NOT NULL DEFAULT 0,
    md5_hash            TEXT NOT NULL DEFAULT '',
    phash               TEXT NOT NULL DEFAULT '',
    -- 方向分类: vertical竖屏 / landscape横屏 / phone_rotated手机横拍竖看 / unknown
    orientation         TEXT NOT NULL DEFAULT 'unknown',

    -- 标签维度
    scene               TEXT NOT NULL DEFAULT '',
    shot_type           TEXT NOT NULL DEFAULT '',
    camera_movement     TEXT NOT NULL DEFAULT '',
    emotion             TEXT NOT NULL DEFAULT 'neutral',
    product_visibility  TEXT NOT NULL DEFAULT 'none',
    has_person          INTEGER NOT NULL DEFAULT 0,
    person_count        INTEGER NOT NULL DEFAULT 0,
    person_role         TEXT NOT NULL DEFAULT '',
    person_feature      TEXT NOT NULL DEFAULT '',
    has_dialogue        INTEGER NOT NULL DEFAULT 0,
    has_bgm             INTEGER NOT NULL DEFAULT 0,
    lighting            TEXT NOT NULL DEFAULT '',
    pace                TEXT NOT NULL DEFAULT 'medium',
    quality_flags       TEXT NOT NULL DEFAULT 'clean',
    material_category   TEXT NOT NULL DEFAULT '',
    tags                TEXT NOT NULL DEFAULT '[]',

    -- 质量评估
    auto_quality_score  REAL NOT NULL DEFAULT 0.0,

    -- 来源
    source_project      TEXT NOT NULL DEFAULT '',
    imported_at         TEXT NOT NULL DEFAULT '',
    notes               TEXT NOT NULL DEFAULT '',

    -- Diversity 追踪
    use_count_total     INTEGER NOT NULL DEFAULT 0,
    use_count_30d       INTEGER NOT NULL DEFAULT 0,
    last_used_at        TEXT NOT NULL DEFAULT '',
    cooldown_hours      INTEGER NOT NULL DEFAULT 48,
    performance_score   REAL NOT NULL DEFAULT 50.0,
    ctr_avg             REAL NOT NULL DEFAULT 0.0,
    cvr_avg             REAL NOT NULL DEFAULT 0.0,
    retention_3s_avg    REAL NOT NULL DEFAULT 0.0,
    retention_5s_avg    REAL NOT NULL DEFAULT 0.0
);

-- 素材标签关联表（自由标签多对多）
CREATE TABLE IF NOT EXISTS material_tags (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    material_id TEXT NOT NULL REFERENCES materials(material_id) ON DELETE CASCADE,
    tag_name    TEXT NOT NULL,
    UNIQUE(material_id, tag_name)
);

CREATE INDEX IF NOT EXISTS idx_material_tags_mid ON material_tags(material_id);
CREATE INDEX IF NOT EXISTS idx_material_tags_tag ON material_tags(tag_name);

-- 素材使用流水
CREATE TABLE IF NOT EXISTS material_usage_log (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    material_id     TEXT NOT NULL REFERENCES materials(material_id),
    ad_variant_id   TEXT NOT NULL DEFAULT '',
    shot_position   INTEGER NOT NULL DEFAULT 0,
    used_at         TEXT NOT NULL DEFAULT '',
    account_id      TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_usage_material ON material_usage_log(material_id);
CREATE INDEX IF NOT EXISTS idx_usage_variant ON material_usage_log(ad_variant_id);
CREATE INDEX IF NOT EXISTS idx_usage_account ON material_usage_log(account_id);

-- 产品信息档案
CREATE TABLE IF NOT EXISTS products (
    product_id          TEXT PRIMARY KEY,
    name                TEXT NOT NULL DEFAULT '',
    category            TEXT NOT NULL DEFAULT '',
    key_selling_points  TEXT NOT NULL DEFAULT '[]',
    target_audience     TEXT NOT NULL DEFAULT '',
    pain_points         TEXT NOT NULL DEFAULT '[]',
    brand_tone          TEXT NOT NULL DEFAULT '',
    prohibited_words    TEXT NOT NULL DEFAULT '[]',
    avg_price_range     TEXT NOT NULL DEFAULT '',
    competitors         TEXT NOT NULL DEFAULT '[]',
    notes               TEXT NOT NULL DEFAULT '',
    created_at          TEXT NOT NULL DEFAULT '',
    updated_at          TEXT NOT NULL DEFAULT ''
);

-- 出片任务
CREATE TABLE IF NOT EXISTS project_tasks (
    task_id             TEXT PRIMARY KEY,
    product_id          TEXT NOT NULL REFERENCES products(product_id),
    platform            TEXT NOT NULL DEFAULT 'ocean_engine',
    account_id          TEXT NOT NULL DEFAULT '',
    target_duration_ms  INTEGER NOT NULL DEFAULT 30000,
    variant_count       INTEGER NOT NULL DEFAULT 5,
    status              TEXT NOT NULL DEFAULT 'pending',
    strategy_id         TEXT NOT NULL DEFAULT '',
    created_at          TEXT NOT NULL DEFAULT '',
    completed_at        TEXT NOT NULL DEFAULT '',
    notes               TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_tasks_status ON project_tasks(status);
CREATE INDEX IF NOT EXISTS idx_tasks_product ON project_tasks(product_id);

-- 创意策略
CREATE TABLE IF NOT EXISTS creative_strategies (
    strategy_id     TEXT PRIMARY KEY,
    task_id         TEXT NOT NULL REFERENCES project_tasks(task_id),
    narrative_type  TEXT NOT NULL DEFAULT '',
    hook_type       TEXT NOT NULL DEFAULT '',
    pace_style      TEXT NOT NULL DEFAULT '',
    tone            TEXT NOT NULL DEFAULT '',
    key_message     TEXT NOT NULL DEFAULT '',
    target_emotion  TEXT NOT NULL DEFAULT '',
    reasoning       TEXT NOT NULL DEFAULT '',
    source_signals  TEXT NOT NULL DEFAULT '{}',
    created_at      TEXT NOT NULL DEFAULT ''
);

-- 分镜脚本
CREATE TABLE IF NOT EXISTS storyboard_scripts (
    script_id           TEXT PRIMARY KEY,
    task_id             TEXT NOT NULL REFERENCES project_tasks(task_id),
    strategy_id         TEXT NOT NULL DEFAULT '',
    cta_text            TEXT NOT NULL DEFAULT '',
    total_duration_ms   INTEGER NOT NULL DEFAULT 0,
    variant_index       INTEGER NOT NULL DEFAULT 0,
    created_at          TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_scripts_task ON storyboard_scripts(task_id);

-- 分镜明细（一行一镜）
CREATE TABLE IF NOT EXISTS storyboard_shots (
    id                          INTEGER PRIMARY KEY AUTOINCREMENT,
    script_id                   TEXT NOT NULL REFERENCES storyboard_scripts(script_id) ON DELETE CASCADE,
    shot_index                  INTEGER NOT NULL DEFAULT 0,
    role                        TEXT NOT NULL DEFAULT 'b_roll',
    duration_ms                 INTEGER NOT NULL DEFAULT 3000,
    description                 TEXT NOT NULL DEFAULT '',
    camera_direction            TEXT NOT NULL DEFAULT '',
    narration_text              TEXT NOT NULL DEFAULT '',
    required_product_visibility TEXT NOT NULL DEFAULT '',
    required_scene              TEXT NOT NULL DEFAULT '',
    required_emotion            TEXT NOT NULL DEFAULT '',
    fallback_notes              TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_shots_script ON storyboard_shots(script_id);

-- 剪辑时间线
CREATE TABLE IF NOT EXISTS edit_timelines (
    timeline_id     TEXT PRIMARY KEY,
    script_id       TEXT NOT NULL DEFAULT '',
    shots           TEXT NOT NULL DEFAULT '[]',
    bgm_file        TEXT NOT NULL DEFAULT '',
    subtitle_tracks TEXT NOT NULL DEFAULT '[]',
    cta_overlay     TEXT NOT NULL DEFAULT '{}',
    variant_metadata TEXT NOT NULL DEFAULT '{}'
);

-- 产出变体
CREATE TABLE IF NOT EXISTS ad_variants (
    variant_id              TEXT PRIMARY KEY,
    task_id                 TEXT NOT NULL REFERENCES project_tasks(task_id),
    script_id               TEXT NOT NULL DEFAULT '',
    timeline_id             TEXT NOT NULL DEFAULT '',
    output_file             TEXT NOT NULL DEFAULT '',
    variant_metadata        TEXT NOT NULL DEFAULT '{}',
    status                  TEXT NOT NULL DEFAULT 'pending_review',
    compliance_check_passed INTEGER NOT NULL DEFAULT 0,
    created_at              TEXT NOT NULL DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_variants_task ON ad_variants(task_id);
CREATE INDEX IF NOT EXISTS idx_variants_status ON ad_variants(status);

-- ============================================================
-- 爆款因子体系 — Analytics
-- ============================================================

-- 爆款标注表（类比量化 signal_records）
CREATE TABLE IF NOT EXISTS hit_labels (
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    video_path          TEXT NOT NULL DEFAULT '',
    video_source        TEXT NOT NULL DEFAULT 'local',
    source_task_id      TEXT NOT NULL DEFAULT '',

    -- 文案（标注关联的文案内容）
    copy_text           TEXT NOT NULL DEFAULT '',

    -- 投放数据（用户提供）
    impressions         INTEGER NOT NULL DEFAULT 0,
    clicks              INTEGER NOT NULL DEFAULT 0,
    conversions         INTEGER NOT NULL DEFAULT 0,
    ctr                 REAL NOT NULL DEFAULT 0.0,
    cvr                 REAL NOT NULL DEFAULT 0.0,
    cost                REAL NOT NULL DEFAULT 0.0,
    play_3s_rate        REAL NOT NULL DEFAULT 0.0,
    play_full_rate      REAL NOT NULL DEFAULT 0.0,
    like_count          INTEGER NOT NULL DEFAULT 0,
    share_count         INTEGER NOT NULL DEFAULT 0,
    comment_count       INTEGER NOT NULL DEFAULT 0,

    -- 标注
    label               TEXT NOT NULL DEFAULT 'normal',
    label_source        TEXT NOT NULL DEFAULT 'manual',
    label_notes         TEXT NOT NULL DEFAULT '',

    labeled_at          TEXT NOT NULL DEFAULT '',
    created_at          TEXT NOT NULL DEFAULT ''
);
CREATE INDEX IF NOT EXISTS idx_hit_label ON hit_labels(label);
CREATE INDEX IF NOT EXISTS idx_hit_task ON hit_labels(source_task_id);

-- 因子快照表（类比量化特征向量）
-- hit_label_id 可为 NULL（AdFlow产出自动快照时尚未标注）
CREATE TABLE IF NOT EXISTS factor_snapshots (
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    hit_label_id        INTEGER,
    source_type         TEXT NOT NULL DEFAULT '',
    source_task_id      TEXT NOT NULL DEFAULT '',

    -- 因子值 (JSON)
    rhythm_factors      TEXT NOT NULL DEFAULT '{}',
    emotion_factors     TEXT NOT NULL DEFAULT '{}',
    visual_factors      TEXT NOT NULL DEFAULT '{}',
    copy_factors        TEXT NOT NULL DEFAULT '{}',
    voice_factors       TEXT NOT NULL DEFAULT '{}',
    structure_factors   TEXT NOT NULL DEFAULT '{}',

    -- 全量因子向量 (JSON array, 30维, 供XGBoost直接使用)
    factor_vector       TEXT NOT NULL DEFAULT '[]',

    extracted_at        TEXT NOT NULL DEFAULT ''
);
CREATE INDEX IF NOT EXISTS idx_fs_label ON factor_snapshots(hit_label_id);
CREATE INDEX IF NOT EXISTS idx_fs_task ON factor_snapshots(source_task_id);
