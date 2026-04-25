#!/usr/bin/env bash
# cc-statusline runtime script
# Usage: bash statusline.sh [preset] [theme] [icon_style]

set -f

PRESET="${1:-full}"
THEME="${2:-aurora}"
ICON_STYLE="${3:-classic}"
CUSTOM_LAYOUT_MODE="${CC_STATUSLINE_CUSTOM_LAYOUT_MODE:-${CUSTOM_LAYOUT_MODE:-false}}"
CUSTOM_THEME="${CC_STATUSLINE_CUSTOM_THEME:-${CUSTOM_THEME:-}}"
CUSTOM_ICON_STYLE="${CC_STATUSLINE_CUSTOM_ICON_STYLE:-${CUSTOM_ICON_STYLE:-}}"
CUSTOM_LINE_1="${CC_STATUSLINE_CUSTOM_LINE_1:-${CUSTOM_LINE_1:-}}"
CUSTOM_LINE_2="${CC_STATUSLINE_CUSTOM_LINE_2:-${CUSTOM_LINE_2:-}}"
CUSTOM_LINE_3="${CC_STATUSLINE_CUSTOM_LINE_3:-${CUSTOM_LINE_3:-}}"

[ -n "$CUSTOM_THEME" ] && THEME="$CUSTOM_THEME"
[ -n "$CUSTOM_ICON_STYLE" ] && ICON_STYLE="$CUSTOM_ICON_STYLE"
[ "$PRESET" = "custom" ] && CUSTOM_LAYOUT_MODE="true"

ESC=$(printf '\033')
RESET="${ESC}[0m"
BOLD="${ESC}[1m"
DIM="${ESC}[2m"

JQ="$HOME/.claude/jq.exe"
[ ! -x "$JQ" ] && JQ="$HOME/.claude/jq"
[ ! -x "$JQ" ] && JQ="jq"

input=$(cat)

if [ -z "$input" ]; then
    printf '✨ Claude Code'
    exit 0
fi

if ! "$JQ" --version >/dev/null 2>&1; then
    printf 'Claude Code | jq missing'
    exit 0
fi

load_theme() {
    case "$THEME" in
        aurora|Aurora)
            COLOR_MODEL="${ESC}[38;2;180;130;255m"
            COLOR_EFFORT="${ESC}[38;2;200;160;255m"
            COLOR_THINK="${ESC}[38;2;255;130;171m"
            COLOR_FAST="${ESC}[38;2;180;230;80m"
            COLOR_PERM_AUTO="${ESC}[38;2;72;201;176m"
            COLOR_PERM_PLAN="${ESC}[38;2;250;215;90m"
            COLOR_PERM_DEFAULT="${ESC}[38;2;100;149;237m"
            COLOR_ACTIVE="${ESC}[38;2;80;200;120m"
            COLOR_VERSION="${ESC}[38;2;72;201;176m"
            COLOR_CONTEXT="${ESC}[38;2;0;206;209m"
            COLOR_SKILLS="${ESC}[38;2;255;165;80m"
            COLOR_MCP="${ESC}[38;2;0;206;209m"
            COLOR_CWD="${ESC}[38;2;250;215;90m"
            COLOR_GIT="${ESC}[38;2;80;200;120m"
            COLOR_CTX_TOKENS="${ESC}[38;2;135;206;250m"
            COLOR_SUM_TOKENS="${ESC}[38;2;200;160;255m"
            COLOR_DURATION="${ESC}[38;2;135;206;250m"
            COLOR_COST="${ESC}[38;2;255;165;80m"
            COLOR_TEXT="${ESC}[38;2;220;220;230m"
            COLOR_MUTED="${ESC}[38;2;130;130;145m"
            COLOR_OK="${ESC}[38;2;80;200;120m"
            COLOR_CAUTION="${ESC}[38;2;250;215;90m"
            COLOR_WARN="${ESC}[38;2;255;165;80m"
            COLOR_DANGER="${ESC}[38;2;255;100;100m"
            ;;
        sunset|Sunset)
            COLOR_MODEL="${ESC}[38;2;255;185;30m"
            COLOR_EFFORT="${ESC}[38;2;255;175;50m"
            COLOR_THINK="${ESC}[38;2;255;120;120m"
            COLOR_FAST="${ESC}[38;2;255;210;60m"
            COLOR_PERM_AUTO="${ESC}[38;2;255;160;100m"
            COLOR_PERM_PLAN="${ESC}[38;2;255;140;40m"
            COLOR_PERM_DEFAULT="${ESC}[38;2;255;100;80m"
            COLOR_ACTIVE="${ESC}[38;2;255;210;60m"
            COLOR_VERSION="${ESC}[38;2;255;160;100m"
            COLOR_CONTEXT="${ESC}[38;2;255;140;40m"
            COLOR_SKILLS="${ESC}[38;2;255;175;50m"
            COLOR_MCP="${ESC}[38;2;255;160;100m"
            COLOR_CWD="${ESC}[38;2;255;185;30m"
            COLOR_GIT="${ESC}[38;2;255;210;60m"
            COLOR_CTX_TOKENS="${ESC}[38;2;255;100;80m"
            COLOR_SUM_TOKENS="${ESC}[38;2;255;175;50m"
            COLOR_DURATION="${ESC}[38;2;255;160;100m"
            COLOR_COST="${ESC}[38;2;255;80;60m"
            COLOR_TEXT="${ESC}[38;2;255;240;210m"
            COLOR_MUTED="${ESC}[38;2;160;130;110m"
            COLOR_OK="${ESC}[38;2;255;210;60m"
            COLOR_CAUTION="${ESC}[38;2;255;185;30m"
            COLOR_WARN="${ESC}[38;2;255;140;40m"
            COLOR_DANGER="${ESC}[38;2;255;80;60m"
            ;;
        ocean|Ocean)
            COLOR_MODEL="${ESC}[38;2;50;220;190m"
            COLOR_EFFORT="${ESC}[38;2;0;200;160m"
            COLOR_THINK="${ESC}[38;2;100;190;240m"
            COLOR_FAST="${ESC}[38;2;100;240;180m"
            COLOR_PERM_AUTO="${ESC}[38;2;80;210;160m"
            COLOR_PERM_PLAN="${ESC}[38;2;0;220;220m"
            COLOR_PERM_DEFAULT="${ESC}[38;2;30;144;255m"
            COLOR_ACTIVE="${ESC}[38;2;100;240;180m"
            COLOR_VERSION="${ESC}[38;2;50;220;190m"
            COLOR_CONTEXT="${ESC}[38;2;0;220;220m"
            COLOR_SKILLS="${ESC}[38;2;0;200;160m"
            COLOR_MCP="${ESC}[38;2;100;190;240m"
            COLOR_CWD="${ESC}[38;2;80;210;160m"
            COLOR_GIT="${ESC}[38;2;50;220;190m"
            COLOR_CTX_TOKENS="${ESC}[38;2;180;230;250m"
            COLOR_SUM_TOKENS="${ESC}[38;2;0;200;160m"
            COLOR_DURATION="${ESC}[38;2;100;190;240m"
            COLOR_COST="${ESC}[38;2;0;220;220m"
            COLOR_TEXT="${ESC}[38;2;180;230;250m"
            COLOR_MUTED="${ESC}[38;2;100;140;160m"
            COLOR_OK="${ESC}[38;2;100;240;180m"
            COLOR_CAUTION="${ESC}[38;2;100;190;240m"
            COLOR_WARN="${ESC}[38;2;0;220;220m"
            COLOR_DANGER="${ESC}[38;2;30;144;255m"
            ;;
        mono|Mono)
            COLOR_MODEL="${ESC}[38;2;240;240;240m"
            COLOR_EFFORT="${ESC}[38;2;200;200;200m"
            COLOR_THINK="${ESC}[38;2;200;200;200m"
            COLOR_FAST="${ESC}[38;2;240;240;240m"
            COLOR_PERM_AUTO="${ESC}[38;2;200;200;200m"
            COLOR_PERM_PLAN="${ESC}[38;2;160;160;160m"
            COLOR_PERM_DEFAULT="${ESC}[38;2;160;160;160m"
            COLOR_ACTIVE="${ESC}[38;2;240;240;240m"
            COLOR_VERSION="${ESC}[38;2;160;160;160m"
            COLOR_CONTEXT="${ESC}[38;2;200;200;200m"
            COLOR_SKILLS="${ESC}[38;2;200;200;200m"
            COLOR_MCP="${ESC}[38;2;160;160;160m"
            COLOR_CWD="${ESC}[38;2;200;200;200m"
            COLOR_GIT="${ESC}[38;2;200;200;200m"
            COLOR_CTX_TOKENS="${ESC}[38;2;160;160;160m"
            COLOR_SUM_TOKENS="${ESC}[38;2;160;160;160m"
            COLOR_DURATION="${ESC}[38;2;160;160;160m"
            COLOR_COST="${ESC}[38;2;200;200;200m"
            COLOR_TEXT="${ESC}[38;2;240;240;240m"
            COLOR_MUTED="${ESC}[38;2;120;120;120m"
            COLOR_OK="${ESC}[38;2;240;240;240m"
            COLOR_CAUTION="${ESC}[38;2;200;200;200m"
            COLOR_WARN="${ESC}[38;2;160;160;160m"
            COLOR_DANGER="${ESC}[38;2;120;120;120m"
            ;;
        *)
            THEME="aurora"
            load_theme
            ;;
    esac
}

load_icons() {
    case "$ICON_STYLE" in
        classic)
            ICON_MODEL='✨'
            ICON_EFFORT='⚡'
            ICON_THINK='🧠'
            ICON_FAST='🚀'
            ICON_PERM_AUTO='🔓'
            ICON_PERM_PLAN='🔐'
            ICON_PERM_DEFAULT='🔒'
            ICON_VERSION='⚙'
            ICON_ACTIVE='●'
            ICON_CONTEXT='🔋'
            ICON_SKILLS='🛠'
            ICON_MCP='🔌'
            ICON_CWD='📂'
            ICON_GIT='🌿'
            ICON_CTX_TOKENS='💬'
            ICON_SUM_TOKENS='📈'
            ICON_API='⏱'
            ICON_TTL='⏳'
            ICON_COST='💰'
            ;;
        minimal)
            ICON_MODEL='M'
            ICON_EFFORT='E'
            ICON_THINK='T'
            ICON_FAST='F'
            ICON_PERM_AUTO='A'
            ICON_PERM_PLAN='P'
            ICON_PERM_DEFAULT='D'
            ICON_VERSION='V'
            ICON_ACTIVE='•'
            ICON_CONTEXT='C'
            ICON_SKILLS='S'
            ICON_MCP='M'
            ICON_CWD='@'
            ICON_GIT='git'
            ICON_CTX_TOKENS='I/O'
            ICON_SUM_TOKENS='Σ'
            ICON_API='api'
            ICON_TTL='ttl'
            ICON_COST='$'
            ;;
        developer)
            ICON_MODEL='λ'
            ICON_EFFORT='≡'
            ICON_THINK='∴'
            ICON_FAST='≫'
            ICON_PERM_AUTO='+'
            ICON_PERM_PLAN='~'
            ICON_PERM_DEFAULT='-'
            ICON_VERSION='#'
            ICON_ACTIVE='●'
            ICON_CONTEXT='[]'
            ICON_SKILLS='sk'
            ICON_MCP='mc'
            ICON_CWD='::'
            ICON_GIT='git'
            ICON_CTX_TOKENS='in'
            ICON_SUM_TOKENS='Σ'
            ICON_API='api'
            ICON_TTL='all'
            ICON_COST='$'
            ;;
        *)
            ICON_STYLE='classic'
            load_icons
            ;;
    esac
}

format_tokens() {
    local num=$1
    if [ "$num" -ge 1000000 ] 2>/dev/null; then
        awk "BEGIN {printf \"%.1fM\", $num / 1000000}"
    elif [ "$num" -ge 1000 ] 2>/dev/null; then
        awk "BEGIN {printf \"%.1fK\", $num / 1000}"
    else
        printf '%d' "$num"
    fi
}

pct_color() {
    local pct=$1
    if [ "$pct" -ge 90 ] 2>/dev/null; then
        printf '%s' "$COLOR_DANGER"
    elif [ "$pct" -ge 70 ] 2>/dev/null; then
        printf '%s' "$COLOR_WARN"
    elif [ "$pct" -ge 50 ] 2>/dev/null; then
        printf '%s' "$COLOR_CAUTION"
    else
        printf '%s' "$COLOR_OK"
    fi
}

progress_bar() {
    local pct=$1
    local width=12
    [ "$pct" -lt 0 ] 2>/dev/null && pct=0
    [ "$pct" -gt 100 ] 2>/dev/null && pct=100
    local filled=$(( pct * width / 100 ))
    local empty=$(( width - filled ))
    local bar=''
    local i
    for (( i=0; i<filled; i++ )); do bar+="█"; done
    for (( i=0; i<empty; i++ )); do bar+="░"; done
    printf '%s' "$bar"
}

fmt_duration() {
    local ms=$1
    [ "$ms" -le 0 ] 2>/dev/null && { printf '0s'; return; }
    local total_sec=$(( ms / 1000 ))
    local min=$(( total_sec / 60 ))
    local sec=$(( total_sec % 60 ))
    if [ "$min" -gt 0 ]; then
        printf '%dm%02ds' "$min" "$sec"
    else
        printf '%ds' "$sec"
    fi
}

join_segments() {
    local delimiter=$1
    shift
    local output=''
    local segment
    for segment in "$@"; do
        [ -z "$segment" ] && continue
        if [ -n "$output" ]; then
            output+="$delimiter"
        fi
        output+="$segment"
    done
    printf '%s' "$output"
}

join_output_lines() {
    local output=''
    local line
    for line in "$@"; do
        [ -z "$line" ] && continue
        if [ -n "$output" ]; then
            output+=$'\n'
        fi
        output+="$line"
    done
    printf '%s' "$output"
}

module_segment() {
    case "$1" in
        model) printf '%s' "$seg_model" ;;
        modes) printf '%s' "$seg_modes" ;;
        version) printf '%s' "$seg_version" ;;
        active) printf '%s' "$seg_active" ;;
        context) printf '%s' "$seg_context" ;;
        tools) printf '%s' "$seg_tools" ;;
        cwd) printf '%s' "$seg_cwd" ;;
        git) printf '%s' "$seg_git" ;;
        ctx_tokens) printf '%s' "$seg_ctx_tokens" ;;
        sum_tokens) printf '%s' "$seg_sum_tokens" ;;
        duration) printf '%s' "$seg_duration" ;;
        cost) printf '%s' "$seg_cost" ;;
        *) printf '' ;;
    esac
}

render_custom_line() {
    local csv=$1
    local old_ifs=$IFS
    IFS=','
    read -r -a modules <<< "$csv"
    IFS=$old_ifs
    local parts=()
    local module trimmed segment
    for module in "${modules[@]}"; do
        trimmed=$(printf '%s' "$module" | tr -d '[:space:]')
        [ -z "$trimmed" ] && continue
        segment=$(module_segment "$trimmed")
        [ -n "$segment" ] && parts+=("$segment")
    done
    join_segments "$SEP" "${parts[@]}"
}

load_theme
load_icons

SEP="${COLOR_MUTED} │ ${RESET}"
DOT="${COLOR_MUTED} · ${RESET}"
AR_UP='↑'
AR_DN='↓'

model_name=$("$JQ" -r '.model.display_name // "Claude"' <<< "$input" 2>/dev/null)
version=$("$JQ" -r '.version // empty' <<< "$input" 2>/dev/null)

ctx_size=$("$JQ" -r '.context_window.context_window_size // 200000' <<< "$input" 2>/dev/null)
[ "$ctx_size" -eq 0 ] 2>/dev/null && ctx_size=200000
ctx_input=$("$JQ" -r '.context_window.current_usage.input_tokens // 0' <<< "$input" 2>/dev/null)
ctx_cache_w=$("$JQ" -r '.context_window.current_usage.cache_creation_input_tokens // 0' <<< "$input" 2>/dev/null)
ctx_cache_r=$("$JQ" -r '.context_window.current_usage.cache_read_input_tokens // 0' <<< "$input" 2>/dev/null)
ctx_output=$("$JQ" -r '.context_window.current_usage.output_tokens // 0' <<< "$input" 2>/dev/null)
ctx_total_in=$(( ctx_input + ctx_cache_w + ctx_cache_r ))
[ "$ctx_size" -gt 0 ] 2>/dev/null && pct_used=$(( ctx_total_in * 100 / ctx_size )) || pct_used=0
[ "$pct_used" -gt 100 ] 2>/dev/null && pct_used=100

cum_raw_in=$("$JQ" -r '.context_window.total_input_tokens // 0' <<< "$input" 2>/dev/null)
cum_cache_w=$("$JQ" -r '.context_window.total_cache_creation_input_tokens // 0' <<< "$input" 2>/dev/null)
cum_cache_r=$("$JQ" -r '.context_window.total_cache_read_input_tokens // 0' <<< "$input" 2>/dev/null)
cum_output=$("$JQ" -r '.context_window.total_output_tokens // 0' <<< "$input" 2>/dev/null)
cum_total_in=$(( cum_raw_in + cum_cache_w + cum_cache_r ))
[ "$cum_total_in" -eq 0 ] 2>/dev/null && cum_total_in=$cum_raw_in
cum_all=$(( cum_total_in + cum_output ))

cwd=$("$JQ" -r '.cwd // .workspace.current_dir // empty' <<< "$input" 2>/dev/null)
full_path=''
if [ -n "$cwd" ]; then
    display_dir="${cwd##*[/\\]}"
    parent="${cwd%[/\\]*}"
    parent_name="${parent##*[/\\]}"
    if [ -n "$parent_name" ] && [ "$parent_name" != "$display_dir" ]; then
        full_path="${parent_name}/${display_dir}"
    else
        full_path="$display_dir"
    fi
fi

git_branch=''
git_staged_add=0
git_staged_del=0
git_unstaged_add=0
git_unstaged_del=0
git_untracked=0
git_clean=true
if [ -n "$cwd" ] && [ -d "$cwd" ]; then
    git_branch=$(git -C "$cwd" rev-parse --abbrev-ref HEAD 2>/dev/null)
    if [ -n "$git_branch" ]; then
        read -r git_staged_add git_staged_del < <(git -C "$cwd" diff --cached --numstat 2>/dev/null | awk '{a+=$1; d+=$2} END {printf "%d %d\n", a, d}')
        read -r git_unstaged_add git_unstaged_del < <(git -C "$cwd" diff --numstat 2>/dev/null | awk '{a+=$1; d+=$2} END {printf "%d %d\n", a, d}')
        git_untracked=$(git -C "$cwd" ls-files --others --exclude-standard 2>/dev/null | wc -l | tr -d ' ')
        total_changes=$(( git_staged_add + git_staged_del + git_unstaged_add + git_unstaged_del + git_untracked ))
        [ "$total_changes" -gt 0 ] && git_clean=false
    fi
fi

settings_path="$HOME/.claude/settings.json"
project_settings="$cwd/.claude/settings.json"

effort_level="high"
[ -n "${CLAUDE_CODE_EFFORT_LEVEL:-}" ] && effort_level="$CLAUDE_CODE_EFFORT_LEVEL"
if [ -f "$settings_path" ]; then
    val=$("$JQ" -r '.effortLevel // empty' "$settings_path" 2>/dev/null)
    [ -n "$val" ] && effort_level="$val"
fi

thinking_enabled="true"
if [ -f "$settings_path" ]; then
    val=$("$JQ" -r '.alwaysThinkingEnabled // empty' "$settings_path" 2>/dev/null)
    [ -n "$val" ] && thinking_enabled="$val"
fi

perm_mode="default"
if [ -f "$project_settings" ]; then
    val=$("$JQ" -r '.permissions.defaultMode // .permissions.allow_mode // empty' "$project_settings" 2>/dev/null)
    [ -n "$val" ] && perm_mode="$val"
fi
if [ "$perm_mode" = "default" ] && [ -f "$settings_path" ]; then
    val=$("$JQ" -r '.permissions.defaultMode // .permissions.allow_mode // empty' "$settings_path" 2>/dev/null)
    [ -n "$val" ] && perm_mode="$val"
fi

fast_mode="false"
if [ -f "$settings_path" ]; then
    val=$("$JQ" -r '.fastMode // empty' "$settings_path" 2>/dev/null)
    [ "$val" = "true" ] && fast_mode="true"
fi

mcp_count=0
if [ -f "$settings_path" ]; then
    val=$("$JQ" -r '.mcpServers // {} | keys | length' "$settings_path" 2>/dev/null)
    [ -n "$val" ] && mcp_count=$val
fi
if [ -f "$project_settings" ]; then
    val=$("$JQ" -r '.mcpServers // {} | keys | length' "$project_settings" 2>/dev/null)
    [ -n "$val" ] && mcp_count=$(( mcp_count + val ))
fi

skills_count=0
skills_dir="$HOME/.claude/skills"
[ -d "$skills_dir" ] && skills_count=$(ls -1 "$skills_dir" 2>/dev/null | wc -l | tr -d ' ')

session_cost=$("$JQ" -r '.cost.total_cost_usd // empty' <<< "$input" 2>/dev/null)
if [ -n "$session_cost" ] && [ "$session_cost" != "null" ]; then
    session_cost=$(awk "BEGIN {printf \"%.2f\", $session_cost}" 2>/dev/null)
fi
api_duration_ms=$("$JQ" -r '.cost.total_api_duration_ms // 0' <<< "$input" 2>/dev/null)
total_duration_ms=$("$JQ" -r '.cost.total_duration_ms // 0' <<< "$input" 2>/dev/null)

seg_model="${COLOR_MODEL}${BOLD}${ICON_MODEL}${RESET} ${COLOR_MODEL}${model_name}${RESET}"

case "$effort_level" in
    low) effort_text='Low' ;;
    medium) effort_text='Med' ;;
    high) effort_text='High' ;;
    max) effort_text='Max' ;;
    *) effort_text="$effort_level" ;;
esac
seg_effort="${COLOR_EFFORT}${ICON_EFFORT}${RESET} ${COLOR_EFFORT}${effort_text}${RESET}"
if [ "$thinking_enabled" = "true" ]; then
    seg_think="${COLOR_THINK}${ICON_THINK}${RESET} ${COLOR_THINK}Think${RESET}"
else
    seg_think="${COLOR_MUTED}${ICON_THINK}${RESET} ${COLOR_MUTED}Off${RESET}"
fi
if [ "$fast_mode" = "true" ]; then
    seg_fast="${COLOR_FAST}${ICON_FAST}${RESET} ${COLOR_FAST}Fast${RESET}"
else
    seg_fast="${COLOR_MUTED}${ICON_FAST}${RESET} ${COLOR_MUTED}Normal${RESET}"
fi
case "$perm_mode" in
    auto-accept|auto) seg_perm="${COLOR_PERM_AUTO}${ICON_PERM_AUTO}${RESET} ${COLOR_PERM_AUTO}Auto${RESET}" ;;
    plan|plan-mode) seg_perm="${COLOR_PERM_PLAN}${ICON_PERM_PLAN}${RESET} ${COLOR_PERM_PLAN}Plan${RESET}" ;;
    *) seg_perm="${COLOR_PERM_DEFAULT}${ICON_PERM_DEFAULT}${RESET} ${COLOR_PERM_DEFAULT}Default${RESET}" ;;
esac
seg_modes=$(join_segments "$DOT" "$seg_effort" "$seg_think" "$seg_fast" "$seg_perm")

if [ -n "$version" ] && [ "$version" != "null" ]; then
    seg_version="${COLOR_VERSION}${ICON_VERSION}${RESET} ${COLOR_VERSION}v${version}${RESET}"
else
    seg_version="${COLOR_MUTED}${ICON_VERSION}${RESET} ${COLOR_MUTED}--${RESET}"
fi
seg_active="${COLOR_ACTIVE}${ICON_ACTIVE}${RESET} ${COLOR_ACTIVE}Active${RESET}"

bc=$(pct_color "$pct_used")
bar=$(progress_bar "$pct_used")
seg_context="${COLOR_CONTEXT}${ICON_CONTEXT}${RESET} ${bc}$(format_tokens "$ctx_total_in")${COLOR_MUTED}/${RESET}${COLOR_TEXT}$(format_tokens "$ctx_size")${RESET} ${bc}${bar} ${pct_used}%${RESET}"

if [ "$skills_count" -gt 0 ]; then
    seg_skills="${COLOR_SKILLS}${ICON_SKILLS}${RESET} ${COLOR_SKILLS}Skills:${skills_count}${RESET}"
else
    seg_skills="${COLOR_MUTED}${ICON_SKILLS}${RESET} ${COLOR_MUTED}Skills:0${RESET}"
fi
if [ "$mcp_count" -gt 0 ]; then
    seg_mcp="${COLOR_MCP}${ICON_MCP}${RESET} ${COLOR_MCP}MCP:${mcp_count}${RESET}"
else
    seg_mcp="${COLOR_MUTED}${ICON_MCP}${RESET} ${COLOR_MUTED}MCP:0${RESET}"
fi
seg_tools=$(join_segments "$DOT" "$seg_skills" "$seg_mcp")

if [ -n "$full_path" ]; then
    seg_cwd="${COLOR_CWD}${ICON_CWD}${RESET} ${COLOR_CWD}${full_path}${RESET}"
else
    seg_cwd="${COLOR_CWD}${ICON_CWD}${RESET} ${DIM}~${RESET}"
fi

if [ -n "$git_branch" ]; then
    git_status=''
    if $git_clean; then
        git_status="${COLOR_OK}✓${RESET}"
    else
        parts=''
        sa=$(( git_staged_add + git_unstaged_add ))
        sd=$(( git_staged_del + git_unstaged_del ))
        [ "$sa" -gt 0 ] && parts+="${COLOR_OK}+${sa}${RESET}"
        [ "$sd" -gt 0 ] && parts+="${parts:+ }${COLOR_DANGER}-${sd}${RESET}"
        [ "$git_untracked" -gt 0 ] && parts+="${parts:+ }${COLOR_WARN}?${git_untracked}${RESET}"
        git_status="${DIM}(${RESET}${parts}${DIM})${RESET}"
    fi
    seg_git="${COLOR_GIT}${ICON_GIT}${RESET} ${COLOR_GIT}${git_branch}${RESET} ${git_status}"
else
    seg_git="${COLOR_MUTED}${ICON_GIT}${RESET} ${COLOR_MUTED}no repo${RESET}"
fi

seg_ctx_tokens="${COLOR_CTX_TOKENS}${ICON_CTX_TOKENS}${RESET} ${COLOR_CTX_TOKENS}Ctx${RESET} ${COLOR_OK}${AR_UP}${RESET}${COLOR_TEXT}$(format_tokens "$ctx_total_in")${RESET} ${COLOR_WARN}${AR_DN}${RESET}${COLOR_TEXT}$(format_tokens "$ctx_output")${RESET}"
seg_sum_tokens="${COLOR_SUM_TOKENS}${ICON_SUM_TOKENS}${RESET} ${COLOR_SUM_TOKENS}Sum${RESET} ${COLOR_OK}${AR_UP}${RESET}${COLOR_TEXT}$(format_tokens "$cum_total_in")${RESET} ${COLOR_WARN}${AR_DN}${RESET}${COLOR_TEXT}$(format_tokens "$cum_output")${RESET} ${DIM}(${RESET}${COLOR_SUM_TOKENS}$(format_tokens "$cum_all")${RESET}${DIM})${RESET}"
seg_duration=$(join_segments "$DOT" \
    "${COLOR_DURATION}${ICON_API}${RESET} ${COLOR_DURATION}API${RESET} ${COLOR_TEXT}$(fmt_duration "$api_duration_ms")${RESET}" \
    "${COLOR_DURATION}${ICON_TTL}${RESET} ${COLOR_DURATION}TTL${RESET} ${COLOR_TEXT}$(fmt_duration "$total_duration_ms")${RESET}")
seg_cost=''
if [ -n "$session_cost" ] && [ "$session_cost" != "null" ] && [ "$session_cost" != "0.00" ]; then
    seg_cost="${COLOR_COST}${ICON_COST}${RESET} ${COLOR_COST}\$${session_cost}${RESET}"
fi

line_full_1=$(join_segments "$SEP" "$seg_model" "$seg_modes" "$seg_version" "$seg_active")
line_full_2=$(join_segments "$SEP" "$seg_context" "$seg_tools" "$seg_cwd" "$seg_git")
line_full_3=$(join_segments "$SEP" "$seg_ctx_tokens" "$seg_sum_tokens" "$seg_duration" "$seg_cost")

line_standard_1="$line_full_1"
line_standard_2="$line_full_2"

line_minimal_1=$(join_segments "$SEP" "$seg_model" "$seg_version" "$seg_active" "$seg_cost")

line_developer_1=$(join_segments "$SEP" "$seg_model" "$seg_modes" "$seg_active")
line_developer_2=$(join_segments "$SEP" "$seg_cwd" "$seg_git" "$seg_context")
line_developer_3=$(join_segments "$SEP" "$seg_ctx_tokens" "$seg_sum_tokens" "$seg_duration" "$seg_cost")

if [ "$CUSTOM_LAYOUT_MODE" = "true" ]; then
    custom_line_1=$(render_custom_line "$CUSTOM_LINE_1")
    custom_line_2=$(render_custom_line "$CUSTOM_LINE_2")
    custom_line_3=$(render_custom_line "$CUSTOM_LINE_3")
    custom_output=$(join_output_lines "$custom_line_1" "$custom_line_2" "$custom_line_3")
    if [ -n "$custom_output" ]; then
        printf '%s' "$custom_output"
        exit 0
    fi
fi

case "$PRESET" in
    full)
        printf '%s\n%s\n%s' "$line_full_1" "$line_full_2" "$line_full_3"
        ;;
    standard)
        printf '%s\n%s' "$line_standard_1" "$line_standard_2"
        ;;
    minimal)
        printf '%s' "$line_minimal_1"
        ;;
    developer)
        printf '%s\n%s\n%s' "$line_developer_1" "$line_developer_2" "$line_developer_3"
        ;;
    *)
        printf '%s\n%s\n%s' "$line_full_1" "$line_full_2" "$line_full_3"
        ;;
esac
