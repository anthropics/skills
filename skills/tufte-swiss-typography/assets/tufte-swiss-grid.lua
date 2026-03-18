-- tufte-swiss-grid.lua
-- ---------------------------------------------------------------------------
-- Observational callbacks for the tufte-swiss typography toolkit.
-- Counts overfull/underfull hboxes, tracks pages, prints a summary at end.
-- Never mutates nodes or layout. Returns nil from all callbacks.
-- ---------------------------------------------------------------------------

local M = {}

local overfull_count  = 0
local underfull_count = 0
local page_count      = 0

-- hpack_quality: count box warnings
local function on_hpack_quality(incident, detail, head, first, last)
    if incident == "overfull" then
        overfull_count = overfull_count + 1
    elseif incident == "underfull" then
        underfull_count = underfull_count + 1
    end
    return nil
end

-- start_page_number: increment page counter
local function on_start_page()
    page_count = page_count + 1
end

-- stop_run: print summary
local function on_stop_run()
    texio.write_nl("tufte-swiss: "
        .. overfull_count .. " overfull, "
        .. underfull_count .. " underfull. "
        .. page_count .. " page(s).")
end

-- Register all callbacks
function M.register()
    local add_cb = luatexbase and luatexbase.add_to_callback or nil

    if add_cb then
        add_cb("hpack_quality", on_hpack_quality, "tufte-swiss.hpack_quality")
        add_cb("stop_run", on_stop_run, "tufte-swiss.stop_run")
        -- start_page_number is exclusive — try managed, fall back to raw
        local ok = pcall(function()
            add_cb("start_page_number", on_start_page, "tufte-swiss.start_page")
        end)
        if not ok then
            pcall(callback.register, "start_page_number", on_start_page)
        end
    else
        callback.register("hpack_quality", on_hpack_quality)
        callback.register("start_page_number", on_start_page)
        callback.register("stop_run", on_stop_run)
    end

    texio.write_nl("tufte-swiss: callbacks registered.")
end

return M
