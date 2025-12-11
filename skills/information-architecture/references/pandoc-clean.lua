-- Simplify EPUB markup when converting to Markdown.
-- Strips formatting attributes while preserving textual content.

function Span(el)
  -- Drop styling attributes; keep inline content.
  if #el.content == 0 then
    return {}
  end
  return pandoc.Span(el.content)
end

function Div(el)
  -- Remove wrapper divs that carry classes/ids only.
  return el.content
end

function Figure(el)
  -- Flatten figures to their children (e.g., images or captions).
  return el.content
end
