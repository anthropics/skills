# File Upload for AI

Drag-and-drop file upload with AI-specific features like context preview and file type indicators.

## When to Use
- Uploading documents for AI analysis
- Attaching files to chat messages
- Adding context to AI prompts
- Knowledge base uploads

## Anatomy

```
┌─────────────────────────────────────────────────────────────┐
│  FileUpload                                                 │
│  ├─ DropZone (drag target with visual feedback)            │
│  │   ├─ Upload Icon                                        │
│  │   ├─ Instructions (drag here or click)                  │
│  │   └─ File Type Hints (PDF, images, etc.)                │
│  ├─ FileList (uploaded files with previews)                │
│  │   ├─ FileChip (thumbnail + name + remove)               │
│  │   └─ FileProgress (upload progress bar)                 │
│  └─ UploadActions (clear all, upload button)               │
└─────────────────────────────────────────────────────────────┘
```

## Token Usage

```css
/* Drop Zone */
.drop-zone {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: var(--spacing-xl);
  background: var(--color-surface-raised);
  border: 2px dashed var(--color-border-default);
  border-radius: var(--radius-xl);
  transition: all var(--duration-fast);
  cursor: pointer;
}

.drop-zone:hover {
  border-color: var(--color-interactive-primary);
  background: rgba(37, 99, 235, 0.05);
}

.drop-zone.drag-over {
  border-color: var(--color-interactive-primary);
  background: rgba(37, 99, 235, 0.1);
  transform: scale(1.02);
}

.drop-zone.error {
  border-color: var(--color-status-error);
  background: rgba(239, 68, 68, 0.05);
}

/* Upload Icon */
.upload-icon {
  width: 48px;
  height: 48px;
  color: var(--color-text-muted);
  margin-bottom: var(--spacing-md);
}

.drop-zone:hover .upload-icon {
  color: var(--color-interactive-primary);
}

/* Instructions */
.upload-text {
  color: var(--color-text-default);
  font-weight: var(--font-weight-medium);
  margin-bottom: var(--spacing-xs);
}

.upload-hint {
  color: var(--color-text-muted);
  font-size: var(--font-size-sm);
}

/* File Type Badges */
.file-types {
  display: flex;
  gap: var(--spacing-xs);
  margin-top: var(--spacing-md);
}

.file-type-badge {
  display: flex;
  align-items: center;
  gap: var(--spacing-2xs);
  padding: var(--spacing-2xs) var(--spacing-xs);
  background: var(--color-surface-sunken);
  border-radius: var(--radius-sm);
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
}

/* File Chip */
.file-chip {
  display: flex;
  align-items: center;
  gap: var(--spacing-sm);
  padding: var(--spacing-sm);
  background: var(--color-surface-raised);
  border: 1px solid var(--color-border-default);
  border-radius: var(--radius-lg);
  max-width: 100%;
}

.file-thumbnail {
  width: 40px;
  height: 40px;
  border-radius: var(--radius-md);
  background: var(--color-surface-sunken);
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
}

.file-thumbnail img {
  width: 100%;
  height: 100%;
  object-fit: cover;
  border-radius: var(--radius-md);
}

.file-thumbnail-icon {
  width: 20px;
  height: 20px;
  color: var(--color-interactive-primary);
}

.file-info {
  flex: 1;
  min-width: 0;
}

.file-name {
  font-weight: var(--font-weight-medium);
  color: var(--color-text-default);
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.file-meta {
  font-size: var(--font-size-xs);
  color: var(--color-text-muted);
}

.file-remove {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 28px;
  height: 28px;
  border: none;
  background: transparent;
  border-radius: var(--radius-md);
  color: var(--color-text-muted);
  cursor: pointer;
  transition: all var(--duration-fast);
  flex-shrink: 0;
}

.file-remove:hover {
  background: rgba(239, 68, 68, 0.1);
  color: var(--color-status-error);
}

/* Progress Bar */
.file-progress {
  margin-top: var(--spacing-xs);
}

.progress-bar {
  height: 4px;
  background: var(--color-surface-sunken);
  border-radius: var(--radius-full);
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: var(--color-interactive-primary);
  border-radius: var(--radius-full);
  transition: width var(--duration-fast);
}

/* Upload Actions */
.upload-actions {
  display: flex;
  justify-content: flex-end;
  gap: var(--spacing-sm);
  margin-top: var(--spacing-md);
  padding-top: var(--spacing-md);
  border-top: 1px solid var(--color-border-default);
}

/* Context Preview (AI Feature) */
.context-preview {
  margin-top: var(--spacing-md);
  padding: var(--spacing-md);
  background: var(--color-surface-sunken);
  border-radius: var(--radius-lg);
  border-left: 3px solid var(--color-interactive-primary);
}

.context-preview h4 {
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-muted);
  text-transform: uppercase;
  letter-spacing: 0.05em;
  margin-bottom: var(--spacing-xs);
}

.context-text {
  font-size: var(--font-size-sm);
  color: var(--color-text-default);
  line-height: var(--line-height-relaxed);
  max-height: 100px;
  overflow-y: auto;
}
```

## State Matrix

| Element | Default | Hover | Drag Over | Error | Uploading |
|---------|---------|-------|-----------|-------|-----------|
| Drop Zone | border-default | border-primary + tint | border-primary + scale | border-error | - |
| Upload Icon | muted | primary | primary | error | - |
| File Chip | raised bg | border-strong | - | - | - |
| Remove Button | ghost | error tint | - | - | - |
| Progress Bar | - | - | - | - | fill animates |

## Accessibility

```html
<div 
  class="drop-zone" 
  role="button"
  tabindex="0"
  aria-label="Drop files here or click to upload"
  onDragOver={handleDragOver}
  onDrop={handleDrop}
  onKeyDown={handleKeyDown}
>
  <UploadIcon aria-hidden="true" />
  <p class="upload-text">Drop files here or click to upload</p>
  <p class="upload-hint">Supports PDF, images, text files up to 10MB</p>
</div>

<!-- File list -->
<ul class="file-list" role="list" aria-label="Uploaded files">
  <li class="file-chip" role="listitem">
    <div class="file-thumbnail">
      <img src="preview.jpg" alt="Preview of document.pdf" />
    </div>
    <div class="file-info">
      <p class="file-name">document.pdf</p>
      <p class="file-meta">2.4 MB • Ready to analyze</p>
    </div>
    <button 
      class="file-remove" 
      aria-label="Remove document.pdf"
      onClick={handleRemove}
    >
      <CloseIcon aria-hidden="true" />
    </button>
  </li>
</ul>

<!-- Screen reader announcements -->
<div aria-live="polite" aria-atomic="true" class="sr-only">
  File uploaded: document.pdf
</div>
```

## Example: AI File Upload

```tsx
function AIFileUpload({ onUpload, acceptedTypes = ['pdf', 'jpg', 'png', 'txt'] }) {
  const [files, setFiles] = useState([]);
  const [isDragging, setIsDragging] = useState(false);
  
  const handleDrop = (e) => {
    e.preventDefault();
    setIsDragging(false);
    const droppedFiles = Array.from(e.dataTransfer.files);
    processFiles(droppedFiles);
  };
  
  const processFiles = async (newFiles) => {
    for (const file of newFiles) {
      const fileWithPreview = {
        id: Math.random().toString(36),
        file,
        preview: file.type.startsWith('image/') ? URL.createObjectURL(file) : null,
        progress: 0,
        status: 'uploading'
      };
      
      setFiles(prev => [...prev, fileWithPreview]);
      
      // Simulate upload progress
      await uploadFile(fileWithPreview);
    }
  };
  
  const uploadFile = async (fileItem) => {
    // Upload logic here
    for (let progress = 0; progress <= 100; progress += 10) {
      await new Promise(r => setTimeout(r, 200));
      setFiles(prev => prev.map(f => 
        f.id === fileItem.id ? { ...f, progress } : f
      ));
    }
    
    setFiles(prev => prev.map(f => 
      f.id === fileItem.id ? { ...f, status: 'ready', progress: 100 } : f
    ));
    
    onUpload?.(fileItem.file);
  };
  
  const removeFile = (id) => {
    setFiles(prev => {
      const file = prev.find(f => f.id === id);
      if (file?.preview) URL.revokeObjectURL(file.preview);
      return prev.filter(f => f.id !== id);
    });
  };
  
  return (
    <div className="file-upload">
      <div 
        className={`drop-zone ${isDragging ? 'drag-over' : ''}`}
        onDragOver={(e) => { e.preventDefault(); setIsDragging(true); }}
        onDragLeave={() => setIsDragging(false)}
        onDrop={handleDrop}
        onClick={() => inputRef.current?.click()}
      >
        <UploadIcon className="upload-icon" />
        <p className="upload-text">Drop files here or click to upload</p>
        <p className="upload-hint">
          Supports {acceptedTypes.join(', ')} up to 10MB
        </p>
        
        <div className="file-types">
          {acceptedTypes.map(type => (
            <span key={type} className="file-type-badge">
              <FileIcon /> {type.toUpperCase()}
            </span>
          ))}
        </div>
      </div>
      
      <input 
        ref={inputRef}
        type="file" 
        multiple 
        accept={acceptedTypes.map(t => `.${t}`).join(',')}
        onChange={(e) => processFiles(Array.from(e.target.files))}
        hidden
      />
      
      {files.length > 0 && (
        <ul className="file-list">
          {files.map(file => (
            <li key={file.id} className="file-chip">
              <div className="file-thumbnail">
                {file.preview ? (
                  <img src={file.preview} alt="" />
                ) : (
                  <FileIcon className="file-thumbnail-icon" />
                )}
              </div>
              
              <div className="file-info">
                <p className="file-name">{file.file.name}</p>
                <p className="file-meta">
                  {formatSize(file.file.size)} • 
                  {file.status === 'uploading' ? ` ${file.progress}%` : ' Ready'}
                </p>
                {file.status === 'uploading' && (
                  <div className="file-progress">
                    <div className="progress-bar">
                      <div 
                        className="progress-fill" 
                        style={{ width: `${file.progress}%` }}
                      />
                    </div>
                  </div>
                )}
              </div>
              
              <button 
                className="file-remove"
                onClick={() => removeFile(file.id)}
                aria-label={`Remove ${file.file.name}`}
              >
                <CloseIcon />
              </button>
            </li>
          ))}
        </ul>
      )}
      
      {files.length > 0 && (
        <div className="upload-actions">
          <button onClick={() => setFiles([])}>Clear all</button>
          <button className="primary">Analyze files</button>
        </div>
      )}
    </div>
  );
}
```

## Example: Inline File Attachments (Chat)

```tsx
function FileAttachments({ files, onRemove }) {
  if (files.length === 0) return null;
  
  return (
    <div className="attachment-list">
      {files.map(file => (
        <div key={file.id} className="attachment-chip">
          {file.preview ? (
            <img src={file.preview} alt="" className="attachment-thumb" />
          ) : (
            <FileIcon />
          )}
          <span className="attachment-name">{file.name}</span>
          <button 
            className="attachment-remove"
            onClick={() => onRemove(file.id)}
          >
            <CloseIcon />
          </button>
        </div>
      ))}
    </div>
  );
}

// Usage in chat input
function ChatInputWithFiles() {
  const [attachments, setAttachments] = useState([]);
  
  return (
    <div className="chat-input-container">
      <FileAttachments 
        files={attachments} 
        onRemove={(id) => setAttachments(prev => prev.filter(f => f.id !== id))}
      />
      
      <div className="input-row">
        <FileUploadButton 
          onFiles={(files) => setAttachments(prev => [...prev, ...files])}
        />
        <textarea placeholder="Ask about these files..." />
        <SendButton />
      </div>
    </div>
  );
}
```

## Tokens Used

- **color**: surface-raised, surface-sunken, interactive-primary, text-default, text-muted, border-default, border-strong, status-error
- **spacing**: 2xs, xs, sm, md, xl
- **radii**: sm, md, lg, xl, full
- **typography**: size-xs, size-sm, weight-medium, weight-semibold
- **motion**: duration-fast
