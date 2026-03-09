// ===== ESTADO GLOBAL DA APLICAÇÃO =====
const appState = {
    player: null,
    videoId: null,
    notes: [],
    selectedNote: null,
    currentTime: 0,
    videoDuration: 0,
    isPlaying: false
};

// ===== CORES DAS NOTAS =====
const NOTE_COLORS = {
    'C': '#90EE90',    // Verde claro
    'C#': '#2d5016',   // Verde escuro
    'D': '#87CEEB',    // Azul claro
    'D#': '#1e3a5f',   // Azul escuro
    'E': '#FFD700',    // Amarelo claro
    'F': '#FF6B6B',    // Vermelho claro
    'F#': '#8B0000',   // Vermelho escuro
    'G': '#DDA0DD',    // Roxo claro
    'G#': '#4B0082',   // Roxo escuro
    'A': '#FFA500',    // Laranja claro
    'A#': '#cc5200',   // Laranja escuro
    'B': '#FFB6C1'     // Rosa claro
};

// ===== INICIALIZAÇÃO =====
document.addEventListener('DOMContentLoaded', () => {
    console.log('🎹 Aplicativo iniciado!');
    setupEventListeners();
    initializeModules();
});

// ===== YOUTUBE API =====
let playerReady = false;
function onYouTubeIframeAPIReady() {
    console.log('✅ YouTube API carregada');
    playerReady = true;
}

// ===== EVENT LISTENERS =====
function setupEventListeners() {
    // Video loading
    const loadVideoBtn = document.getElementById('loadVideo');
    const videoUrlInput = document.getElementById('videoUrl');

    if (loadVideoBtn) loadVideoBtn.addEventListener('click', loadVideo);
    if (videoUrlInput) {
        videoUrlInput.addEventListener('keypress', (e) => {
            if (e.key === 'Enter') loadVideo();
        });
    }

    // Video controls
    const playPauseBtn = document.getElementById('playPause');
    const rewindBtn = document.getElementById('rewind');
    const forwardBtn = document.getElementById('forward');

    if (playPauseBtn) playPauseBtn.addEventListener('click', togglePlayPause);
    if (rewindBtn) rewindBtn.addEventListener('click', () => seekVideo(-5));
    if (forwardBtn) forwardBtn.addEventListener('click', () => seekVideo(5));

    // Note selection
    document.querySelectorAll('.note-btn').forEach(btn => {
        btn.addEventListener('click', () => selectNote(btn));
    });

    // Add note
    const addNoteBtn = document.getElementById('addNoteAtCurrentTime');
    if (addNoteBtn) addNoteBtn.addEventListener('click', addNoteAtCurrentTime);

    // Prompts
    const generatePromptBtn = document.getElementById('generatePrompt');
    if (generatePromptBtn) generatePromptBtn.addEventListener('click', generatePrompts);

    document.querySelectorAll('.prompt-btn').forEach(btn => {
        btn.addEventListener('click', () => addCategoryPrompt(btn.dataset.category));
    });

    // Export/Import
    const saveProjectBtn = document.getElementById('saveProject');
    const loadProjectBtn = document.getElementById('loadProject');
    const projectFileInput = document.getElementById('projectFileInput');
    const exportNotesBtn = document.getElementById('exportNotes');

    if (saveProjectBtn) saveProjectBtn.addEventListener('click', saveProject);
    if (loadProjectBtn) {
        loadProjectBtn.addEventListener('click', () => {
            if (projectFileInput) projectFileInput.click();
        });
    }
    if (projectFileInput) projectFileInput.addEventListener('change', loadProjectFile);
    if (exportNotesBtn) exportNotesBtn.addEventListener('click', exportNotesCSV);

    // Transcription
    const transcribeBtn = document.getElementById('transcribeAudio');
    if (transcribeBtn && typeof TranscriptionHandler !== 'undefined') {
        transcribeBtn.addEventListener('click', () => TranscriptionHandler.transcribeVideo());
    }

    // MIDI
    const connectMIDIBtn = document.getElementById('connectMIDI');
    if (connectMIDIBtn && typeof MIDIHandler !== 'undefined') {
        connectMIDIBtn.addEventListener('click', () => MIDIHandler.connect());
    }

    // Practice Mode
    const startPracticeBtn = document.getElementById('startPractice');
    const stopPracticeBtn = document.getElementById('stopPractice');
    const resetPracticeBtn = document.getElementById('resetPractice');

    if (startPracticeBtn && typeof PracticeMode !== 'undefined') {
        startPracticeBtn.addEventListener('click', () => PracticeMode.start());
    }
    if (stopPracticeBtn && typeof PracticeMode !== 'undefined') {
        stopPracticeBtn.addEventListener('click', () => PracticeMode.stop());
    }
    if (resetPracticeBtn && typeof PracticeMode !== 'undefined') {
        resetPracticeBtn.addEventListener('click', () => PracticeMode.reset());
    }

    // Score Generation
    const generateScoreBtn = document.getElementById('generateScore');
    if (generateScoreBtn && typeof ScoreRenderer !== 'undefined') {
        generateScoreBtn.addEventListener('click', () => ScoreRenderer.generateScore());
    }

    // Update timeline periodically
    setInterval(updateTimeline, 100);
}

// ===== INICIALIZAR MÓDULOS =====
function initializeModules() {
    // Inicializar modo prática
    if (typeof PracticeMode !== 'undefined') {
        PracticeMode.init();
        console.log('✅ Practice Mode inicializado');
    }

    // Tentar inicializar MIDI automaticamente (não bloqueia se falhar)
    if (typeof MIDIHandler !== 'undefined') {
        MIDIHandler.init().catch(err => {
            console.log('⚠️ MIDI não disponível:', err.message);
        });
    }

    console.log('✅ Módulos inicializados!');
}

// ===== FUNÇÕES DE VÍDEO =====
function extractVideoId(url) {
    const patterns = [
        /(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([^&\n?#]+)/,
        /^([a-zA-Z0-9_-]{11})$/
    ];

    for (const pattern of patterns) {
        const match = url.match(pattern);
        if (match) return match[1];
    }
    return null;
}

function loadVideo() {
    const url = document.getElementById('videoUrl').value.trim();

    if (!url) {
        alert('Por favor, insira um link do YouTube!');
        return;
    }

    const videoId = extractVideoId(url);

    if (!videoId) {
        alert('URL inválida! Por favor, insira um link válido do YouTube.');
        return;
    }

    appState.videoId = videoId;

    // Destruir player anterior se existir
    if (appState.player && typeof appState.player.destroy === 'function') {
        appState.player.destroy();
    }

    // Criar novo player
    try {
        appState.player = new YT.Player('player', {
            videoId: videoId,
            playerVars: {
                'playsinline': 1,
                'controls': 1
            },
            events: {
                'onReady': onPlayerReady,
                'onStateChange': onPlayerStateChange
            }
        });
    } catch (error) {
        console.error('Erro ao criar player:', error);
        alert('Erro ao carregar vídeo. Verifique se o YouTube API está carregado.');
    }
}

function onPlayerReady(event) {
    console.log('✅ Player pronto!');
    try {
        appState.videoDuration = appState.player.getDuration();
        updateDurationDisplay();
        createTimelineRuler();
    } catch (error) {
        console.error('Erro ao configurar player:', error);
    }
}

function onPlayerStateChange(event) {
    appState.isPlaying = (event.data === YT.PlayerState.PLAYING);
}

function togglePlayPause() {
    if (!appState.player) {
        alert('Carregue um vídeo primeiro!');
        return;
    }

    try {
        if (appState.isPlaying) {
            appState.player.pauseVideo();
        } else {
            appState.player.playVideo();
        }
    } catch (error) {
        console.error('Erro ao controlar reprodução:', error);
    }
}

function seekVideo(seconds) {
    if (!appState.player) return;

    try {
        const currentTime = appState.player.getCurrentTime();
        const newTime = Math.max(0, Math.min(appState.videoDuration, currentTime + seconds));
        appState.player.seekTo(newTime, true);
    } catch (error) {
        console.error('Erro ao buscar tempo:', error);
    }
}

// ===== TIMELINE =====
function updateTimeline() {
    if (!appState.player || typeof appState.player.getCurrentTime !== 'function') return;

    try {
        appState.currentTime = appState.player.getCurrentTime();
        const currentTimeEl = document.getElementById('currentTime');
        if (currentTimeEl) {
            currentTimeEl.textContent = formatTime(appState.currentTime);
        }

        // Atualizar marcador de tempo
        const timeline = document.getElementById('timeline');
        if (!timeline) return;

        let marker = timeline.querySelector('.time-marker');

        if (!marker) {
            marker = document.createElement('div');
            marker.className = 'time-marker';
            timeline.appendChild(marker);
        }

        if (appState.videoDuration > 0) {
            const percent = (appState.currentTime / appState.videoDuration) * 100;
            marker.style.left = percent + '%';
        }
    } catch (error) {
        // Silencioso - erro esperado antes do vídeo carregar
    }
}

function updateDurationDisplay() {
    const durationEl = document.getElementById('duration');
    if (durationEl) {
        durationEl.textContent = formatTime(appState.videoDuration);
    }
}

function formatTime(seconds) {
    if (isNaN(seconds) || seconds < 0) return '0:00';
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${secs.toString().padStart(2, '0')}`;
}

function createTimelineRuler() {
    const ruler = document.getElementById('timelineRuler');
    if (!ruler) return;

    ruler.innerHTML = '';

    const duration = appState.videoDuration;
    if (!duration || duration <= 0) return;

    const interval = duration > 120 ? 10 : 5; // Intervalos de 10s ou 5s

    for (let i = 0; i <= duration; i += interval) {
        const marker = document.createElement('div');
        marker.style.position = 'absolute';
        marker.style.left = ((i / duration) * 100) + '%';
        marker.style.height = '100%';
        marker.style.borderLeft = '1px solid #999';
        marker.style.fontSize = '0.8em';
        marker.style.paddingLeft = '3px';
        marker.textContent = formatTime(i);
        ruler.appendChild(marker);
    }
}

// ===== NOTAS =====
function selectNote(button) {
    // Remover seleção anterior
    document.querySelectorAll('.note-btn').forEach(btn => {
        btn.classList.remove('selected');
    });

    // Adicionar nova seleção
    button.classList.add('selected');
    appState.selectedNote = button.dataset.note;
}

function addNoteAtCurrentTime() {
    if (!appState.selectedNote) {
        alert('Selecione uma nota primeiro!');
        return;
    }

    if (!appState.player) {
        alert('Carregue um vídeo primeiro!');
        return;
    }

    const octaveInput = document.getElementById('octave');
    const durationInput = document.getElementById('noteDuration');

    const octave = octaveInput ? parseInt(octaveInput.value) : 4;
    const duration = durationInput ? parseFloat(durationInput.value) : 0.5;
    const startTime = appState.currentTime;

    const note = {
        id: Date.now() + Math.random(),
        note: appState.selectedNote,
        octave: octave,
        startTime: startTime,
        duration: duration,
        color: NOTE_COLORS[appState.selectedNote] || '#ccc',
        source: 'manual'
    };

    appState.notes.push(note);
    renderNotes();
    updateNotesList();
}

function renderNotes() {
    const timeline = document.getElementById('timeline');
    if (!timeline) return;

    // Remover blocos de notas existentes
    timeline.querySelectorAll('.note-block').forEach(block => block.remove());

    // Adicionar novos blocos
    appState.notes.forEach(note => {
        const block = createNoteBlock(note);
        if (block) timeline.appendChild(block);
    });
}

function createNoteBlock(note) {
    if (!appState.videoDuration || appState.videoDuration <= 0) return null;

    const block = document.createElement('div');
    block.className = 'note-block';
    block.dataset.id = note.id;

    const startPercent = (note.startTime / appState.videoDuration) * 100;
    const widthPercent = (note.duration / appState.videoDuration) * 100;

    block.style.left = startPercent + '%';
    block.style.width = Math.max(widthPercent, 1) + '%';
    block.style.backgroundColor = note.color || '#ccc';
    block.style.top = '50%';
    block.style.transform = 'translateY(-50%)';

    // Texto da nota
    const label = document.createElement('span');
    label.textContent = `${note.note}${note.octave}`;
    block.appendChild(label);

    // Botão de deletar
    const deleteBtn = document.createElement('button');
    deleteBtn.className = 'delete-btn';
    deleteBtn.textContent = '×';
    deleteBtn.onclick = (e) => {
        e.stopPropagation();
        deleteNote(note.id);
    };
    block.appendChild(deleteBtn);

    // Click para ir ao tempo da nota
    block.onclick = () => {
        if (appState.player && typeof appState.player.seekTo === 'function') {
            appState.player.seekTo(note.startTime, true);
        }
    };

    return block;
}

function updateNotesList() {
    const list = document.getElementById('notesList');
    if (!list) return;

    list.innerHTML = '';

    if (appState.notes.length === 0) {
        list.innerHTML = '<p style="color: #999;">Nenhuma nota adicionada ainda.</p>';
        return;
    }

    // Ordenar notas por tempo
    const sortedNotes = [...appState.notes].sort((a, b) => a.startTime - b.startTime);

    sortedNotes.forEach(note => {
        const item = document.createElement('div');
        item.className = 'note-item';

        const colorDiv = document.createElement('div');
        colorDiv.className = 'note-color';
        colorDiv.style.backgroundColor = note.color || '#ccc';

        const info = document.createElement('div');
        info.className = 'note-info';
        info.innerHTML = `
            <strong>${note.note}${note.octave}</strong> -
            Início: ${formatTime(note.startTime)} -
            Duração: ${note.duration}s
        `;

        const goBtn = document.createElement('button');
        goBtn.textContent = '▶️ Ir';
        goBtn.onclick = () => {
            if (appState.player && typeof appState.player.seekTo === 'function') {
                appState.player.seekTo(note.startTime, true);
            }
        };

        const delBtn = document.createElement('button');
        delBtn.textContent = '🗑️';
        delBtn.style.background = '#dc3545';
        delBtn.onclick = () => deleteNote(note.id);

        item.appendChild(colorDiv);
        item.appendChild(info);
        item.appendChild(goBtn);
        item.appendChild(delBtn);

        list.appendChild(item);
    });
}

function deleteNote(id) {
    appState.notes = appState.notes.filter(note => note.id !== id);
    renderNotes();
    updateNotesList();
}

// ===== PROMPTS =====
function generatePrompts() {
    const prompts = [];
    const noteCount = appState.notes.length;

    if (noteCount === 0) {
        alert('Adicione algumas notas primeiro!');
        return;
    }

    const uniqueNotes = new Set(appState.notes.map(n => n.note));
    const hasBlackKeys = appState.notes.some(n => n.note.includes('#'));

    prompts.push('=== DICAS PERSONALIZADAS PARA ESTE VÍDEO ===\n');
    prompts.push('📚 VISÃO GERAL:');
    prompts.push(`- Total de notas: ${noteCount}`);
    prompts.push(`- Notas únicas: ${uniqueNotes.size}`);
    prompts.push(`- Usa teclas pretas: ${hasBlackKeys ? 'Sim' : 'Não'}\n`);

    prompts.push('✋ POSIÇÃO DAS MÃOS:');
    prompts.push('- Mantenha os dedos curvados, como se segurasse uma bola');
    prompts.push('- Pulsos alinhados com os antebraços');
    prompts.push('- Use o peso natural do braço\n');

    prompts.push('💪 INTENSIDADE:');
    prompts.push('- Comece em mezzoforte (volume médio)');
    prompts.push('- Pressione com firmeza, sem bater');
    prompts.push('- Varie a intensidade para expressão\n');

    prompts.push('🎵 USO DO PEDAL:');
    if (noteCount > 10) {
        prompts.push('- Use o pedal sustain para conectar notas');
        prompts.push('- Pressione DEPOIS de tocar a nota');
    } else {
        prompts.push('- Para iniciantes: pratique sem pedal primeiro');
    }
    prompts.push('- Mantenha o calcanhar no chão\n');

    prompts.push('⏱️ RITMO:');
    prompts.push('- Use metrônomo');
    prompts.push('- Comece devagar e aumente gradualmente');
    prompts.push('- Conte em voz alta: 1-2-3-4\n');

    prompts.push('🎹 TÉCNICA:');
    if (hasBlackKeys) {
        prompts.push('- Para teclas pretas: mova a mão para frente');
    }
    prompts.push('- Pratique cada mão separadamente');
    prompts.push('- Relaxe os ombros\n');

    prompts.push('🎓 DICAS DE APRENDIZADO:');
    prompts.push('- Pratique 15-30 min por dia');
    prompts.push('- Grave-se para identificar melhorias');
    prompts.push('- Seja paciente e consistente');
    prompts.push('- Divirta-se! 🎶');

    const textarea = document.getElementById('promptsText');
    if (textarea) {
        textarea.value = prompts.join('\n');
    }
}

function addCategoryPrompt(category) {
    const textarea = document.getElementById('promptsText');
    if (!textarea) return;

    const prompts = {
        posicao: '\n\n✋ POSIÇÃO DAS MÃOS:\n- Dedos curvados naturalmente\n- Pulsos nivelados\n- Polegares relaxados',
        intensidade: '\n\n💪 INTENSIDADE:\n- Toque firme mas controlado\n- Varie entre piano e forte\n- Use peso do braço',
        pedal: '\n\n🎵 PEDAL:\n- Pressione após tocar\n- Solte ao mudar harmonia\n- Calcanhar no chão',
        ritmo: '\n\n⏱️ RITMO:\n- Use metrônomo\n- Comece lento (60-80 BPM)\n- Conte em voz alta',
        tecnica: '\n\n🎹 TÉCNICA:\n- Pratique mãos separadas\n- Relaxe ombros\n- Respire naturalmente'
    };

    textarea.value += prompts[category] || '';
}

// ===== EXPORTAÇÃO =====
function saveProject() {
    const project = {
        version: '1.0',
        videoId: appState.videoId,
        videoUrl: document.getElementById('videoUrl')?.value || '',
        notes: appState.notes,
        prompts: document.getElementById('promptsText')?.value || '',
        createdAt: new Date().toISOString()
    };

    const blob = new Blob([JSON.stringify(project, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `music-notes-${appState.videoId || 'project'}-${Date.now()}.json`;
    a.click();
    URL.revokeObjectURL(url);
}

function loadProjectFile(event) {
    const file = event.target.files?.[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (e) => {
        try {
            const project = JSON.parse(e.target.result);

            const videoUrlInput = document.getElementById('videoUrl');
            const promptsTextarea = document.getElementById('promptsText');

            if (videoUrlInput && project.videoUrl) {
                videoUrlInput.value = project.videoUrl;
            }

            appState.notes = project.notes || [];

            if (promptsTextarea && project.prompts) {
                promptsTextarea.value = project.prompts;
            }

            if (project.videoUrl) {
                loadVideo();
            }

            renderNotes();
            updateNotesList();

            alert('✅ Projeto carregado com sucesso!');
        } catch (error) {
            console.error('Erro ao carregar projeto:', error);
            alert('❌ Erro ao carregar projeto: ' + error.message);
        }
    };
    reader.readAsText(file);
}

function exportNotesCSV() {
    if (appState.notes.length === 0) {
        alert('Adicione algumas notas primeiro!');
        return;
    }

    let csv = 'Nota,Oitava,Tempo Início (s),Duração (s),Cor,Fonte\n';

    appState.notes
        .sort((a, b) => a.startTime - b.startTime)
        .forEach(note => {
            csv += `${note.note},${note.octave},${note.startTime.toFixed(2)},${note.duration},${note.color},${note.source || 'manual'}\n`;
        });

    const blob = new Blob([csv], { type: 'text/csv;charset=utf-8;' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `music-notes-${appState.videoId || 'export'}-${Date.now()}.csv`;
    a.click();
    URL.revokeObjectURL(url);
}

// Exportar para uso global
if (typeof window !== 'undefined') {
    window.appState = appState;
    window.NOTE_COLORS = NOTE_COLORS;
    window.renderNotes = renderNotes;
    window.updateNotesList = updateNotesList;
}
