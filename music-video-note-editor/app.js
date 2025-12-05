// Estado global da aplicação
const appState = {
    player: null,
    videoId: null,
    notes: [],
    selectedNote: null,
    currentTime: 0,
    videoDuration: 0,
    isPlaying: false
};

// Cores das notas (mesmas do CSS)
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

// Inicialização quando a página carregar
document.addEventListener('DOMContentLoaded', () => {
    setupEventListeners();
    initializeModules();
});

// YouTube API Ready
let playerReady = false;
function onYouTubeIframeAPIReady() {
    console.log('YouTube API carregada');
    playerReady = true;
}

// Configurar event listeners
function setupEventListeners() {
    // Video loading
    document.getElementById('loadVideo').addEventListener('click', loadVideo);
    document.getElementById('videoUrl').addEventListener('keypress', (e) => {
        if (e.key === 'Enter') loadVideo();
    });

    // Video controls
    document.getElementById('playPause').addEventListener('click', togglePlayPause);
    document.getElementById('rewind').addEventListener('click', () => seekVideo(-5));
    document.getElementById('forward').addEventListener('click', () => seekVideo(5));

    // Note selection
    document.querySelectorAll('.note-btn').forEach(btn => {
        btn.addEventListener('click', () => selectNote(btn));
    });

    // Add note
    document.getElementById('addNoteAtCurrentTime').addEventListener('click', addNoteAtCurrentTime);

    // Prompts
    document.getElementById('generatePrompt').addEventListener('click', generatePrompts);
    document.querySelectorAll('.prompt-btn').forEach(btn => {
        btn.addEventListener('click', () => addCategoryPrompt(btn.dataset.category));
    });

    // Export/Import
    document.getElementById('saveProject').addEventListener('click', saveProject);
    document.getElementById('loadProject').addEventListener('click', () => {
        document.getElementById('projectFileInput').click();
    });
    document.getElementById('projectFileInput').addEventListener('change', loadProjectFile);
    document.getElementById('exportNotes').addEventListener('click', exportNotesCSV);

    // Transcription
    const transcribeBtn = document.getElementById('transcribeAudio');
    if (transcribeBtn) {
        transcribeBtn.addEventListener('click', () => TranscriptionHandler.transcribeVideo());
    }

    // MIDI
    const connectMIDIBtn = document.getElementById('connectMIDI');
    if (connectMIDIBtn) {
        connectMIDIBtn.addEventListener('click', () => MIDIHandler.connect());
    }

    // Practice Mode
    const startPracticeBtn = document.getElementById('startPractice');
    const stopPracticeBtn = document.getElementById('stopPractice');
    const resetPracticeBtn = document.getElementById('resetPractice');

    if (startPracticeBtn) startPracticeBtn.addEventListener('click', () => PracticeMode.start());
    if (stopPracticeBtn) stopPracticeBtn.addEventListener('click', () => PracticeMode.stop());
    if (resetPracticeBtn) resetPracticeBtn.addEventListener('click', () => PracticeMode.reset());

    // Score Generation
    const generateScoreBtn = document.getElementById('generateScore');
    if (generateScoreBtn) {
        generateScoreBtn.addEventListener('click', () => ScoreRenderer.generateScore());
    }

    // Update timeline periodically
    setInterval(updateTimeline, 100);
}

// Inicializar módulos
function initializeModules() {
    // Inicializar modo prática
    if (typeof PracticeMode !== 'undefined') {
        PracticeMode.init();
    }

    // Tentar inicializar MIDI automaticamente (não bloqueia se falhar)
    if (typeof MIDIHandler !== 'undefined') {
        MIDIHandler.init().catch(err => {
            console.log('MIDI não disponível:', err.message);
        });
    }

    console.log('Módulos inicializados!');
}

// Extrair ID do vídeo do YouTube
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

// Carregar vídeo
function loadVideo() {
    const url = document.getElementById('videoUrl').value.trim();
    const videoId = extractVideoId(url);

    if (!videoId) {
        alert('URL inválida! Por favor, insira um link válido do YouTube.');
        return;
    }

    appState.videoId = videoId;

    // Destruir player anterior se existir
    if (appState.player) {
        appState.player.destroy();
    }

    // Criar novo player
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
}

function onPlayerReady(event) {
    console.log('Player pronto!');
    appState.videoDuration = appState.player.getDuration();
    updateDurationDisplay();
    createTimelineRuler();
}

function onPlayerStateChange(event) {
    appState.isPlaying = (event.data === YT.PlayerState.PLAYING);
}

// Controles de vídeo
function togglePlayPause() {
    if (!appState.player) return;

    if (appState.isPlaying) {
        appState.player.pauseVideo();
    } else {
        appState.player.playVideo();
    }
}

function seekVideo(seconds) {
    if (!appState.player) return;
    const currentTime = appState.player.getCurrentTime();
    appState.player.seekTo(currentTime + seconds, true);
}

// Atualizar timeline
function updateTimeline() {
    if (!appState.player || !appState.player.getCurrentTime) return;

    appState.currentTime = appState.player.getCurrentTime();
    document.getElementById('currentTime').textContent = formatTime(appState.currentTime);

    // Atualizar marcador de tempo
    const timeline = document.getElementById('timeline');
    let marker = timeline.querySelector('.time-marker');

    if (!marker) {
        marker = document.createElement('div');
        marker.className = 'time-marker';
        timeline.appendChild(marker);
    }

    const percent = (appState.currentTime / appState.videoDuration) * 100;
    marker.style.left = percent + '%';
}

function updateDurationDisplay() {
    document.getElementById('duration').textContent = formatTime(appState.videoDuration);
}

function formatTime(seconds) {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${secs.toString().padStart(2, '0')}`;
}

// Criar régua da timeline
function createTimelineRuler() {
    const ruler = document.getElementById('timelineRuler');
    ruler.innerHTML = '';

    const duration = appState.videoDuration;
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

// Seleção de nota
function selectNote(button) {
    // Remover seleção anterior
    document.querySelectorAll('.note-btn').forEach(btn => {
        btn.classList.remove('selected');
    });

    // Adicionar nova seleção
    button.classList.add('selected');
    appState.selectedNote = button.dataset.note;
}

// Adicionar nota no tempo atual
function addNoteAtCurrentTime() {
    if (!appState.selectedNote) {
        alert('Selecione uma nota primeiro!');
        return;
    }

    if (!appState.player) {
        alert('Carregue um vídeo primeiro!');
        return;
    }

    const octave = parseInt(document.getElementById('octave').value);
    const duration = parseFloat(document.getElementById('noteDuration').value);
    const startTime = appState.currentTime;

    const note = {
        id: Date.now(),
        note: appState.selectedNote,
        octave: octave,
        startTime: startTime,
        duration: duration,
        color: NOTE_COLORS[appState.selectedNote]
    };

    appState.notes.push(note);
    renderNotes();
    updateNotesList();
}

// Renderizar notas na timeline
function renderNotes() {
    const timeline = document.getElementById('timeline');

    // Remover blocos de notas existentes
    timeline.querySelectorAll('.note-block').forEach(block => block.remove());

    // Adicionar novos blocos
    appState.notes.forEach(note => {
        const block = createNoteBlock(note);
        timeline.appendChild(block);
    });
}

function createNoteBlock(note) {
    const block = document.createElement('div');
    block.className = 'note-block';
    block.dataset.id = note.id;

    const startPercent = (note.startTime / appState.videoDuration) * 100;
    const widthPercent = (note.duration / appState.videoDuration) * 100;

    block.style.left = startPercent + '%';
    block.style.width = widthPercent + '%';
    block.style.backgroundColor = note.color;
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
        if (appState.player) {
            appState.player.seekTo(note.startTime, true);
        }
    };

    return block;
}

// Atualizar lista de notas
function updateNotesList() {
    const list = document.getElementById('notesList');
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
        colorDiv.style.backgroundColor = note.color;

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
            if (appState.player) {
                appState.player.seekTo(note.startTime, true);
            }
        };

        const delBtn = document.createElement('button');
        delBtn.textContent = '🗑️ Deletar';
        delBtn.style.background = '#dc3545';
        delBtn.onclick = () => deleteNote(note.id);

        item.appendChild(colorDiv);
        item.appendChild(info);
        item.appendChild(goBtn);
        item.appendChild(delBtn);

        list.appendChild(item);
    });
}

// Deletar nota
function deleteNote(id) {
    appState.notes = appState.notes.filter(note => note.id !== id);
    renderNotes();
    updateNotesList();
}

// Gerador de prompts educacionais
function generatePrompts() {
    const prompts = [];

    // Análise das notas
    const noteCount = appState.notes.length;
    const uniqueNotes = new Set(appState.notes.map(n => n.note));
    const hasBlackKeys = appState.notes.some(n => n.note.includes('#'));

    prompts.push('=== DICAS PERSONALIZADAS PARA ESTE VÍDEO ===\n');

    // Dicas gerais
    prompts.push('📚 VISÃO GERAL:');
    prompts.push(`- Total de notas: ${noteCount}`);
    prompts.push(`- Notas únicas: ${uniqueNotes.size}`);
    prompts.push(`- Usa teclas pretas: ${hasBlackKeys ? 'Sim' : 'Não'}\n`);

    // Posição das mãos
    prompts.push('✋ POSIÇÃO DAS MÃOS:');
    prompts.push('- Mantenha os dedos curvados, como se segurasse uma bola');
    prompts.push('- Pulsos alinhados com os antebraços, sem dobrar para cima ou para baixo');
    prompts.push('- Polegares relaxados, não esticados');
    prompts.push('- Use o peso natural do braço, evite força excessiva\n');

    // Intensidade
    prompts.push('💪 INTENSIDADE E DINÂMICA:');
    prompts.push('- Comece praticando em mezzoforte (volume médio)');
    prompts.push('- Pressione as teclas com firmeza, mas sem bater');
    prompts.push('- Escute cada nota até o final antes de tocar a próxima');
    prompts.push('- Varie a intensidade para expressão musical\n');

    // Pedal
    prompts.push('🎵 USO DO PEDAL:');
    if (noteCount > 10) {
        prompts.push('- Use o pedal sustain para conectar as notas suavemente');
        prompts.push('- Pressione o pedal DEPOIS de tocar a nota, não antes');
        prompts.push('- Solte e pressione novamente ao mudar de harmonia');
    } else {
        prompts.push('- Para iniciantes: primeiro pratique sem pedal');
        prompts.push('- Adicione pedal somente após dominar as notas');
    }
    prompts.push('- Mantenha o calcanhar no chão, use apenas a parte da frente do pé\n');

    // Ritmo e timing
    prompts.push('⏱️ RITMO E TIMING:');
    prompts.push('- Use metrônomo para manter tempo constante');
    prompts.push('- Comece devagar e aumente gradualmente a velocidade');
    prompts.push('- Conte em voz alta: 1-2-3-4 para manter o ritmo');
    prompts.push('- Pratique seções difíceis em loop lento\n');

    // Técnica específica
    prompts.push('🎹 TÉCNICA ESPECÍFICA:');
    if (hasBlackKeys) {
        prompts.push('- Para teclas pretas: mova a mão ligeiramente para frente');
        prompts.push('- Use a ponta dos dedos nas teclas pretas');
        prompts.push('- Mantenha os dedos curvados mesmo nas teclas pretas');
    }
    prompts.push('- Pratique cada mão separadamente antes de juntar');
    prompts.push('- Memorize pequenas seções de cada vez');
    prompts.push('- Relaxe os ombros, evite tensão\n');

    // Dicas de aprendizado
    prompts.push('🎓 DICAS DE APRENDIZADO:');
    prompts.push('- Pratique 15-30 minutos por dia (melhor que 2h uma vez por semana)');
    prompts.push('- Grave-se tocando para identificar áreas de melhoria');
    prompts.push('- Divida a música em seções pequenas (4-8 compassos)');
    prompts.push('- Seja paciente: progresso vem com repetição consistente');
    prompts.push('- Divirta-se! A música é para ser apreciada 🎶');

    document.getElementById('promptsText').value = prompts.join('\n');
}

// Adicionar prompts por categoria
function addCategoryPrompt(category) {
    const textarea = document.getElementById('promptsText');
    const prompts = {
        posicao: '\n\n✋ POSIÇÃO DAS MÃOS:\n' +
            '- Dedos curvados naturalmente\n' +
            '- Pulsos nivelados com os antebraços\n' +
            '- Polegares relaxados\n' +
            '- Cotovelos ligeiramente afastados do corpo',

        intensidade: '\n\n💪 INTENSIDADE:\n' +
            '- Toque firme mas controlado\n' +
            '- Varie entre piano (suave) e forte (intenso)\n' +
            '- Use o peso do braço, não só os dedos\n' +
            '- Escute cada nota completamente',

        pedal: '\n\n🎵 PEDAL:\n' +
            '- Pressione após tocar a nota\n' +
            '- Solte ao mudar de harmonia\n' +
            '- Calcanhar no chão sempre\n' +
            '- Use com moderação no início',

        ritmo: '\n\n⏱️ RITMO:\n' +
            '- Use metrônomo\n' +
            '- Comece lento (60-80 BPM)\n' +
            '- Aumente 5 BPM quando dominar\n' +
            '- Conte em voz alta: 1-2-3-4',

        tecnica: '\n\n🎹 TÉCNICA GERAL:\n' +
            '- Pratique mãos separadas primeiro\n' +
            '- Relaxe ombros e pescoço\n' +
            '- Respire naturalmente\n' +
            '- Faça pausas a cada 20-30 minutos'
    };

    textarea.value += prompts[category] || '';
}

// Salvar projeto
function saveProject() {
    const project = {
        version: '1.0',
        videoId: appState.videoId,
        videoUrl: document.getElementById('videoUrl').value,
        notes: appState.notes,
        prompts: document.getElementById('promptsText').value,
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

// Carregar projeto
function loadProjectFile(event) {
    const file = event.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (e) => {
        try {
            const project = JSON.parse(e.target.result);

            // Restaurar dados
            document.getElementById('videoUrl').value = project.videoUrl || '';
            appState.notes = project.notes || [];
            document.getElementById('promptsText').value = project.prompts || '';

            // Carregar vídeo se tiver
            if (project.videoUrl) {
                loadVideo();
            }

            renderNotes();
            updateNotesList();

            alert('Projeto carregado com sucesso!');
        } catch (error) {
            alert('Erro ao carregar projeto: ' + error.message);
        }
    };
    reader.readAsText(file);
}

// Exportar notas para CSV
function exportNotesCSV() {
    if (appState.notes.length === 0) {
        alert('Adicione algumas notas primeiro!');
        return;
    }

    let csv = 'Nota,Oitava,Tempo Início (s),Duração (s),Cor\n';

    appState.notes
        .sort((a, b) => a.startTime - b.startTime)
        .forEach(note => {
            csv += `${note.note},${note.octave},${note.startTime.toFixed(2)},${note.duration},${note.color}\n`;
        });

    const blob = new Blob([csv], { type: 'text/csv' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `music-notes-${appState.videoId || 'export'}-${Date.now()}.csv`;
    a.click();
    URL.revokeObjectURL(url);
}
