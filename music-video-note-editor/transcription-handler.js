// Transcription Handler - Transcrição de áudio para MIDI
// Integração com Spotify Basic Pitch / Magenta Onsets & Frames
// Para produção: use @spotify/basic-pitch ou Magenta.js

const TranscriptionHandler = {
    isProcessing: false,
    audioContext: null,
    analyser: null,

    // Inicializar Web Audio API
    initAudio() {
        if (!this.audioContext) {
            this.audioContext = new (window.AudioContext || window.webkitAudioContext)();
        }
    },

    // Transcrever áudio do vídeo atual
    async transcribeVideo() {
        if (this.isProcessing) {
            alert('Já existe uma transcrição em andamento...');
            return;
        }

        if (!appState.player) {
            alert('Carregue um vídeo primeiro!');
            return;
        }

        this.updateStatus('Preparando transcrição...', 'info');
        this.isProcessing = true;

        try {
            // NOTA: Esta é uma implementação simulada para demonstração
            // Para produção real, você precisaria:
            // 1. Extrair o áudio do vídeo
            // 2. Processar com Basic Pitch ou Magenta Onsets & Frames
            // 3. Converter o resultado para notas

            this.updateStatus('⚠️ MODO DEMONSTRAÇÃO: Transcrição simulada', 'warning');

            await this.simulateTranscription();

        } catch (error) {
            console.error('Erro na transcrição:', error);
            this.updateStatus('Erro: ' + error.message, 'error');
        } finally {
            this.isProcessing = false;
        }
    },

    // Simulação de transcrição para demonstração
    async simulateTranscription() {
        this.updateStatus('Analisando áudio... (0%)', 'info');

        // Simular progresso
        for (let i = 0; i <= 100; i += 10) {
            await this.sleep(200);
            this.updateStatus(`Analisando áudio... (${i}%)`, 'info');
        }

        // Gerar algumas notas de exemplo baseadas na duração do vídeo
        const duration = appState.videoDuration || 60;
        const sampleNotes = this.generateSampleNotes(duration);

        this.updateStatus(`Transcrição concluída! ${sampleNotes.length} notas detectadas.`, 'success');

        // Adicionar notas se opção estiver marcada
        if (document.getElementById('autoAddTranscribedNotes').checked) {
            this.addTranscribedNotes(sampleNotes);
        }

        // Mostrar instruções para integração real
        this.showRealIntegrationInfo();
    },

    // Gerar notas de exemplo (para demonstração)
    generateSampleNotes(duration) {
        const notes = [];
        const noteNames = ['C', 'D', 'E', 'F', 'G', 'A', 'B'];
        const octaves = [3, 4, 5];

        // Gerar notas a cada 2-4 segundos
        let currentTime = 0;
        while (currentTime < Math.min(duration, 30)) {
            const note = noteNames[Math.floor(Math.random() * noteNames.length)];
            const octave = octaves[Math.floor(Math.random() * octaves.length)];
            const noteDuration = 0.3 + Math.random() * 0.7; // 0.3-1.0s

            notes.push({
                note: note,
                octave: octave,
                startTime: currentTime,
                duration: noteDuration,
                confidence: 0.7 + Math.random() * 0.3 // 70-100%
            });

            currentTime += 2 + Math.random() * 2; // 2-4s
        }

        return notes;
    },

    // Adicionar notas transcritas ao projeto
    addTranscribedNotes(transcribedNotes) {
        const confidenceThreshold = document.getElementById('confidenceThreshold').value / 100;

        transcribedNotes.forEach(note => {
            if (note.confidence >= confidenceThreshold) {
                const newNote = {
                    id: Date.now() + Math.random(),
                    note: note.note,
                    octave: note.octave,
                    startTime: note.startTime,
                    duration: note.duration,
                    color: NOTE_COLORS[note.note],
                    source: 'transcription',
                    confidence: note.confidence
                };

                appState.notes.push(newNote);
            }
        });

        renderNotes();
        updateNotesList();

        const addedCount = transcribedNotes.filter(n => n.confidence >= confidenceThreshold).length;
        this.updateStatus(`${addedCount} notas adicionadas ao projeto!`, 'success');
    },

    // Mostrar informações sobre integração real
    showRealIntegrationInfo() {
        const info = `
═══════════════════════════════════════════════════════════════
📘 IMPLEMENTAÇÃO REAL - TRANSCRIÇÃO DE ÁUDIO
═══════════════════════════════════════════════════════════════

Esta é uma DEMONSTRAÇÃO. Para implementação real, use:

🎵 OPÇÃO 1: Spotify Basic Pitch (Recomendado para MVP)
   - NPM: @spotify/basic-pitch
   - Leve, roda no browser com TensorFlow.js
   - GitHub: spotify/basic-pitch
   - Exemplo:
     import * as basicPitch from '@spotify/basic-pitch';
     const model = await basicPitch.loadModel();
     const frames = await basicPitch.detectNotes(audioData);

🎹 OPÇÃO 2: Magenta Onsets & Frames
   - Parte do projeto Magenta (Google)
   - Ótimo para piano
   - Exemplo demo: Piano Scribe
   - CDN: https://cdn.jsdelivr.net/npm/@magenta/music

🔧 OPÇÃO 3: Backend com ByteDance Piano Transcription
   - Melhor qualidade (deteta pedal também!)
   - Requer Python + PyTorch + GPU
   - GitHub: bytedance/piano_transcription
   - Use FastAPI + Celery para processamento assíncrono

📦 INTEGRAÇÃO SUGERIDA:
   1. Frontend: Captura áudio do vídeo (Web Audio API)
   2. Processa com Basic Pitch no browser OU
   3. Envia para backend (FastAPI) com modelo ByteDance
   4. Retorna MIDI/notas para visualização

═══════════════════════════════════════════════════════════════
        `.trim();

        console.log(info);
    },

    // Integração real com Basic Pitch (exemplo comentado)
    /*
    async transcribeWithBasicPitch(audioBuffer) {
        // Carregar modelo
        const model = await basicPitch.loadModel();

        // Processar áudio
        const frames = await basicPitch.detectNotes(audioBuffer, {
            // Parâmetros
            onsetThreshold: 0.5,
            frameThreshold: 0.3,
            minNoteLength: 0.1
        });

        // Converter para formato de notas
        const notes = frames.map(frame => ({
            note: this.midiToNoteName(frame.pitch),
            octave: Math.floor(frame.pitch / 12) - 1,
            startTime: frame.startTime,
            duration: frame.endTime - frame.startTime,
            confidence: frame.confidence
        }));

        return notes;
    },
    */

    // Converter número MIDI para nome de nota
    midiToNoteName(midiNumber) {
        const noteNames = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
        return noteNames[midiNumber % 12];
    },

    // Atualizar status
    updateStatus(message, type = 'info') {
        const statusEl = document.getElementById('transcriptionStatus');
        if (statusEl) {
            statusEl.textContent = message;
            statusEl.className = 'status-message ' + type;
        }
    },

    // Utilitário: sleep
    sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
};

// Event listener para o slider de confiança
if (document.getElementById('confidenceThreshold')) {
    document.getElementById('confidenceThreshold').addEventListener('input', (e) => {
        document.getElementById('confidenceValue').textContent = e.target.value + '%';
    });
}
