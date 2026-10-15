// ===== TRANSCRIPTION HANDLER =====
// Framework de integração para transcrição de áudio para MIDI
// Spotify Basic Pitch / Magenta Onsets & Frames

const TranscriptionHandler = {
    isProcessing: false,

    // Transcrever áudio do vídeo atual
    async transcribeVideo() {
        if (this.isProcessing) {
            alert('Já existe uma transcrição em andamento...');
            return;
        }

        if (typeof appState === 'undefined' || !appState.player) {
            alert('Carregue um vídeo primeiro!');
            return;
        }

        this.updateStatus('⚠️ MODO DEMONSTRAÇÃO: Transcrição simulada', 'warning');
        this.isProcessing = true;

        try {
            await this.simulateTranscription();
        } catch (error) {
            console.error('Erro na transcrição:', error);
            this.updateStatus('❌ Erro: ' + error.message, 'error');
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

        // Gerar notas de exemplo
        const duration = appState.videoDuration || 60;
        const sampleNotes = this.generateSampleNotes(duration);

        this.updateStatus(`✅ Transcrição concluída! ${sampleNotes.length} notas detectadas.`, 'success');

        // Adicionar notas se opção estiver marcada
        const autoAdd = document.getElementById('autoAddTranscribedNotes');
        if (autoAdd && autoAdd.checked) {
            this.addTranscribedNotes(sampleNotes);
        }

        // Mostrar instruções
        this.showRealIntegrationInfo();
    },

    // Gerar notas de exemplo (demonstração)
    generateSampleNotes(duration) {
        const notes = [];
        const noteNames = ['C', 'D', 'E', 'F', 'G', 'A', 'B'];
        const octaves = [3, 4, 5];

        let currentTime = 0;
        while (currentTime < Math.min(duration, 30)) {
            const note = noteNames[Math.floor(Math.random() * noteNames.length)];
            const octave = octaves[Math.floor(Math.random() * octaves.length)];
            const noteDuration = 0.3 + Math.random() * 0.7;

            notes.push({
                note: note,
                octave: octave,
                startTime: currentTime,
                duration: noteDuration,
                confidence: 0.7 + Math.random() * 0.3
            });

            currentTime += 2 + Math.random() * 2;
        }

        return notes;
    },

    // Adicionar notas transcritas
    addTranscribedNotes(transcribedNotes) {
        const thresholdEl = document.getElementById('confidenceThreshold');
        const confidenceThreshold = thresholdEl ? (thresholdEl.value / 100) : 0.7;

        transcribedNotes.forEach(note => {
            if (note.confidence >= confidenceThreshold) {
                const newNote = {
                    id: Date.now() + Math.random(),
                    note: note.note,
                    octave: note.octave,
                    startTime: note.startTime,
                    duration: note.duration,
                    color: (typeof NOTE_COLORS !== 'undefined' && NOTE_COLORS[note.note]) || '#ccc',
                    source: 'transcription',
                    confidence: note.confidence
                };

                if (typeof appState !== 'undefined') {
                    appState.notes.push(newNote);
                }
            }
        });

        // Atualizar visualizações
        if (typeof renderNotes === 'function') renderNotes();
        if (typeof updateNotesList === 'function') updateNotesList();

        const addedCount = transcribedNotes.filter(n => n.confidence >= confidenceThreshold).length;
        this.updateStatus(`✅ ${addedCount} notas adicionadas ao projeto!`, 'success');
    },

    // Informações de integração real
    showRealIntegrationInfo() {
        const info = `
═══════════════════════════════════════════════════
📘 IMPLEMENTAÇÃO REAL - TRANSCRIÇÃO DE ÁUDIO
═══════════════════════════════════════════════════

Esta é uma DEMONSTRAÇÃO. Para implementação real:

🎵 OPÇÃO 1: Spotify Basic Pitch (Recomendado)
   npm install @spotify/basic-pitch
   GitHub: spotify/basic-pitch

   import * as basicPitch from '@spotify/basic-pitch';
   const model = await basicPitch.loadModel();
   const frames = await basicPitch.detectNotes(audioData);

🎹 OPÇÃO 2: Magenta Onsets & Frames
   CDN: https://cdn.jsdelivr.net/npm/@magenta/music
   Exemplo: Piano Scribe demo

🔧 OPÇÃO 3: Backend ByteDance Piano Transcription
   pip install piano-transcription-inference
   Melhor qualidade (detecta até pedal!)

═══════════════════════════════════════════════════
        `.trim();

        console.log(info);
    },

    // Atualizar status
    updateStatus(message, type = 'info') {
        const statusEl = document.getElementById('transcriptionStatus');
        if (statusEl) {
            statusEl.textContent = message;
            statusEl.className = 'status-message ' + type;
        }
    },

    // Sleep helper
    sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
};

// Event listener para slider de confiança
if (typeof document !== 'undefined') {
    document.addEventListener('DOMContentLoaded', () => {
        const slider = document.getElementById('confidenceThreshold');
        const valueDisplay = document.getElementById('confidenceValue');

        if (slider && valueDisplay) {
            slider.addEventListener('input', (e) => {
                valueDisplay.textContent = e.target.value + '%';
            });
        }
    });
}

// Exportar para uso global
if (typeof window !== 'undefined') {
    window.TranscriptionHandler = TranscriptionHandler;
}
