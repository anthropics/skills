// ===== PRACTICE MODE =====
// Modo de prática guiada com feedback em tempo real, gamificação e métricas

const PracticeMode = {
    isActive: false,
    startTime: null,
    currentNoteIndex: 0,
    expectedNotes: [],
    playedNotes: [],
    animationFrame: null,

    // Estatísticas
    stats: {
        correct: 0,
        wrong: 0,
        streak: 0,
        maxStreak: 0,
        totalNotes: 0,
        accuracy: 100,
        timingErrors: [],
        pitchErrors: []
    },

    // Configurações
    config: {
        timingTolerance: 500, // ms
        enableVisualFeedback: true
    },

    // Canvas
    canvas: null,
    ctx: null,

    // Inicializar
    init() {
        this.canvas = document.getElementById('noteVisualization');
        if (this.canvas) {
            this.ctx = this.canvas.getContext('2d');
        }

        // Registrar callback MIDI
        if (typeof MIDIHandler !== 'undefined') {
            MIDIHandler.onNote((type, noteData) => {
                if (this.isActive && type === 'noteon') {
                    this.handleNotePlayed(noteData);
                }
            });
        }
    },

    // Iniciar prática
    start() {
        if (typeof appState === 'undefined' || appState.notes.length === 0) {
            alert('❌ Adicione algumas notas primeiro!\n\nDica: Use a transcrição automática ou adicione manualmente.');
            return;
        }

        // Verificar MIDI
        if (typeof MIDIHandler === 'undefined' || !MIDIHandler.enabled || !MIDIHandler.currentInput) {
            const tryConnect = confirm('❌ Nenhum teclado MIDI conectado!\n\nDeseja conectar agora?');
            if (tryConnect && typeof MIDIHandler !== 'undefined') {
                MIDIHandler.connect();
            }
            return;
        }

        this.isActive = true;
        this.startTime = Date.now();
        this.currentNoteIndex = 0;

        // Preparar notas
        this.expectedNotes = [...appState.notes].sort((a, b) => a.startTime - b.startTime);
        this.playedNotes = [];

        // Reset stats
        this.resetStats();
        this.updateUI();
        this.updateButtons(true);

        // Iniciar vídeo
        if (appState.player && typeof appState.player.seekTo === 'function') {
            appState.player.seekTo(0, true);
            appState.player.playVideo();
        }

        // Iniciar visualização
        this.startVisualization();

        this.showFeedback('🎵 Prática iniciada! Toque as notas no momento certo!', 'info');
    },

    // Parar prática
    stop() {
        this.isActive = false;

        if (appState && appState.player && typeof appState.player.pauseVideo === 'function') {
            appState.player.pauseVideo();
        }

        this.updateButtons(false);
        this.stopVisualization();

        if (this.stats.totalNotes > 0) {
            this.showFinalReport();
        }
    },

    // Reset
    reset() {
        this.stop();
        this.resetStats();
        this.updateUI();
        this.showFeedback('🔄 Prática resetada. Clique em "Iniciar" quando estiver pronto!', 'info');
    },

    // Reset stats
    resetStats() {
        this.stats = {
            correct: 0,
            wrong: 0,
            streak: 0,
            maxStreak: 0,
            totalNotes: 0,
            accuracy: 100,
            timingErrors: [],
            pitchErrors: []
        };
    },

    // Handle nota tocada
    handleNotePlayed(noteData) {
        if (!this.isActive || this.currentNoteIndex >= this.expectedNotes.length) {
            return;
        }

        const expected = this.expectedNotes[this.currentNoteIndex];
        const currentTime = appState.currentTime;

        this.playedNotes.push({ ...noteData, timestamp: currentTime });

        const isCorrectPitch = this.checkPitch(noteData, expected);
        const isCorrectTiming = this.checkTiming(currentTime, expected);

        if (isCorrectPitch && isCorrectTiming) {
            this.handleCorrectNote(noteData, expected);
        } else {
            this.handleWrongNote(noteData, expected, isCorrectPitch, isCorrectTiming);
        }

        this.updateUI();
    },

    // Verificar pitch
    checkPitch(played, expected) {
        const playedNote = played.note.replace(/[♯♭#b]/g, match => match === '♯' || match === '#' ? '#' : 'b');
        return playedNote === expected.note && played.octave === expected.octave;
    },

    // Verificar timing
    checkTiming(playedTime, expectedNote) {
        const timeDiff = Math.abs(playedTime - expectedNote.startTime);
        return timeDiff <= (this.config.timingTolerance / 1000);
    },

    // Nota correta
    handleCorrectNote(played, expected) {
        this.stats.correct++;
        this.stats.streak++;
        this.stats.totalNotes++;

        if (this.stats.streak > this.stats.maxStreak) {
            this.stats.maxStreak = this.stats.streak;
        }

        this.calculateAccuracy();

        this.showFeedback(`✅ Correto! ${expected.note}${expected.octave}`, 'success');
        this.flashNote(expected, 'green');

        if (this.stats.streak > 0 && this.stats.streak % 5 === 0) {
            this.showFeedback(`🔥 INCRÍVEL! Streak de ${this.stats.streak}!`, 'success');
        }

        this.currentNoteIndex++;

        if (this.currentNoteIndex >= this.expectedNotes.length) {
            setTimeout(() => this.stop(), 1000);
        }
    },

    // Nota errada
    handleWrongNote(played, expected, correctPitch, correctTiming) {
        this.stats.wrong++;
        this.stats.streak = 0;
        this.stats.totalNotes++;

        this.calculateAccuracy();

        let errorMsg = '❌ ';
        if (!correctPitch && !correctTiming) {
            errorMsg += `Nota e timing errados! Esperava: ${expected.note}${expected.octave}`;
            this.stats.pitchErrors.push(expected);
            this.stats.timingErrors.push(expected);
        } else if (!correctPitch) {
            errorMsg += `Nota errada! Esperava: ${expected.note}${expected.octave}`;
            this.stats.pitchErrors.push(expected);
        } else {
            errorMsg += `Timing errado! Toque no momento certo.`;
            this.stats.timingErrors.push(expected);
        }

        this.showFeedback(errorMsg, 'error');
        this.flashNote(expected, 'red');

        this.currentNoteIndex++;
    },

    // Calcular precisão
    calculateAccuracy() {
        if (this.stats.totalNotes > 0) {
            this.stats.accuracy = Math.round((this.stats.correct / this.stats.totalNotes) * 100);
        }
    },

    // Visualização
    startVisualization() {
        if (!this.canvas || !this.ctx) return;

        const draw = () => {
            if (!this.isActive) return;

            try {
                this.clearCanvas();
                this.drawUpcomingNotes();
                this.drawCurrentNote();
                this.drawProgress();

                this.animationFrame = requestAnimationFrame(draw);
            } catch (error) {
                console.error('Erro na visualização:', error);
            }
        };

        draw();
    },

    stopVisualization() {
        if (this.animationFrame) {
            cancelAnimationFrame(this.animationFrame);
            this.animationFrame = null;
        }
        if (this.canvas && this.ctx) {
            this.clearCanvas();
        }
    },

    clearCanvas() {
        this.ctx.fillStyle = '#f8f9fa';
        this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    },

    drawUpcomingNotes() {
        if (!appState) return;

        const currentTime = appState.currentTime;
        const lookAhead = 5;

        const upcomingNotes = this.expectedNotes.filter(note =>
            note.startTime >= currentTime && note.startTime <= currentTime + lookAhead
        );

        upcomingNotes.forEach(note => {
            const x = ((note.startTime - currentTime) / lookAhead) * this.canvas.width;
            const y = this.canvas.height / 2;

            this.ctx.fillStyle = note.color || '#667eea';
            this.ctx.fillRect(x - 5, y - 20, 10, 40);

            this.ctx.fillStyle = '#000';
            this.ctx.font = '12px Arial';
            this.ctx.textAlign = 'center';
            this.ctx.fillText(`${note.note}${note.octave}`, x, y + 55);
        });
    },

    drawCurrentNote() {
        if (this.currentNoteIndex >= this.expectedNotes.length) return;

        const note = this.expectedNotes[this.currentNoteIndex];

        this.ctx.strokeStyle = '#ff0000';
        this.ctx.lineWidth = 3;
        this.ctx.strokeRect(50, this.canvas.height / 2 - 25, 20, 50);

        this.ctx.fillStyle = '#000';
        this.ctx.font = 'bold 16px Arial';
        this.ctx.textAlign = 'center';
        this.ctx.fillText(`AGORA: ${note.note}${note.octave}`, 60, this.canvas.height / 2 - 35);
    },

    drawProgress() {
        const progress = (this.currentNoteIndex / this.expectedNotes.length) * 100;

        this.ctx.fillStyle = '#e0e0e0';
        this.ctx.fillRect(0, this.canvas.height - 20, this.canvas.width, 20);

        this.ctx.fillStyle = '#4caf50';
        this.ctx.fillRect(0, this.canvas.height - 20, (progress / 100) * this.canvas.width, 20);

        this.ctx.fillStyle = '#000';
        this.ctx.font = '12px Arial';
        this.ctx.textAlign = 'center';
        this.ctx.fillText(`${Math.round(progress)}%`, this.canvas.width / 2, this.canvas.height - 6);
    },

    flashNote(note, color) {
        const noteBlocks = document.querySelectorAll('.note-block');
        noteBlocks.forEach(block => {
            if (parseInt(block.dataset.id) === note.id) {
                block.style.boxShadow = `0 0 20px ${color}`;
                setTimeout(() => { block.style.boxShadow = ''; }, 500);
            }
        });
    },

    showFeedback(message, type = 'info') {
        const feedbackEl = document.getElementById('feedbackMessage');
        if (feedbackEl) {
            feedbackEl.textContent = message;
            feedbackEl.className = 'feedback-message ' + type;

            setTimeout(() => {
                if (feedbackEl.textContent === message) {
                    feedbackEl.textContent = '';
                }
            }, 3000);
        }
    },

    updateUI() {
        const elements = {
            correctNotes: document.getElementById('correctNotes'),
            wrongNotes: document.getElementById('wrongNotes'),
            accuracy: document.getElementById('accuracy'),
            streak: document.getElementById('streak')
        };

        if (elements.correctNotes) elements.correctNotes.textContent = this.stats.correct;
        if (elements.wrongNotes) elements.wrongNotes.textContent = this.stats.wrong;
        if (elements.accuracy) elements.accuracy.textContent = this.stats.accuracy + '%';
        if (elements.streak) elements.streak.textContent = this.stats.streak + ' 🔥';
    },

    updateButtons(practicing) {
        const startBtn = document.getElementById('startPractice');
        const stopBtn = document.getElementById('stopPractice');

        if (startBtn) startBtn.disabled = practicing;
        if (stopBtn) stopBtn.disabled = !practicing;
    },

    showFinalReport() {
        const report = `
🎉 PRÁTICA CONCLUÍDA!

📊 Estatísticas:
• Acertos: ${this.stats.correct}
• Erros: ${this.stats.wrong}
• Precisão: ${this.stats.accuracy}%
• Melhor streak: ${this.stats.maxStreak}

${this.getPerformanceAnalysis()}

${this.getImprovementTips()}
        `.trim();

        this.showFeedback(report, 'success');
        console.log(report);
        alert(report);
    },

    getPerformanceAnalysis() {
        let analysis = '🎯 ANÁLISE:\n';

        if (this.stats.accuracy >= 90) {
            analysis += '• Excelente! Você está dominando esta música! 🌟';
        } else if (this.stats.accuracy >= 70) {
            analysis += '• Bom trabalho! Continue praticando para melhorar.';
        } else {
            analysis += '• Continue praticando! A repetição é a chave.';
        }

        if (this.stats.pitchErrors.length > this.stats.timingErrors.length) {
            analysis += '\n• Foco nas notas corretas (pitch).';
        } else if (this.stats.timingErrors.length > this.stats.pitchErrors.length) {
            analysis += '\n• Foco no timing (momento certo).';
        }

        return analysis;
    },

    getImprovementTips() {
        let tips = '\n💡 DICAS:\n';

        if (this.stats.timingErrors.length > 3) {
            tips += '• Use metrônomo\n• Pratique mais devagar\n';
        }

        if (this.stats.pitchErrors.length > 3) {
            tips += '• Revise as notas\n• Pratique seções isoladamente\n';
        }

        if (this.stats.accuracy < 80) {
            tips += '• Divida em seções menores\n• Pratique 15-20 min/dia\n';
        }

        return tips;
    }
};

// Exportar
if (typeof window !== 'undefined') {
    window.PracticeMode = PracticeMode;
}
