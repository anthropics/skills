// Practice Mode - Modo de prática guiada com feedback em tempo real
// Gamificação, métricas e análise de performance

const PracticeMode = {
    isActive: false,
    isPaused: false,
    startTime: null,
    currentNoteIndex: 0,
    expectedNotes: [],
    playedNotes: [],

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
        timingTolerance: 500, // ms de tolerância para timing
        enableVisualFeedback: true,
        enableSoundFeedback: true,
        loopOnError: false
    },

    // Canvas para visualização
    canvas: null,
    ctx: null,

    // Inicializar
    init() {
        this.canvas = document.getElementById('noteVisualization');
        if (this.canvas) {
            this.ctx = this.canvas.getContext('2d');
        }

        // Registrar callback MIDI
        if (MIDIHandler.enabled || MIDIHandler.init) {
            MIDIHandler.onNote((type, noteData) => {
                if (this.isActive && type === 'noteon') {
                    this.handleNotePlayed(noteData);
                }
            });
        }
    },

    // Iniciar prática
    start() {
        if (appState.notes.length === 0) {
            alert('Adicione algumas notas primeiro! Use a transcrição automática ou adicione manualmente.');
            return;
        }

        // Verificar se MIDI está conectado
        if (!MIDIHandler.enabled || !MIDIHandler.currentInput) {
            const tryConnect = confirm('Nenhum teclado MIDI conectado. Deseja conectar agora?');
            if (tryConnect) {
                MIDIHandler.connect();
            }
            return;
        }

        this.isActive = true;
        this.isPaused = false;
        this.startTime = Date.now();
        this.currentNoteIndex = 0;

        // Preparar notas esperadas (ordenadas por tempo)
        this.expectedNotes = [...appState.notes].sort((a, b) => a.startTime - b.startTime);
        this.playedNotes = [];

        // Reset stats
        this.resetStats();

        // UI
        this.updateUI();
        this.updateButtons(true);

        // Iniciar vídeo
        if (appState.player) {
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
        this.isPaused = false;

        if (appState.player) {
            appState.player.pauseVideo();
        }

        this.updateButtons(false);
        this.stopVisualization();

        // Mostrar relatório final
        this.showFinalReport();
    },

    // Reset
    reset() {
        this.stop();
        this.resetStats();
        this.updateUI();
        this.showFeedback('Prática resetada. Clique em "Iniciar" quando estiver pronto!', 'info');
    },

    // Resetar estatísticas
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

    // Handle nota tocada pelo usuário
    handleNotePlayed(noteData) {
        if (!this.isActive || this.currentNoteIndex >= this.expectedNotes.length) {
            return;
        }

        const expectedNote = this.expectedNotes[this.currentNoteIndex];
        const currentTime = appState.currentTime;

        // Registrar nota tocada
        this.playedNotes.push({
            ...noteData,
            timestamp: currentTime
        });

        // Verificar se a nota está correta
        const isCorrectPitch = this.checkPitch(noteData, expectedNote);
        const isCorrectTiming = this.checkTiming(currentTime, expectedNote);

        if (isCorrectPitch && isCorrectTiming) {
            this.handleCorrectNote(noteData, expectedNote);
        } else {
            this.handleWrongNote(noteData, expectedNote, isCorrectPitch, isCorrectTiming);
        }

        this.updateUI();
    },

    // Verificar pitch (altura da nota)
    checkPitch(played, expected) {
        const playedNote = played.note.replace(/[♯♭#b]/g, match => {
            return match === '♯' || match === '#' ? '#' : 'b';
        });
        const expectedNote = expected.note;

        return playedNote === expectedNote && played.octave === expected.octave;
    },

    // Verificar timing
    checkTiming(playedTime, expectedNote) {
        const timeDiff = Math.abs(playedTime - expectedNote.startTime);
        return timeDiff <= (this.config.timingTolerance / 1000);
    },

    // Handle nota correta
    handleCorrectNote(played, expected) {
        this.stats.correct++;
        this.stats.streak++;
        this.stats.totalNotes++;

        if (this.stats.streak > this.stats.maxStreak) {
            this.stats.maxStreak = this.stats.streak;
        }

        this.calculateAccuracy();

        // Feedback visual
        this.showFeedback(`✅ Correto! ${expected.note}${expected.octave}`, 'success');
        this.flashNote(expected, 'green');

        // Streak especial
        if (this.stats.streak > 0 && this.stats.streak % 5 === 0) {
            this.showFeedback(`🔥 INCRÍVEL! Streak de ${this.stats.streak}!`, 'success');
        }

        // Avançar para próxima nota
        this.currentNoteIndex++;

        // Verificar se terminou
        if (this.currentNoteIndex >= this.expectedNotes.length) {
            setTimeout(() => this.stop(), 1000);
        }
    },

    // Handle nota errada
    handleWrongNote(played, expected, correctPitch, correctTiming) {
        this.stats.wrong++;
        this.stats.streak = 0;
        this.stats.totalNotes++;

        this.calculateAccuracy();

        // Identificar tipo de erro
        let errorMsg = '❌ ';
        if (!correctPitch && !correctTiming) {
            errorMsg += `Nota e timing errados! Esperava: ${expected.note}${expected.octave}`;
            this.stats.pitchErrors.push(expected);
            this.stats.timingErrors.push(expected);
        } else if (!correctPitch) {
            errorMsg += `Nota errada! Esperava: ${expected.note}${expected.octave}, Tocou: ${played.note}${played.octave}`;
            this.stats.pitchErrors.push(expected);
        } else if (!correctTiming) {
            errorMsg += `Timing errado! Toque no momento certo.`;
            this.stats.timingErrors.push(expected);
        }

        this.showFeedback(errorMsg, 'error');
        this.flashNote(expected, 'red');

        // Loop no erro (opcional)
        if (this.config.loopOnError && appState.player) {
            const loopStart = Math.max(0, expected.startTime - 2);
            appState.player.seekTo(loopStart, true);
        } else {
            this.currentNoteIndex++;
        }
    },

    // Calcular precisão
    calculateAccuracy() {
        if (this.stats.totalNotes > 0) {
            this.stats.accuracy = Math.round((this.stats.correct / this.stats.totalNotes) * 100);
        }
    },

    // Visualização em tempo real
    startVisualization() {
        if (!this.canvas || !this.ctx) return;

        const draw = () => {
            if (!this.isActive) return;

            this.clearCanvas();
            this.drawUpcomingNotes();
            this.drawCurrentNote();
            this.drawProgress();

            requestAnimationFrame(draw);
        };

        draw();
    },

    stopVisualization() {
        if (this.canvas && this.ctx) {
            this.clearCanvas();
        }
    },

    clearCanvas() {
        this.ctx.fillStyle = '#f8f9fa';
        this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    },

    // Desenhar notas futuras
    drawUpcomingNotes() {
        const currentTime = appState.currentTime;
        const lookAhead = 5; // segundos

        const upcomingNotes = this.expectedNotes.filter(note =>
            note.startTime >= currentTime &&
            note.startTime <= currentTime + lookAhead
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

    // Desenhar nota atual
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

    // Desenhar progresso
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

    // Flash visual em nota
    flashNote(note, color) {
        // Implementar flash visual na timeline
        const noteBlocks = document.querySelectorAll('.note-block');
        noteBlocks.forEach(block => {
            if (parseInt(block.dataset.id) === note.id) {
                block.style.boxShadow = `0 0 20px ${color}`;
                setTimeout(() => {
                    block.style.boxShadow = '';
                }, 500);
            }
        });
    },

    // Mostrar feedback
    showFeedback(message, type = 'info') {
        const feedbackEl = document.getElementById('feedbackMessage');
        if (feedbackEl) {
            feedbackEl.textContent = message;
            feedbackEl.className = 'feedback-message ' + type;

            // Auto-hide após 3 segundos
            setTimeout(() => {
                if (feedbackEl.textContent === message) {
                    feedbackEl.textContent = '';
                }
            }, 3000);
        }
    },

    // Atualizar UI
    updateUI() {
        document.getElementById('correctNotes').textContent = this.stats.correct;
        document.getElementById('wrongNotes').textContent = this.stats.wrong;
        document.getElementById('accuracy').textContent = this.stats.accuracy + '%';
        document.getElementById('streak').textContent = this.stats.streak + ' 🔥';
    },

    // Atualizar botões
    updateButtons(practicing) {
        document.getElementById('startPractice').disabled = practicing;
        document.getElementById('stopPractice').disabled = !practicing;
    },

    // Relatório final
    showFinalReport() {
        const report = `
🎉 PRÁTICA CONCLUÍDA!

📊 Estatísticas:
• Notas corretas: ${this.stats.correct}
• Notas erradas: ${this.stats.wrong}
• Precisão: ${this.stats.accuracy}%
• Melhor streak: ${this.stats.maxStreak}

${this.getPerformanceAnalysis()}

${this.getImprovementTips()}
        `.trim();

        this.showFeedback(report, 'success');
        console.log(report);
        alert(report);
    },

    // Análise de performance
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
            analysis += '\n• Foco nas notas corretas (altura/pitch).';
        } else if (this.stats.timingErrors.length > this.stats.pitchErrors.length) {
            analysis += '\n• Foco no timing (momento certo).';
        }

        return analysis;
    },

    // Dicas de melhoria
    getImprovementTips() {
        let tips = '\n💡 DICAS:\n';

        if (this.stats.timingErrors.length > 3) {
            tips += '• Use metrônomo para melhorar o timing\n';
            tips += '• Pratique em velocidade mais lenta\n';
        }

        if (this.stats.pitchErrors.length > 3) {
            tips += '• Revise as notas na partitura\n';
            tips += '• Pratique seções difíceis isoladamente\n';
        }

        if (this.stats.accuracy < 80) {
            tips += '• Divida a música em seções menores\n';
            tips += '• Pratique 15-20 minutos por dia\n';
        }

        return tips;
    }
};
