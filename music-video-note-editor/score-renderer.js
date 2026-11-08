// ===== SCORE RENDERER =====
// Renderização de partituras musicais usando VexFlow

const ScoreRenderer = {
    vf: null,
    renderer: null,
    context: null,

    // Inicializar VexFlow
    init() {
        if (typeof Vex === 'undefined') {
            console.error('❌ VexFlow não está carregado!');
            return false;
        }

        this.vf = Vex.Flow;
        return true;
    },

    // Gerar partitura
    generateScore() {
        if (!this.init()) {
            alert('❌ Erro ao carregar VexFlow.\n\nVerifique sua conexão com a internet e recarregue a página.');
            return;
        }

        if (typeof appState === 'undefined' || appState.notes.length === 0) {
            alert('❌ Adicione algumas notas primeiro!');
            return;
        }

        const outputDiv = document.getElementById('scoreOutput');
        if (!outputDiv) return;

        outputDiv.innerHTML = ''; // Limpar

        try {
            const width = Math.min(800, outputDiv.clientWidth || 800);
            const height = 300;

            this.renderer = new this.vf.Renderer(outputDiv, this.vf.Renderer.Backends.SVG);
            this.renderer.resize(width, height);
            this.context = this.renderer.getContext();

            const clefType = document.getElementById('clefType')?.value || 'treble';
            const timeSignature = document.getElementById('timeSignature')?.value || '4/4';

            // Criar pauta
            const stave = new this.vf.Stave(10, 40, width - 20);
            stave.addClef(clefType);
            stave.addTimeSignature(timeSignature);
            stave.setContext(this.context).draw();

            // Converter notas
            const vexNotes = this.convertNotesToVexFlow(appState.notes, clefType);

            if (vexNotes.length > 0) {
                const voice = new this.vf.Voice({
                    num_beats: 4,
                    beat_value: 4
                });
                voice.addTickables(vexNotes);

                const formatter = new this.vf.Formatter();
                formatter.joinVoices([voice]).format([voice], width - 50);
                voice.draw(this.context, stave);

                this.colorizeNotes(vexNotes, appState.notes);
            }

            console.log('✅ Partitura gerada com sucesso!');

        } catch (error) {
            console.error('Erro ao gerar partitura:', error);
            alert('❌ Erro ao gerar partitura:\n' + error.message);
        }
    },

    // Converter notas para VexFlow
    convertNotesToVexFlow(notes, clef) {
        const sortedNotes = [...notes].sort((a, b) => a.startTime - b.startTime);
        const vexNotes = [];

        sortedNotes.slice(0, 16).forEach(note => {
            try {
                const vexNote = this.noteToVexFormat(note, clef);
                const staveNote = new this.vf.StaveNote({
                    clef: clef,
                    keys: [vexNote],
                    duration: this.durationToVexFormat(note.duration)
                });

                if (note.note.includes('#')) {
                    staveNote.addModifier(new this.vf.Accidental('#'), 0);
                } else if (note.note.includes('b')) {
                    staveNote.addModifier(new this.vf.Accidental('b'), 0);
                }

                vexNotes.push(staveNote);

            } catch (error) {
                console.warn('⚠️ Erro ao converter nota:', note, error);
            }
        });

        if (vexNotes.length === 0) {
            vexNotes.push(new this.vf.StaveNote({
                clef: clef,
                keys: ['b/4'],
                duration: 'qr'
            }));
        }

        return vexNotes;
    },

    // Converter nota para formato VexFlow
    noteToVexFormat(note, clef) {
        let noteName = note.note.toLowerCase().replace('#', '');
        let octave = note.octave;

        if (clef === 'bass') {
            octave = Math.max(2, octave - 1);
        }

        return `${noteName}/${octave}`;
    },

    // Converter duração para formato VexFlow
    durationToVexFormat(durationSeconds) {
        if (durationSeconds < 0.3) return '16';
        if (durationSeconds < 0.6) return '8';
        if (durationSeconds < 1.2) return 'q';
        if (durationSeconds < 2.4) return 'h';
        return 'w';
    },

    // Colorir notas
    colorizeNotes(vexNotes, originalNotes) {
        vexNotes.forEach((vexNote, index) => {
            if (originalNotes[index] && originalNotes[index].color) {
                try {
                    vexNote.setStyle({
                        fillStyle: originalNotes[index].color,
                        strokeStyle: originalNotes[index].color
                    });
                } catch (error) {
                    console.warn('⚠️ Erro ao colorir nota:', error);
                }
            }
        });
    },

    // Exportar como imagem
    exportAsImage() {
        const outputDiv = document.getElementById('scoreOutput');
        const svg = outputDiv?.querySelector('svg');

        if (!svg) {
            alert('❌ Gere a partitura primeiro!');
            return;
        }

        const svgData = new XMLSerializer().serializeToString(svg);
        const canvas = document.createElement('canvas');
        const ctx = canvas.getContext('2d');
        const img = new Image();

        img.onload = () => {
            canvas.width = img.width;
            canvas.height = img.height;
            ctx.drawImage(img, 0, 0);

            canvas.toBlob((blob) => {
                const url = URL.createObjectURL(blob);
                const a = document.createElement('a');
                a.href = url;
                a.download = `partitura-${Date.now()}.png`;
                a.click();
                URL.revokeObjectURL(url);
            });
        };

        img.src = 'data:image/svg+xml;base64,' + btoa(unescape(encodeURIComponent(svgData)));
    },

    // Gerar MIDI (stub)
    generateMIDI() {
        console.log('📝 Exportação MIDI:');
        console.log('Para implementação completa, use @tonejs/midi ou midi-writer-js');

        if (typeof appState === 'undefined' || !appState.notes) return;

        const midiData = {
            header: {
                format: 0,
                numTracks: 1,
                ticksPerBeat: 480
            },
            tracks: [{
                name: 'Piano',
                notes: appState.notes.map(note => ({
                    midi: this.noteToMIDINumber(note),
                    time: note.startTime,
                    duration: note.duration,
                    velocity: 0.8
                }))
            }]
        };

        console.log('MIDI Data:', JSON.stringify(midiData, null, 2));
        alert('✅ Dados MIDI gerados!\n\nVeja o console do navegador para detalhes.\n\nPara exportação real de MIDI, integre @tonejs/midi.');
    },

    // Converter nota para número MIDI
    noteToMIDINumber(note) {
        const noteMap = {
            'C': 0, 'C#': 1, 'D': 2, 'D#': 3,
            'E': 4, 'F': 5, 'F#': 6, 'G': 7,
            'G#': 8, 'A': 9, 'A#': 10, 'B': 11
        };

        const noteValue = noteMap[note.note];
        if (noteValue === undefined) return 60;

        return (note.octave + 1) * 12 + noteValue;
    }
};

// Exportar
if (typeof window !== 'undefined') {
    window.ScoreRenderer = ScoreRenderer;
}
