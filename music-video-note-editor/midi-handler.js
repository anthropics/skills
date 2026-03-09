// ===== MIDI HANDLER =====
// Gerenciamento de conexão e entrada de teclados MIDI usando WebMIDI.js

const MIDIHandler = {
    enabled: false,
    connectedDevices: [],
    currentInput: null,
    noteCallbacks: [],
    lastNotes: [],

    // Inicializar WebMIDI
    async init() {
        // Verificar se WebMIDI está disponível
        if (typeof WebMidi === 'undefined') {
            console.warn('WebMIDI.js não está carregado');
            return false;
        }

        try {
            await WebMidi.enable();
            this.enabled = true;
            console.log('✅ WebMIDI habilitado!');
            this.updateStatus('WebMIDI pronto para conectar');
            return true;
        } catch (err) {
            console.error('Erro ao habilitar WebMIDI:', err);
            this.updateStatus('Erro: ' + err.message);
            return false;
        }
    },

    // Conectar dispositivo MIDI
    async connect() {
        if (!this.enabled) {
            const initialized = await this.init();
            if (!initialized) return false;
        }

        const inputs = WebMidi.inputs;

        if (inputs.length === 0) {
            this.updateStatus('Nenhum dispositivo MIDI encontrado. Conecte um teclado MIDI e tente novamente.');
            alert('⚠️ Nenhum dispositivo MIDI encontrado!\n\nVerifique se:\n- O teclado está ligado\n- O cabo USB está conectado\n- O dispositivo está reconhecido pelo sistema');
            return false;
        }

        // Mostrar dispositivos disponíveis
        this.displayDevices(inputs);

        // Conectar ao primeiro dispositivo
        this.currentInput = inputs[0];
        this.setupInputListeners(this.currentInput);

        this.updateStatus(`✅ Conectado: ${this.currentInput.name}`);
        console.log(`🎹 MIDI conectado: ${this.currentInput.name}`);
        return true;
    },

    // Configurar listeners de entrada MIDI
    setupInputListeners(input) {
        // Note On
        input.addListener('noteon', e => {
            const noteData = {
                note: e.note.name + (e.note.accidental || ''),
                octave: e.note.octave,
                number: e.note.number,
                velocity: e.rawVelocity,
                timestamp: Date.now()
            };

            this.handleNoteOn(noteData);
        });

        // Note Off
        input.addListener('noteoff', e => {
            const noteData = {
                note: e.note.name + (e.note.accidental || ''),
                octave: e.note.octave,
                number: e.note.number,
                timestamp: Date.now()
            };

            this.handleNoteOff(noteData);
        });
    },

    // Handle note on
    handleNoteOn(noteData) {
        // Adicionar às últimas notas
        this.lastNotes.unshift(noteData);
        if (this.lastNotes.length > 10) {
            this.lastNotes.pop();
        }

        // Atualizar display
        this.updateNoteDisplay();

        // Chamar callbacks
        this.noteCallbacks.forEach(callback => {
            try {
                callback('noteon', noteData);
            } catch (error) {
                console.error('Erro em callback MIDI:', error);
            }
        });
    },

    // Handle note off
    handleNoteOff(noteData) {
        this.noteCallbacks.forEach(callback => {
            try {
                callback('noteoff', noteData);
            } catch (error) {
                console.error('Erro em callback MIDI:', error);
            }
        });
    },

    // Registrar callback para eventos de nota
    onNote(callback) {
        if (typeof callback === 'function') {
            this.noteCallbacks.push(callback);
        }
    },

    // Remover callback
    removeCallback(callback) {
        const index = this.noteCallbacks.indexOf(callback);
        if (index > -1) {
            this.noteCallbacks.splice(index, 1);
        }
    },

    // Atualizar status
    updateStatus(message) {
        const statusEl = document.getElementById('midiStatus');
        if (statusEl) {
            statusEl.textContent = 'Status: ' + message;
            statusEl.className = 'status-message ' +
                (message.includes('Conectado') || message.includes('✅') ? 'success' :
                 message.includes('Erro') || message.includes('❌') ? 'error' :
                 message.includes('⚠️') ? 'warning' : 'info');
        }
    },

    // Mostrar dispositivos disponíveis
    displayDevices(inputs) {
        const devicesEl = document.getElementById('midiDevices');
        if (!devicesEl) return;

        devicesEl.innerHTML = '<h4>Dispositivos MIDI Disponíveis:</h4>';

        inputs.forEach((input, index) => {
            const deviceDiv = document.createElement('div');
            deviceDiv.className = 'device-item';
            deviceDiv.innerHTML = `
                <strong>${input.name}</strong>
                ${input.manufacturer ? `(${input.manufacturer})` : ''}
                ${index === 0 ? '<span class="badge">Conectado</span>' : ''}
            `;
            devicesEl.appendChild(deviceDiv);
        });
    },

    // Atualizar display de notas
    updateNoteDisplay() {
        const displayEl = document.getElementById('midiNoteDisplay');
        if (!displayEl) return;

        displayEl.innerHTML = '';

        this.lastNotes.slice(0, 5).forEach(note => {
            const noteDiv = document.createElement('div');
            noteDiv.className = 'midi-note-item';

            const noteName = this.convertToPortugueseName(note.note);
            const color = (typeof NOTE_COLORS !== 'undefined' && NOTE_COLORS[note.note]) || '#ccc';

            noteDiv.innerHTML = `
                <div class="note-color" style="background: ${color}"></div>
                <span><strong>${noteName}${note.octave}</strong> - Vel: ${note.velocity}</span>
            `;
            displayEl.appendChild(noteDiv);
        });

        if (this.lastNotes.length === 0) {
            displayEl.innerHTML = '<p style="color: #999;">Toque algumas notas no seu teclado MIDI...</p>';
        }
    },

    // Converter nome de nota para português
    convertToPortugueseName(note) {
        const nameMap = {
            'C': 'Dó', 'C#': 'Dó#', 'Db': 'Réb',
            'D': 'Ré', 'D#': 'Ré#', 'Eb': 'Mib',
            'E': 'Mi',
            'F': 'Fá', 'F#': 'Fá#', 'Gb': 'Solb',
            'G': 'Sol', 'G#': 'Sol#', 'Ab': 'Láb',
            'A': 'Lá', 'A#': 'Lá#', 'Bb': 'Sib',
            'B': 'Si'
        };
        return nameMap[note] || note;
    },

    // Desconectar
    disconnect() {
        if (this.currentInput && typeof this.currentInput.removeListener === 'function') {
            this.currentInput.removeListener();
            this.currentInput = null;
        }
        this.lastNotes = [];
        this.updateStatus('Desconectado');
        this.updateNoteDisplay();
    }
};

// Exportar para uso global
if (typeof window !== 'undefined') {
    window.MIDIHandler = MIDIHandler;
}
