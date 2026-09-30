chrome.storage.local.get(['brianjosh_selection'], (result) => {
  if (result.brianjosh_selection) {
    document.getElementById('selectionBox').value = result.brianjosh_selection;
  }
});
chrome.storage.onChanged.addListener((changes, namespace) => {
  if (namespace === 'local' && changes.brianjosh_selection) {
    document.getElementById('selectionBox').value = changes.brianjosh_selection.newValue;
  }
});
document.getElementById('auditBtn').addEventListener('click', () => {
  const text = document.getElementById('selectionBox').value;
  if (!text) return;
  const resultDiv = document.getElementById('result');
  resultDiv.innerHTML = "<em>Running BrianJosh evidence crosswalk... (This is where the headless engine will connect).</em><br><br><strong>Text captured:</strong> " + text.length + " characters.";
});
