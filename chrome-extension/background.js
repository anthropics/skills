chrome.runtime.onInstalled.addListener(() => {
  chrome.contextMenus.create({ id: "brianjosh-audit", title: "Send to BrianJosh", contexts: ["selection"] });
});
chrome.contextMenus.onClicked.addListener((info, tab) => {
  if (info.menuItemId === "brianjosh-audit") {
    chrome.sidePanel.open({ windowId: tab.windowId });
    chrome.storage.local.set({ brianjosh_selection: info.selectionText });
  }
});
