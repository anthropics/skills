#Requires AutoHotkey v2.0
#SingleInstance Force

SaveDir := EnvGet("USERPROFILE") "\Pictures\Claude_Screenshots"

#HotIf WinActive("ahk_exe WindowsTerminal.exe") or WinActive("ahk_exe powershell.exe") or WinActive("ahk_exe cmd.exe")

~^v::
{
    ; Check if clipboard contains a bitmap image (CF_BITMAP=2 or CF_DIB=8)
    if DllCall("IsClipboardFormatAvailable", "uint", 2) || DllCall("IsClipboardFormatAvailable", "uint", 8)
    {
        Timestamp := FormatTime(, "yyyyMMdd_HHmmss")
        FilePath := SaveDir "\Screenshot_" Timestamp ".png"

        If (!FileExist(SaveDir))
            DirCreate(SaveDir)

        ; Write a temp PS1 script to avoid quoting issues with file paths
        ps1 := EnvGet("TEMP") "\claude_save_img.ps1"
        if FileExist(ps1)
            FileDelete(ps1)
        FileAppend(
            "Add-Type -AssemblyName System.Windows.Forms`n"
            . '$img = [System.Windows.Forms.Clipboard]::GetImage()`n'
            . 'if ($img) { $img.Save("' FilePath '") }',
            ps1
        )

        RunWait('powershell.exe -NoProfile -WindowStyle Hidden -ExecutionPolicy Bypass -File "' ps1 '"',, "Hide")

        if FileExist(FilePath)
            SendInput(FilePath)
        else
            MsgBox("Failed to save image.")

        return
    }
}
#HotIf
