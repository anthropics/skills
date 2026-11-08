-- Export job-application emails (subject contains "应聘" + a keyword) from the macOS Mail app.
-- Usage: osascript export_mail.applescript OUT_DIR KEYWORDS [DAY_COUNT] [ACCOUNT_NAME]
--   KEYWORDS      comma-separated, matched case-insensitively against the subject, e.g. "ai开发,AI人工智能"
--   DAY_COUNT     only messages received in the last N days (default 30)
--   ACCOUNT_NAME  restrict to one Mail account (default: all accounts)
-- Writes OUT_DIR/<message id>/body.txt (subject, blank line, body) plus every attachment,
-- and returns one manifest line per message: id, account, date, subject.

on splitText(theText, delimiter)
	set AppleScript's text item delimiters to delimiter
	set parts to text items of theText
	set AppleScript's text item delimiters to ""
	return parts
end splitText

on run argv
	set outDir to item 1 of argv
	set kwList to my splitText(item 2 of argv, ",")
	set dayCount to 30
	if (count of argv) ≥ 3 then set dayCount to (item 3 of argv) as integer
	set accountFilter to ""
	if (count of argv) ≥ 4 then set accountFilter to item 4 of argv
	set cutoff to (current date) - (dayCount * days)
	set skipNames to {"Sent Messages", "Sent", "Drafts", "Deleted Messages", "Trash", "Junk", "已发送", "草稿", "已删除邮件", "废纸篓", "垃圾邮件"}
	set manifest to ""
	tell application "Mail"
		repeat with acc in accounts
			set accName to name of acc
			if accountFilter is "" or accName is accountFilter then
				repeat with mb in mailboxes of acc
					if skipNames does not contain (name of mb) then
						try
							set msgs to (messages of mb whose subject contains "应聘" and date received > cutoff)
							repeat with m in msgs
								set subj to subject of m
								set hit to false
								repeat with kw in kwList
									if subj contains (kw as text) then set hit to true
								end repeat
								if hit then
									set idText to (id of m) as text
									set dirPath to outDir & "/" & idText
									set bodyText to content of m
									do shell script "mkdir -p " & quoted form of dirPath & " && printf '%s\\n\\n%s' " & quoted form of subj & " " & quoted form of bodyText & " > " & quoted form of (dirPath & "/body.txt")
									repeat with a in mail attachments of m
										try
											save a in POSIX file (dirPath & "/" & (name of a))
										end try
									end repeat
									set manifest to manifest & idText & tab & accName & tab & ((date received of m) as text) & tab & subj & linefeed
								end if
							end repeat
						end try
					end if
				end repeat
			end if
		end repeat
	end tell
	return manifest
end run
