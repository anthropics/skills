Attribute VB_Name = "LegalBriefAutomation"
' ==========================================================================================
' NINTH CIRCUIT BRIEF AUTOMATION MACRO
' ==========================================================================================
' This macro automates the creation of the Table of Authorities (TOA) and updates the
' Table of Contents (TOC).
'
' INSTRUCTIONS:
' 1. Open your generated Word document.
' 2. Press Alt+F11 to open the VBA Editor.
' 3. Right-click "Normal" or "Project", select Insert > Module.
' 4. Paste this code.
' 5. Modify the "LoadAuthorities" subroutine with your specific case citations.
' 6. Run the "FinalizeBrief" macro.
' ==========================================================================================

Option Explicit

Sub FinalizeBrief()
    ' Main entry point
    Application.ScreenUpdating = False
    
    MsgBox "Starting Brief Automation..." & vbCrLf & "1. Marking Authorities" & vbCrLf & "2. Updating TOC/TOA", vbInformation, "Legal Automation"
    
    ' 1. Mark all authorities defined in the list
    MarkAllAuthorities
    
    ' 2. Link Record Citations (ECF/ER)
    LinkAllRecordCitations
    
    ' 3. Update all fields (TOC, TOA, Page Numbers)
    UpdateAllFields
    
    Application.ScreenUpdating = True
    MsgBox "Automation Complete!", vbInformation, "Success"
End Sub

Sub LinkAllRecordCitations()
    ' ==============================================================================
    ' EDIT THIS LIST WITH YOUR RECORD LINKS
    ' Format: LinkRecord "Search Text", "URL or File Path"
    ' ==============================================================================
    
    ' Example: Link to local files or web URLs
    ' LinkRecord "ECF No. 1", "C:\CaseFiles\Complaint.pdf"
    ' LinkRecord "ER 25", "C:\CaseFiles\Excerpts.pdf#page=25"
    
    ' You can generate this list programmatically using the python script
    
End Sub

Sub LinkRecord(ByVal strSearch As String, ByVal strAddress As String)
    ' Searches for text and adds a hyperlink
    Dim rng As Range
    Set rng = ActiveDocument.Content
    
    With rng.Find
        .ClearFormatting
        .Text = strSearch
        .MatchCase = False
        .MatchWholeWord = True
        
        Do While .Execute
            ' Add Hyperlink
            ActiveDocument.Hyperlinks.Add _
                Anchor:=rng, _
                Address:=strAddress
            
            ' Collapse range to end to continue search
            rng.Collapse Direction:=wdCollapseEnd
        Loop
    End With
End Sub

Sub MarkAllAuthorities()
    ' ==============================================================================
    ' EDIT THIS LIST WITH YOUR CITATIONS
    ' Format: MarkCitation "Search Text", "Long Citation for Table", Category
    ' Categories: 1=Cases, 2=Statutes, 3=Other, 4=Rules
    ' ==============================================================================
    
    ' --- CASES (Category 1) ---
    MarkCitation "Roe v. Wade", "Roe v. Wade, 410 U.S. 113 (1973)", 1
    MarkCitation "Miranda", "Miranda v. Arizona, 384 U.S. 436 (1966)", 1
    MarkCitation "Johnson", "Johnson v. Johnson (2019) 200 Cal.App.4th 200", 1
    
    ' --- STATUTES (Category 2) ---
    MarkCitation "28 U.S.C. § 1291", "28 U.S.C. § 1291", 2
    MarkCitation "Fed. R. Civ. P. 12(b)(6)", "Fed. R. Civ. P. 12(b)(6)", 4
    
    ' Add more here...
    
End Sub

Sub MarkCitation(ByVal strSearch As String, ByVal strLongCite As String, ByVal intCategory As Integer)
    ' Searches for text and marks it for the Table of Authorities
    Dim rng As Range
    Set rng = ActiveDocument.Content
    
    With rng.Find
        .ClearFormatting
        .Text = strSearch
        .MatchCase = False
        .MatchWholeWord = True
        
        Do While .Execute
            ' Mark the citation
            ' This inserts the hidden { TA } field next to the text
            ActiveDocument.TablesOfAuthorities.MarkCitation _
                Range:=rng, _
                ShortCitation:=strSearch, _
                LongCitation:=strLongCite, _
                Category:=intCategory
            
            ' Collapse range to end to continue search
            rng.Collapse Direction:=wdCollapseEnd
        Loop
    End With
End Sub

Sub UpdateAllFields()
    ' Updates TOC, TOA, and Page Numbers
    Dim toc As TableOfContents
    Dim toa As TableOfAuthorities
    
    ' Update TOCs
    For Each toc In ActiveDocument.TablesOfContents
        toc.Update
    Next toc
    
    ' Update TOAs
    For Each toa In ActiveDocument.TablesOfAuthorities
        toa.Update
    Next toa
    
    ' Update other fields (Page numbers, etc)
    ActiveDocument.Fields.Update
End Sub
