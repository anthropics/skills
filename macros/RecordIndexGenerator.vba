Attribute VB_Name = "RecordIndexGenerator"
' ==========================================================================================
' RECORD INDEX GENERATOR
' ==========================================================================================
' Scans the document for Record Citations (ECF/ER), builds a custom index with page numbers,
' and adds links to view the external exhibits.
' ==========================================================================================

Option Explicit

Sub GenerateRecordIndex()
    Dim doc As Document
    Set doc = ActiveDocument
    
    Dim regEx As Object
    Set regEx = CreateObject("VBScript.RegExp")
    
    ' --- CONFIGURATION: REGEX PATTERNS ---
    ' Pattern 1: ECF No. 123 page 45
    ' Pattern 2: ER 123
    regEx.Pattern = "(ECF\s+(?:No\.?\s*)?\d+(?:\s+page\s+[\d,]+)?)|(ER\s+\d+)|(\d+-ER-\d+)"
    regEx.Global = True
    regEx.IgnoreCase = True
    
    Dim rng As Range
    Set rng = doc.Content
    
    ' Dictionary to store unique citations and their locations
    ' Key: Citation Text (e.g. "ECF 8 page 2")
    ' Value: String of Page Numbers (e.g. "5, 12")
    Dim dictCites As Object
    Set dictCites = CreateObject("Scripting.Dictionary")
    
    ' Dictionary for External URLs (Populated by helper)
    Dim dictUrls As Object
    Set dictUrls = GetRecordUrls()
    
    Dim matches As Object
    Dim match As Object
    Dim strCite As String
    Dim pageNum As String
    
    ' 1. Scan Document
    If regEx.Test(rng.Text) Then
        Set matches = regEx.Execute(rng.Text)
        For Each match In matches
            strCite = match.Value
            
            ' Find the range of this match to get the page number
            ' Note: Regex gives position, we need to find it in Word range to get page
            ' This is a simplified approach; for large docs, Find loop is better than Regex text scan
            ' But for simplicity, we'll use Find to locate the specific instance
            
            Selection.Find.ClearFormatting
            With Selection.Find
                .Text = strCite
                .Wrap = wdFindContinue
            End With
            
            ' We use a Find loop below instead of Regex matches for accurate page numbers
        Next match
    End If
    
    ' 2. Robust Find Loop (Better for Page Numbers)
    Set rng = doc.Content
    With rng.Find
        .ClearFormatting
        .MatchWildcards = True
        ' Word Wildcards are different from Regex.
        ' We'll search for generic patterns and filter.
        ' Searching for "ECF" and "ER" generally
        .Text = "<[EE][CR][F ]*" ' Rough wildcard for ECF or ER
        
        ' Actually, let's stick to the Regex logic but map it to ranges
        ' It's safer to iterate matches and use Range.SetRange
    End With
    
    ' Let's use the Regex matches to find ranges
    Set matches = regEx.Execute(doc.Content.Text)
    
    For Each match In matches
        strCite = match.Value
        ' Get page number of this match
        ' Range.Start = match.FirstIndex
        Set rng = doc.Range(match.FirstIndex, match.FirstIndex + match.Length)
        pageNum = rng.Information(wdActiveEndAdjustedPageNumber)
        
        If dictCites.Exists(strCite) Then
            If InStr(dictCites(strCite), pageNum) = 0 Then
                dictCites(strCite) = dictCites(strCite) & ", " & pageNum
            End If
        Else
            dictCites.Add strCite, pageNum
        End If
    Next match
    
    ' 3. Create the Index Table
    CreateIndexTable doc, dictCites, dictUrls
    
    MsgBox "Record Index Generated!", vbInformation
End Sub

Sub CreateIndexTable(doc As Document, dictCites As Object, dictUrls As Object)
    Dim rng As Range
    Set rng = doc.Content
    rng.Collapse Direction:=wdCollapseEnd
    
    ' Add Header
    rng.InsertBreak Type:=wdPageBreak
    rng.InsertAfter "INDEX OF RECORD CITATIONS" & vbCr
    rng.Style = doc.Styles("Heading 1")
    rng.Collapse Direction:=wdCollapseEnd
    
    ' Create Table
    Dim tbl As Table
    Dim key As Variant
    Dim row As Row
    Dim url As String
    
    Set tbl = doc.Tables.Add(rng, dictCites.Count + 1, 3)
    tbl.Borders.Enable = False
    
    ' Header Row
    tbl.Cell(1, 1).Range.Text = "Citation"
    tbl.Cell(1, 2).Range.Text = "Brief Page(s)"
    tbl.Cell(1, 3).Range.Text = "Link"
    tbl.Rows(1).Range.Font.Bold = True
    
    Dim i As Integer
    i = 2
    
    For Each key In dictCites.Keys
        ' Col 1: Citation
        tbl.Cell(i, 1).Range.Text = key
        
        ' Col 2: Page Numbers (Internal Linking could be added here)
        tbl.Cell(i, 2).Range.Text = dictCites(key)
        
        ' Col 3: External Link
        ' Extract the Doc Number for lookup (e.g. "ECF 8" -> "ECF 8")
        ' Simple lookup logic
        url = ""
        If dictUrls.Exists(key) Then
            url = dictUrls(key)
        Else
            ' Try partial match (e.g. map "ECF 8" to "ECF 8 page 2")
            ' For now, exact match or empty
        End If
        
        If url <> "" Then
            doc.Hyperlinks.Add Anchor:=tbl.Cell(i, 3).Range, _
                Address:=url, _
                TextToDisplay:="<view-exhibit>"
        End If
        
        i = i + 1
    Next key
    
    ' Formatting
    tbl.Columns(1).Width = Inches(3)
    tbl.Columns(2).Width = Inches(1.5)
    tbl.Columns(3).Width = Inches(1.5)
    
End Sub

Function GetRecordUrls() As Object
    ' Populated by Python Script or Manual Entry
    Dim dict As Object
    Set dict = CreateObject("Scripting.Dictionary")
    
    ' Example Data - This will be replaced by your Python generator
    ' dict.Add "ECF 8 page 2", "https://ecf.court.gov/doc8"
    
    Set GetRecordUrls = dict
End Function
