import mermaid from 'mermaid';

/**
 * Checks if the content contains any Mermaid syntax errors using mermaid.parse.
 * Also detects unclosed Mermaid blocks.
 * @param content The markdown content to check.
 * @returns A promise that resolves to the number of errors found.
 */
export async function checkMermaidErrors(content: string): Promise<number> {
    const mermaidBlockRegex = /^(?:[ \t]*)(?:```|~~~)\s*mermaid\b[^\n]*\n([\s\S]*?)\n(?:[ \t]*)(?:```|~~~)/gim;
    let match;
    let errorCount = 0;
    
    // Initialize mermaid if needed (though usually handled by the app/plugin load)
    // We use a safe configuration
    mermaid.initialize({ startOnLoad: false, suppressErrorRendering: true });

    // Check closed blocks
    while ((match = mermaidBlockRegex.exec(content)) !== null) {
        try {
            await mermaid.parse(match[1]);
        } catch (error) {
            errorCount++;
        }
    }
    return errorCount;
}

/**
 * Processes markdown content to validate and fix Mermaid syntax issues.
 * Specifically ensures that ```mermaid blocks are properly closed after the last arrow (`-->`).
 * Also applies deep debug fixes if Mermaid errors still exist after basic fixes.
 * Adapted from logic in LMStudio-Markdown-Content-Generator/mermaid.py.
 */
export async function refineMermaidBlocks(content: string): Promise<string> {
	const lines = content.split('\n');
	let resultLines: string[] = [];
	let inMermaid = false;
	let currentBlockLines: string[] = [];
	let lastArrowIndexInBlock = -1;

	for (let line of lines) { // Use 'let' so we can modify the line
		const stripped = line.trim();

		// Regex to detect ```(mermaid) or ``` mermaid with optional space/parentheses
		const mermaidStartRegex = /^```\s*\(?\s*mermaid\s*\)?/;


		if (mermaidStartRegex.test(stripped)) {
			// Normalize the starting line
			line = line.replace(mermaidStartRegex, '```mermaid');

			// If already in a block, finish the previous one before starting new
			if (inMermaid) {
				if (lastArrowIndexInBlock !== -1) {
					// Ensure the line after the last arrow isn't already the closer
					if (currentBlockLines[lastArrowIndexInBlock + 1]?.trim() !== '```') {
						currentBlockLines.splice(lastArrowIndexInBlock + 1, 0, '```');
					}
				} else if (currentBlockLines.length > 0) {
                    // Block started but no arrows, ensure it's closed if not already
                     if (currentBlockLines[0].trim().startsWith('```mermaid') && currentBlockLines[currentBlockLines.length - 1].trim() !== '```') {
                         // Check if the line after start isn't the closer
                         if (currentBlockLines.length === 1 || currentBlockLines[1]?.trim() !== '```') {
                            currentBlockLines.splice(1, 0, '```'); // Close after the opening line
                         }
                     }
                }
				resultLines.push(...currentBlockLines);
			}
			// Start new block
			inMermaid = true;
			currentBlockLines = [line];
			lastArrowIndexInBlock = -1;
		} else if (inMermaid) {
			// Handle ; # comments - convert to labeled arrows
			const commentMatch = line.match(/^(\w+)\s*-->\s*(\w+);\s*#(.*)$/);
			if (commentMatch) {
				line = `${commentMatch[1]} -- "${commentMatch[3].trim()}" --> ${commentMatch[2]};`;
			}

			// Apply new quote rules BEFORE removing brackets, ONLY if 'subgraph' is NOT on the line
			if (!line.includes('subgraph')) {
				// 先保护 |" 和 "| 的情况
				const placeholder = '___PROTECTED_QUOTE___';
				line = line.replace(/\|"/g, `|${placeholder}`);
				line = line.replace(/"\|/g, `${placeholder}|`);

				// Rule 1 (Revised - No Lookbehind):
				// 1a: Handle quote at the start of the line
				line = line.replace(/^"(?!;|\s)(?!\])/g, '["');
				// 1b: Handle quote preceded by a non-space, non-[ character
				line = line.replace(/([^\s\[])"(?!;|\s)(?!\])/g, '$1["');

				// Rule 2: Replace "; with ];
				line = line.replace(/";/g, '"];');

				// 还原被保护的引号
				line = line.replace(new RegExp(placeholder, 'g'), '"');
				
				// Rule 3: Replace ["; with "];
				line = line.replace(/\[";/g, '"];');
				// New Rule 4: Replace ?["; with ?"];
				line = line.replace(/\?\[";/g, '?"];');
				
				// 添加额外的清理步骤，确保没有残留的[";模式
				// 重复应用Rule 3直到没有更多的[";模式
				while (line.includes('[";')) {
					line = line.replace(/\[";/g, '"];');
					
					// New Rule 4: Replace ?["; with ?"];
					line = line.replace(/\?\[";/g, '?"];');
				}
                // Safeguard: Final replacements to ensure ["; and ?["; are corrected
                line = line.replace(/\[";/g, '"];');
                line = line.replace(/\?\[";/g, '?"];');

				// New User Rule 1: If line ends with [;";, change to "];
				line = line.replace(/\[";$/, '"];');
				// New User Rule 2: Then, if line ends with [", change to "]
				line = line.replace(/\["$/, '"]');

                // New User Rule 3: Fix broken edge labels `--["Text["-->` to `-- "Text" -->`
                // Example: `CapRate --["Inverse Relationship["-->` becomes `CapRate -- "Inverse Relationship" -->`
                line = line.replace(/--\s*\["(.+?)\["\s*-->/g, '-- "$1" -->');

                // --- User Requested "Fix Mode" Logic for [ ... ] ---
                // Detects Node[Label] where Label isn't fully quoted but contains brackets/quotes.
                // Targeted cases:
                // 1. `Investment[Corporate Investment "[企业投资]"]` -> `Investment["Corporate Investment [企业投资]"]`
                // 2. `Consumption[Consumption [消费]]` -> `Consumption["Consumption [消费]"]`
                // 3. `WhiteDwarf[白矮星 [White Dwarf]]` -> `WhiteDwarf["白矮星 [White Dwarf]"]`
                
                // Improved regex to handle one level of nested brackets:
                // ([^\s\[]+)  : NodeID (non-whitespace AND non-[ chars)
                // \s*\[       : Opening bracket
                // (?!"|')     : Content does NOT start with " or ' (already quoted nodes are skipped)
                // (           : Start capturing content
                //   (?:       : Non-capturing group for content parts
                //     [^\[\]] : Any character EXCEPT [ or ]
                //     |       : OR
                //     \[[^\[\]]*\] : A nested [...] block with no brackets inside
                //   )*        : Repeat content parts
                // )           : End capturing content
                // \]          : Closing bracket
                
                line = line.replace(/([^\s\[]+)\s*\[(?!"|')((?:[^\[\]]|\[[^\[\]]*\])*)\]/g, (match, nodeId, content) => {
                     // Filter out matches that don't actually contain broken characters we care about.
                     // The regex already excludes things starting with ".
                     // We specifically want to fix things that have [ or ] inside.
                     if (/[\[\]|]/.test(content)) {
                         // Logic:
                         // 1. Remove existing double quotes from content to avoid syntax errors (as per user example where inner quotes were removed).
                         // 2. Wrap in double quotes.
                         const cleanContent = content.replace(/"/g, ''); 
                         return `${nodeId}["${cleanContent}"]`;
                     }
                     return match;
                });
			}

			// Remove parentheses and curly braces from the line content within the mermaid block
			let lineWithoutBrackets = line.replace(/[(){}]/g, ''); // Updated regex

			// Fix [" at the end of the line
			if (lineWithoutBrackets.endsWith('\["')) {
				lineWithoutBrackets = lineWithoutBrackets.slice(0, -2) + '"]';
			}

			currentBlockLines.push(lineWithoutBrackets);
			if (lineWithoutBrackets.includes('-->')) { // Check the modified line for arrows
				lastArrowIndexInBlock = currentBlockLines.length - 1; // Index within currentBlockLines
			}
			if (stripped === '```') {
				// Found the intended closing tag, finalize this block
				resultLines.push(...currentBlockLines);
				inMermaid = false;
				currentBlockLines = [];
				lastArrowIndexInBlock = -1;
			}
		} else {
			// Line outside any mermaid block
			resultLines.push(line);
		}
	}

	// Handle unclosed block at the very end of the file
	if (inMermaid) {
		if (lastArrowIndexInBlock !== -1) {
			// Ensure the line after the last arrow isn't already the closer
            // Check if the index exists before accessing trim()
			if (lastArrowIndexInBlock + 1 >= currentBlockLines.length || currentBlockLines[lastArrowIndexInBlock + 1]?.trim() !== '```') {
				currentBlockLines.splice(lastArrowIndexInBlock + 1, 0, '```');
			}
		} else if (currentBlockLines.length > 0) {
            // Block started but no arrows, ensure it's closed if not already
            if (currentBlockLines[0].trim().startsWith('```mermaid') && currentBlockLines[currentBlockLines.length - 1].trim() !== '```') {
                 // Check if the line after start isn't the closer
                 if (currentBlockLines.length === 1 || currentBlockLines[1]?.trim() !== '```') {
                    currentBlockLines.splice(1, 0, '```'); // Close after the opening line
                 } else if (currentBlockLines[currentBlockLines.length -1].trim() !== '```') {
                     // If it wasn't closed after line 1, add closer at the end
                     currentBlockLines.push('```');
                 }
            } else if (currentBlockLines[currentBlockLines.length -1].trim() !== '```') {
                 // Failsafe if somehow the last line isn't a closer
                 currentBlockLines.push('```');
            }
        }
		resultLines.push(...currentBlockLines);
	}

	let result = resultLines.join('\n');

	// Check for remaining errors to decide if we need deep debug
	const errorCount = await checkMermaidErrors(result);

    // Regex to find mermaid blocks and apply fixes ONLY inside them
    // Matches ```mermaid followed by content and ending with ```
    // We use [\s\S]*? for non-greedy multiline match
    const mermaidBlockRegex = /(```\s*mermaid\n)([\s\S]*?)(\n```)/gi;

    result = result.replace(mermaidBlockRegex, (match, startTag, blockContent, endTag) => {
        let processedBlock = blockContent;

        // Apply scoped replacements inside mermaid blocks
        
        // Replace note "Sentences" with Note1[/"Sentences"/], Note2[/"Sentences"/]...
        let noteCounter = 1;
        processedBlock = processedBlock.replace(/note\s+"([^"]*)"/g, (match: string, noteContent: string) => {
            return `Note${noteCounter++}[/"${noteContent}"/]`;
        });

        // Remove content after ; if the line contains % after ;
        processedBlock = processedBlock.replace(/;(.*)$/gm, (match: string, p1: string) => p1.includes('%') ? ';' : match);

        // Apply deep debug fixes if errors were found in the file
        // (Optimally we would check this block specifically, but this preserves original logic trigger)
        if (errorCount > 0) {
            processedBlock = deepDebugMermaid(processedBlock);
        }

        return `${startTag}${processedBlock}${endTag}`;
    });

	return result;
}

/**
 * Applies deep debug fixes ONLY to the content within Mermaid code blocks.
 * This is a safe alternative to calling deepDebugMermaid on the entire file.
 * @param content The markdown content.
 * @returns The processed content with Mermaid blocks debugged.
 */
export function applyDeepDebugToMermaidBlocks(content: string): string {
    const mermaidBlockRegex = /(```\s*mermaid\n)([\s\S]*?)(\n```)/gi;

    return content.replace(mermaidBlockRegex, (match, startTag, blockContent, endTag) => {
        const processedBlock = deepDebugMermaid(blockContent);
        return `${startTag}${processedBlock}${endTag}`;
    });
}

/**
 * Cleans up LaTeX math delimiters.
 * Converts \( and \) to $.
 * Removes extra spaces around $.
 * Ensures space before $ if preceded by a hyphen.
 * Removes \$ escape sequence.
 *
 * @param content The markdown content string.
 * @returns Content with cleaned math delimiters.
 */
export function cleanupLatexDelimiters(content: string): string {
	const placeholder = '___TEMP_DOLLAR_ESCAPE___';
	let processed = content;

	// 1. Protect escaped dollars
	processed = processed.replace(/\\\$/g, placeholder);

	// 2. Convert \( and \) to $
	processed = processed.replace(/\\\(/g, '$').replace(/\\\)/g, '$');

	// 3. Trim whitespace inside single $...$ (non-greedy)
	// This regex finds a $ followed by optional whitespace, captures the content (non-greedily),
	// followed by optional whitespace and a closing $. It replaces the whole match with $content$.
	// It avoids matching $$ by ensuring the captured content doesn't start or end with $.
	processed = processed.replace(/\$\s*([^$]*?)\s*\$/g, (match, group1) => {
        // Avoid affecting display math $$...$$
        if (match.startsWith('$$') && match.endsWith('$$')) {
            return match; // Leave display math untouched
        }
        // Trim the captured group and reconstruct
        const trimmedGroup = group1.trim();
        return `$${trimmedGroup}$`;
    });


	// 4. Restore escaped dollars
	processed = processed.replace(new RegExp(placeholder, 'g'), '$');

	return processed;
}

/**
 * Deep debug function for Mermaid syntax.
 * Applies all available fixes in a specific order.
 * 0. Fix Smart Quotes (curly quotes to straight quotes, slashed notes).
 * 1. Fix Mermaid Pipes (handle `|`).
 * 2. Fix Mermaid Notes.
 * 3. Fix Malformed Arrows.
 * 4. Merge Double Labels.
 * 5. Fix Missing Brackets.
 * 6. Fix Inline Subgraphs.
 * 7. Fix Mermaid Comments.
 * 8. Fix Unquoted Node Labels.
 * 9. Fix Intermediate Nodes.
 * 10. Fix Doubled IDs.
 * 11. Fix Excessive Brackets (including ]]] -> ]).
 * 12. Fix Semicolon Positioning.
 * 13. Fix Unquoted Labels with Semicolons.
 * 14. Enhanced Note and Semicolon Cleanup.
 */
export function deepDebugMermaid(content: string): string {
    // --- SAFEGUARD: Protect Table Lines ---
    // User requirement: Ensure no modification to lines containing ':-- :'
    // Also protecting standard markdown table separators to prevent corruption
    const tableLinePlaceholderPrefix = '___PROTECTED_TABLE_LINE_';
    const protectedTableLines: string[] = [];
    
    // Regex for table separator line: starts with |, contains dashes/colons/pipes, ends with | (roughly)
    const tableSeparatorRegex = /^\s*\|(?:[\s\t]*:?[\s\t]*-+[\s\t]*:?[\s\t]*\|)+[\s\t]*$/;

    let processed = content.split('\n').map(line => {
        if (line.includes(':-- :') || tableSeparatorRegex.test(line)) {
            const placeholder = `${tableLinePlaceholderPrefix}${protectedTableLines.length}___`;
            protectedTableLines.push(line);
            return placeholder;
        }
        return line;
    }).join('\n');

    // 0. Fix Smart Quotes FIRST - handles “” -> "" and Note["/“text”/"] -> Note["/text/"]
    processed = fixSmartQuotes(processed);

    // 1. Fix Mermaid Pipes (handle `|`) - Requested to be first
    processed = fixMermaidPipes(processed);

    // 2. Fix Mermaid Notes (move "note right of" to edge labels)
    processed = fixMermaidNotes(processed);

    // 2.5. Fix Notes to Nodes (note right of A : Text -> NoteA["Note: Text"] A -.- NoteA)
    processed = fixNotesToNodes(processed);

    // 3. Fix Malformed Arrows (handle `-->"` and `"-- `)
    processed = fixMalformedArrows(processed);

    // 3.5 Fix Invalid Arrows (handle `--|>` -> `-->`)
    processed = fixInvalidArrows(processed);

    // 4. Merge Double Labels
    processed = mergeDoubleLabels(processed);

    // 5. Fix Missing Brackets (existing logic)
    processed = fixMissingBrackets(processed);

    // 6. Fix Inline Subgraphs (convert subgraph "Label" end; to edge label)
    processed = fixInlineSubgraphs(processed);

    // 7. Fix Mermaid Comments (Move % comments to label)
    processed = fixMermaidComments(processed);

    // 17. Fix Double Slash Comments (// -> -- "..." -->) - Apply before general label fixes
    processed = fixDoubleSlashComments(processed);

    // 8. Fix Unquoted Node Labels (Quote labels with special chars)
    processed = fixUnquotedNodeLabels(processed);

    // 9. Fix Intermediate Nodes (NodeA -- NodeB[...] --> NodeC)
    processed = fixIntermediateNodes(processed);

    // 10. Fix Doubled IDs (SplitSplit Sample -> Split[Split Sample])
    processed = fixDoubledID(processed);

    // 11. Fix Excessive Brackets (including ]]] -> ]).
    processed = fixExcessiveBrackets(processed);

    // 12. Fix Semicolon Positioning (Move "] before ;)
    processed = fixSemicolonPositioning(processed);

    // 12.5. Fix Concatenated Labels (SubdivideSubdivide... -> Subdivide["Subdivide..."])
    processed = fixConcatenatedLabels(processed);

    // 13. Fix Unquoted Labels Ending with Semicolons
    processed = fixUnquotedLabelsWithSemicolons(processed);

    // 14. Enhanced Note and Semicolon Cleanup.
    processed = enhancedNoteAndSemicolonCleanup(processed);

    // 15. Fix Reverse Arrows (<--)
    processed = fixReverseArrows(processed);

    // 16. Fix Subgraph Direction (Direction -> direction)
    processed = fixSubgraphDirection(processed);

    // 18. Fix Duplicate Labels (["..."]["..."] -> ["..."])
    processed = fixDuplicateLabels(processed);

    // 19. Fix Nested Mermaid Quotes (["...["..."]...."] -> ["...[...]..."])
    processed = fixNestedMermaidQuotes(processed);

    // 20. Fix Quoted Labels After Semicolon (A --> B; "Label" -> A -- "Label" --> B;)
    processed = fixQuotedLabelsAfterSemicolon(processed);

    // 21. Fix Double Dash To Arrow (... -- ...; -> ... --> ...;)
    processed = fixDoubleDashToArrow(processed);

    // 22. Fix Targeted Notes (note Node "Content" -> NoteNode["Content"] \n Node -.- NoteNode)
    processed = fixTargetedNotes(processed);

    // 23. Fix Double Arrow Labels (Node -- L1 -- L2 --> Node)
    processed = fixDoubleArrowLabels(processed);

    // 24. Fix Unquoted Edge Labels (Node -- Unquoted --> Node)
    processed = fixUnquotedEdgeLabels(processed);

    // 26. Fix Shape Mismatch ([/["...["/] -> ["..."])
    processed = fixShapeMismatch(processed);

    // 27. Cleanup Placeholder Artifacts
    processed = fixPlaceholderArtifacts(processed);

    // 28. Cleanup `|\"\"|\"`
    processed = processed.replace(/\|""\|"/g, '');

    // 29. Cleanup `\[""\]`
    processed = processed.replace(/\[""\]/g, '');

    // 29 Fix Misplaced Pipes (>|"..."| ...)
    processed = fixMisplacedPipes(processed);

    // 30 Fix Misplaced Pipes (>|"..."| ...)
    processed = processed.replace(/\"\[\]\"/g, '');

    // 31 Fix Misplaced Pipes (>|"..."| ...)
    processed = fixBlankArrows(processed);

    
    // --- RESTORE: Table Lines ---
    if (protectedTableLines.length > 0) {
        // We need to restore them. Since we operate on the whole string, we can replace the placeholders.
        // However, some functions might have shifted things around? 
        // Most functions are line-preserving or map lines.
        // But `fixMermaidNotes` removes lines. `fixTargetedNotes` adds lines.
        // The placeholders should persist as lines.
        
        // We iterate through the protected lines and replace their corresponding placeholder
        protectedTableLines.forEach((originalLine, index) => {
             const placeholder = `${tableLinePlaceholderPrefix}${index}___`;
             // Use split/join to replace all occurrences (though strictly should be one)
             processed = processed.split(placeholder).join(originalLine);
        });
    }

    return processed;
}

/**
 * Fixes invalid arrow syntax `--|>` by converting it to the standard `-->`.
 * This often appears as a malformed attempt at an arrow or a typo.
 * @param content The markdown content.
 * @returns Content with `--|>` replaced by `-->`.
 */
export function fixInvalidArrows(content: string): string {
    // Global replacement of --|> with -->
    return content.replace(/--\|>/g, '-->');
}


/**
 * Fixes invalid arrow syntax `--|>` by converting it to the standard `-->`.
 * This often appears as a malformed attempt at an arrow or a typo.
 * @param content The markdown content.
 * @returns Content with `--|>` replaced by `-->`.
 */
export function fixBlankArrows(content: string): string {
    // Global replacement of -- > with -->
    return content.replace(/-- >/g, '-->');
}

/**
 * Fixes shape mismatch where node shape definitions are mixed with quoted labels.
 * Specifically targets the pattern `[/["...["/]` and converts it to standard `["..."]`.
 * Example: `note1[/["Path Difference = CB + BD["/] -> note1["Path Difference = CB + BD"]`
 */
export function fixShapeMismatch(content: string): string {
    let processed = content;
    // Fix start: [/[" -> ["
    processed = processed.replace(/\[\/\["/g, '["');
    // Fix end: ["/] -> "]
    processed = processed.replace(/\["\/\]/g, '"]');
    return processed;
}

/**
 * Cleans up leftover placeholder artifacts.
 * Deletes '___BRACKET_BLOCK_0___' and similar artifacts.
 */
export function fixPlaceholderArtifacts(content: string): string {
    return content.replace(/___BRACKET_BLOCK_\d+___/g, '');
}

/**
 * Fixes double arrow labels.
 * Pattern: `Node -- Label1 -- Label2 --> Node` or `Node -- Label1 -- Label2 --- Node`
 * Result: `Node -- "Label1<br>Label2" --> Node`
 * Handles quoted or unquoted labels.
 * Refined to avoid matching `---` or `-->` as label separators.
 */
export function fixDoubleArrowLabels(content: string): string {
    const lines = content.split('\n');
    return lines.map(line => {
        // Regex: Start -- L1 -- L2 (Arrow) End
        // Arrow can be --> or ---
        // We match non-greedy content between dashes.
        // We use lookbehind (?<!-) and lookahead (?!>|-) to ensure we match exactly "--"
        // and not parts of "---" or "-->".
        
        const regex = /^(.*?)\s*(?<!-)--(?!>|-)\s*((?:(?!-->|---|(?<!-)--(?!>|-)\s).)*?)\s*(?<!-)--(?!>|-)\s*((?:(?!-->|---|(?<!-)--(?!>|-)\s).)*?)\s*(-->|---)\s*(.*)$/;
        
        const match = line.match(regex);
        if (match) {
            const start = match[1];
            let l1 = match[2].trim();
            let l2 = match[3].trim();
            const arrow = match[4]; // "-->" or "---"
            const end = match[5];

            // Strip quotes if present
            if (l1.startsWith('"') && l1.endsWith('"')) l1 = l1.slice(1, -1);
            if (l2.startsWith('"') && l2.endsWith('"')) l2 = l2.slice(1, -1);

            // Combine with <br>
            const combined = `${l1}<br>${l2}`;
            
            return `${start} -- "${combined}" ${arrow} ${end}`;
        }
        return line;
    }).join('\n');
}

/**
 * Fixes unquoted edge labels.
 * Pattern: `Node -- Unquoted Text --> Node`
 * Result: `Node -- "Unquoted Text" --> Node`
 * Skips if already quoted.
 */
export function fixUnquotedEdgeLabels(content: string): string {
    const lines = content.split('\n');
    return lines.map(line => {
        // Regex: (Start) -- (Label) --> (End)
        // Label must NOT start with ".
        // We need to be careful about `Node -- Node` (no label) which uses `---` or `-->` directly.
        // This regex targets ` -- ` space-dash-dash-space specifically used for labels.
        // Refined to use (?<!-)--(?!>|-) to avoid matching ---
        
        const regex = /^(.*?)\s*(?<!-)--(?!>|-)\s*([^">]+?)\s*-->\s*(.*)$/;
        
        // Exclude if it looks like `Node -- Node -->` (which is invalid anyway but...)
        // We assume valid label text doesn't contain `-->` which regex enforces.
        
        const match = line.match(regex);
        if (match) {
            const start = match[1];
            const label = match[2].trim();
            const end = match[3];

            // Double check it's not starting with quote (regex might miss if whitespace handled poorly)
            if (label.startsWith('"')) return line;
            
            // Also ignore if label is empty (e.g. `A -- --> B` ? Invalid but possible typo)
            if (!label) return line;

            return `${start} -- "${label}" --> ${end}`;
        }
        return line;
    }).join('\n');
}

/**
 * Fixes "note position of Node : Content" by converting to a Note Node.
 * Pattern: `note right of A : Text`
 * Result: 
 * NoteA["Note: Text"]
 * A -.- NoteA
 * 
 * Also handles `note : Text` (standalone) -> `NoteX["Text"]` (no connection? or standalone)
 */
export function fixNotesToNodes(content: string): string {
    const lines = content.split('\n');
    const resultLines: string[] = [];
    let standaloneCounter = 1;

    // Regex for targeted notes (standard mermaid: note right of ...)
    const targetedRegex = /^\s*note\s+(?:right|left|top|bottom)\s+of\s+([a-zA-Z0-9_]+)\s*:\s*(.*)$/i;
    
    // Regex for "note for/of Node Content" (User Extension)
    // Matches: note for Node "Content"
    const noteForOfRegex = /^\s*note\s+(?:for|of)\s+([a-zA-Z0-9_]+)\s+(.*)$/i;
    
    // Regex for standalone notes (note : Content)
    // Sometimes people write `note "Content"` which is handled elsewhere, but `note :` is specific.
    const standaloneRegex = /^\s*note\s*:\s*(.*)$/i;

    for (const line of lines) {
        // Check Targeted (Standard)
        const tMatch = line.match(targetedRegex);
        if (tMatch) {
            const nodeId = tMatch[1];
            const text = tMatch[2].trim();
            const noteId = `Note${nodeId}`;
            
            // Format: NoteA["Note: ..."]
            // If text is already quoted, strip them?
            // User example: `Very High...` -> `["Note: Very High..."]`
            let cleanText = text;
            if (cleanText.startsWith('"') && cleanText.endsWith('"')) {
                cleanText = cleanText.slice(1, -1);
            }
            
            resultLines.push(`${noteId}["Note: ${cleanText}"]`);
            resultLines.push(`${nodeId} -.- ${noteId}`);
            continue;
        }

        // Check Targeted (Note For/Of - User Extension)
        const nfMatch = line.match(noteForOfRegex);
        if (nfMatch) {
            const nodeId = nfMatch[1];
            let text = nfMatch[2].trim();

            // Handle artifact where line ends with ]
            if (text.endsWith(']')) {
                 text = text.slice(0, -1).trim();
            }

            const noteId = `Note${nodeId}`;

            // Clean quotes
            if (text.startsWith('"') && text.endsWith('"')) {
                text = text.slice(1, -1);
            }
            
            // User requested format: NoteM00[" Gaussian Intensity Profile"] (with leading space)
            resultLines.push(`${noteId}[" ${text}"]`);
            resultLines.push(`${nodeId} -.- ${noteId}`);
            continue;
        }

        // Check Standalone
        const sMatch = line.match(standaloneRegex);
        if (sMatch) {
            let text = sMatch[1].trim();
             if (text.startsWith('"') && text.endsWith('"')) {
                text = text.slice(1, -1);
            }
            const noteId = `Note${standaloneCounter++}`;
            resultLines.push(`${noteId}["${text}"]`);
            continue;
        }

        resultLines.push(line);
    }
    return resultLines.join('\n');
}

/**
 * Fixes nested quotes within Mermaid node labels.
 * Ensures that if a label is wrapped in `["..."]`, any internal double quotes are removed.
 * This handles cases like: `SP --> Martingale["Martingale<br>E["Future | Past"] = Present"];`
 * converting it to: `SP --> Martingale["Martingale<br>E[Future | Past] = Present"];`
 * Uses a balanced bracket approach to identify the outer block.
 */
export function fixNestedMermaidQuotes(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Optimization: Skip if no `["` present
        if (!line.includes('["')) return line;

        let newLine = '';
        let currentIndex = 0;
        
        while (currentIndex < line.length) {
            // Find start of a potential `["` block
            const openQuoteIndex = line.indexOf('["', currentIndex);
            
            if (openQuoteIndex === -1) {
                // No more blocks, append rest of line
                newLine += line.slice(currentIndex);
                break;
            }

            // Append everything before the block
            newLine += line.slice(currentIndex, openQuoteIndex);
            
            // Now scan for the closing `"]` using balanced brackets
            let depth = 0;
            let foundClose = false;
            let closeIndex = -1;
            
            // Start scanning from the `[`
            for (let i = openQuoteIndex; i < line.length; i++) {
                const char = line[i];
                
                if (char === '[') {
                    depth++;
                } else if (char === ']') {
                    depth--;
                }
                
                // Check if we are at depth 0 (closed) and it's a `"]` pattern
                // The closing pattern is `"]`. So current char is `]` and prev was `"`.
                // Note: We need to be careful. The block starts with `["`.
                // If we have `["abc"]`, at `]` depth becomes 0.
                if (depth === 0) {
                    // Check if it's `"]`
                    if (line[i] === ']' && line[i-1] === '"') {
                        closeIndex = i;
                        foundClose = true;
                        break;
                    }
                }
            }
            
            if (foundClose) {
                // We found a complete `[" ... "]` block
                // Extract content: between `["` (start+2) and `"]` (end-1)
                const fullBlock = line.slice(openQuoteIndex, closeIndex + 1);
                const innerContent = line.slice(openQuoteIndex + 2, closeIndex - 1); // remove `["` and `"]`
                
                // Process inner content: remove all quotes `"`
                // Requirement: "remove all redundant `"` characters"
                // This keeps `["` and `"]` valid as brackets [ ] inside.
                const cleanContent = innerContent.replace(/"/g, '');
                
                // Reconstruct block
                newLine += `["${cleanContent}"]`;
                
                // Advance index past this block
                currentIndex = closeIndex + 1;
            } else {
                // Unbalanced or malformed, just keep the `["` and move on
                // To avoid infinite loop, advance past the `["`
                newLine += '["';
                currentIndex = openQuoteIndex + 2;
            }
        }
        
        return newLine;
    });
    return processedLines.join('\n');
}

/**
 * Fixes formatted arrows followed by a semicolon and a string literal.
 * Converts `A --> B; "Label"` into `A -- "Label" --> B;`.
 * Example: `Levy --> Stationary; "Increments are stationary"`
 */
export function fixQuotedLabelsAfterSemicolon(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Regex to look for:
        // 1. Everything before the arrow (Source)
        // 2. The arrow (-->)
        // 3. The target node (Target)
        // 4. A semicolon
        // 5. Optional whitespace
        // 6. A quoted string ("Label")
        // 7. Optional trailing content (ignored or kept?) -> usually assume end of meaningful instruction
        
        // We match `-->` specifically as per request.
        if (!line.includes('-->')) return line;
        
        // Regex:
        // ^(start) (-->) (target) (;)\s* " (label) " \s* $
        const regex = /^(.*?)\s*(-->)\s*(.*?);\s*"([^"]+)"\s*$/;
        
        const match = line.match(regex);
        if (match) {
            const source = match[1].trim();
            const arrow = match[2].trim(); // "-->"
            const target = match[3].trim();
            const label = match[4].trim(); // content inside quotes
            
            // Construct new line
            // Source -- "Label" --> Target;
            // We insert the label into the arrow.
            return `${source} -- "${label}" ${arrow} ${target};`;
        }
        
        return line;
    });
    return processedLines.join('\n');
}


/**
 * Fixes excessive brackets like `[["` -> `["` and `["]` -> `"]`.
 * Also ensures `[";` becomes `"];` if not already handled.
 * Enhanced to handle complex patterns like:
 * - `Target -- Result --> PT___BRACKET_BLOCK_0______BRACKET_BLOCK_0______BRACKET_BLOCK_0___[["Final...["` 
 * - Should become: `Target -- Result --> PT___BRACKET_BLOCK_0______BRACKET_BLOCK_0______BRACKET_BLOCK_0___["Final..."]`
 */
export function fixExcessiveBrackets(content: string): string {
    let lines = content.split('\n');
    lines = lines.map(line => {
        let processedLine = line;
        
        // Multiple passes to handle nested/repeated patterns
        let previousLine = '';
        let maxIterations = 10; // Prevent infinite loops
        let iteration = 0;
        
        while (processedLine !== previousLine && iteration < maxIterations) {
            previousLine = processedLine;
            
            // Replace [[" with ["
            processedLine = processedLine.replace(/\[\["/g, '["');
            
            // Replace ["] with "] (but be careful not to break valid patterns)
            // Only replace if it's truly excessive (e.g., ends improperly)
            processedLine = processedLine.replace(/\["\]/g, '"]');
            
            // Fix pattern like `text["` at end of line -> `text"]`
            processedLine = processedLine.replace(/\["$/g, '"]');
            
            // Fix pattern like `text[";` -> `text"];`
            processedLine = processedLine.replace(/\[";/g, '"];');
            
            // Fix pattern like [[[ or ]]] (excessive brackets without quotes)
            processedLine = processedLine.replace(/\[\[\[/g, '[');
            processedLine = processedLine.replace(/\]\]\]/g, ']');

            // NEW: Fix end of line ]] or ]];
            processedLine = processedLine.replace(/\]\](;?)\s*$/g, ']$1');
            
            iteration++;
        }

        return processedLine;
    });
    return lines.join('\n');
}

/**
 * Fixes intermediate nodes defined inside an edge.
 * Pattern: `A -- B[...] --> C`
 * Result:
 * A --> B[...]
 * B[...] --> C
 */
export function fixIntermediateNodes(content: string): string {
    const lines = content.split('\n');
    const resultLines: string[] = [];

    for (const line of lines) {
        // Regex to detect: NodeA ... -- NodeB[...] ... --> NodeC
        // We look for ` -- ` followed by `NodeID[...]` followed by ` --> `
        // Be careful with greedy matches.
        // We assume the intermediate node has brackets [ ... ]
        
        // Group 1: Start (NodeA)
        // Group 2: Intermediate Node (NodeB[...])
        // Group 3: End (NodeC)
        const match = line.match(/^(.*?)\s*--\s*([a-zA-Z0-9_]+\s*\[.*?\])\s*-->\s*(.*)$/);
        
        if (match) {
            const start = match[1].trim();
            const middle = match[2].trim();
            const end = match[3].trim();
            
            // Extract the NodeID from middle to use in the second line
            const middleIdMatch = middle.match(/^([a-zA-Z0-9_]+)/);
            const middleId = middleIdMatch ? middleIdMatch[1] : middle; // Fallback to full middle if parse fails (unlikely)

            // Line 1: A --> B[...] 
            // Note: Use --> for the first connection as well, or preserve --?
            // The user example converted `Reactants -- Barrier1 -->` to `Reactants --> Barrier1`.
            resultLines.push(`${start} --> ${middle}`);
            
            // Line 2: B[...] --> C
            // User example: Barrier1["..."] --> Products
            // Actually user example uses the full definition `Barrier1["..."]` in the second line too.
            // "Barrier1["Activation Energy Ea1"] --> Products[...]"
            // This is valid Mermaid (re-defining node is fine).
            resultLines.push(`${middle} --> ${end}`);
        } else {
            resultLines.push(line);
        }
    }
    return resultLines.join('\n');
}

/**
 * Fixes doubled IDs causing malformed definitions.
 * Pattern: `Arrow SplitSplit Sample` -> `Arrow Split[Split Sample]`
 */
export function fixDoubledID(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Look for pattern: (Arrow) (Word)(SameWord) (Space) (Rest)
        // \1 backreference to match repeated word
        // We only target lines with arrows to avoid false positives in text
        if (!line.includes('-->') && !line.includes('---') && !line.includes('--')) {
            return line;
        }

        return line.replace(/(\s*(?:---|-->|--)\s*)([A-Z][a-z]+)\2(\s+)(.*)$/, (match, arrow, word, space, rest) => {
            // arrow: " --> "
            // word: "Split"
            // space: " "
            // rest: "Sample for..."
            
            // Result: " --> Split[Split Sample for...]"
            // We append the word back to the start of the label
            return `${arrow}${word}[${word}${space}${rest}]`;
        });
    });
    return processedLines.join('\n');
}

/**
 * Fixes unquoted node labels containing characters that might cause rendering issues.
 * Heuristic: Quote labels containing ", ', =, *, ±, -
 * Example: Plot[Plot "A"] -> Plot["Plot "A""]
 * Handles trailing semicolons by moving them outside the quotes.
 */
export function fixUnquotedNodeLabels(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Match NodeID[Content] where Content is not fully quoted
        // Exclude content that starts with " (heuristic for already quoted)
        // We use a safe regex that doesn't cross brackets to avoid breaking nested structures
        return line.replace(/([a-zA-Z0-9_]+)\s*\[(?!")([^\[\]]+)\]/g, (match, nodeId, innerContent) => {
             // Check for triggers: quotes, equals, asterisk, plus-minus, minus
             // These are characters that often require quoting in Mermaid labels
             if (/["'=*±\/-]/.test(innerContent)) {
                 // Check if innerContent ends with semicolon
                 let contentToQuote = innerContent;
                 let suffix = '';
                 // Trim trailing whitespace first to check for semicolon
                 const trimmedContent = contentToQuote.trim();
                 if (trimmedContent.endsWith(';')) {
                     // Remove semicolon from content
                     contentToQuote = trimmedContent.slice(0, -1);
                     suffix = ';';
                 }
                 
                 return `${nodeId}["${contentToQuote}"]${suffix}`;
             }
             return match;
        });
    });
    return processedLines.join('\n');
}

/**
 * Fixes Mermaid comments that break syntax by merging them into the label.
 * Example: `A -- Label --> B; % Comment` -> `A -- "Label(Comment)" --> B;`
 */
export function fixMermaidComments(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Simple check for potential Mermaid comment
        if (!line.includes('%') || !line.includes('-->')) {
            return line;
        }

        // We only care about lines that look like: ... -- ... --> ... % ...
        // Split by '%' first to safely isolate the comment, ensuring % isn't inside a quoted label.
        
        const parts = line.split('%');
        
        let codePart = parts[0];
        let commentPart = '';
        let foundComment = false;
        
        // Re-assemble parts if the % was inside a quote.
        for (let i = 1; i < parts.length; i++) {
             const potentialCode = parts.slice(0, i).join('%');
             const quoteCount = (potentialCode.match(/"/g) || []).length;
             if (quoteCount % 2 === 0) {
                 // Even quotes means we are outside a string, so this % starts a comment
                 codePart = potentialCode;
                 commentPart = parts.slice(i).join('%');
                 foundComment = true;
                 break;
             }
        }
        
        if (!foundComment) return line; // No valid comment found or % was inside quotes
        
        // Clean up parts
        let cleanCode = codePart.trim();
        const cleanComment = commentPart.trim();
        
        if (!cleanComment) return line; // Empty comment, keep as is
        
        // Check for trailing semicolon in code
        let hasSemi = false;
        if (cleanCode.endsWith(';')) {
            cleanCode = cleanCode.slice(0, -1).trim();
            hasSemi = true;
        }
        
        // Parse the arrow relation in cleanCode
        // We support: A -- Label --> B
        // Regex: (Start) (-- ) (Label) ( --> ) (End)
        const arrowLabelRegex = /^(.*?)(--\s*)(.*?)(\s*-->\s*)(.*?)$/;
        const match = cleanCode.match(arrowLabelRegex);
        
        if (match) {
            const pre = match[1];
            const arrowStart = match[2];
            let label = match[3];
            const arrowEnd = match[4];
            const post = match[5];
            
            // If label is quoted, strip quotes
            if (label.startsWith('"') && label.endsWith('"')) {
                label = label.slice(1, -1);
            }
            
            // Append comment
            const newLabel = `${label}(${cleanComment})`;
            
            // Reconstruct
            return `${pre}${arrowStart}"${newLabel}"${arrowEnd}${post}${hasSemi ? ';' : ''}`;
        }
        
        return line;
    });
    
    return processedLines.join('\n');
}

/**
 * Fixes inline subgraphs used as edge labels.
 * Pattern: `NodeA --> NodeB; subgraph "Label" end;`
 * Result: `NodeA -- "Label" --> NodeB;`
 */
export function fixInlineSubgraphs(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Regex to detect: Node ... Arrow ... Node; subgraph "Label" end;
        // Captures:
        // 1. Source (lazy)
        // 2. Arrow (--> or ---)
        // 3. Target (lazy)
        // 4. Label (inside quotes)
        
        const regex = /^(.*?)\s*(---|-->)\s*(.*?);\s*subgraph\s+"(.*?)"\s*end;?\s*$/;
        const match = line.match(regex);
        
        if (match) {
            const source = match[1].trim();
            const arrow = match[2].trim(); // '-->' or '---'
            const target = match[3].trim();
            const label = match[4].trim();
            
            // Construct new line: source -- "label" --> target;
            // We use the arrow type to determine the connector.
            // --> becomes -- "label" -->
            // --- becomes -- "label" ---
            
            let newArrow = arrow;
            if (arrow === '-->') {
                newArrow = ` -- "${label}" --> `;
            } else if (arrow === '---') {
                newArrow = ` -- "${label}" --- `;
            } else {
                 // Fallback if regex matched something else (unlikely given regex)
                 newArrow = ` -- "${label}" ${arrow} `;
            }
            
            return `${source}${newArrow}${target};`;
        }
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Merges double labels on a single edge.
 * Pattern: `-- "Label1" -->|"Label2"|`
 * Result: `-- "Label1<br>(Label2)" -->`
 * This relies on fixMermaidPipes having already standardized the pipe label to `|"..."|`.
 */
export function mergeDoubleLabels(content: string): string {
    // Regex to capture:
    // -- "Label1" --> |"Label2"|
    // We allow whitespace flexibility.
    
    return content.replace(/--\s*"([^"]*)"\s*-->\s*\|"([^"]*)"\|/g, (match, label1, label2) => {
        return `-- "${label1}<br>(${label2})" -->`;
    });
}

/**
 * Fixes Mermaid edge labels involving pipes `|`.
 * Ensures that labels are properly quoted and delimited.
 * 1. `-->|Text|` -> `-->|"Text"|`
 * 2. `-- Text |` -> `--|"Text"|`
 * 3. Handles complex cases like `-->|Fourier Transform|^2|` -> `|"Fourier Transform|^2"|` (quoting the content)
 */
export function fixMermaidPipes(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Skip lines without pipes or arrows
        if (!line.includes('|') || (!line.includes('-->') && !line.includes('--'))) {
            return line;
        }

        // 1. Protect Bracketed Content [...]
        const placeholders: string[] = [];
        let protectedLine = '';
        let depth = 0;
        let currentBlock = '';
        
        for (let i = 0; i < line.length; i++) {
            const char = line[i];
            if (char === '[') {
                if (depth === 0) protectedLine += '___BRACKET_BLOCK_' + placeholders.length + '___';
                depth++;
                currentBlock += char;
            } else if (char === ']') {
                depth--;
                currentBlock += char;
                if (depth === 0) {
                    placeholders.push(currentBlock);
                    currentBlock = '';
                }
            } else {
                if (depth > 0) currentBlock += char;
                else protectedLine += char;
            }
        }
        if (depth > 0) protectedLine += currentBlock;

        // 2. Fix Pipes in Protected Line
        // Regex: (Arrow)(Space)(Content Ending in Pipe)(Space)(NodeStart)
        // Content must NOT contain Arrow markers to prevent over-greediness.
        // NodeStart includes brackets, parens, quotes, or word chars.
        
        const arrowRegex = /((?:---|-->|--))(\s*)((?:(?!(?:---|-->|--)).)*\|)(\s*)(?=[a-zA-Z0-9_\[\(\{\"])/g;
        
        protectedLine = protectedLine.replace(arrowRegex, (match, arrow, space1, labelCandidate, space2) => {
            // labelCandidate is the text between arrow and Node, ending with `|`.
            
            let content = labelCandidate.trim();
            
            // Logic:
            // If it matches `|...|` (standard), extract inner.
            // If it matches `...|` (separator), extract all.
            // If it matches `|...|...|`, extract inner from first/last pipe?
            
            let inner = content;
            
            if (content.startsWith('|') && content.endsWith('|') && content.length > 1) {
                // Remove outer pipes
                inner = content.substring(1, content.length - 1);
            } else if (content.endsWith('|')) {
                // Remove trailing pipe
                inner = content.substring(0, content.length - 1).trim();
            }
            
            // Check if already quoted
            if (inner.startsWith('"') && inner.endsWith('"')) {
                return match;
            }
            
            // Quote it and wrap in pipes
            return `${arrow}${space1}|"${inner}"|${space2}`;
        });

        // 3. Restore Bracketed Content
        placeholders.forEach((block, index) => {
            const placeholder = '___BRACKET_BLOCK_' + index + '___';
            protectedLine = protectedLine.split(placeholder).join(block);
        });

        return protectedLine;
    });

    return processedLines.join('\n');
}


/**
 * Fixes malformed arrow labels where the arrow syntax is absorbed into quotes.
 * Rule: Replace ` -->"` with `" -->` and `"-- ` with `--" `, unless inside `[...]`.
 * Example: `AbInitio -- "Provides Parameters For -->" MM` -> `AbInitio -- "Provides Parameters For" --> MM`
 */
export function fixMalformedArrows(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Simple check to avoid processing lines without arrow-like patterns
        if (!line.includes('--') && !line.includes('-->')) {
            return line;
        }

        // 1. Protect Bracketed Content [...]
        // We use a placeholder to hide content inside top-level brackets
        const placeholders: string[] = [];
        let protectedLine = '';
        let depth = 0;
        let currentBlock = '';
        
        for (let i = 0; i < line.length; i++) {
            const char = line[i];
            
            if (char === '[') {
                if (depth === 0) {
                    protectedLine += '___BRACKET_BLOCK_' + placeholders.length + '___';
                }
                depth++;
                currentBlock += char;
            } else if (char === ']') {
                depth--;
                currentBlock += char;
                if (depth === 0) {
                    placeholders.push(currentBlock);
                    currentBlock = '';
                }
            } else {
                if (depth > 0) {
                    currentBlock += char;
                } else {
                    protectedLine += char;
                }
            }
        }
        // Handle unclosed brackets (append remaining)
        if (depth > 0) {
            protectedLine += currentBlock;
        }

        // 2. Perform Replacements on Protected Line
        // Fix A: ` -->"` -> `" -->`
        // We look for the pattern and replace it. 
        // Note: The user said "instances of ` -->"` ".
        // We assume this means literally space-dash-dash-gt-quote.
        protectedLine = protectedLine.replace(/ -->"/g, '" -->');

        // Fix B: `"-- ` -> `--" `
        // Quote-dash-dash-space
        protectedLine = protectedLine.replace(/"-- /g, '--" ');

        // 3. Restore Bracketed Content
        placeholders.forEach((block, index) => {
            const placeholder = '___BRACKET_BLOCK_' + index + '___';
            protectedLine = protectedLine.split(placeholder).join(block);
        });

        return protectedLine;
    });

    return processedLines.join('\n');
}

/**
 * Internal function to fix missing brackets in Mermaid nodes.
 * Example: `... --> SpreadCalc价差计算 Spread Calculation;` -> `... --> SpreadCalc[价差计算 Spread Calculation];`
 */
export function fixMissingBrackets(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Skip if not in a mermaid block context or no arrows
        if (!line.includes('-->') && !line.includes('---') && !line.includes('--')) {
            return line;
        }

        // Regex to find:
        // 1. Arrow (standard or labeled). We use a flexible match for labeled arrows: -- ... -->
        // 2. ASCII NodeID ([a-zA-Z0-9_]+)
        // 3. Content that is NOT empty, DOES NOT START with [, and ends at ;
        // We use non-greedy match .*? to capture content until ;
        
        const regex = /((?:---|-->|--.*?-->)\s*)([a-zA-Z0-9_]+\b)\s*([^\[\n].*?)(;)/g;
        
        if (regex.test(line)) {
             return line.replace(regex, '$1$2[$3]$4');
        }
        
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Converts "note right of Node: Text" lines into edge labels on the nearest preceding connection.
 * Requirements:
 * - Detect `note right of words: ...`
 * - Relocate sentence to nearest `words -->` block (Source) or `--> words` block (Target).
 * - Replace `-->` with `-- "Sentences" -->`.
 * - Remove the original note line.
 */
export function fixMermaidNotes(content: string): string {
    const lines = content.split('\n');
    const notesToProcess: { lineIndex: number; nodeId: string; text: string; }[] = [];

    // 1. Identify all notes
    // Regex allows "note right/left/top/bottom of Node: Text"
    const noteRegex = /^\s*note\s+(right|left|top|bottom)\s+of\s+([a-zA-Z0-9_]+)\s*:\s*(.*)$/i;

    lines.forEach((line, index) => {
        const match = line.match(noteRegex);
        if (match) {
            notesToProcess.push({
                lineIndex: index,
                nodeId: match[2],
                text: match[3].trim()
            });
        }
    });

    if (notesToProcess.length === 0) return content;

    const linesToDelete = new Set<number>();
    
    // Process notes
    for (const note of notesToProcess) {
        const { lineIndex, nodeId, text } = note;
        let found = false;

        // Search backwards from the note's position
        for (let j = lineIndex - 1; j >= 0; j--) {
            if (linesToDelete.has(j)) continue;

            const line = lines[j];
            
            // Check for Node as SOURCE (Outgoing)
            // Regex: Start or space(s) + NodeID + word boundary + optional brackets + space + (---|-->)
            const sourceRegex = new RegExp(`(?:^|\\s+)${nodeId}\\b(?:\\[.*?\\])?\\s*(---|-->)`);
            
            // Check for Node as TARGET (Incoming)
            // Regex: (---|-->) + space + NodeID + word boundary + optional brackets + (semicolon, end, or space)
            const targetRegex = new RegExp(`(---|-->)\\s*${nodeId}\\b(?:\\[.*?\\])?(?:;|$|\\s)`);

            // Apply replacement
            // Priority: Source (Outgoing) first, then Target (Incoming)
            
            if (sourceRegex.test(line)) {
                const escapedText = text.replace(/"/g, '\\"');
                lines[j] = line.replace(sourceRegex, (match) => {
                    return match.replace(/\s*(---|-->)$/, (fullMatch, arrow) => ` -- "${escapedText}" ${arrow}`);
                });
                found = true;
            } else if (targetRegex.test(line)) {
                const escapedText = text.replace(/"/g, '\\"');
                lines[j] = line.replace(targetRegex, (match) => {
                     return match.replace(/^(---|-->)/, (arrow) => `-- "${escapedText}" ${arrow}`);
                });
                found = true;
            }

            if (found) {
                linesToDelete.add(lineIndex);
                break; // Stop searching for this note
            }
        }
    }

    // Return joined lines, filtering out deleted ones
    return lines.filter((_, index) => !linesToDelete.has(index)).join('\n');
}

/**
 * Fixes semicolon positioning in Mermaid node labels.
 * Ensures that closing brackets `"]` appear before semicolons `;`.
 * Example: `Node["Label"];` is correct, but `Node["Label];` should become `Node["Label"];`
 * Also handles: `text];` -> `text"];` when text should be quoted
 */
export function fixSemicolonPositioning(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Skip lines without semicolons or arrows
        if (!line.includes(';') || (!line.includes('-->') && !line.includes('--'))) {
            return line;
        }

        // Pattern 1: Fix `"];` that might be incorrectly positioned
        // Look for patterns where ] comes after ; when it should be before
        // Pattern: `"...];` should be `"..."];`
        let processedLine = line.replace(/("\s*)\];/g, '"];');

        // Pattern 2: Ensure quoted labels ending with semicolon have proper bracket placement
        // `["text;` -> `["text"];`
        processedLine = processedLine.replace(/\["([^"\]]*);/g, '["$1"];');

        // Pattern 3: Handle unquoted text after arrow ending with semicolon
        // This catches patterns like: `--> NodeIDText Text;` and converts to `--> NodeID["Text Text"];`
        // We need to be careful to identify where the NodeID ends and label begins
        
        return processedLine;
    });
    return processedLines.join('\n');
}

/**
 * Fixes unquoted node labels that end with semicolons.
 * Converts patterns like: `NodeID Text Content;` to `NodeID["Text Content"];`
 * Example: `Evaluate1E: Evaluate $f$;` -> `Evaluate1["E: Evaluate $f$"];`
 */
export function fixUnquotedLabelsWithSemicolons(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Skip lines without semicolons or arrows
        if (!line.includes(';') || (!line.includes('-->') && !line.includes('--'))) {
            return line;
        }

        // Pattern: Arrow followed by NodeID followed by unquoted text ending with semicolon
        // Regex: (Arrow) (Space) (NodeID) (Unquoted Text Content) (Semicolon)
        // We look for: `--> NodeIDText Text...;` where there's no opening bracket after NodeID
        
        // Match pattern: `(-->) (NodeID)(Content without brackets)(;)`
        const regex = /((?:--|---)->)\s*([a-zA-Z0-9_]+)([^[\n;]+);/g;
        
        return line.replace(regex, (match, arrow, nodeId, content) => {
            // Check if content starts with a bracket (already has label)
            if (content.trim().startsWith('[')) {
                return match;
            }
            
            // Extract the label from content
            // Often NodeID is partially in the content (e.g., "E: Text" where NodeID was "Evaluate1E")
            const trimmedContent = content.trim();
            
            // If content is empty or very short, skip
            if (!trimmedContent || trimmedContent.length < 2) {
                return match;
            }
            
            // Build new syntax: arrow NodeID["Content"];
            return `${arrow} ${nodeId}["${trimmedContent}"];`;
        });
    });
    return processedLines.join('\n');
}

/**
 * Enhanced note pattern and semicolon content removal.
 * 1. Replaces `note "Sentences"` with `Note1[/"Sentences"/]`
 * 2. Removes content after `;` if line contains `%` after the semicolon
 * 3. Specifically handles `-.- Words["Sentences"]; % notes` pattern
 */
export function enhancedNoteAndSemicolonCleanup(content: string): string {
    let processed = content;
    
    // 1. Replace note "Sentences" with Note1[/"Sentences"/]
    // This pattern catches standalone note statements (not "note right of")
    // Use a counter to avoid aliasing multiple notes to Note1
    let noteCounter = 1;
    processed = processed.replace(/\bnote\s+"([^"]*)"/gi, (match: string, noteContent: string) => {
        return `Note${noteCounter++}[/"${noteContent}"/]`;
    });
    
    // 2. Remove content after ; if the line contains % after ;
    // Pattern: `;...%...` on any line
    // We want to keep everything before `;`, the `;` itself, but remove everything after if `%` appears
    processed = processed.replace(/;([^;\n]*%[^\n]*)/g, ';');
    
    // 3. Specific pattern: Lines with `-.-` (dotted lines) containing `["..."];` followed by `% comment`
    // Example: `A -.- B["Text"]; % comment` -> `A -.- B["Text"];`
    // This is already handled by rule 2 above
    
    return processed;
}

/**
 * Fixes smart (curly) quotes in Mermaid labels.
 * Converts “” ‘’ to "" ''
 * Specifically fixes Note["/“Sentences”/"] -> Note["/Sentences/"]
 * Also handles general cases of excessive closing brackets if needed.
 */
export function fixSmartQuotes(content: string): string {
    let processed = content
        .replace(/[\u201C\u201D]/g, '"') // Curly double quotes to straight
        .replace(/[\u2018\u2019]/g, "'"); // Curly single quotes to straight

    // Fix slashed note pattern: Note["/“Sentences”/"] -> Note["/Sentences/"]
    // Handle with spaces or without
    processed = processed.replace(/Note\s*\["\s*\/\s*(["\u201C][^"\u201D]*["\u201D])\s*\/\s*"\]/g, (match, innerQuotes) => {
        const innerText = innerQuotes.replace(/[\u201C\u201D]/g, '"').replace(/^["']|["']$/g, '');
        return `Note["/${innerText}/"]`;
    });
    processed = processed.replace(/Note\s*\["\/([^"]+)\"\/"\]/g, (match, text) => `Note["/${text.trim()}/"]`);

    // General for any node: [" / “text” / "] -> [" / text / "]
    processed = processed.replace(/\["\s*\/\s*(["\u201C][^"\u201D]*["\u201D])\s*\/\s*"\]/g, (match, innerQuotes) => {
        const innerText = innerQuotes.replace(/[\u201C\u201D]/g, '"').replace(/^["']|["']$/g, '');
        return `["/${innerText}/"]`;
    });
    processed = processed.replace(/\["\/([^"]+)\"\/"\]/g, (match, text) => `["/${text.trim()}/"]`);

    return processed;
}

/**
 * Fixes reverse arrows `A <-- B` to `B --> A`.
 * Supports optional brackets/quotes on nodes.
 * Example: `ExSitu["Ex-situ..."] <-- Sample;` -> `Sample --> ExSitu["Ex-situ..."];`
 */
export function fixReverseArrows(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        if (!line.includes('<--')) return line;

        // Regex to capture:
        // Group 1: Left Node (lazy)
        // Group 2: <-- (literal)
        // Group 3: Right Node (lazy)
        // Group 4: Optional Semicolon
        const regex = /^(.*?)\s*<--\s*(.*?)(;?)\s*$/;
        const match = line.match(regex);

        if (match) {
            const leftNode = match[1].trim();
            const rightNode = match[2].trim();
            const semicolon = match[3] || '';
            
            return `${rightNode} --> ${leftNode}${semicolon}`;
        }
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Fixes `Direction` keyword case in subgraphs.
 * Mermaid is case-sensitive inside subgraphs: `Direction TB` -> `direction TB`.
 */
export function fixSubgraphDirection(content: string): string {
    const lines = content.split('\n');
    let insideSubgraph = false;
    const processedLines = lines.map(line => {
        if (line.trim().startsWith('subgraph')) {
            insideSubgraph = true;
        } else if (line.trim() === 'end') {
            insideSubgraph = false;
        }

        if (insideSubgraph) {
            // Replace `Direction` with `direction` if followed by TB, BT, LR, RL, TD
            return line.replace(/^\s*Direction\s+(TB|BT|LR|RL|TD)\b/g, (match) => {
                return match.replace('Direction', 'direction');
            });
        }
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Fixes comments designated by `//` on arrow lines, converting them to edge labels.
 * Example: `Thermal --> Optical; // Thermo-optic effect` 
 * Become: `Thermal -- "Thermo-optic effect" --> Optical;`
 */
export function fixDoubleSlashComments(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        if (!line.includes('//') || !line.includes('-->')) return line;

        // Regex to find arrow relation followed by // comment
        // Handle optional semicolon before //
        // Group 1: Pre-arrow part
        // Group 2: Arrow (-->)
        // Group 3: Post-arrow part (target node)
        // Group 4: Semicolon (optional)
        // Group 5: Comment text
        
        // This regex assumes standard `-->` arrow. 
        // We match `//` specifically.
        
        const regex = /^(.*?)(\s*-->\s*)(.*?)(;?)\s*\/\/\s*(.*)$/;
        const match = line.match(regex);
        
        if (match) {
            const preArrow = match[1]; // "Thermal"
            const arrow = match[2]; // " --> "
            const target = match[3].trim(); // "Optical"
            const semicolon = match[4]; // ";"
            const comment = match[5].trim(); // "Thermo-optic effect"
            
            if (comment) {
                // Construct: Pre -- "Comment" --> Target;
                // Note: arrow variable contains " --> ". We change it to " -- "Comment" --> "
                const newArrow = ` -- "${comment}" --> `;
                return `${preArrow}${newArrow}${target}${semicolon}`;
            }
        }
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Fixes duplicated bracketed labels.
 * Example: `Node["Label"]["Label"]` -> `Node["Label"]`
 * Retains only the last occurrence if they differ, or just collapses them.
 * The prompt says: "only the final occurrence shall be retained".
 */
export function fixDuplicateLabels(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Regex to match consecutive quoted brackets: ["..."]["..."]...
        // We want to replace the whole sequence with just the last ["..."]
        
        // Improved Regex to handle escaped quotes: \[\"(?:[^"\\]|\\.)*\"\]
        const blockRegexStr = '\\["(?:[^"\\\\]|\\\\.)*"\\]';
        const blockRegex = new RegExp(blockRegexStr, 'g');
        
        // We look for 2 or more occurrences
        const chainRegex = new RegExp(`((?:${blockRegexStr}\\s*){2,})`, 'g');
        
        return line.replace(chainRegex, (match) => {
             // Split match into blocks
             const blocks = match.match(blockRegex);
             if (blocks && blocks.length > 0) {
                 return blocks[blocks.length - 1];
             }
             return match;
        });
    });
    return processedLines.join('\n');
}

/**
 * Fixes lines ending with `;` where the last delimiter is `--` instead of `-->`.
 * Example: `A -- B;` -> `A --> B;`
 */
export function fixDoubleDashToArrow(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Target: ... -- Words...; where Words contains no -- or -->
        if (!line.trim().endsWith(';')) return line;
        
        // Regex to capture:
        // Group 1: Everything before
        // Group 2: Pre-dash whitespace
        // Group 3: Post-dash whitespace
        // Group 4: Content
        
        // We match `--` explicitly using lookbehind/lookahead to avoid ---
        // (?<!-)--(?!>|-)
        
        const regex = /^(.*?)(\s*)(?<!-)--(?!>|-)(\s*)((?:(?!--|-->).)*?);\s*$/;
        
        const match = line.match(regex);
        if (match) {
            const p1 = match[1];
            const s1 = match[2];
            const s2 = match[3];
            const p4 = match[4]; // Content
            
            // The regex lookbehind handles the --- cases now, but we can double check logic
            // strict logic is better
            
            // We reconstruct with -->
            // We preserve s1 and s2 whitespace.
            return `${p1}${s1}-->${s2}${p4};`;
        }
        return line;
    }).join('\n');
    return processedLines;
}

/**
 * Scans the content to identify valid Node IDs.
 * Used to heuristically fix malformed node definitions.
 */
function getValidNodeIDs(content: string): Set<string> {
    const validIDs = new Set<string>();
    
    // Regex patterns to find node IDs
    // We strictly look for definitions (brackets) or usage as SOURCE.
    // We exclude usage as TARGET (--> Node) because that might be the typo we are trying to fix (e.g. --> BSupercapacitor).
    const patterns = [
        /\b([a-zA-Z0-9_]+)\s*\[/g,       // Node[...
        /\b([a-zA-Z0-9_]+)\s*-->/g,      // Node -->
        // /-->\s*([a-zA-Z0-9_]+)\b/g,   // REMOVED: --> Node (Target)
        /\b([a-zA-Z0-9_]+)\s*---/g,      // Node ---
        // /---\s*([a-zA-Z0-9_]+)\b/g,   // REMOVED: --- Node (Target)
        /^\s*([a-zA-Z0-9_]+)\s*-->/gm,   // Start of line Node -->
        /^\s*([a-zA-Z0-9_]+)\s*--\s/gm,  // Start of line Node -- (Labeled arrow start)
        /\b([a-zA-Z0-9_]+)\s*--\s/g,     // Node -- (anywhere)
    ];

    patterns.forEach(regex => {
        let match;
        while ((match = regex.exec(content)) !== null) {
            // Filter out common keywords
            const id = match[1];
            if (!['graph', 'subgraph', 'style', 'class', 'click', 'linkStyle', 'TD', 'LR', 'TB', 'BT', 'RL'].includes(id)) {
                validIDs.add(id);
            }
        }
    });
    
    return validIDs;
}

/**
 * Fixes concatenated node labels where the NodeID is repeated or the label starts with the NodeID,
 * and the label is unquoted.
 * Example: `... --> SubdivideSubdivide into 8 Octants;`
 * If `Subdivide` is a valid ID, converts to `... --> Subdivide["Subdivide into 8 Octants"];`
 */
export function fixConcatenatedLabels(content: string): string {
    const validIDs = getValidNodeIDs(content);
    // console.log('Valid IDs:', Array.from(validIDs));
    
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Skip lines that don't look like they have arrows and unquoted text
        // Relaxed check for semicolon or arrow
        if ((!line.includes('-->') && !line.includes('---'))) {
            return line;
        }
        
        // Regex:
        // Group 1: Arrow prefix (e.g. `-->` or `--> |Label| `)
        // Group 2: The Unquoted Text (NodeID + Label)
        // Match up to ; or end of line
        const regex = /((?:---|-->)(?:\s*\|[^|]+\|)?\s*)([^"\[\];\n]+)(?:;|$)/;
        
        const match = line.match(regex);
        if (match) {
            const arrowPrefix = match[1];
            const text = match[2].trim();
            // console.log('Checking text:', text);
            
            // Check if text starts with a valid ID
            // We iterate over validIDs to find a match at the start
            // Prefer longest match?
            let bestId = '';
            
            for (const id of validIDs) {
                if (text.startsWith(id)) {
                    if (id.length > bestId.length) {
                        bestId = id;
                    }
                }
            }
            
            if (bestId) {
                // Determine label.
                // If text is exactly the ID, we might not want to do anything?
                // Example `A --> B;`. Text "B". ID "B".
                // We leave it as is.
                if (text === bestId) {
                    return line;
                }
                
                // If text is longer, we assume it's `ID` + `Label` (concatenated or just unquoted)
                // Example `SubdivideSubdivide...` ID `Subdivide`.
                // Example `BLabel Text`. ID `B`.
                
                // Construct replacement: Arrow ID["Text"]
                // But wait, the `text` variable contains the FULL text including the ID prefix.
                // In `SubdivideSubdivide...`, the full text IS the label we want?
                // User example: `SubdivideSubdivide into...` -> `Subdivide["Subdivide into..."]`
                // Wait, if the text is `SubdivideSubdivide into...`
                // And we output `Subdivide["Subdivide into..."]`.
                // The label inside quotes starts with `Subdivide`.
                // So we assume the *entire* text is the label?
                // Or do we strip the ID?
                // `SubdivideSubdivide...`. ID `Subdivide`. Remainder `Subdivide...`.
                // If we treat remainder as label: `Subdivide["Subdivide..."]`.
                // If we treat whole text as label: `Subdivide["SubdivideSubdivide..."]`.
                // The user example output is `Subdivide["Subdivide into 8 Octants"]`.
                // Broken input: `SubdivideSubdivide into 8 Octants`.
                // It seems the "broken" text is basically `ID` + `Label`.
                // And the User wants `ID` + `["Label"]`.
                // So we need to remove the FIRST instance of ID from the text.
                // `Subdivide` (ID) + `Subdivide into...` (Label).
                // `text` starts with `bestId`.
                // Label = text.substring(bestId.length).
                
                let label = text.substring(bestId.length).trim();
                
                // Special check for `SubdivideSubdivide` pattern where label matches ID?
                // Actually if `label` itself starts with `bestId`?
                // In `SubdivideSubdivide...`, label is `Subdivide into...`.
                // It starts with `Subdivide`.
                // This seems consistent.
                
                // What if `BLabel Text`. ID `B`. Label `Label Text`.
                // Result `B["Label Text"]`.
                
                // If label is empty (e.g. `A --> A;`), we already skipped it.
                if (!label) return line;

                // FIX: Check if label looks like valid Mermaid syntax (e.g. starts with --- or --> or -- )
                // This happens when we match `C1 --- C2` and capture `C1 --- C2` as text.
                // bestId is C1. Label is `--- C2`.
                if (label.startsWith('---') || label.startsWith('-->') || label.startsWith('-- ')) {
                    return line;
                }

                // Determine if we need to append a semicolon
                // If the original line had a semicolon at the end of the match, or generally ended with it.
                // The regex `(?:;|$)` consumed the semicolon if present.
                // To be safe, we append `;` if the line ends with `;` or if the match consumed it.
                // But `match[0]` includes the consumed part?
                // `match[0]` is the whole match.
                const hadSemi = match[0].trim().endsWith(';');
                const suffix = hadSemi ? ';' : '';
                
                return line.replace(match[0], `${arrowPrefix}${bestId}["${label}"]${suffix}`);
            }
        }
        
        return line;
    });
    
    return processedLines.join('\n');
}

/**
 * Fixes misplaced edge labels that appear at the start of the line with a leading `>`.
 * Pattern: `>|"Label"| Source --> Target` or `> | "Label" | Source --> Target`
 * Result: `Source -->|"Label"| Target`
 * Now supports escaped quotes inside the label and flexible whitespace.
 */
export function fixMisplacedPipes(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.map(line => {
        // Regex to capture:
        // > | "Label" | Source Arrow Target
        // We handle --> and ---
        // Label matches: "((?:[^"\\]|\\.)*)" -> non-greedy quoted string with escapes
        const regex = /^\s*>\s*\|\s*"((?:[^"\\]|\\.)*)"\s*\|\s*(.*?)\s*(-->|---)\s*(.*)$/;
        const match = line.match(regex);
        
        if (match) {
            const label = match[1];
            const source = match[2].trim();
            const arrow = match[3]; // "-->" or "---"
            const target = match[4].trim();
            
            // Construct: Source Arrow|"Label"| Target
            return `${source} ${arrow}|"${label}"| ${target}`;
        }
        return line;
    });
    return processedLines.join('\n');
}

/**
 * Fixes targeted note format: `note NodeId "Content"`
 * Converts to:
 * NoteNodeId["Content"]
 * NodeId -.- NoteNodeId
 * Also removes `[""]` artifacts from the content.
 */
export function fixTargetedNotes(content: string): string {
    const lines = content.split('\n');
    const processedLines = lines.flatMap(line => {
        // Regex: note (NodeID) "(Content)"
        // Use greedy match (.*) to handle potential unescaped quotes inside, assuming line ends with quote.
        const regex = /^\s*note\s+([a-zA-Z0-9_]+)\s+"(.*)"\s*$/;
        
        const match = line.match(regex);
        if (match) {
            const nodeId = match[1];
            let content = match[2];
            
            // Clean content: remove [""] if present
            content = content.replace(/\[""\]/g, '');
            // Handle potentially escaped versions if they exist
            content = content.replace(/\[\\""\\""\]/g, '');
            content = content.replace(/\[\\"\\"\]/g, '');

            const noteId = `Note${nodeId}`;
            
            // Return two lines
            return [
                `${noteId}["${content}"]`,
                `${nodeId} -.- ${noteId}`
            ];
        }
        return [line];
    });
    return processedLines.join('\n');
}
