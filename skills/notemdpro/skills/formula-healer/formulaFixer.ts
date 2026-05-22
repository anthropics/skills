import { App, TFile, TFolder } from 'obsidian';
import { ProgressReporter } from './types';
import { delay } from './utils';

/**
 * Fixes single-line math formulas delimited by single '$' to double '$$'
 * Matches: ^(\s*)\$(\s*)$
 * Replaces with: $1$$$$$2
 * 
 * @param content The markdown content to process
 * @returns The content with fixed formulas
 */
export function fixFormulaFormats(content: string): string {
    // (?m) is handled by 'm' flag in JS regex
    // ^      Start of line
    // (\s*)  Group 1: Leading whitespace
    // \$     Literal $
    // (\s*)  Group 2: Trailing whitespace
    // $      End of line
    const pattern = /^(\s*)\$(\s*)$/gm;
    return content.replace(pattern, '$1$$$$$2');
}

/**
 * Fixes formula formats in a single file.
 * Reads the file, applies fixFormulaFormats, and writes back if changed.
 */
export async function fixFormulaFormatsInFile(app: App, file: TFile, reporter?: ProgressReporter): Promise<boolean> {
    try {
        const content = await app.vault.read(file);
        const newContent = fixFormulaFormats(content);
        
        if (newContent !== content) {
            await app.vault.modify(file, newContent);
            if (reporter) reporter.log(`Fixed formulas in ${file.name}`);
            return true;
        } else {
            // if (reporter) reporter.log(`No formula fixes needed for ${file.name}`);
            return false;
        }
    } catch (error) {
        const msg = `Error processing formulas in ${file.name}: ${error}`;
        if (reporter) reporter.log(msg);
        console.error(msg);
        throw error;
    }
}

/**
 * Batch fixes formula formats in a folder.
 */
export async function batchFixFormulaFormatsInFolder(
    app: App, 
    folderPath: string, 
    reporter: ProgressReporter
): Promise<{ modifiedCount: number; errors: { file: string; message: string }[] }> {
    
    const folder = app.vault.getAbstractFileByPath(folderPath);
    if (!folder || !(folder instanceof TFolder)) {
        throw new Error(`Invalid folder path: ${folderPath}`);
    }

    const files = app.vault.getFiles().filter(f => 
        (f.extension === 'md' || f.extension === 'txt') &&
        (f.path === folderPath || f.path.startsWith(folderPath === '/' ? '' : folderPath + '/'))
    );

    if (files.length === 0) {
        reporter.log(`No eligible files found in ${folderPath}`);
        return { modifiedCount: 0, errors: [] };
    }

    let modifiedCount = 0;
    const errors: { file: string; message: string }[] = [];

    for (let i = 0; i < files.length; i++) {
        const file = files[i];
        if (reporter.cancelled) break;

        const progress = Math.floor((i / files.length) * 100);
        reporter.updateStatus(`Checking formulas in ${file.name}...`, progress);

        try {
            const modified = await fixFormulaFormatsInFile(app, file, reporter);
            if (modified) modifiedCount++;
        } catch (error: any) {
            const message = error.message || String(error);
            errors.push({ file: file.name, message });
            reporter.log(`❌ Error in ${file.name}: ${message}`);
        }
        
        // Small delay to keep UI responsive
        if (i % 10 === 0) await delay(10);
    }

    return { modifiedCount, errors };
}
