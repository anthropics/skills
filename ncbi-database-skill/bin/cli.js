#!/usr/bin/env node

import { parseArgs } from 'node:util';
import { NCBIClient } from '../src/ncbi-client.js';
import { 
  NCBIError, 
  ValidationError, 
  APIError, 
  NetworkError, 
  TimeoutError,
  RateLimitError,
  AuthenticationError,
  parseNcbiError
} from '../src/errors.js';

const client = new NCBIClient();

const COMMANDS = {
  // 搜索命令
  search: {
    aliases: ['s'],
    description: 'Search NCBI databases using E-search',
    examples: [
      'ncbi search gene "BRCA1[gene]"',
      'ncbi search pubmed "cancer[title]" -d 5',
    ]
  },
  
  // 获取记录命令
  fetch: {
    aliases: ['f', 'efetch'],
    description: 'Fetch records using E-fetch',
    examples: [
      'ncbi fetch gene 672',
      'ncbi fetch protein NP_000001 -o json',
    ]
  },
  
  // 摘要命令
  summary: {
    aliases: ['sum', 'esummary'],
    description: 'Get summaries using E-summary',
    examples: [
      'ncbi summary gene 672,675',
      'ncbi summary pubmed 12345678',
    ]
  },
  
  // 链接命令
  link: {
    aliases: ['l', 'elink'],
    description: 'Find linked records using E-link',
    examples: [
      'ncbi link gene 672 pubmed',
      'ncbi link protein NP_000001 gene',
    ]
  },
  
  // 数据库信息命令
  info: {
    aliases: ['i', 'einfo'],
    description: 'Get database information using E-info',
    examples: [
      'ncbi info gene',
      'ncbi info pubmed',
    ]
  },
  
  // 帮助命令
  help: {
    aliases: ['h'],
    description: 'Show this help message'
  },
  
  // 配置命令
  config: {
    aliases: ['cfg'],
    description: 'Configure API key or default options',
    examples: [
      'ncbi config set apikey YOUR_API_KEY',
      'ncbi config show',
    ]
  },

  // 解析组装名称命令
  assembly: {
    aliases: ['asm'],
    description: 'Resolve assembly name to RefSeq accession',
    examples: [
      'ncbi assembly GRCh38',
      'ncbi assembly "GRCh38.p14"',
    ]
  },

  // 基因全景命令
  'gene-panorama': {
    aliases: ['gp'],
    description: 'Get gene info with linked PubMed literature',
    examples: [
      'ncbi gene-panorama BRCA1',
      'ncbi gene-panorama 672',
    ]
  },

  // 变异解释命令
  variant: {
    aliases: ['var'],
    description: 'Query ClinVar/dbsnp for clinical significance',
    examples: [
      'ncbi variant rs123456',
      'ncbi variant "SCV000123456"',
    ]
  },

  // BLAST序列命令
  blast: {
    aliases: [],
    description: 'BLAST sequence search',
    examples: [
      'ncbi blast "ATCG..." -d protein',
      'ncbi blast "MSEQ1" --program megablast',
    ]
  },

  // SRA信息命令
    sra: {
    aliases: [],
    description: 'Get SRA run information and download URLs',
    examples: [
      'ncbi sra SRR123456',
      'ncbi sra PRJNA123456',
    ]
  },
  espell: {
    aliases: [],
    description: 'Check spelling of search terms using NCBI spell checker',
    examples: [
      'ncbi espell "brca1"', 
      'ncbi espell "crispr cas9"'
    ]
  },
  ecitmatch: {
    aliases: [],
    description: 'Match citations to PubMed records',
    examples: [
      'ncbi ecitmatch "Smith J, Nature 2020"',
      'ncbi ecitmatch "PMID:12345678"'
    ]
  }
};

/**
 * 显示帮助信息
 */
function showHelp() {
  console.log(`
🔬 NCBI Database CLI - E-utilities API Tool

使用方法:
  ncbi <command> [options] [arguments]

可用命令:
${Object.entries(COMMANDS).map(([name, cmd]) => {
    const aliases = cmd.aliases?.length > 1 ? ` (${cmd.aliases.slice(1).join(', ')})` : '';
    return `  ${name}${aliases.padEnd(12)} ${cmd.description}`;
  }).join('\n')}

全局选项:
  -d, --delay <ms>      请求间隔毫秒数 (默认: 100ms, 有API key可用10ms)
  -o, --output <format>  输出格式: json, xml, text (默认: json)
  -k, --apikey <key>   NCBI API Key
  -h, --help            显示帮助信息
  -v, --verbose         详细输出模式

示例:
  # 搜索基因
  ncbi search gene "BRCA1[gene]" -d 10

  # 获取基因记录
  ncbi fetch gene 672 -o json

  # 获取 PubMed 文章摘要
  ncbi summary pubmed 12345678

  # 查找基因与PubMed的链接
  ncbi link gene 672 pubmed

  # 查看数据库信息
  ncbi info gene

获取更多信息请访问: https://www.ncbi.nlm.nih.gov/books/NBK25497/
`.trim());
}

/**
 * 解析命令行参数
 */
function parseCommandArgs(args) {
  const options = {
    delay: { type: 'string', default: '100' },
    output: { type: 'string', short: 'o', default: 'json' },
    apikey: { type: 'string', short: 'k', default: '' },
    verbose: { type: 'boolean', short: 'v', default: false },
    help: { type: 'boolean', short: 'h', default: false },
    format: { type: 'string', short: 'f', default: 'json' },
    retmax: { type: 'string', short: 'n', default: '20' },
    retstart: { type: 'string', default: '0' },
    idtype: { type: 'string', default: 'uid' },
    term: { type: 'string', default: '' },
    db: { type: 'string', default: 'gene' },
    ids: { type: 'string', default: '' },
    linkeddb: { type: 'string', default: '' },
    email: { type: 'string', short: 'e', default: '' },
    
    assembly: { type: 'string', default: '' },
    summary: { type: 'boolean', default: false },
    variant: { type: 'string', default: '' },
    database: { type: 'string', short: 'd', default: 'nucleotide' },
    program: { type: 'string', default: 'megablast' },
    expect: { type: 'string', default: '10' },
    sequence: { type: 'string', short: 'q', default: '' },
    sra: { type: 'string', default: '' },
  };

  try {
    const parsed = parseArgs({ args, options, allowPositionals: true });
    return {
      options: parsed.values,
      positionals: parsed.positionals
    };
  } catch (e) {
    console.error(`参数错误: ${e.message}`);
    process.exit(1);
  }
}

/**
 * Execute search command
 */
async function handleSearch(parsed) {
  const { options, positionals } = parsed;
  const db = options.db || positionals[0] || 'gene';
  const term = options.term || positionals.slice(1).join(' ') || '';
  
  if (!term) {
    console.error('Error: Please provide search term');
    console.error('Usage: ncbi search <db> <term>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Searching database: ${db}, term: ${term}`);
    
    const result = await client.esearch({
      db,
      term,
      retmax: parseInt(options.retmax),
      retstart: parseInt(options.retstart),
      apikey: options.apikey,
      delay: parseInt(options.delay)
    });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Search failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

/**
 * 执行获取命令
 */
async function handleFetch(parsed) {
  const { options, positionals } = parsed;
  const db = options.db || positionals[0] || 'gene';
  const ids = options.ids || positionals[1] || '';
  
  if (!ids) {
    console.error('错误: 请提供ID');
    console.error('用法: ncbi fetch <db> <ids>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`获取数据库: ${db}, IDs: ${ids}`);
    
    const result = await client.efetch({
      db,
      ids: ids.split(',').map(id => id.trim()),
      retmode: options.output === 'xml' ? 'xml' : 'json',
      apikey: options.apikey,
      delay: parseInt(options.delay)
    });

    if (options.output === 'json') {
      console.log(JSON.stringify(result, null, 2));
    } else {
      console.log(result);
    }
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Fetch failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

/**
 * 执行摘要命令
 */
async function handleSummary(parsed) {
  const { options, positionals } = parsed;
  const db = options.db || positionals[0] || 'gene';
  const ids = options.ids || positionals[1] || '';
  
  if (!ids) {
    console.error('错误: 请提供ID');
    console.error('用法: ncbi summary <db> <ids>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`摘要数据库: ${db}, IDs: ${ids}`);
    
    const result = await client.esummary({
      db,
      ids: ids.split(',').map(id => id.trim()),
      apikey: options.apikey,
      delay: parseInt(options.delay)
    });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    console.error(`获取摘要失败: ${e.message}`);
    process.exit(1);
  }
}

/**
 * 执行链接命令
 */
async function handleLink(parsed) {
  const { options, positionals } = parseCommandArgs(process.argv.slice(3));
  const sourceDb = options.db || positionals[0] || 'gene';
  const ids = options.ids || positionals[1] || '';
  const linkedDb = options.linkeddb || positionals[2] || '';
  
  if (!ids || !linkedDb) {
    console.error('错误: 请提供源ID和目标数据库');
    console.error('用法: ncbi link <sourceDb> <ids> <targetDb>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`链接: ${sourceDb}:${ids} -> ${linkedDb}`);
    
    const result = await client.elink({
      db: sourceDb,
      ids: ids.split(',').map(id => id.trim()),
      linkeddb: linkedDb,
      apikey: options.apikey,
      delay: parseInt(options.delay)
    });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    console.error(`链接查询失败: ${e.message}`);
    process.exit(1);
  }
}

/**
 * 执行数据库信息命令
 */
async function handleInfo(parsed) {
  const { options, positionals } = parsed;
  const db = options.db || positionals[0] || 'gene';

  try {
    if (options.verbose) console.log(`获取数据库信息: ${db}`);
    
    const result = await client.einfo({
      db,
      apikey: options.apikey
    });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    console.error(`获取信息失败: ${e.message}`);
    process.exit(1);
  }
}

async function handleAssembly(parsed) {
  const { options, positionals } = parsed;
  const assemblyName = options.assembly || positionals[0] || '';

  if (!assemblyName) {
    console.error('Error: Please provide assembly name');
    console.error('Usage: ncbi assembly <name>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Resolving assembly: ${assemblyName}`);
    
    const result = await client.resolveAssembly(assemblyName);

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Assembly lookup failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleGenePanorama(parsed) {
  const { options, positionals } = parsed;
  const geneIdOrSymbol = options.gene || positionals[0] || '';

  if (!geneIdOrSymbol) {
    console.error('Error: Please provide gene ID or symbol');
    console.error('Usage: ncbi gene-panorama <gene_id_or_symbol>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Getting gene panorama: ${geneIdOrSymbol}`);
    
    const result = await client.getGenePanorama(geneIdOrSymbol);

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Gene panorama failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleVariant(parsed) {
  const { options, positionals } = parsed;
  const variantInput = options.variant || positionals[0] || '';

  if (!variantInput) {
    console.error('Error: Please provide variant ID (rs number or SCV accession)');
    console.error('Usage: ncbi variant <variant_id>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Querying variant: ${variantInput}`);
    
    const result = await client.getVariantInfo(variantInput);

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Variant lookup failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleBlast(parsed) {
  const { options, positionals } = parsed;
  const sequence = options.sequence || positionals[0] || '';

  if (!sequence) {
    console.error('Error: Please provide sequence');
    console.error('Usage: ncbi blast <sequence>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Running BLAST search...`);
    
    const result = await client.blastSequence({
      sequence,
      database: options.database || 'nt',
      program: options.program || 'megablast',
      expect: options.expect || '10',
      megablast: options.program === 'megablast'
    });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`BLAST search failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleSRA(parsed) {
  const { options, positionals } = parsed;
  const sraInput = options.sra || positionals[0] || '';

  if (!sraInput) {
    console.error('Error: Please provide SRA ID (SRR, SRP, or PRJNA)');
    console.error('Usage: ncbi sra <sra_id>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Getting SRA info: ${sraInput}`);
    
    const result = await client.getSRAInfo(sraInput);

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`SRA lookup failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleEspell(parsed) {
  const { options, positionals } = parsed;
  const term = options.term || positionals[0] || '';

  if (!term) {
    console.error('Error: Please provide search term to check spelling');
    console.error('Usage: ncbi espell <term>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Checking spelling: ${term}`);
    
    const result = await client.espell({ term, retmode: 'json' });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Spell check failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

async function handleEcitmatch(parsed) {
  const { options, positionals } = parsed;
  const citation = options.term || positionals.join(' ');

  if (!citation) {
    console.error('Error: Please provide citation to match');
    console.error('Usage: ncbi ecitmatch <citation>');
    process.exit(1);
  }

  try {
    if (options.verbose) console.log(`Matching citation: ${citation}`);
    
    const result = await client.ecitmatch({ citations: [citation] });

    console.log(JSON.stringify(result, null, 2));
  } catch (e) {
    const errorInfo = parseNcbiError(e);
    console.error(`Citation matching failed: ${errorInfo.message}`);
    if (errorInfo.suggestion) {
      console.error(`Hint: ${errorInfo.suggestion}`);
    }
    process.exit(1);
  }
}

/**
 * 主函数
 */
async function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0 || args[0] === 'help' || args[0] === '-h' || args[0] === '--help') {
    showHelp();
    return;
  }

  const command = args[0].toLowerCase();
  const commandArgs = args.slice(1);
  
  // 解析参数
  const parsed = parseCommandArgs(commandArgs);
  
  // 设置 API key
  if (parsed.options.apikey) {
    client.setApiKey(parsed.options.apikey);
  }
  
  // 设置请求延迟
  if (parsed.options.delay) {
    client.setDelay(parseInt(parsed.options.delay));
  }

  // 执行命令
  switch (command) {
    case 'search':
    case 's':
      await handleSearch(parsed);
      break;
      
    case 'fetch':
    case 'f':
    case 'efetch':
      await handleFetch(parsed);
      break;
      
    case 'summary':
    case 'sum':
    case 'esummary':
      await handleSummary(parsed);
      break;
      
    case 'link':
    case 'l':
    case 'elink':
      await handleLink(parsed);
      break;
      
    case 'info':
    case 'i':
    case 'einfo':
      await handleInfo(parsed);
      break;
      
    case 'config':
    case 'cfg':
      console.log('配置功能待实现');
      break;
      
    case 'assembly':
    case 'asm':
      await handleAssembly(parsed);
      break;
      
    case 'gene-panorama':
    case 'gp':
      await handleGenePanorama(parsed);
      break;
      
    case 'variant':
    case 'var':
      await handleVariant(parsed);
      break;
      
    case 'blast':
      await handleBlast(parsed);
      break;
      
    case 'sra':
      await handleSRA(parsed);
      break;
    
    case 'espell':
      await handleEspell(parsed);
      break;
    
    case 'ecitmatch':
      await handleEcitmatch(parsed);
      break;
    
    default:
      console.error(`未知命令: ${command}`);
      console.error('运行 "ncbi help" 查看可用命令');
      process.exit(1);
  }
}

main().catch(console.error);
