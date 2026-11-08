const VALID_DBS = new Set([
  'pubmed', 'protein', 'nucleotide', 'nuccore', 'gene', 'genome',
  'structure', 'pmc', 'taxonomy', 'snp', 'geo', 'sra', 'books',
  'cancerchromosomes', 'cddev', 'gap', 'gds', 'homedb', 'journal',
  'mesh', 'ncbisearch', 'nlmcatalog', 'omim', 'omia', 'popset', 'probe',
  'proteinclusters', 'pcassay', 'pccompound', 'pcsubstance', 'toolkit',
  'unigene', 'unists', 'assembly', 'bioproject', 'biosample', 'blast',
  'clinvar', 'clone', 'dbvar', 'doi', 'ena', 'medgen', 'nbk25497',
  'orgtrack', 'plantgenomes', 'protclustdb', 'trace'
]);

const RETRY_AFTER = 333;

export function validateDb(db) {
  if (!db || typeof db !== 'string') {
    throw new Error('数据库名称不能为空');
  }
  const dbLower = db.toLowerCase().trim();
  if (!VALID_DBS.has(dbLower)) {
    throw new Error(`无效的数据库: ${db}. 有效选项: ${[...VALID_DBS].join(', ')}`);
  }
  return dbLower;
}

export function validateId(ids) {
  if (!ids) {
    throw new Error('ID不能为空');
  }
  const idList = Array.isArray(ids) ? ids : String(ids).split(',');
  const cleaned = idList.map(id => {
    const trimmed = String(id).trim();
    if (!trimmed) {
      throw new Error('ID列表包含空值');
    }
    if (!/^[\d,]+$/.test(trimmed) && !/^[A-Z0-9._]+$/i.test(trimmed)) {
      throw new Error(`无效的ID格式: ${trimmed}`);
    }
    return trimmed;
  });
  return cleaned.join(',');
}

export function validateTerm(term) {
  if (!term || typeof term !== 'string') {
    throw new Error('搜索词不能为空');
  }
  const trimmed = term.trim();
  if (trimmed.length === 0) {
    throw new Error('搜索词不能为空');
  }
  if (trimmed.length > 10000) {
    throw new Error('搜索词过长(最大10000字符)');
  }
  return trimmed;
}

export function validateDateRange(start, end) {
  if (!start && !end) {
    return null;
  }
  const parseDate = (d) => {
    if (!d) return null;
    if (d instanceof Date) return d;
    const parsed = new Date(d);
    if (isNaN(parsed.getTime())) {
      throw new Error(`无效日期格式: ${d}`);
    }
    return parsed;
  };
  const startDate = parseDate(start);
  const endDate = parseDate(end);
  if (startDate && endDate && startDate > endDate) {
    throw new Error('开始日期不能晚于结束日期');
  }
  const formatDate = (d) => d ? d.toISOString().split('T')[0] : '';
  return `${formatDate(startDate)}:${formatDate(endDate)}`;
}

export function validateRetType(rettype, db) {
  const validTypes = {
    default: ['fasta', 'gb', 'xml', 'json', 'text', 'html', 'asn1'],
    protein: ['fasta', 'gb', 'xml', 'json', 'text'],
    nucleotide: ['fasta', 'gb', 'xml', 'json', 'text', 'gbwithparts'],
    gene: ['xml', 'json', 'text', 'fasta', 'summary'],
    pubmed: ['xml', 'json', 'text', 'abstract', 'medline', 'uilist']
  };
  const types = validTypes[db] || validTypes.default;
  if (!types.includes(rettype)) {
    throw new Error(`无效的返回类型: ${rettype}. ${db}的有效选项: ${types.join(', ')}`);
  }
  return rettype;
}

export function validateRetMode(retmode) {
  const validModes = ['json', 'xml', 'text', 'html'];
  if (!validModes.includes(retmode)) {
    throw new Error(`无效的返回模式: ${retmode}. 有效选项: ${validModes.join(', ')}`);
  }
  return retmode;
}

export function validateRetMax(retmax) {
  const num = parseInt(retmax, 10);
  if (isNaN(num) || num < 1) {
    throw new Error('retmax必须为正整数');
  }
  if (num > 100000) {
    throw new Error('retmax不能超过100000');
  }
  return Math.min(num, 10000);
}

export function validateEmail(email) {
  if (!email) return '';
  const trimmed = String(email).trim();
  if (!trimmed) return '';
  const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  if (!emailRegex.test(trimmed)) {
    throw new Error(`无效的邮箱格式: ${email}`);
  }
  return trimmed;
}

export function validateApiKey(key) {
  if (!key) return '';
  const trimmed = String(key).trim();
  if (trimmed.length < 10) {
    throw new Error('API密钥无效');
  }
  return trimmed;
}

export function validateDelay(delay) {
  const num = parseInt(delay, 10);
  if (isNaN(num) || num < 0) {
    throw new Error('延迟必须为非负整数');
  }
  if (num > 10000) {
    throw new Error('延迟不能超过10000ms');
  }
  return Math.max(num, RETRY_AFTER);
}

export function validatePagination(retstart, retmax) {
  const start = parseInt(retstart, 10);
  const max = parseInt(retmax, 10);
  if (isNaN(start) || start < 0) {
    throw new Error('retstart必须为非负整数');
  }
  if (isNaN(max) || max < 1) {
    throw new Error('retmax必须为正整数');
  }
  return { retstart: start, retmax: Math.min(max, 10000) };
}

export function validateSort(sort) {
  const validSorts = ['', 'pub+date', 'pub+date', 'first+author', 'last+author', 'relevance', 'relevance'];
  const normalized = sort.toLowerCase().replace(/ /g, '+');
  if (validSorts.includes(normalized)) {
    return normalized;
  }
  return 'relevance';
}

export const VALIDATORS = {
  validateDb,
  validateId,
  validateTerm,
  validateDateRange,
  validateRetType,
  validateRetMode,
  validateRetMax,
  validateEmail,
  validateApiKey,
  validateDelay,
  validatePagination,
  validateSort
};

export default VALIDATORS;
