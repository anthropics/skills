import axios from 'axios';
import { URL } from 'node:url';
import { pipeline } from 'node:stream';
import { finished } from 'node:stream/promises';
import { createWriteStream } from 'node:fs';
import { NCBIError, ValidationError, APIError, NetworkError, TimeoutError } from './errors.js';
import { validateDb, validateId, validateTerm, validateRetMax, validateRetMode, validateEmail, validateDelay } from './validators.js';
import RateLimiter from './rate-limiter.js';

const BASE_URL = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils';
const VALID_DBS = ['pubmed', 'gene', 'protein', 'nucleotide', 'nuccore', 'pep', 'cdd', 'gap', 'gds', 'homologene', 'journals', 'mesh', 'ncbisearch', 'omia', 'omim', 'popset', 'probe', 'proteinclusters', 'pcassay', 'pccompound', 'pcsubstance', 'toolkit', 'unigene', 'unists'];
const VALID_RETMODE = ['json', 'xml', 'text', 'html', 'gb', 'fasta', 'gbwithparts', 'abstract', 'medline', 'docsum', 'uilist', 'ftable', 'asn1', 'rd'];
const DEFAULT_RETMAX = 20;
const MAX_RETMAX = 100000;

class NCBIClient {
  constructor(options = {}) {
    this.apikey = options.apikey || '';
    this.email = options.email || '';
    this.rateLimiter = new RateLimiter({
      requestsPerSecond: this.apikey ? 10 : 3
    });
    this.baseUrl = options.baseUrl || BASE_URL;
    this.timeout = options.timeout || 30000;
  }

  setApiKey(key) {
    if (key && typeof key === 'string') {
      this.apikey = key;
      this.rateLimiter.setRate(10);
    }
  }

  setEmail(email) {
    if (email && typeof email === 'string') {
      this.email = email;
    }
  }

  setDelay(ms) {
    validateDelay(ms);
    this.rateLimiter.delayMs = ms;
  }

  setTimeout(ms) {
    if (typeof ms === 'number' && ms > 0) {
      this.timeout = ms;
    }
  }

  async request(url, options = {}) {
    const method = options.method || 'GET';
    return this.rateLimiter.execute(async () => {
      try {
        const response = await axios({
          method,
          url,
          data: options.body,
          timeout: options.timeout || this.timeout,
          maxContentLength: Infinity,
          maxBodyLength: Infinity,
          validateStatus: (status) => status === 200
        });
        if (typeof response.data === 'string' && response.data.includes('<eutilsError>')) {
          const match = response.data.match(/<Message>(.*?)<\/Message>/);
          throw new APIError(match ? match[1] : 'Unknown API error');
        }
        if (typeof response.data === 'string') {
          return response.data;
        }
        return JSON.stringify(response.data);
      } catch (err) {
        if (err.response) {
          if (err.response.status === 429) {
            throw new APIError('Rate limit exceeded. Please wait before making more requests.');
          }
          if (err.response.status === 503) {
            throw new APIError('Service temporarily unavailable.');
          }
          throw new APIError(`API returned status ${err.response.status}`);
        }
        if (err.code === 'ECONNREFUSED') {
          throw new NetworkError('Connection refused. Please check your internet connection.');
        }
        if (err.code === 'ETIMEDOUT' || err.code === 'ECONNABORTED') {
          throw new TimeoutError('Request timed out.');
        }
        throw new NetworkError(err.message);
      }
    });
  }

  buildUrl(endpoint, params) {
    const url = new URL(`${this.baseUrl}/${endpoint}.cgi`);
    if (this.apikey) url.searchParams.set('api_key', this.apikey);
    if (this.email) url.searchParams.set('email', this.email);
    Object.entries(params).forEach(([k, v]) => {
      if (v !== undefined && v !== '') url.searchParams.set(k, v);
    });
    return url.toString();
  }

  async esearch({ db, term, retmax = DEFAULT_RETMAX, retstart = 0, sort = '' }) {
    validateDb(db);
    validateTerm(term);
    validateRetMax(retmax);
    if (retmax > MAX_RETMAX) {
      throw new ValidationError(`retmax cannot exceed ${MAX_RETMAX}`);
    }
    const url = this.buildUrl('esearch', {
      db,
      term,
      retmax,
      retstart,
      sort,
      usehistory: 'y',
      format: 'json'
    });
    const res = await this.request(url);
    try {
      return JSON.parse(res);
    } catch {
      throw new APIError('Failed to parse ESearch response');
    }
  }

  async efetch({ db, ids, rettype = 'fasta', retmode = 'text', retmax = DEFAULT_RETMAX }) {
    validateDb(db);
    validateId(ids);
    validateRetMode(retmode);
    validateRetMax(retmax);
    const idList = Array.isArray(ids) ? ids.join(',') : ids;
    const params = {
      db,
      id: idList,
      rettype,
      retmode,
      retmax
    };
    const url = this.buildUrl('efetch', params);
    const res = await this.request(url);
    if (retmode === 'json' || rettype === 'json') {
      try { return JSON.parse(res); } catch { return res; }
    }
    return res;
  }

  async esummary({ db, ids, retmode = 'json' }) {
    validateDb(db);
    validateId(ids);
    validateRetMode(retmode);
    const idList = Array.isArray(ids) ? ids.join(',') : ids;
    const url = this.buildUrl('esummary', {
      db,
      id: idList,
      retmode
    });
    const res = await this.request(url);
    try {
      return JSON.parse(res);
    } catch {
      throw new APIError('Failed to parse ESummary response');
    }
  }

  async elink({ db, ids, linkeddb }) {
    validateDb(db);
    validateId(ids);
    validateDb(linkeddb);
    const idList = Array.isArray(ids) ? ids.join(',') : ids;
    const url = this.buildUrl('elink', {
      db,
      id: idList,
      linkname: `${db}_${linkeddb}`,
      format: 'json'
    });
    const res = await this.request(url);
    try {
      return JSON.parse(res);
    } catch {
      throw new APIError('Failed to parse ELink response');
    }
  }

  async einfo({ db }) {
    validateDb(db);
    const url = this.buildUrl('einfo', { db, format: 'json' });
    const res = await this.request(url);
    try {
      return JSON.parse(res);
    } catch {
      throw new APIError('Failed to parse EInfo response');
    }
  }

  // ========================================
  // ESPELL - Spell Check
  // ========================================

  /**
   * Check spelling of PubMed search terms
   * Returns suggested corrections and if the term is valid
   */
  async espell({ term, db = 'pubmed' }) {
    if (!term || typeof term !== 'string') {
      throw new ValidationError('Search term is required');
    }
    const url = this.buildUrl('espell', { db, term });
    const res = await this.request(url);
    // Parse XML response to JSON
    return this.parseEspellXml(res);
  }

  /**
   * Parse eSpell XML response to JSON
   */
  parseEspellXml(xml) {
    const result = {
      originalQuery: '',
      correctedQuery: '',
      corrections: [],
      isQueryCorrect: true
    };

    try {
      // Extract OriginalQuery
      const originalMatch = xml.match(/<OriginalQuery>([^<]*)<\/OriginalQuery>/);
      if (originalMatch) result.originalQuery = originalMatch[1];

      // Extract CorrectedQuery
      const correctedMatch = xml.match(/<CorrectedQuery>([^<]*)<\/CorrectedQuery>/);
      if (correctedMatch) result.correctedQuery = correctedMatch[1];

      // Extract IsQueryCorrect
      const isCorrectMatch = xml.match(/<IsQueryCorrect>([^<]*)<\/IsQueryCorrect>/);
      if (isCorrectMatch) result.isQueryCorrect = isCorrectMatch[1].toLowerCase() === 'true';

      // Extract all corrections
      const correctionMatches = xml.matchAll(/<Correction>([^<]*)<\/Correction>/g);
      for (const match of correctionMatches) {
        const [original, replacement] = match[1].split('|');
        result.corrections.push({ original: original || '', replacement: replacement || '' });
      }
    } catch (e) {
      // If parsing fails, return raw XML with error info
      return { error: 'Failed to parse XML', raw: xml };
    }

    return result;
  }

  // ========================================
  // ECITMATCH - Citation Match
  // ========================================

  /**
   * Match citations against PubMed database
   * Returns matching PMIDs for given citation strings
   */
  async ecitmatch({ citations, db = 'pubmed', auto = 'OR' }) {
    if (!citations || !Array.isArray(citations) || citations.length === 0) {
      throw new ValidationError('Citations array is required');
    }
    if (citations.length > 200) {
      throw new ValidationError('Maximum 200 citations per request');
    }
    
    // Build citation string (one per line)
    const citationStr = citations.join('\n');
    const url = this.buildUrl('ecitmatch', { 
      db, 
      citation: citationStr,
      auto
    });
    const res = await this.request(url);
    // Parse the pipe-separated response
    const lines = res.trim().split('\n');
    return lines.map(line => {
      const parts = line.split('|');
      if (parts.length >= 3) {
        return {
          original: parts[0].trim(),
          pmid: parts[1].trim() || null,
          matched: parts[2].trim() === 'y'
        };
      }
      return { original: line, pmid: null, matched: false };
    });
  }

  // ========================================
  // Assembly Resolution
  // ========================================
  
  /**
   * Resolve assembly name to RefSeq accession
   * Converts common assembly names like "GRCh38" → GCF_000001405.40
   */
  async resolveAssembly(assemblyName) {
    if (!assemblyName || typeof assemblyName !== 'string') {
      throw new ValidationError('Assembly name is required');
    }
    
    // Common assembly name mappings
    const assemblyMap = {
      'grch38': 'GCF_000001405.40',
      'grch37': 'GCF_000001405.14',
      'mm39': 'GCF_000001635.10',
      'mm10': 'GCF_000001635.4',
      'rn7': 'GCF_016699045.2',
      'rn6': 'GCF_000001895.1',
      'danrer11': 'GCF_000002035.6',
      'danrer10': 'GCF_000001035.2',
      'galgal7': 'GCF_000002315.5',
      'galgal6': 'GCF_000002315.3'
    };
    
    const normalized = assemblyName.toLowerCase().replace(/[.\s]/g, '');
    
    // Check known assemblies
    if (assemblyMap[normalized]) {
      return {
        name: assemblyName,
        accession: assemblyMap[normalized],
        isKnown: true
      };
    }
    
    // Try to search NCBI Assembly database
    try {
      const searchUrl = this.buildUrl('esearch', {
        db: 'assembly',
        term: assemblyName,
        retmax: 1,
        format: 'json'
      });
      const searchRes = await this.request(searchUrl);
      const searchData = JSON.parse(searchRes);
      
      if (searchData.esearchresult && searchData.esearchresult.idlist && searchData.esearchresult.idlist.length > 0) {
        const assemblyId = searchData.esearchresult.idlist[0];
        
        // Get assembly summary
        const summaryUrl = this.buildUrl('esummary', {
          db: 'assembly',
          id: assemblyId,
          format: 'json'
        });
        const summaryRes = await this.request(summaryUrl);
        const summaryData = JSON.parse(summaryRes);
        
        if (summaryData.result && summaryData.result[assemblyId]) {
          const info = summaryData.result[assemblyId];
          return {
            name: assemblyName,
            assemblyId: assemblyId,
            accession: info.assemblyaccession || info.assemblyaccn,
            assemblyName: info.assemblyname,
            isKnown: false,
            isReference: info.refseq_category === 'reference genome'
          };
        }
      }
      
      return {
        name: assemblyName,
        error: 'Assembly not found'
      };
    } catch (e) {
      throw new APIError(`Failed to resolve assembly: ${e.message}`);
    }
  }

  // ========================================
  // Gene Panorama (Gene + Linked PubMed)
  // ========================================
  
  /**
   * Get gene information with linked PubMed literature
   */
  async getGenePanorama(geneIdOrSymbol) {
    if (!geneIdOrSymbol) {
      throw new ValidationError('Gene ID or symbol is required');
    }
    
    // First, find the gene
    const searchUrl = this.buildUrl('esearch', {
      db: 'gene',
      term: geneIdOrSymbol,
      retmax: 1,
      format: 'json'
    });
    const searchRes = await this.request(searchUrl);
    const searchData = JSON.parse(searchRes);
    
    if (!searchData.esearchresult || !searchData.esearchresult.idlist || searchData.esearchresult.idlist.length === 0) {
      throw new APIError(`Gene not found: ${geneIdOrSymbol}`);
    }
    
    const geneId = searchData.esearchresult.idlist[0];
    
    // Get gene summary
    const summaryUrl = this.buildUrl('esummary', {
      db: 'gene',
      id: geneId,
      format: 'json'
    });
    const summaryRes = await this.request(summaryUrl);
    const summaryData = JSON.parse(summaryRes);
    
    const geneInfo = summaryData.result && summaryData.result[geneId];
    if (!geneInfo) {
      throw new APIError('Failed to get gene summary');
    }
    
    // Get linked PubMed articles
    const linkUrl = this.buildUrl('elink', {
      db: 'gene',
      id: geneId,
      linkeddb: 'pubmed',
      format: 'json'
    });
    const linkRes = await this.request(linkUrl);
    const linkData = JSON.parse(linkRes);
    
    let pubmedIds = [];
    if (linkData.linksets && linkData.linksets[0] && linkData.linksets[0].linksetdbs) {
      for (const linkset of linkData.linksets[0].linksetdbs) {
        if (linkset.linksetdbname === 'gene_pubmed') {
          pubmedIds = linkset.links || [];
          break;
        }
      }
    }
    
    // Get top PubMed articles (limit to 10 for performance)
    let pubmedArticles = [];
    if (pubmedIds.length > 0) {
      const topIds = pubmedIds.slice(0, 10);
      const pubmedUrl = this.buildUrl('esummary', {
        db: 'pubmed',
        id: topIds.join(','),
        format: 'json'
      });
      const pubmedRes = await this.request(pubmedUrl);
      const pubmedData = JSON.parse(pubmedRes);
      
      if (pubmedData.result) {
        pubmedArticles = topIds.map(id => pubmedData.result[id]).filter(Boolean);
      }
    }
    
    return {
      gene: {
        id: geneId,
        symbol: geneInfo.name,
        description: geneInfo.description,
        chromosome: geneInfo.chromosome,
        mapLocation: geneInfo.maplocation,
        otherAliases: geneInfo.otheraliases,
        summary: geneInfo.summary
      },
      pubmedCount: pubmedIds.length,
      pubmedArticles: pubmedArticles.map(article => ({
        id: article.uid,
        title: article.title,
        authors: article.authors?.map(a => a.name),
        journal: article.fulljournalname,
        pubdate: article.pubdate,
        source: article.source
      }))
    };
  }

  // ========================================
  // Variant Interpreter (ClinVar/dbsnp)
  // ========================================
  
  /**
   * Get variant information from ClinVar and dbSNP
   */
  async getVariantInfo(variantInput) {
    if (!variantInput) {
      throw new ValidationError('Variant ID or rs number is required');
    }
    
    // Normalize input (rs123456 -> 123456)
    let searchTerm = variantInput.toString().toLowerCase();
    if (searchTerm.startsWith('rs')) {
      searchTerm = searchTerm.substring(2);
    }
    
    // Try ClinVar first
    try {
      const clinvarSearch = this.buildUrl('esearch', {
        db: 'clinvar',
        term: `rs${searchTerm}`,
        retmax: 1,
        format: 'json'
      });
      const clinvarRes = await this.request(clinvarSearch);
      const clinvarData = JSON.parse(clinvarRes);
      
      if (clinvarData.esearchresult && clinvarData.esearchresult.idlist && clinvarData.esearchresult.idlist.length > 0) {
        const clinvarId = clinvarData.esearchresult.idlist[0];
        
        const clinvarSummary = this.buildUrl('esummary', {
          db: 'clinvar',
          id: clinvarId,
          format: 'json'
        });
        const summaryRes = await this.request(clinvarSummary);
        const summaryData = JSON.parse(summaryRes);
        
        const clinvarInfo = summaryData.result && summaryData.result[clinvarId];
        
        if (clinvarInfo) {
          return {
            variant: variantInput,
            source: 'clinvar',
            clinvarId: clinvarId,
            clinicalSignificance: clinvarInfo.clinicalsignificance?.value,
            reviewStatus: clinvarInfo.reviewstatus,
            conditions: clinvarInfo.conditions?.map(c => c.name),
            variantType: clinvarInfo.variationtype,
            genes: clinvarInfo.gene || clinvarInfo.genes?.map(g => g.name),
            references: clinvarInfo.references?.map(r => r.citation)
          };
        }
      }
    } catch (e) {
      // Continue to dbSNP if ClinVar fails
    }
    
    // Try dbSNP
    try {
      const dbsnpSearch = this.buildUrl('esearch', {
        db: 'snp',
        term: searchTerm,
        retmax: 1,
        format: 'json'
      });
      const dbsnpRes = await this.request(dbsnpSearch);
      const dbsnpData = JSON.parse(dbsnpRes);
      
      if (dbsnpData.esearchresult && dbsnpData.esearchresult.idlist && dbsnpData.esearchresult.idlist.length > 0) {
        const snpId = dbsnpData.esearchresult.idlist[0];
        
        const dbsnpSummary = this.buildUrl('esummary', {
          db: 'snp',
          id: snpId,
          format: 'json'
        });
        const snpRes = await this.request(dbsnpSummary);
        const snpData = JSON.parse(snpRes);
        
        const snpInfo = snpData.result && snpData.result[snpId];
        
        if (snpInfo) {
          return {
            variant: variantInput,
            source: 'dbsnp',
            snpId: snpId,
            rsId: `rs${searchTerm}`,
            alleles: snpInfo.allele,
            function: snpInfo.function,
            gene: snpInfo.gene,
            globalMaf: snpInfo.global_maf,
            validated: snpInfo.validated,
            assembly: snpInfo.assembly
          };
        }
      }
    } catch (e) {
      // Continue to error
    }
    
    throw new APIError(`Variant not found: ${variantInput}`);
  }

  // ========================================
  // Primer/Seq Search (BLAST-like)
  // ========================================
  
  /**
   * Search for similar sequences using BLAST
   */
    async blastSequence({ sequence, database = 'nt', program = 'blastn', expect = 10, megablast = true }) {
    if (!sequence) {
      throw new ValidationError('Sequence is required');
    }
    
    const cleanSeq = sequence.replace(/[^a-zA-Z]/g, '').toUpperCase();
    
    if (cleanSeq.length < 20) {
      throw new ValidationError('Sequence must be at least 20 nucleotides');
    }
    
    const blastBaseUrl = 'https://blast.ncbi.nlm.nih.gov/blast/Blast.cgi';
    
    const submitParams = new URLSearchParams({
      CMD: 'PUT',
      QUERY: cleanSeq,
      DATABASE: database,
      PROGRAM: program,
      EXPECT: expect.toString(),
      MEGABLAST: megablast ? 'TRUE' : 'FALSE',
      FORMAT_TYPE: 'JSON'
    });
    
    const submitUrl = `${blastBaseUrl}?${submitParams.toString()}`;
    
    let rid = null;
    try {
      const submitRes = await this.request(submitUrl);
      
      const ridMatch = submitRes.match(/RID\s*=\s*["']?([A-Z0-9]+)["']?/i);
      if (ridMatch) {
        rid = ridMatch[1];
      } else {
        const ridMatch2 = submitRes.match(/<input[^>]*name="RID"[^>]*value="([^"]+)"/);
        if (ridMatch2) {
          rid = ridMatch2[1];
        }
      }
      
      if (!rid) {
        return {
          raw: submitRes.substring(0, 5000),
          message: 'Could not get RID from BLAST. Showing raw output.'
        };
      }
      
      const maxAttempts = 20;
      const pollInterval = 3000;
      
      for (let attempt = 0; attempt < maxAttempts; attempt++) {
        await this.sleep(pollInterval);
        
        const statusUrl = `${blastBaseUrl}?CMD=GET&FORMAT_TYPE=JSON&RID=${rid}`;
        const statusRes = await this.request(statusUrl);
        
        if (statusRes.includes('"Status":"READY"') || statusRes.includes('Status":"READY"')) {
          const jsonMatch = statusRes.match(/\{[\s\S]*}/);
          if (jsonMatch) {
            return JSON.parse(jsonMatch[0]);
          }
          return { raw: statusRes.substring(0, 5000), message: 'Results ready but could not parse JSON' };
        }
        
        if (statusRes.includes('"Status":"FAILURE"') || statusRes.includes('Status":"FAILURE"')) {
          throw new APIError('BLAST search failed on server side');
        }
      }
      
      throw new APIError('BLAST search timed out');
      
    } catch (e) {
      if (e instanceof APIError || e instanceof ValidationError) {
        throw e;
      }
      throw new APIError(`BLAST search failed: ${e.message}`);
    }
  }

  async getSRAInfo(experimentId) {
    if (!experimentId) {
      throw new ValidationError('Experiment ID (SRX/ERR/DRX) is required');
    }
    
    // Search for the experiment
    const searchUrl = this.buildUrl('esearch', {
      db: 'sra',
      term: experimentId,
      retmax: 1,
      format: 'json'
    });
    const searchRes = await this.request(searchUrl);
    const searchData = JSON.parse(searchRes);
    
    if (!searchData.esearchresult || !searchData.esearchresult.idlist || searchData.esearchresult.idlist.length === 0) {
      throw new APIError(`SRA experiment not found: ${experimentId}`);
    }
    
    const sraId = searchData.esearchresult.idlist[0];
    
    // Get SRA summary
    const summaryUrl = this.buildUrl('esummary', {
      db: 'sra',
      id: sraId,
      format: 'json'
    });
    const summaryRes = await this.request(summaryUrl);
    const summaryData = JSON.parse(summaryRes);
    
    const sraInfo = summaryData.result && summaryData.result[sraId];
    if (!sraInfo) {
      throw new APIError('Failed to get SRA information');
    }
    
    // Extract run info
    let runsData = [];
    if (sraInfo.runs) {
      const runs = Array.isArray(sraInfo.runs) ? sraInfo.runs : [sraInfo.runs];
      runsData = runs.map(run => {
        const runStr = typeof run === 'string' ? run : JSON.stringify(run);
        const [runId, baseCount] = runStr.split('(');
        return {
          runId: runId.trim(),
          baseCount: baseCount ? baseCount.replace(')', '').replace(' Mb', '') : null
        };
      });
    }
    
    // Get linked experiment
    const linkUrl = this.buildUrl('elink', {
      db: 'sra',
      id: sraId,
      linkeddb: 'sra',
      format: 'json'
    });
    const linkRes = await this.request(linkUrl);
    const linkData = JSON.parse(linkRes);
    
    let experiments = [];
    if (linkData.linksets && linkData.linksets[0] && linkData.linksets[0].linksetdbs) {
      for (const linkset of linkData.linksets[0].linksetdbs) {
        if (linkset.linksetdbname === 'sra_sra') {
          experiments = linkset.links || [];
          break;
        }
      }
    }
    
    return {
      experiment: experimentId,
      sraId: sraId,
      study: sraInfo.study,
      biosample: sraInfo.biosample,
      platform: sraInfo.platform,
      instrument: sraInfo.instrument,
      library: sraInfo.library,
      layout: sraInfo.layout,
      runs: runsData,
      totalRuns: runsData.length,
      experiments: experiments.slice(0, 10),
      ftpUrl: sraInfo.srafile?.map(f => f.url) || []
    };
  }

  getRateLimitStatus() {
    return {
      isRunning: this.rateLimiter.isRunning,
      queueLength: this.rateLimiter.queueLength,
      requestsPerSecond: this.rateLimiter.requestsPerSecond,
      hasApiKey: !!this.apikey
    };
  }
}

export { NCBIClient, VALID_DBS, VALID_RETMODE, DEFAULT_RETMAX, MAX_RETMAX };
export default NCBIClient;
