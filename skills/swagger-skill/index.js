import { execSync } from 'child_process';
import { createRequire } from 'module';
import { fileURLToPath } from 'url';
import path from 'path';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const require = createRequire(import.meta.url);

function ensureDependencies() {
  const deps = ['axios', 'form-data'];
  const missing = deps.filter(dep => {
    try { require.resolve(dep); return false; } catch { return true; }
  });
  if (missing.length > 0) {
    const pkgJsonPath = path.join(__dirname, 'package.json');
    try { require.resolve(pkgJsonPath); } catch {
      execSync(`npm init -y --prefix "${__dirname}" && node -e "const fs=require('fs');const p=JSON.parse(fs.readFileSync('${pkgJsonPath}','utf8'));p.type='module';fs.writeFileSync('${pkgJsonPath}',JSON.stringify(p,null,2))"`, { stdio: 'pipe' });
    }
    execSync(`npm install --prefix "${__dirname}" ${missing.join(' ')}`, { stdio: 'pipe' });
  }
}

ensureDependencies();

const axios = (await import('axios')).default;

const HTTP_METHODS = new Set(['get', 'post', 'put', 'delete', 'patch', 'head', 'options']);

class SwaggerAPISkill {
  constructor() {
    this.swaggerSpec = null;
    this.baseUrl = null;
    this.apiIndex = null;       // 轻量搜索索引
    this.apiDetailMap = null;   // O(1) 详情查找
    this.sessionId = `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    this.authToken = null;
    this.authCookies = null;
    this.authHeaders = {};
  }

  getSessionId() {
    return this.sessionId;
  }

  refreshSession() {
    this.swaggerSpec = null;
    this.baseUrl = null;
    this.apiIndex = null;
    this.apiDetailMap = null;
    this.sessionId = `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    return { success: true, message: '会话已刷新' };
  }

  setAuthToken(token, options = {}) {
    if (!token || typeof token !== 'string') {
      return { success: false, message: 'Token 必须是非空字符串' };
    }
    const tokenType = options.tokenType || 'Bearer';
    const headerName = options.headerName || 'Authorization';
    this.authToken = token;
    this.authHeaders = { ...this.authHeaders, [headerName]: `${tokenType} ${token}` };
    return { success: true, message: '认证 Token 已设置' };
  }

  setAuthCookies(cookies = {}) {
    if (!cookies || typeof cookies !== 'object' || Array.isArray(cookies)) {
      return { success: false, message: 'cookies 必须是对象' };
    }
    const entries = Object.entries(cookies).filter(([, v]) => v !== undefined && v !== null);
    if (entries.length === 0) {
      return { success: false, message: 'cookies 不能为空' };
    }
    const invalid = entries.find(([name, value]) => {
      if (!name || typeof name !== 'string') return true;
      if (typeof value !== 'string' && typeof value !== 'number' && typeof value !== 'boolean') return true;
      return /[;\r\n]/.test(name) || /[\r\n]/.test(String(value));
    });
    if (invalid) {
      return { success: false, message: `无效的 Cookie 键值: ${invalid[0]}` };
    }
    this.authCookies = Object.fromEntries(entries.map(([n, v]) => [n, String(v)]));
    this.authHeaders = {
      ...this.authHeaders,
      Cookie: Object.entries(this.authCookies).map(([n, v]) => `${n}=${encodeURIComponent(v)}`).join('; ')
    };
    return { success: true, message: '认证 Cookie 已设置' };
  }

  clearAuth() {
    this.authToken = null;
    this.authCookies = null;
    this.authHeaders = {};
    return { success: true, message: '认证信息已清除' };
  }

  async fetchSwaggerSpec(url, options = {}) {
    try {
      if (this.swaggerSpec && this.apiIndex) {
        return { success: true, apiCount: this.apiIndex.length, cached: true };
      }

      if (options.token) {
        const r = this.setAuthToken(options.token, options.tokenOptions);
        if (!r.success) return r;
      }
      if (options.cookies) {
        const r = this.setAuthCookies(options.cookies);
        if (!r.success) return r;
      }

      let specUrl = url;
      if (!url.match(/\/(swagger\.json|openapi\.json|api-docs|v3\/api-docs)$/)) {
        specUrl = url.endsWith('/') ? url + 'swagger.json' : url + '/swagger.json';
      }

      const response = await axios.get(specUrl, { headers: this.authHeaders });
      this.swaggerSpec = response.data;
      this.baseUrl = url.replace(/\/(swagger\.json|openapi\.json|v3\/api-docs)$/, '');
      this._buildAPICache();

      return { success: true, apiCount: this.apiIndex.length };
    } catch (error) {
      return { success: false, error: `获取 Swagger 规范失败: ${error.message}` };
    }
  }

  _buildAPICache() {
    this.apiIndex = [];
    this.apiDetailMap = new Map();

    if (!this.swaggerSpec?.paths) return;

    for (const path in this.swaggerSpec.paths) {
      const pathItem = this.swaggerSpec.paths[path];
      for (const method in pathItem) {
        if (!HTTP_METHODS.has(method.toLowerCase())) continue;
        const op = pathItem[method];
        const key = `${method.toUpperCase()} ${path}`;

        this.apiIndex.push({
          path,
          method: method.toUpperCase(),
          summary: op.summary || '',
          description: op.description || '',
          operationId: op.operationId || '',
          tags: op.tags || []
        });

        this.apiDetailMap.set(key, {
          path,
          method: method.toUpperCase(),
          summary: op.summary || '',
          description: op.description || '',
          parameters: op.parameters || [],
          requestBody: op.requestBody || null,
          responses: op.responses || {},
          tags: op.tags || []
        });
      }
    }
  }

  getAllAPIs() {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范，请先调用 fetchSwaggerSpec' };
    }
    if (!this.apiIndex) this._buildAPICache();
    return {
      success: true,
      total: this.apiIndex.length,
      apis: this.apiIndex
    };
  }

  searchAPI(query) {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范' };
    }
    if (!this.apiIndex) this._buildAPICache();

    const results = [];
    const queryLower = query.toLowerCase();
    const queryWords = this._tokenizeQuery(query);

    for (const api of this.apiIndex) {
      let score = 0;
      const { summary, description, path, operationId, tags } = api;
      const pathLower = path.toLowerCase();

      // 精确匹配
      if (summary === query) { score = 100; }
      else if (description === query) { score = 80; }
      else {
        // 完整包含匹配
        if (summary.includes(query)) score += 50;
        if (description.includes(query)) score += 30;
        if (pathLower.includes(queryLower)) score += 20;
        if (operationId?.toLowerCase().includes(queryLower)) score += 10;

        // tags 匹配
        if (tags.some(t => t.toLowerCase().includes(queryLower))) score += 15;

        // 分词匹配（仅当没有完整匹配时）
        if (score < 50) {
          for (const word of queryWords) {
            const wordLower = word.toLowerCase();
            if (summary.includes(word)) score += 15;
            if (description.includes(word)) score += 10;
            if (pathLower.includes(wordLower)) score += 5;
            if (tags.some(t => t.toLowerCase().includes(wordLower))) score += 8;
          }
        }
      }

      if (score > 0) {
        const item = { path, method: api.method, summary: summary || '无描述', score: score / 100 };
        if (description) item.description = description;
        results.push(item);
      }
    }

    results.sort((a, b) => b.score - a.score);
    return {
      success: true,
      query,
      matchCount: results.length,
      results: results.slice(0, 10)
    };
  }

  getAPIDetail(path, method) {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范' };
    }
    if (!this.apiDetailMap) this._buildAPICache();

    const api = this.apiDetailMap.get(`${method.toUpperCase()} ${path}`);
    if (!api) {
      return { success: false, error: `接口 ${method.toUpperCase()} ${path} 不存在` };
    }
    return { success: true, detail: api };
  }

  async callAPI(path, method, params = {}) {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范' };
    }
    try {
      const url = this._buildURL(path, params.query);
      const isFormData = params.isFormData || (params.body instanceof FormData);
      const config = {
        method: method.toLowerCase(),
        url,
        headers: isFormData
          ? { ...this.authHeaders, ...params.headers }
          : { 'Content-Type': 'application/json', ...this.authHeaders, ...params.headers }
      };
      if (params.body) config.data = params.body;
      if (params.query) config.params = params.query;

      const response = await axios(config);
      return { success: true, status: response.status, data: response.data };
    } catch (error) {
      return {
        success: false,
        status: error.response?.status,
        error: error.message,
        data: error.response?.data || {}
      };
    }
  }

  async callAPIByInstruction(instruction, params = {}) {
    const searchResult = this.searchAPI(instruction);
    if (!searchResult.success || searchResult.results.length === 0) {
      return {
        success: false,
        instruction,
        error: `未找到匹配的 API: ${instruction}`,
        suggestion: '请尝试使用其他关键词或查看 getAllAPIs() 获取所有可用接口'
      };
    }

    const topMatch = searchResult.results[0];
    const result = await this.callAPI(topMatch.path, topMatch.method, params);
    return {
      success: result.success,
      instruction,
      matchedAPI: { path: topMatch.path, method: topMatch.method, summary: topMatch.summary, matchScore: topMatch.score },
      result
    };
  }

  async uploadFile(path, formData = {}, query = null) {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范' };
    }
    try {
      const FormDataLib = (await import('form-data')).default;
      const fs = (await import('fs')).default;
      const form = new FormDataLib();

      for (const [key, value] of Object.entries(formData)) {
        if (key === 'file' && typeof value === 'string') {
          form.append(key, fs.createReadStream(value));
        } else if (key === 'file' && Buffer.isBuffer(value)) {
          form.append(key, value, 'file');
        } else {
          form.append(key, String(value));
        }
      }

      const url = this._buildURL(path, query);
      const config = {
        method: 'post',
        url,
        data: form,
        headers: { ...form.getHeaders(), ...this.authHeaders }
      };
      if (query) config.params = query;

      const response = await axios(config);
      return { success: true, status: response.status, data: response.data };
    } catch (error) {
      return {
        success: false,
        status: error.response?.status,
        error: error.message,
        data: error.response?.data || {}
      };
    }
  }

  getFullAPIDetail(path, method) {
    if (!this.swaggerSpec) {
      return { success: false, error: '未加载 Swagger 规范' };
    }

    const basicDetail = this.getAPIDetail(path, method);
    if (!basicDetail.success) return basicDetail;

    const detail = basicDetail.detail;
    const schemas = this.swaggerSpec.components?.schemas
      || this.swaggerSpec.definitions
      || {};

    const relatedSchemas = {};
    const schemaNames = new Set();

    // 从 requestBody 提取 $ref (OpenAPI 3.0)
    if (detail.requestBody?.content?.['application/json']?.schema?.$ref) {
      schemaNames.add(detail.requestBody.content['application/json'].schema.$ref.split('/').pop());
    }

    // 从 parameters 提取 $ref (Swagger 2.0 body 参数)
    (detail.parameters || []).forEach(param => {
      if (param.schema?.$ref) {
        schemaNames.add(param.schema.$ref.split('/').pop());
      }
    });

    // 从 responses 提取 $ref (兼容 OpenAPI 3.0 和 Swagger 2.0)
    Object.values(detail.responses || {}).forEach(response => {
      const ref = response.content?.['application/json']?.schema?.$ref
        || response.schema?.$ref;
      if (ref) schemaNames.add(ref.split('/').pop());
    });

    const collectSchemas = (schemaName, visited = new Set()) => {
      if (visited.has(schemaName) || !schemas[schemaName]) return;
      visited.add(schemaName);
      const schema = schemas[schemaName];
      relatedSchemas[schemaName] = schema;

      if (schema.properties) {
        Object.values(schema.properties).forEach(prop => {
          if (prop.$ref) collectSchemas(prop.$ref.split('/').pop(), visited);
          else if (prop.items?.$ref) collectSchemas(prop.items.$ref.split('/').pop(), visited);
        });
      }
      if (schema.anyOf) {
        schema.anyOf.forEach(item => {
          if (item.$ref) collectSchemas(item.$ref.split('/').pop(), visited);
        });
      }
      if (schema.items?.$ref) {
        collectSchemas(schema.items.$ref.split('/').pop(), visited);
      }
    };

    schemaNames.forEach(name => collectSchemas(name));

    return {
      success: true,
      detail: { ...detail, relatedSchemas, schemaCount: Object.keys(relatedSchemas).length }
    };
  }

  // Private helpers

  _buildURL(path, queryParams = {}) {
    if (!queryParams || Object.keys(queryParams).length === 0) {
      return this.baseUrl + path;
    }
    return this.baseUrl + path.replace(/\{(\w+)\}/g, (_, key) => queryParams[key] ?? `{${key}}`);
  }

  _tokenizeQuery(query) {
    const tokens = [];
    let word = '';
    for (let i = 0; i < query.length; i++) {
      const code = query.charCodeAt(i);
      const isChinese = code >= 0x4e00 && code <= 0x9fff;
      const isAlphaNum = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122) || code === 95;
      if (isChinese) {
        if (word) { tokens.push(word); word = ''; }
        tokens.push(query[i]);
      } else if (isAlphaNum) {
        word += query[i];
      } else {
        if (word) { tokens.push(word); word = ''; }
      }
    }
    if (word) tokens.push(word);
    return tokens;
  }
}

export default SwaggerAPISkill;
