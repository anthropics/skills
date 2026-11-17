/**
 * Pre-Deploy Validator Skill
 * Conducts comprehensive pre-deployment flight checks for agent ability verification
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

class PreDeployValidator {
  constructor(config = {}) {
    this.config = {
      checkCodeQuality: config.checkCodeQuality !== false,
      checkSecurity: config.checkSecurity !== false,
      checkTests: config.checkTests !== false,
      checkDependencies: config.checkDependencies !== false,
      checkDocumentation: config.checkDocumentation !== false,
      failOnWarnings: config.failOnWarnings || false,
      ...config
    };
    this.results = {
      passed: [],
      warnings: [],
      failures: [],
      errors: []
    };
  }

  /**
   * Run all validation checks
   */
  async validate() {
    console.log('🚀 Starting Pre-Deployment Flight Checks...\n');

    try {
      if (this.config.checkCodeQuality) await this.checkCodeQuality();
      if (this.config.checkSecurity) await this.checkSecurity();
      if (this.config.checkTests) await this.checkTests();
      if (this.config.checkDependencies) await this.checkDependencies();
      if (this.config.checkDocumentation) await this.checkDocumentation();
    } catch (error) {
      this.results.errors.push(error.message);
    }

    return this.generateReport();
  }

  /**
   * Validate code quality
   */
  async checkCodeQuality() {
    console.log('📊 Checking code quality...');

    try {
      // Check for package.json and run linting
      if (fs.existsSync('package.json')) {
        const pkg = JSON.parse(fs.readFileSync('package.json', 'utf8'));

        if (pkg.scripts?.lint) {
          try {
            execSync('npm run lint', { stdio: 'pipe' });
            this.results.passed.push('Code linting passed');
          } catch (error) {
            this.results.failures.push('Linting errors detected');
          }
        }
      }

      this.results.passed.push('Code quality check completed');
    } catch (error) {
      this.results.warnings.push(`Code quality check: ${error.message}`);
    }
  }

  /**
   * Security validation
   */
  async checkSecurity() {
    console.log('🔒 Checking security...');

    const sensitivePatterns = [
      { pattern: /sk-[A-Za-z0-9]{48}/, name: 'OpenAI API key' },
      { pattern: /AKIA[0-9A-Z]{16}/, name: 'AWS access key' },
      { pattern: /ghp_[A-Za-z0-9]{36}/, name: 'GitHub token' },
      { pattern: /password\s*[:=]\s*['"]/, name: 'Password field' },
      { pattern: /api[_-]?key\s*[:=]\s*['"]/, name: 'API key field' }
    ];

    const filesToCheck = this.getFilesToCheck(['.js', '.ts', '.json', '.md', '.env']);
    const foundSecrets = [];

    filesToCheck.forEach(file => {
      try {
        const content = fs.readFileSync(file, 'utf8');
        sensitivePatterns.forEach(({ pattern, name }) => {
          if (pattern.test(content)) {
            foundSecrets.push(`${name} detected in ${file}`);
          }
        });
      } catch (error) {
        // Skip files that can't be read
      }
    });

    if (foundSecrets.length > 0) {
      this.results.failures.push(`Security: ${foundSecrets.join(', ')}`);
    } else {
      this.results.passed.push('No sensitive patterns detected');
    }
  }

  /**
   * Test validation
   */
  async checkTests() {
    console.log('✅ Checking tests...');

    try {
      if (fs.existsSync('package.json')) {
        const pkg = JSON.parse(fs.readFileSync('package.json', 'utf8'));

        if (pkg.scripts?.test) {
          try {
            execSync('npm test', { stdio: 'pipe' });
            this.results.passed.push('All tests passed');
          } catch (error) {
            this.results.failures.push('Test suite failed');
          }
        } else {
          this.results.warnings.push('No test script found in package.json');
        }
      } else {
        this.results.warnings.push('No package.json found');
      }
    } catch (error) {
      this.results.warnings.push(`Test check: ${error.message}`);
    }
  }

  /**
   * Dependency validation
   */
  async checkDependencies() {
    console.log('📦 Checking dependencies...');

    try {
      if (fs.existsSync('package.json')) {
        try {
          execSync('npm audit --audit-level=moderate', { stdio: 'pipe' });
          this.results.passed.push('No moderate or high vulnerabilities found');
        } catch (error) {
          this.results.warnings.push('Vulnerabilities detected in dependencies');
        }
      } else if (fs.existsSync('requirements.txt')) {
        this.results.passed.push('Python project - dependency check skipped');
      } else {
        this.results.warnings.push('No dependency file found');
      }
    } catch (error) {
      this.results.warnings.push(`Dependency check: ${error.message}`);
    }
  }

  /**
   * Documentation validation
   */
  async checkDocumentation() {
    console.log('📚 Checking documentation...');

    const requiredDocs = ['README.md', 'LICENSE.txt'];
    const missingDocs = [];

    requiredDocs.forEach(doc => {
      if (!fs.existsSync(doc)) {
        missingDocs.push(doc);
      }
    });

    if (missingDocs.length > 0) {
      this.results.failures.push(`Missing documentation: ${missingDocs.join(', ')}`);
    } else {
      this.results.passed.push('Required documentation found');
    }
  }

  /**
   * Get files to check by extension
   */
  getFilesToCheck(extensions) {
    const files = [];
    const walk = (dir) => {
      try {
        fs.readdirSync(dir).forEach(file => {
          const fullPath = path.join(dir, file);
          const stat = fs.statSync(fullPath);

          if (stat.isDirectory() && !file.startsWith('.') && file !== 'node_modules') {
            walk(fullPath);
          } else if (stat.isFile() && extensions.some(ext => file.endsWith(ext))) {
            files.push(fullPath);
          }
        });
      } catch (error) {
        // Skip unreadable directories
      }
    };

    walk('.');
    return files;
  }

  /**
   * Generate validation report
   */
  generateReport() {
    console.log('\n' + '='.repeat(50));
    console.log('📋 PRE-DEPLOYMENT VALIDATION REPORT\n');

    console.log(`✅ Passed: ${this.results.passed.length}`);
    this.results.passed.forEach(item => console.log(`   • ${item}`));

    if (this.results.warnings.length > 0) {
      console.log(`\n⚠️  Warnings: ${this.results.warnings.length}`);
      this.results.warnings.forEach(item => console.log(`   • ${item}`));
    }

    if (this.results.failures.length > 0) {
      console.log(`\n❌ Failures: ${this.results.failures.length}`);
      this.results.failures.forEach(item => console.log(`   • ${item}`));
    }

    if (this.results.errors.length > 0) {
      console.log(`\n🔥 Errors: ${this.results.errors.length}`);
      this.results.errors.forEach(item => console.log(`   • ${item}`));
    }

    console.log('\n' + '='.repeat(50));

    const status = this.results.failures.length === 0 && this.results.errors.length === 0
      ? 'READY FOR DEPLOYMENT ✅'
      : 'DEPLOYMENT BLOCKED ❌';

    console.log(`\nStatus: ${status}`);

    return {
      success: this.results.failures.length === 0 && this.results.errors.length === 0,
      results: this.results
    };
  }
}

module.exports = PreDeployValidator;

// CLI Usage
if (require.main === module) {
  const validator = new PreDeployValidator();
  validator.validate().then(report => {
    process.exit(report.success ? 0 : 1);
  });
}
