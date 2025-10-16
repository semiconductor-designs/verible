# VeriPG Validator CI/CD Integration Guide

**Version 5.0.0** | Complete guide to integrating VeriPG Validator into your CI/CD pipeline

## Table of Contents

1. [Overview](#overview)
2. [GitHub Actions](#github-actions)
3. [GitLab CI](#gitlab-ci)
4. [Jenkins](#jenkins)
5. [Azure Pipelines](#azure-pipelines)
6. [Pre-Commit Hooks](#pre-commit-hooks)
7. [Make Integration](#make-integration)
8. [Docker Integration](#docker-integration)
9. [Best Practices](#best-practices)

---

## Overview

Integrating VeriPG Validator into your CI/CD pipeline ensures consistent code quality and catches violations early in the development cycle.

### Integration Benefits

- **Automated validation** on every commit/PR
- **Consistent enforcement** of coding standards
- **Early detection** of CDC, timing, and design issues
- **Code review automation** with inline comments
- **Quality metrics** tracking over time
- **Blocking builds** on critical violations

### Integration Approaches

1. **Advisory**: Report violations but don't block
2. **Warning**: Block on errors, allow warnings
3. **Strict**: Block on any violation

---

## GitHub Actions

### Basic Integration

Create `.github/workflows/veripg.yml`:

```yaml
name: VeriPG Validation

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  veripg-validate:
    runs-on: ubuntu-latest
    
    steps:
    - name: Checkout code
      uses: actions/checkout@v3
    
    - name: Download Verible
      run: |
        wget https://github.com/chipsalliance/verible/releases/download/v0.0-3428-gcfcbb82b/verible-v0.0-3428-gcfcbb82b-Ubuntu-22.04-jammy-x86_64.tar.gz
        tar -xzf verible-*.tar.gz
        echo "$PWD/verible-v0.0-3428-gcfcbb82b/bin" >> $GITHUB_PATH
    
    - name: Run VeriPG Validator
      run: |
        veripg-validator \
          --format=text \
          --config=.veripg.yml \
          rtl/**/*.sv
```

### SARIF Integration with Code Scanning

Upload results to GitHub Code Scanning:

```yaml
    - name: Run VeriPG Validator (SARIF)
      run: |
        veripg-validator \
          --format=sarif \
          --output=veripg-results.sarif \
          --config=.veripg.yml \
          rtl/**/*.sv
      continue-on-error: true
    
    - name: Upload SARIF results
      uses: github/codeql-action/upload-sarif@v2
      if: always()
      with:
        sarif_file: veripg-results.sarif
```

### PR Comments

Add inline comments to pull requests:

```yaml
    - name: Run VeriPG Validator (JSON)
      id: veripg
      run: |
        veripg-validator \
          --format=json \
          --output=veripg.json \
          rtl/**/*.sv || true
    
    - name: Comment on PR
      uses: actions/github-script@v6
      if: github.event_name == 'pull_request'
      with:
        script: |
          const fs = require('fs');
          const results = JSON.parse(fs.readFileSync('veripg.json', 'utf8'));
          
          let comment = '## VeriPG Validation Results\n\n';
          comment += `**Total Violations:** ${results.total_violations}\n`;
          comment += `- Errors: ${results.errors}\n`;
          comment += `- Warnings: ${results.warnings}\n\n`;
          
          if (results.violations.length > 0) {
            comment += '### Violations:\n\n';
            results.violations.forEach(v => {
              comment += `- **${v.rule}** (${v.severity}): ${v.message}\n`;
              comment += `  File: ${v.location}\n\n`;
            });
          }
          
          github.rest.issues.createComment({
            issue_number: context.issue.number,
            owner: context.repo.owner,
            repo: context.repo.name,
            body: comment
          });
```

### Block on Errors

```yaml
    - name: Check for errors
      run: |
        if grep -q '"severity": "error"' veripg.json; then
          echo "❌ VeriPG validation found errors"
          exit 1
        else
          echo "✅ VeriPG validation passed"
        fi
```

### Complete Example

See: [`verible/verilog/tools/veripg/ci/github-actions-example.yml`](../verible/verilog/tools/veripg/ci/github-actions-example.yml)

---

## GitLab CI

### Basic Integration

Create `.gitlab-ci.yml`:

```yaml
stages:
  - validate

veripg-validation:
  stage: validate
  image: ubuntu:22.04
  
  before_script:
    - apt-get update && apt-get install -y wget tar
    - wget https://github.com/chipsalliance/verible/releases/download/v0.0-3428-gcfcbb82b/verible-v0.0-3428-gcfcbb82b-Ubuntu-22.04-jammy-x86_64.tar.gz
    - tar -xzf verible-*.tar.gz
    - export PATH="$PWD/verible-v0.0-3428-gcfcbb82b/bin:$PATH"
  
  script:
    - veripg-validator --format=text --config=.veripg.yml rtl/**/*.sv
  
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
    - if: '$CI_COMMIT_BRANCH == "main"'
```

### Code Quality Report

Generate GitLab Code Quality report:

```yaml
veripg-validation:
  stage: validate
  script:
    - veripg-validator --format=json --output=veripg.json rtl/**/*.sv || true
    - python3 convert_to_codequality.py veripg.json > codequality.json
  
  artifacts:
    reports:
      codequality: codequality.json
    paths:
      - veripg.json
    when: always
```

`convert_to_codequality.py`:
```python
import json
import sys

with open(sys.argv[1]) as f:
    veripg_results = json.load(f)

codequality = []
for violation in veripg_results['violations']:
    location = violation['location'].split(':')
    codequality.append({
        "description": f"{violation['rule']}: {violation['message']}",
        "severity": violation['severity'],
        "location": {
            "path": location[0],
            "lines": {
                "begin": int(location[1]) if len(location) > 1 else 1
            }
        }
    })

print(json.dumps(codequality, indent=2))
```

### Complete Example

See: [`verible/verilog/tools/veripg/ci/gitlab-ci-example.yml`](../verible/verilog/tools/veripg/ci/gitlab-ci-example.yml)

---

## Jenkins

### Jenkinsfile (Declarative Pipeline)

```groovy
pipeline {
    agent any
    
    environment {
        VERIBLE_VERSION = 'v0.0-3428-gcfcbb82b'
        VERIBLE_URL = "https://github.com/chipsalliance/verible/releases/download/${VERIBLE_VERSION}/verible-${VERIBLE_VERSION}-Ubuntu-22.04-jammy-x86_64.tar.gz"
    }
    
    stages {
        stage('Setup Verible') {
            steps {
                sh '''
                    wget ${VERIBLE_URL}
                    tar -xzf verible-*.tar.gz
                    export PATH="$PWD/verible-${VERIBLE_VERSION}/bin:$PATH"
                    veripg-validator --version
                '''
            }
        }
        
        stage('VeriPG Validation') {
            steps {
                sh '''
                    export PATH="$PWD/verible-${VERIBLE_VERSION}/bin:$PATH"
                    veripg-validator \
                        --format=text \
                        --output=veripg-results.txt \
                        --config=.veripg.yml \
                        rtl/**/*.sv
                '''
            }
        }
        
        stage('Publish Results') {
            steps {
                archiveArtifacts artifacts: 'veripg-results.txt', fingerprint: true
                
                script {
                    def violations = sh(
                        script: 'grep -c "ERROR" veripg-results.txt || true',
                        returnStdout: true
                    ).trim()
                    
                    if (violations.toInteger() > 0) {
                        error("VeriPG found ${violations} errors")
                    }
                }
            }
        }
    }
    
    post {
        always {
            publishHTML([
                allowMissing: false,
                alwaysLinkToLastBuild: true,
                keepAll: true,
                reportDir: '.',
                reportFiles: 'veripg-results.txt',
                reportName: 'VeriPG Validation Report'
            ])
        }
    }
}
```

### Complete Example

See: [`verible/verilog/tools/veripg/ci/jenkins-example.groovy`](../verible/verilog/tools/veripg/ci/jenkins-example.groovy)

---

## Azure Pipelines

### azure-pipelines.yml

```yaml
trigger:
  branches:
    include:
    - main
    - develop

pool:
  vmImage: 'ubuntu-latest'

steps:
- task: Bash@3
  displayName: 'Download Verible'
  inputs:
    targetType: 'inline'
    script: |
      wget https://github.com/chipsalliance/verible/releases/download/v0.0-3428-gcfcbb82b/verible-v0.0-3428-gcfcbb82b-Ubuntu-22.04-jammy-x86_64.tar.gz
      tar -xzf verible-*.tar.gz
      echo "##vso[task.prependpath]$(pwd)/verible-v0.0-3428-gcfcbb82b/bin"

- task: Bash@3
  displayName: 'Run VeriPG Validator'
  inputs:
    targetType: 'inline'
    script: |
      veripg-validator \
        --format=json \
        --output=$(Build.ArtifactStagingDirectory)/veripg.json \
        --config=.veripg.yml \
        rtl/**/*.sv

- task: PublishBuildArtifacts@1
  displayName: 'Publish Results'
  inputs:
    PathtoPublish: '$(Build.ArtifactStagingDirectory)'
    ArtifactName: 'veripg-results'

- task: Bash@3
  displayName: 'Check for Errors'
  inputs:
    targetType: 'inline'
    script: |
      if grep -q '"severity": "error"' $(Build.ArtifactStagingDirectory)/veripg.json; then
        echo "##vso[task.logissue type=error]VeriPG validation found errors"
        exit 1
      fi
```

---

## Pre-Commit Hooks

### Git Pre-Commit Hook

`.git/hooks/pre-commit`:

```bash
#!/bin/bash

# Get list of staged SystemVerilog files
FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\.sv$')

if [ -z "$FILES" ]; then
  exit 0
fi

echo "Running VeriPG Validator on staged files..."

# Run validator
veripg-validator --format=text --config=.veripg.yml $FILES

RESULT=$?

if [ $RESULT -ne 0 ]; then
  echo ""
  echo "❌ VeriPG validation failed!"
  echo "Fix violations or use 'git commit --no-verify' to skip"
  exit 1
fi

echo "✅ VeriPG validation passed"
exit 0
```

Make executable:
```bash
chmod +x .git/hooks/pre-commit
```

### Pre-Commit Framework

`.pre-commit-config.yaml`:

```yaml
repos:
  - repo: local
    hooks:
      - id: veripg-validator
        name: VeriPG Validator
        entry: veripg-validator
        language: system
        args: ['--format=text', '--config=.veripg.yml']
        files: \.sv$
```

Install:
```bash
pip install pre-commit
pre-commit install
```

---

## Make Integration

### Makefile

```makefile
# VeriPG Validator Integration

VERIPG := veripg-validator
VERIPG_CONFIG := .veripg.yml
SV_FILES := $(shell find rtl -name '*.sv')

.PHONY: validate validate-strict validate-report

# Standard validation
validate:
	@echo "Running VeriPG validation..."
	$(VERIPG) --config=$(VERIPG_CONFIG) $(SV_FILES)

# Strict validation (fail on any violation)
validate-strict:
	@echo "Running strict VeriPG validation..."
	$(VERIPG) --config=$(VERIPG_CONFIG) --severity=info $(SV_FILES)

# Generate detailed report
validate-report:
	@echo "Generating VeriPG validation report..."
	$(VERIPG) \
		--format=json \
		--output=reports/veripg-report.json \
		--config=$(VERIPG_CONFIG) \
		$(SV_FILES)
	@echo "Report generated: reports/veripg-report.json"

# Batch validation with progress
validate-batch:
	@echo "Running batch validation..."
	$(VERIPG) \
		--batch \
		--parallel=8 \
		--format=text \
		--output=reports/veripg-batch.txt \
		--config=$(VERIPG_CONFIG) \
		$(SV_FILES)

# Integration with build
all: validate build

build: validate
	@echo "Building design..."
	# Your build commands here
```

---

## Docker Integration

### Dockerfile

```dockerfile
FROM ubuntu:22.04

# Install dependencies
RUN apt-get update && apt-get install -y \
    wget \
    tar \
    && rm -rf /var/lib/apt/lists/*

# Install Verible
RUN wget https://github.com/chipsalliance/verible/releases/download/v0.0-3428-gcfcbb82b/verible-v0.0-3428-gcfcbb82b-Ubuntu-22.04-jammy-x86_64.tar.gz \
    && tar -xzf verible-*.tar.gz \
    && mv verible-v0.0-3428-gcfcbb82b /opt/verible \
    && rm verible-*.tar.gz

ENV PATH="/opt/verible/bin:${PATH}"

# Set working directory
WORKDIR /workspace

# Default command
CMD ["veripg-validator", "--help"]
```

Build and use:
```bash
# Build image
docker build -t veripg-validator .

# Run validation
docker run --rm -v $(pwd):/workspace veripg-validator \
  veripg-validator --config=.veripg.yml rtl/**/*.sv
```

### Docker Compose

`docker-compose.yml`:

```yaml
version: '3.8'

services:
  veripg-validator:
    image: veripg-validator:latest
    volumes:
      - ./:/workspace
    command: veripg-validator --config=.veripg.yml rtl/**/*.sv
```

Run:
```bash
docker-compose run veripg-validator
```

---

## Best Practices

### 1. Configuration Management

- **Version control config**: Commit `.veripg.yml` to repository
- **Consistent across environments**: Same config in local/CI
- **Team agreement**: Discuss and agree on rule enablement
- **Gradual adoption**: Start lenient, tighten over time

### 2. CI/CD Strategy

**Advisory Mode** (Week 1-2):
```yaml
# Report violations, don't block
continue-on-error: true
```

**Warning Mode** (Week 3-4):
```yaml
# Block on errors only
--severity=error
```

**Strict Mode** (Week 5+):
```yaml
# Block on any violation
--severity=info
exit 1 if any violations
```

### 3. Performance Optimization

```yaml
# Cache Verible download
- uses: actions/cache@v3
  with:
    path: verible-*/
    key: verible-${{ env.VERIBLE_VERSION }}

# Parallel validation
--parallel=8 --batch

# Validate only changed files
git diff --name-only origin/main...HEAD | grep '\.sv$'
```

### 4. Reporting and Metrics

```yaml
# Track violations over time
- name: Record metrics
  run: |
    VIOLATIONS=$(jq '.total_violations' veripg.json)
    echo "veripg_violations ${VIOLATIONS}" >> metrics.txt
    
# Upload to monitoring system
curl -X POST monitoring-system/metrics -d @metrics.txt
```

### 5. Integration with Other Tools

```makefile
# Run multiple checks
ci: lint validate cdc-check synth

lint:
	verible-verilog-lint $(SV_FILES)

validate:
	veripg-validator --config=.veripg.yml $(SV_FILES)

cdc-check:
	spyglass -cdc design.sv

synth:
	yosys -p "synth_ecp5" design.sv
```

---

## Troubleshooting

### CI Timeout

**Problem:** Validation takes too long in CI

**Solutions:**
```yaml
# 1. Validate only changed files
git diff --name-only origin/main...HEAD | grep '\.sv$' | xargs veripg-validator

# 2. Use caching
cache_enabled: true

# 3. Parallel processing
--parallel=8

# 4. Split into multiple jobs
validate-frontend:
  script: veripg-validator rtl/frontend/**/*.sv
validate-backend:
  script: veripg-validator rtl/backend/**/*.sv
```

### False Positives Blocking CI

**Problem:** Known false positives blocking merges

**Solutions:**
```yaml
# 1. Exclude specific files
exclusions:
  - "rtl/legacy/known_issue.sv"

# 2. Disable specific rules temporarily
rules:
  NAM_001:
    enabled: false  # TODO: Re-enable after cleanup

# 3. Use advisory mode for specific rules
rules:
  STR_002:
    severity: info  # Don't block on complexity
```

### Cache Issues

**Problem:** Cached results causing issues

**Solution:**
```bash
# Clear cache in CI
- name: Clear cache
  run: rm -rf .veripg_cache

# Or disable caching
cache:
  enabled: false
```

---

## Example Workflows

### Minimal (Start Here)

```yaml
# .github/workflows/veripg-minimal.yml
name: VeriPG
on: [push, pull_request]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    - name: Setup Verible
      run: |
        wget https://github.com/chipsalliance/verible/releases/download/v0.0-3428-gcfcbb82b/verible-v0.0-3428-gcfcbb82b-Ubuntu-22.04-jammy-x86_64.tar.gz
        tar -xzf verible-*.tar.gz
        echo "$PWD/verible-v0.0-3428-gcfcbb82b/bin" >> $GITHUB_PATH
    - name: Validate
      run: veripg-validator rtl/**/*.sv
```

### Production-Ready

See complete examples in:
- [`ci/github-actions-example.yml`](../verible/verilog/tools/veripg/ci/github-actions-example.yml)
- [`ci/gitlab-ci-example.yml`](../verible/verilog/tools/veripg/ci/gitlab-ci-example.yml)
- [`ci/jenkins-example.groovy`](../verible/verilog/tools/veripg/ci/jenkins-example.groovy)

---

For more information:
- [User Guide](./veripg-validator-user-guide.md)
- [Rules Reference](./veripg-validator-rules-reference.md)
- [Configuration Guide](./veripg-validator-config-guide.md)
- [Auto-Fix Guide](./veripg-validator-autofix-guide.md)

