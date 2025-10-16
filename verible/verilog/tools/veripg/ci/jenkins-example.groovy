// Example Jenkinsfile for VeriPG Validator
// Copyright 2017-2025 The Verible Authors.

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
                        --config=.veripg.yml \
                        --output=veripg-results.txt \
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

