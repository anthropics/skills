#!/bin/bash
# Create new ml-gradle project with boilerplate
# Usage: ./scripts/new-project.sh <project-name>

set -e

if [ -z "$1" ]; then
  echo "Usage: $0 <project-name>"
  echo "Example: $0 my-marklogic-app"
  exit 1
fi

PROJECT_NAME="$1"

echo "🚀 Creating new ml-gradle project: $PROJECT_NAME"
echo "=================================================="

# Create project using gradle
gradle mlNewProject -PprojectName="$PROJECT_NAME"

cd "$PROJECT_NAME"

echo ""
echo "✅ Project created: $PROJECT_NAME"
echo ""
echo "📝 Next steps:"
echo "1. cd $PROJECT_NAME"
echo "2. Edit gradle.properties (set mlHost, mlRestPort, etc.)"
echo "3. Run 'gradle mlDeploy' to deploy your application"
echo ""
echo "📖 See ml-gradle skill documentation for more details"
