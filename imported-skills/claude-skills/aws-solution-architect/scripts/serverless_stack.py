"""
Serverless stack generator for AWS.
Creates CloudFormation/CDK templates for serverless applications.
"""

from typing import Dict, List, Any, Optional


class ServerlessStackGenerator:
    """Generate serverless application stacks."""

    def __init__(self, app_name: str, requirements: Dict[str, Any]):
        """
        Initialize with application requirements.

        Args:
            app_name: Application name (used for resource naming)
            requirements: Dictionary with API, database, auth requirements
        """
        self.app_name = app_name.lower().replace(' ', '-')
        self.requirements = requirements
        self.region = requirements.get('region', 'us-east-1')

    def generate_cloudformation_template(self) -> str:
        """
        Generate CloudFormation template for serverless stack.

        Returns:
            YAML CloudFormation template as string
        """
        template = f"""AWSTemplateFormatVersion: '2010-09-09'
Transform: AWS::Serverless-2016-10-31
Description: Serverless stack for {self.app_name}

Parameters:
  Environment:
    Type: String
    Default: dev
    AllowedValues:
      - dev
      - staging
      - production
    Description: Deployment environment

  CorsAllowedOrigins:
    Type: String
    Default: '*'
    Description: CORS allowed origins for API Gateway

Resources:
  # DynamoDB Table
  {self.app_name.replace('-', '')}Table:
    Type: AWS::DynamoDB::Table
    Properties:
      TableName: !Sub '${{Environment}}-{self.app_name}-data'
      BillingMode: PAY_PER_REQUEST
      AttributeDefinitions:
        - AttributeName: PK
          AttributeType: S
        - AttributeName: SK
          AttributeType: S
      KeySchema:
        - AttributeName: PK
          KeyType: HASH
        - AttributeName: SK
          KeyType: RANGE
      PointInTimeRecoverySpecification:
        PointInTimeRecoveryEnabled: true
      SSESpecification:
        SSEEnabled: true
      StreamSpecification:
        StreamViewType: NEW_AND_OLD_IMAGES
      Tags:
        - Key: Environment
          Value: !Ref Environment
        - Key: Application
          Value: {self.app_name}

  # Lambda Execution Role
  LambdaExecutionRole:
    Type: AWS::IAM::Role
    Properties:
      AssumeRolePolicyDocument:
        Version: '2012-10-17'
        Statement:
          - Effect: Allow
            Principal:
              Service: lambda.amazonaws.com
            Action: sts:AssumeRole
      ManagedPolicyArns:
        - arn:aws:iam::aws:policy/service-role/AWSLambdaBasicExecutionRole
      Policies:
        - PolicyName: DynamoDBAccess
          PolicyDocument:
            Version: '2012-10-17'
            Statement:
              - Effect: Allow
                Action:
                  - dynamodb:GetItem
                  - dynamodb:PutItem
                  - dynamodb:UpdateItem
                  - dynamodb:DeleteItem
                  - dynamodb:Query
                  - dynamodb:Scan
                Resource: !GetAtt {self.app_name.replace('-', '')}Table.Arn

  # Lambda Function
  ApiFunction:
    Type: AWS::Serverless::Function
    Properties:
      FunctionName: !Sub '${{Environment}}-{self.app_name}-api'
      Handler: index.handler
      Runtime: nodejs18.x
      CodeUri: ./src
      MemorySize: 512
      Timeout: 10
      Role: !GetAtt LambdaExecutionRole.Arn
      Environment:
        Variables:
          TABLE_NAME: !Ref {self.app_name.replace('-', '')}Table
          ENVIRONMENT: !Ref Environment
      Events:
        ApiEvent:
          Type: Api
          Properties:
            Path: /{{proxy+}}
            Method: ANY
            RestApiId: !Ref ApiGateway
      Tags:
        Environment: !Ref Environment
        Application: {self.app_name}

  # API Gateway
  ApiGateway:
    Type: AWS::Serverless::Api
    Properties:
      Name: !Sub '${{Environment}}-{self.app_name}-api'
      StageName: !Ref Environment
      Cors:
        AllowMethods: "'GET,POST,PUT,DELETE,OPTIONS'"
        AllowHeaders: "'Content-Type,Authorization,X-Amz-Date,X-Api-Key,X-Amz-Security-Token'"
        AllowOrigin: !Sub "'${{CorsAllowedOrigins}}'"
      Auth:
        DefaultAuthorizer: CognitoAuthorizer
        Authorizers:
          CognitoAuthorizer:
            UserPoolArn: !GetAtt UserPool.Arn
      ThrottleSettings:
        BurstLimit: 200
        RateLimit: 100
      Tags:
        Environment: !Ref Environment
        Application: {self.app_name}

  # Cognito User Pool
  UserPool:
    Type: AWS::Cognito::UserPool
    Properties:
      UserPoolName: !Sub '${{Environment}}-{self.app_name}-users'
      UsernameAttributes:
        - email
      AutoVerifiedAttributes:
        - email
      Policies:
        PasswordPolicy:
          MinimumLength: 8
          RequireUppercase: true
          RequireLowercase: true
          RequireNumbers: true
          RequireSymbols: false
      MfaConfiguration: OPTIONAL
      EnabledMfas:
        - SOFTWARE_TOKEN_MFA
      UserAttributeUpdateSettings:
        AttributesRequireVerificationBeforeUpdate:
          - email
      Schema:
        - Name: email
          Required: true
          Mutable: true

  # Cognito User Pool Client
  UserPoolClient:
    Type: AWS::Cognito::UserPoolClient
    Properties:
      ClientName: !Sub '${{Environment}}-{self.app_name}-client'
      UserPoolId: !Ref UserPool
      GenerateSecret: false
      RefreshTokenValidity: 30
      AccessTokenValidity: 1
      IdTokenValidity: 1
      TokenValidityUnits:
        RefreshToken: days
        AccessToken: hours
        IdToken: hours
      ExplicitAuthFlows:
        - ALLOW_USER_SRP_AUTH
        - ALLOW_REFRESH_TOKEN_AUTH

  # CloudWatch Log Group
  ApiLogGroup:
    Type: AWS::Logs::LogGroup
    Properties:
      LogGroupName: !Sub '/aws/lambda/${{Environment}}-{self.app_name}-api'
      RetentionInDays: 7

Outputs:
  ApiUrl:
    Description: API Gateway endpoint URL
    Value: !Sub 'https://${{ApiGateway}}.execute-api.${{AWS::Region}}.amazonaws.com/${{Environment}}'
    Export:
      Name: !Sub '${{Environment}}-{self.app_name}-ApiUrl'

  UserPoolId:
    Description: Cognito User Pool ID
    Value: !Ref UserPool
    Export:
      Name: !Sub '${{Environment}}-{self.app_name}-UserPoolId'

  UserPoolClientId:
    Description: Cognito User Pool Client ID
    Value: !Ref UserPoolClient
    Export:
      Name: !Sub '${{Environment}}-{self.app_name}-UserPoolClientId'

  TableName:
    Description: DynamoDB Table Name
    Value: !Ref {self.app_name.replace('-', '')}Table
    Export:
      Name: !Sub '${{Environment}}-{self.app_name}-TableName'
"""
        return template

    def generate_cdk_stack(self) -> str:
        """
        Generate AWS CDK stack in TypeScript.

        Returns:
            CDK stack code as string
        """
        stack = f"""import * as cdk from 'aws-cdk-lib';
import * as lambda from 'aws-cdk-lib/aws-lambda';
import * as apigateway from 'aws-cdk-lib/aws-apigateway';
import * as dynamodb from 'aws-cdk-lib/aws-dynamodb';
import * as cognito from 'aws-cdk-lib/aws-cognito';
import {{ Construct }} from 'constructs';

export class {self.app_name.replace('-', '').title()}Stack extends cdk.Stack {{
  constructor(scope: Construct, id: string, props?: cdk.StackProps) {{
    super(scope, id, props);

    // DynamoDB Table
    const table = new dynamodb.Table(this, '{self.app_name}Table', {{
      tableName: `${{cdk.Stack.of(this).stackName}}-data`,
      partitionKey: {{ name: 'PK', type: dynamodb.AttributeType.STRING }},
      sortKey: {{ name: 'SK', type: dynamodb.AttributeType.STRING }},
      billingMode: dynamodb.BillingMode.PAY_PER_REQUEST,
      encryption: dynamodb.TableEncryption.AWS_MANAGED,
      pointInTimeRecovery: true,
      stream: dynamodb.StreamViewType.NEW_AND_OLD_IMAGES,
      removalPolicy: cdk.RemovalPolicy.RETAIN,
    }});

    // Cognito User Pool
    const userPool = new cognito.UserPool(this, '{self.app_name}UserPool', {{
      userPoolName: `${{cdk.Stack.of(this).stackName}}-users`,
      selfSignUpEnabled: true,
      signInAliases: {{ email: true }},
      autoVerify: {{ email: true }},
      passwordPolicy: {{
        minLength: 8,
        requireLowercase: true,
        requireUppercase: true,
        requireDigits: true,
        requireSymbols: false,
      }},
      mfa: cognito.Mfa.OPTIONAL,
      mfaSecondFactor: {{
        sms: false,
        otp: true,
      }},
      removalPolicy: cdk.RemovalPolicy.RETAIN,
    }});

    const userPoolClient = userPool.addClient('{self.app_name}Client', {{
      authFlows: {{
        userSrp: true,
      }},
      accessTokenValidity: cdk.Duration.hours(1),
      refreshTokenValidity: cdk.Duration.days(30),
    }});

    // Lambda Function
    const apiFunction = new lambda.Function(this, '{self.app_name}ApiFunction', {{
      functionName: `${{cdk.Stack.of(this).stackName}}-api`,
      runtime: lambda.Runtime.NODEJS_18_X,
      handler: 'index.handler',
      code: lambda.Code.fromAsset('./src'),
      memorySize: 512,
      timeout: cdk.Duration.seconds(10),
      environment: {{
        TABLE_NAME: table.tableName,
        USER_POOL_ID: userPool.userPoolId,
      }},
      logRetention: 7, // days
    }});

    // Grant Lambda permissions to DynamoDB
    table.grantReadWriteData(apiFunction);

    // API Gateway
    const api = new apigateway.RestApi(this, '{self.app_name}Api', {{
      restApiName: `${{cdk.Stack.of(this).stackName}}-api`,
      description: 'API for {self.app_name}',
      defaultCorsPreflightOptions: {{
        allowOrigins: apigateway.Cors.ALL_ORIGINS,
        allowMethods: apigateway.Cors.ALL_METHODS,
        allowHeaders: ['Content-Type', 'Authorization'],
      }},
      deployOptions: {{
        stageName: 'prod',
        throttlingRateLimit: 100,
        throttlingBurstLimit: 200,
        metricsEnabled: true,
        loggingLevel: apigateway.MethodLoggingLevel.INFO,
      }},
    }});

    // Cognito Authorizer
    const authorizer = new apigateway.CognitoUserPoolsAuthorizer(this, 'ApiAuthorizer', {{
      cognitoUserPools: [userPool],
    }});

    // API Integration
    const integration = new apigateway.LambdaIntegration(apiFunction);

    // Add proxy resource (/{{proxy+}})
    const proxyResource = api.root.addProxy({{
      defaultIntegration: integration,
      anyMethod: true,
      defaultMethodOptions: {{
        authorizer: authorizer,
        authorizationType: apigateway.AuthorizationType.COGNITO,
      }},
    }});

    // Outputs
    new cdk.CfnOutput(this, 'ApiUrl', {{
      value: api.url,
      description: 'API Gateway URL',
    }});

    new cdk.CfnOutput(this, 'UserPoolId', {{
      value: userPool.userPoolId,
      description: 'Cognito User Pool ID',
    }});

    new cdk.CfnOutput(this, 'UserPoolClientId', {{
      value: userPoolClient.userPoolClientId,
      description: 'Cognito User Pool Client ID',
    }});

    new cdk.CfnOutput(this, 'TableName', {{
      value: table.tableName,
      description: 'DynamoDB Table Name',
    }});
  }}
}}
"""
        return stack

    def generate_terraform_configuration(self) -> str:
        """
        Generate Terraform configuration for serverless stack.

        Returns:
            Terraform HCL configuration as string
        """
        terraform = f"""terraform {{
  required_version = ">= 1.0"
  required_providers {{
    aws = {{
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }}
  }}
}}

provider "aws" {{
  region = var.aws_region
}}

variable "aws_region" {{
  description = "AWS region"
  type        = string
  default     = "{self.region}"
}}

variable "environment" {{
  description = "Environment name"
  type        = string
  default     = "dev"
}}

variable "app_name" {{
  description = "Application name"
  type        = string
  default     = "{self.app_name}"
}}

# DynamoDB Table
resource "aws_dynamodb_table" "main" {{
  name           = "${{var.environment}}-${{var.app_name}}-data"
  billing_mode   = "PAY_PER_REQUEST"
  hash_key       = "PK"
  range_key      = "SK"

  attribute {{
    name = "PK"
    type = "S"
  }}

  attribute {{
    name = "SK"
    type = "S"
  }}

  server_side_encryption {{
    enabled = true
  }}

  point_in_time_recovery {{
    enabled = true
  }}

  stream_enabled   = true
  stream_view_type = "NEW_AND_OLD_IMAGES"

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

# Cognito User Pool
resource "aws_cognito_user_pool" "main" {{
  name = "${{var.environment}}-${{var.app_name}}-users"

  username_attributes = ["email"]
  auto_verified_attributes = ["email"]

  password_policy {{
    minimum_length    = 8
    require_lowercase = true
    require_numbers   = true
    require_uppercase = true
    require_symbols   = false
  }}

  mfa_configuration = "OPTIONAL"

  software_token_mfa_configuration {{
    enabled = true
  }}

  schema {{
    name                = "email"
    attribute_data_type = "String"
    required            = true
    mutable             = true
  }}

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

resource "aws_cognito_user_pool_client" "main" {{
  name         = "${{var.environment}}-${{var.app_name}}-client"
  user_pool_id = aws_cognito_user_pool.main.id

  generate_secret = false

  explicit_auth_flows = [
    "ALLOW_USER_SRP_AUTH",
    "ALLOW_REFRESH_TOKEN_AUTH"
  ]

  refresh_token_validity = 30
  access_token_validity  = 1
  id_token_validity      = 1

  token_validity_units {{
    refresh_token = "days"
    access_token  = "hours"
    id_token      = "hours"
  }}
}}

# IAM Role for Lambda
resource "aws_iam_role" "lambda" {{
  name = "${{var.environment}}-${{var.app_name}}-lambda-role"

  assume_role_policy = jsonencode({{
    Version = "2012-10-17"
    Statement = [{{
      Action = "sts:AssumeRole"
      Effect = "Allow"
      Principal = {{
        Service = "lambda.amazonaws.com"
      }}
    }}]
  }})

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

resource "aws_iam_role_policy_attachment" "lambda_basic" {{
  role       = aws_iam_role.lambda.name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AWSLambdaBasicExecutionRole"
}}

resource "aws_iam_role_policy" "dynamodb" {{
  name = "dynamodb-access"
  role = aws_iam_role.lambda.id

  policy = jsonencode({{
    Version = "2012-10-17"
    Statement = [{{
      Effect = "Allow"
      Action = [
        "dynamodb:GetItem",
        "dynamodb:PutItem",
        "dynamodb:UpdateItem",
        "dynamodb:DeleteItem",
        "dynamodb:Query",
        "dynamodb:Scan"
      ]
      Resource = aws_dynamodb_table.main.arn
    }}]
  }})
}}

# Lambda Function
resource "aws_lambda_function" "api" {{
  filename      = "lambda.zip"
  function_name = "${{var.environment}}-${{var.app_name}}-api"
  role          = aws_iam_role.lambda.arn
  handler       = "index.handler"
  runtime       = "nodejs18.x"
  memory_size   = 512
  timeout       = 10

  environment {{
    variables = {{
      TABLE_NAME   = aws_dynamodb_table.main.name
      USER_POOL_ID = aws_cognito_user_pool.main.id
      ENVIRONMENT  = var.environment
    }}
  }}

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

# CloudWatch Log Group
resource "aws_cloudwatch_log_group" "lambda" {{
  name              = "/aws/lambda/${{aws_lambda_function.api.function_name}}"
  retention_in_days = 7

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

# API Gateway
resource "aws_api_gateway_rest_api" "main" {{
  name        = "${{var.environment}}-${{var.app_name}}-api"
  description = "API for ${{var.app_name}}"

  tags = {{
    Environment = var.environment
    Application = var.app_name
  }}
}}

resource "aws_api_gateway_authorizer" "cognito" {{
  name          = "cognito-authorizer"
  rest_api_id   = aws_api_gateway_rest_api.main.id
  type          = "COGNITO_USER_POOLS"
  provider_arns = [aws_cognito_user_pool.main.arn]
}}

resource "aws_api_gateway_resource" "proxy" {{
  rest_api_id = aws_api_gateway_rest_api.main.id
  parent_id   = aws_api_gateway_rest_api.main.root_resource_id
  path_part   = "{{proxy+}}"
}}

resource "aws_api_gateway_method" "proxy" {{
  rest_api_id   = aws_api_gateway_rest_api.main.id
  resource_id   = aws_api_gateway_resource.proxy.id
  http_method   = "ANY"
  authorization = "COGNITO_USER_POOLS"
  authorizer_id = aws_api_gateway_authorizer.cognito.id
}}

resource "aws_api_gateway_integration" "lambda" {{
  rest_api_id = aws_api_gateway_rest_api.main.id
  resource_id = aws_api_gateway_resource.proxy.id
  http_method = aws_api_gateway_method.proxy.http_method

  integration_http_method = "POST"
  type                    = "AWS_PROXY"
  uri                     = aws_lambda_function.api.invoke_arn
}}

resource "aws_lambda_permission" "apigw" {{
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.api.function_name
  principal     = "apigateway.amazonaws.com"
  source_arn    = "${{aws_api_gateway_rest_api.main.execution_arn}}/*/*"
}}

resource "aws_api_gateway_deployment" "main" {{
  depends_on = [
    aws_api_gateway_integration.lambda
  ]

  rest_api_id = aws_api_gateway_rest_api.main.id
  stage_name  = var.environment
}}

# Outputs
output "api_url" {{
  description = "API Gateway URL"
  value       = aws_api_gateway_deployment.main.invoke_url
}}

output "user_pool_id" {{
  description = "Cognito User Pool ID"
  value       = aws_cognito_user_pool.main.id
}}

output "user_pool_client_id" {{
  description = "Cognito User Pool Client ID"
  value       = aws_cognito_user_pool_client.main.id
}}

output "table_name" {{
  description = "DynamoDB Table Name"
  value       = aws_dynamodb_table.main.name
}}
"""
        return terraform
