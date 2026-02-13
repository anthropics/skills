import { Stack, StackProps } from "aws-cdk-lib";
import { Construct } from "constructs";
import * as apprunner from "aws-cdk-lib/aws-apprunner";
import * as iam from "aws-cdk-lib/aws-iam";
import * as ecr_assets from "aws-cdk-lib/aws-ecr-assets";
import * as path from "path";

export class AgentAppRunnerStack extends Stack {
  constructor(scope: Construct, id: string, props?: StackProps) {
    super(scope, id, props);

    // Create IAM role for App Runner instance
    const instanceRole = new iam.Role(this, "AppRunnerInstanceRole", {
      assumedBy: new iam.ServicePrincipal("tasks.apprunner.amazonaws.com"),
    });

    // Add Bedrock permissions
    instanceRole.addToPolicy(
      new iam.PolicyStatement({
        actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
        resources: ["*"],
      })
    );

    // Create IAM role for App Runner to access ECR
    const accessRole = new iam.Role(this, "AppRunnerAccessRole", {
      assumedBy: new iam.ServicePrincipal("build.apprunner.amazonaws.com"),
      managedPolicies: [
        iam.ManagedPolicy.fromAwsManagedPolicyName(
          "service-role/AWSAppRunnerServicePolicyForECRAccess"
        ),
      ],
    });

    // Build Docker image for x86_64 (App Runner requirement)
    const dockerAsset = new ecr_assets.DockerImageAsset(this, "AppRunnerImage", {
      directory: path.join(__dirname, "../docker"),
      platform: ecr_assets.Platform.LINUX_AMD64, // App Runner requires x86_64
    });

    // Grant App Runner access to pull the image
    dockerAsset.repository.grantPull(accessRole);

    // Create App Runner service
    const service = new apprunner.CfnService(this, "AgentAppRunnerService", {
      serviceName: "agent-service",
      sourceConfiguration: {
        authenticationConfiguration: {
          accessRoleArn: accessRole.roleArn,
        },
        imageRepository: {
          imageIdentifier: dockerAsset.imageUri,
          imageRepositoryType: "ECR",
          imageConfiguration: {
            port: "8000",
            runtimeEnvironmentVariables: [
              {
                name: "LOG_LEVEL",
                value: "INFO",
              },
            ],
          },
        },
      },
      instanceConfiguration: {
        cpu: "1 vCPU",
        memory: "2 GB",
        instanceRoleArn: instanceRole.roleArn,
      },
      healthCheckConfiguration: {
        protocol: "HTTP",
        path: "/health",
        interval: 10,
        timeout: 5,
        healthyThreshold: 1,
        unhealthyThreshold: 5,
      },
    });

    // Output the service URL
    this.exportValue(service.attrServiceUrl, {
      name: "AppRunnerServiceUrl",
      description: "The URL of the App Runner service",
    });
  }
}
