import { Duration, Stack, StackProps, SymlinkFollowMode } from "aws-cdk-lib";
import { Construct } from "constructs";
import * as lambda from "aws-cdk-lib/aws-lambda";
import * as iam from "aws-cdk-lib/aws-iam";
import * as path from "path";

export class AgentLambdaStack extends Stack {
  constructor(scope: Construct, id: string, props?: StackProps) {
    super(scope, id, props);

    const packagingDirectory = path.join(__dirname, "../packaging");

    const zipDependencies = path.join(packagingDirectory, "dependencies.zip");
    const zipApp = path.join(packagingDirectory, "app.zip");

    // Create a lambda layer with dependencies to keep the code readable in the Lambda console
    const dependenciesLayer = new lambda.LayerVersion(this, "DependenciesLayer", {
      code: lambda.Code.fromAsset(zipDependencies),
      compatibleRuntimes: [lambda.Runtime.PYTHON_3_12],
      description: "Dependencies needed for agent-based lambda",
    });

    // Define the Lambda function
    const weatherFunction = new lambda.Function(this, "AgentLambda", {
      runtime: lambda.Runtime.PYTHON_3_12,
      functionName: "AgentFunction",
      description: "A function that invokes a weather forecasting agent",
      handler: "agent_handler.handler",
      code: lambda.Code.fromAsset(zipApp),

      timeout: Duration.seconds(30),
      memorySize: 128,
      layers: [dependenciesLayer],
      architecture: lambda.Architecture.ARM_64,
    });

    // Add permissions for the Lambda function to invoke Bedrock APIs
    weatherFunction.addToRolePolicy(
      new iam.PolicyStatement({
        actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
        resources: ["*"],
      }),
    );
  }
}
