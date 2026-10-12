import { Stack, StackProps, CfnOutput } from "aws-cdk-lib";
import { Construct } from "constructs";
import * as ec2 from "aws-cdk-lib/aws-ec2";
import * as iam from "aws-cdk-lib/aws-iam";
import * as path from "path";
import { Asset } from "aws-cdk-lib/aws-s3-assets";

export class AgentEC2Stack extends Stack {
  constructor(scope: Construct, id: string, props?: StackProps) {
    super(scope, id, props);

    // Create a simple VPC for our EC2 instance
    const vpc = new ec2.Vpc(this, "AgentVpc", {
      maxAzs: 1, // Use just 1 Availability Zone for simplicity
      natGateways: 0, // No NAT Gateway needed since we'll use a public subnet
    });

    // Upload the application code to S3
    const appAsset = new Asset(this, "AgentAppAsset", {
      path: path.join(__dirname, "../app"),
    });

    // Upload dependencies to S3
    // This could also be replaced by a pip install if all dependencies are public
    const dependenciesAsset = new Asset(this, "AgentDependenciesAsset", {
      path: path.join(__dirname, "../packaging/_dependencies"),
    });

    // Create a role for the EC2 instance
    const instanceRole = new iam.Role(this, "AgentInstanceRole", {
      assumedBy: new iam.ServicePrincipal("ec2.amazonaws.com"),
    });

    // Add permissions for the instance to access S3 and invoke Bedrock APIs
    instanceRole.addManagedPolicy(iam.ManagedPolicy.fromAwsManagedPolicyName("AmazonS3ReadOnlyAccess"));

    instanceRole.addToPolicy(
      new iam.PolicyStatement({
        actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
        resources: ["*"],
      }),
    );

    // Create a security group for the EC2 instance
    const instanceSG = new ec2.SecurityGroup(this, "AgentInstanceSG", {
      vpc,
      description: "Security group for Agent EC2 Instance",
      allowAllOutbound: true,
    });

    // Uncomment the following line to enable SSH access to the instance
    // instanceSG.addIngressRule(ec2.Peer.anyIpv4(), ec2.Port.tcp(22), "Allow SSH access");

    // Allow inbound traffic on port 8000 for direct access to the application
    instanceSG.addIngressRule(ec2.Peer.anyIpv4(), ec2.Port.tcp(8000), "Allow inbound traffic on port 8000");

    // Create an EC2 instance in a public subnet with a public IP
    const instance = new ec2.Instance(this, "AgentInstance", {
      vpc,
      vpcSubnets: { subnetType: ec2.SubnetType.PUBLIC }, // Use public subnet
      instanceType: ec2.InstanceType.of(ec2.InstanceClass.T4G, ec2.InstanceSize.MEDIUM), // ARM-based instance
      machineImage: ec2.MachineImage.latestAmazonLinux2023({
        cpuType: ec2.AmazonLinuxCpuType.ARM_64,
      }),
      securityGroup: instanceSG,
      role: instanceRole,
      associatePublicIpAddress: true, // Assign a public IP address
    });

    // Create user data script to set up the application
    const userData = ec2.UserData.forLinux();
    userData.addCommands(
      "#!/bin/bash",
      "set -o verbose",
      "yum update -y",
      "yum install -y python3.12 python3.12-pip git unzip ec2-instance-connect",

      // Create app directory
      "mkdir -p /opt/agent-app",

      // Download application files from S3
      `aws s3 cp ${appAsset.s3ObjectUrl} /tmp/app.zip`,
      `aws s3 cp ${dependenciesAsset.s3ObjectUrl} /tmp/dependencies.zip`,

      // Extract application files
      "unzip /tmp/app.zip -d /opt/agent-app",
      "unzip /tmp/dependencies.zip -d /opt/agent-app/_dependencies",

      // Create a systemd service file
      "cat > /etc/systemd/system/agent-app.service << 'EOL'",
      "[Unit]",
      "Description=Weather Agent Application",
      "After=network.target",
      "",
      "[Service]",
      "User=ec2-user",
      "WorkingDirectory=/opt/agent-app",
      "ExecStart=/usr/bin/python3.12 -m uvicorn app:app --host=0.0.0.0 --port=8000 --workers=2",
      "Restart=always",
      "Environment=PYTHONPATH=/opt/agent-app:/opt/agent-app/_dependencies",
      "Environment=LOG_LEVEL=INFO",
      "",
      "[Install]",
      "WantedBy=multi-user.target",
      "EOL",

      // Enable and start the service
      "systemctl enable agent-app.service",
      "systemctl start agent-app.service",
    );

    instance.addUserData(userData.render());

    // Grant the instance role access to the S3 assets
    appAsset.grantRead(instanceRole);
    dependenciesAsset.grantRead(instanceRole);

    // Add outputs for easy access
    new CfnOutput(this, "InstanceId", {
      value: instance.instanceId,
      description: "The ID of the EC2 instance",
    });

    new CfnOutput(this, "InstancePublicIP", {
      value: instance.instancePublicIp,
      description: "The public IP address of the EC2 instance",
    });

    new CfnOutput(this, "ServiceEndpoint", {
      value: `${instance.instancePublicIp}:8000`,
      description: "The endpoint URL for the weather service",
      exportName: "Ec2ServiceEndpoint",
    });

    new CfnOutput(this, "EC2ConnectCommand", {
      value: `aws ec2-instance-connect ssh --instance-id ${instance.instanceId}`,
      description: "Command to connect to the instance using EC2 Instance Connect",
    });
  }
}
