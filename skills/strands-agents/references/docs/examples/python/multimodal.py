from strands import Agent, tool
from strands_tools import generate_image, image_reader


artist = Agent(tools=[generate_image], system_prompt=(
    "You will be instructed to generate a number of images of a given subject. Vary the prompt for each generated image to create a variety of options. "
    "Your final output must contain ONLY a comma-separated list of the filesystem paths of generated images."
))



critic = Agent(tools=[image_reader], system_prompt=(
    "You will be provided with a list of filesystem paths, each containing an image. "
    "Describe each image, and then choose which one is best. "
    "Your final line of output must be as follows: "
    "FINAL DECISION: <path to final decision image>"
))

result = artist("Generate 3 images of a dog")
critic(str(result))