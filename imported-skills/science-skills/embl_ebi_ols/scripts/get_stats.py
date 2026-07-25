# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Retrieves statistics from the EMBL-EBI Ontology Lookup Service.

This script fetches index statistics from the OLS4 v2 stats API,
including counts of ontologies, classes, properties, and individuals.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import ols_utils


def get_stats(args: argparse.Namespace):
  """Fetches and writes OLS index statistics.

  This function calls the OLS4 v2 stats API, parses the JSON response,
  and writes the extracted statistics to an output file or stdout.

  Args:
    args: An argparse.Namespace object containing command-line arguments,
      including the 'output' file path.
  """
  url = "https://www.ebi.ac.uk/ols4/api/v2/stats"
  data = ols_utils.CLIENT.fetch_json(url)

  stats = {
      "numberOfOntologies": data.get("numberOfOntologies", 0),
      "numberOfClasses": data.get("numberOfClasses", 0),
      "numberOfProperties": data.get("numberOfProperties", 0),
      "numberOfIndividuals": data.get("numberOfIndividuals", 0),
      "lastModified": data.get("lastModified", ""),
  }

  ols_utils.write_output(
      {"status": "success", "statistics": stats}, args.output
  )


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(description="Get OLS index statistics")
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  get_stats(main_args)
