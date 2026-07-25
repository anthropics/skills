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

"""CLI script template for skills that wrap external APIs.

Copy and adapt this pattern when generating a multi-command CLI script for a
new skill. This follows the same structure as clinvar_api.py and screen_api.py.

Key design decisions:
- Uses argparse with subcommands (one per workflow step).
- All subcommands write output to a JSON file via --output.
- Uses stdlib only (urllib, json, argparse) — no requests, no third-party deps.
- Built-in rate limiting with dedicated RateLimitError and retry logic.
"""

import argparse
import json
import sys
import time
from urllib import error as urllib_error
from urllib import parse as urllib_parse
from urllib import request as urllib_request


class RateLimitError(Exception):
  """Raised when the API rate limit is exceeded."""


class MyAPIClient:
  """Client for the Example API with built-in rate limiting.

  Replace with your actual API. Adapt this class as follows:
  1. Set BASE_URL to your API's base URL.
  2. Set REQUESTS_PER_SECOND to the documented rate limit.
  3. Implement domain-specific query methods.
  """

  BASE_URL = 'https://api.example.com/v1'
  REQUESTS_PER_SECOND = 5

  def __init__(self):
    self.delay = 1.0 / self.REQUESTS_PER_SECOND
    self.last_request_time = 0.0

  def _wait_for_rate_limit(self):
    """Blocks until enough time has passed since the last request."""
    elapsed = time.monotonic() - self.last_request_time
    if elapsed < self.delay:
      time.sleep(self.delay - elapsed)

  def _request(self, path, params=None, retries=3):
    """Makes an HTTP GET request with rate limiting and retry logic.

    Args:
      path: URL path relative to BASE_URL (e.g., '/search').
      params: Optional dict of query parameters.
      retries: Number of retry attempts for transient server errors.

    Returns:
      Parsed JSON response as a Python dict/list.

    Raises:
      RateLimitError: If the server responds with HTTP 429.
      RuntimeError: If the request fails after all retries.
    """
    url = f'{self.BASE_URL}{path}'
    if params:
      url = f'{url}?{urllib_parse.urlencode(params)}'

    for attempt in range(retries):
      self._wait_for_rate_limit()
      try:
        req = urllib_request.Request(url)
        req.add_header('Accept', 'application/json')
        with urllib_request.urlopen(req, timeout=30) as response:
          self.last_request_time = time.monotonic()
          return json.loads(response.read().decode('utf-8'))
      except urllib_error.HTTPError as e:
        self.last_request_time = time.monotonic()
        if e.code == 429:
          # Rate limited — exponential backoff before retry
          wait = 2**attempt
          print(
              f'Rate limited (429), retrying in {wait}s '
              f'(attempt {attempt + 1}/{retries})...',
              file=sys.stderr,
          )
          if attempt == retries - 1:
            raise RateLimitError(
                f'HTTP 429 Too Many Requests from {self.BASE_URL}. '
                f'The API rate limit ({self.REQUESTS_PER_SECOND} req/s) has '
                f'been exceeded after {retries} retries.'
            ) from e
          time.sleep(wait)
          continue
        if e.code >= 500:
          # Transient server error — exponential backoff
          wait = 2**attempt
          print(
              f'Server error {e.code}, retrying in {wait}s '
              f'(attempt {attempt + 1}/{retries})...',
              file=sys.stderr,
          )
          if attempt == retries - 1:
            raise RuntimeError(
                f'Server error {e.code} from {url} after {retries} retries.'
            ) from e
          time.sleep(wait)
          continue
        # Non-retriable client error — read the response body for details
        try:
          body = e.read().decode('utf-8', errors='replace')[:1000]
        except OSError:
          body = e.reason
        raise RuntimeError(f'HTTP {e.code} from {url}: {body}') from e
      except urllib_error.URLError as e:
        if attempt == retries - 1:
          raise RuntimeError(
              f'Failed to connect to {url} after {retries} attempts: {e}'
          ) from e
        time.sleep(2**attempt)

  def search(self, query, limit=100):
    """Example search method. Replace with your API's search endpoint."""
    return self._request('/search', params={'q': query, 'limit': limit})

  def get_details(self, item_id):
    """Example detail method. Replace with your API's detail endpoint."""
    return self._request(f'/items/{item_id}')


def write_output(data, output_file):
  """Writes data to a JSON file.

  Args:
    data: The data to serialize (dict or list).
    output_file: Path to the output file.
  """
  try:
    with open(output_file, 'w', encoding='utf-8') as f:
      json.dump(data, f, indent=2)
    print(f'Success! Data written to: {output_file}')
  except (OSError, TypeError) as e:
    print(f'Error writing to file {output_file}: {e}', file=sys.stderr)
    sys.exit(1)


def main():
  parser = argparse.ArgumentParser(description='Example API Wrapper Script')
  subparsers = parser.add_subparsers(dest='command', required=True)

  # --- Subcommand: search ---
  p_search = subparsers.add_parser(
      'search',
      help='Search for items by query',
  )
  p_search.add_argument(
      '--query',
      required=True,
      help='Search query string',
  )
  p_search.add_argument(
      '--limit',
      type=int,
      required=True,
      help='Maximum number of results to return',
  )
  p_search.add_argument(
      '--output',
      required=True,
      help='Output JSON file path',
  )

  # --- Subcommand: details ---
  p_details = subparsers.add_parser(
      'details',
      help='Get detailed information for a specific item',
  )
  p_details.add_argument(
      '--id',
      required=True,
      dest='item_id',
      help='Item ID to retrieve',
  )
  p_details.add_argument(
      '--output',
      required=True,
      help='Output JSON file path',
  )

  args = parser.parse_args()
  client = MyAPIClient()

  if args.command == 'search':
    data = client.search(args.query, limit=args.limit)
  elif args.command == 'details':
    data = client.get_details(args.item_id)
  else:
    print(f'Unknown command: {args.command}', file=sys.stderr)
    sys.exit(1)

  write_output(data, args.output)


if __name__ == '__main__':
  main()
