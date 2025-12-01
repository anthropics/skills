/**
 * Deal Machine API Client
 * Handles all API communication with Deal Machine
 */

import axios, { AxiosInstance, AxiosError } from 'axios';
import { HttpsProxyAgent } from 'https-proxy-agent';
import type { Lead, DealMachineAPIResponse } from './types.js';

const API_BASE_URL = 'https://api.dealmachine.com/public/v1';
const RATE_LIMIT_PER_SECOND = 10;
const RATE_LIMIT_PER_DAY = 5000;

export class DealMachineAPIClient {
  private client: AxiosInstance;
  private requestCount: number = 0;
  private dailyRequestCount: number = 0;
  private lastResetTime: number = Date.now();

  constructor(apiKey: string) {
    if (!apiKey) {
      throw new Error('Deal Machine API key is required');
    }

    // Configure proxy if environment variable is set
    const proxyUrl = process.env.HTTPS_PROXY || process.env.https_proxy || process.env.HTTP_PROXY || process.env.http_proxy;
    const httpsAgent = proxyUrl ? new HttpsProxyAgent(proxyUrl) : undefined;

    this.client = axios.create({
      baseURL: API_BASE_URL,
      headers: {
        'Authorization': `Bearer ${apiKey}`,
        'Content-Type': 'application/json',
        'Accept': 'application/json',
      },
      timeout: 30000,
      httpsAgent,
      proxy: false, // Disable axios default proxy handling
    });

    // Reset rate limit counter every second
    setInterval(() => {
      this.requestCount = 0;
    }, 1000);

    // Reset daily counter every 24 hours
    setInterval(() => {
      this.dailyRequestCount = 0;
      this.lastResetTime = Date.now();
    }, 24 * 60 * 60 * 1000);
  }

  /**
   * Check rate limits before making a request
   */
  private async checkRateLimit(): Promise<void> {
    if (this.requestCount >= RATE_LIMIT_PER_SECOND) {
      await new Promise(resolve => setTimeout(resolve, 1000));
    }
    if (this.dailyRequestCount >= RATE_LIMIT_PER_DAY) {
      throw new Error('Daily rate limit exceeded (5000 requests per day)');
    }
  }

  /**
   * Handle API errors with detailed messages
   */
  private handleError(error: any): never {
    if (axios.isAxiosError(error)) {
      const axiosError = error as AxiosError;
      if (axiosError.response) {
        const status = axiosError.response.status;
        const data = axiosError.response.data as any;

        switch (status) {
          case 401:
            throw new Error('Invalid API key. Please check your DEALMACHINE_API_KEY in the environment variables.');
          case 403:
            throw new Error('Access forbidden. Ensure your API key has the necessary permissions.');
          case 429:
            throw new Error('Rate limit exceeded. Please wait before making more requests.');
          case 404:
            throw new Error(`Resource not found: ${axiosError.config?.url}`);
          case 400:
            throw new Error(`Bad request: ${data?.message || 'Invalid parameters provided'}`);
          default:
            throw new Error(`API error (${status}): ${data?.message || axiosError.message}`);
        }
      } else if (axiosError.request) {
        throw new Error('No response from Deal Machine API. Please check your internet connection.');
      }
    }
    throw new Error(`Unexpected error: ${error.message}`);
  }

  /**
   * Get team members
   */
  async getTeamMembers(): Promise<any> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.get('/team-members/');
      return response.data;
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Add a new lead
   */
  async addLead(lead: Partial<Lead>): Promise<DealMachineAPIResponse> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.post('/leads/', lead);
      return {
        success: true,
        data: response.data,
        message: 'Lead added successfully'
      };
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Update an existing lead
   */
  async updateLead(leadId: string, updates: Partial<Lead>): Promise<DealMachineAPIResponse> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.put(`/leads/${leadId}/`, updates);
      return {
        success: true,
        data: response.data,
        message: 'Lead updated successfully'
      };
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Add tags to a lead
   */
  async addTagsToLead(leadId: string, tags: string[]): Promise<DealMachineAPIResponse> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.post(`/leads/${leadId}/tags/`, { tags });
      return {
        success: true,
        data: response.data,
        message: 'Tags added successfully'
      };
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Create a note for a lead
   */
  async createNote(leadId: string, note: string): Promise<DealMachineAPIResponse> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.post(`/leads/${leadId}/notes/`, { note });
      return {
        success: true,
        data: response.data,
        message: 'Note created successfully'
      };
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Get lead details (if endpoint exists)
   */
  async getLead(leadId: string): Promise<Lead> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.get(`/leads/${leadId}/`);
      return response.data;
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Get all leads (if endpoint exists)
   */
  async getLeads(filters?: any): Promise<Lead[]> {
    await this.checkRateLimit();
    try {
      this.requestCount++;
      this.dailyRequestCount++;
      const response = await this.client.get('/leads/', { params: filters });
      return response.data;
    } catch (error) {
      this.handleError(error);
    }
  }

  /**
   * Get current rate limit status
   */
  getRateLimitStatus(): { requestsThisSecond: number; requestsToday: number; dailyLimit: number } {
    return {
      requestsThisSecond: this.requestCount,
      requestsToday: this.dailyRequestCount,
      dailyLimit: RATE_LIMIT_PER_DAY
    };
  }
}
