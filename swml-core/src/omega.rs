//! Implementation of the Omega (Ω) Skill Weaving Function
//! 
//! Reference: SWML Paper Section 3.3 - The Weaving Function
//! 
//! The Omega function Ω: S × C × E → S is the core transformation
//! that weaves skills together based on context and evolution.

use std::sync::Arc;
use uuid::Uuid;
use nalgebra::{DVector, DMatrix};
use serde::{Serialize, Deserialize};
use crate::spaces::{Skill, Context, EvolutionPath};

/// Result of the weaving operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WeavingResult {
    /// The newly woven skill
    pub skill: Skill,
    /// Confidence score of the weaving (0.0 to 1.0)
    pub confidence: f64,
    /// Transformation metrics
    pub metrics: WeavingMetrics,
}

/// Metrics collected during the weaving process
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WeavingMetrics {
    /// Coherence measure of the weaving
    pub coherence: f64,
    /// Stability of the transformation
    pub stability: f64,
    /// Information preserved during weaving
    pub information_preserved: f64,
    /// Computational cost (in arbitrary units)
    pub cost: f64,
}

/// The Omega function implementation
/// Reference: SWML Paper Definition 3.3
pub struct OmegaFunction {
    /// Weaving kernel function K(s,s')
    #[allow(dead_code)]
    kernel: Arc<dyn Fn(&Skill, &Skill) -> f64 + Send + Sync>,
    /// Learning rate for adaptive weaving
    learning_rate: f64,
    /// Regularization parameter
    regularization: f64,
}

impl OmegaFunction {
    /// Create a new Omega function with default parameters
    pub fn new() -> Self {
        Self {
            // Default RBF kernel
            kernel: Arc::new(|s1, s2| {
                let diff = &s1.vector - &s2.vector;
                let gamma = 0.1; // Bandwidth parameter
                (-gamma * diff.norm_squared()).exp()
            }),
            learning_rate: 0.01,
            regularization: 0.001,
        }
    }
    
    /// The main weaving function Ω(s, c, e)
    /// Reference: SWML Paper Equation 3.3
    /// "Ω: S × C × E → S weaves skills based on context and evolution"
    pub fn weave(&self, skills: &[Skill], context: &Context, evolution: &EvolutionPath) -> Result<WeavingResult, String> {
        if skills.is_empty() {
            return Err("Cannot weave empty skill set".to_string());
        }
        
        // Step 1: Context adaptation
        // Reference: SWML Paper Section 3.3.1
        let adapted_skills = self.adapt_to_context(skills, context)?;
        
        // Step 2: Evolution transformation
        // Reference: SWML Paper Section 3.3.2
        let evolved_skills = self.apply_evolution(&adapted_skills, evolution)?;
        
        // Step 3: Skill synthesis through kernel weaving
        // Reference: SWML Paper Section 3.3.3
        let woven_skill = self.synthesize_skills(&evolved_skills)?;
        
        // Step 4: Calculate metrics
        let metrics = self.calculate_metrics(&woven_skill, skills, context);
        
        Ok(WeavingResult {
            skill: woven_skill,
            confidence: metrics.coherence * metrics.stability,
            metrics,
        })
    }
    
    /// Adapt skills to a specific context
    fn adapt_to_context(&self, skills: &[Skill], context: &Context) -> Result<Vec<Skill>, String> {
        skills.iter().map(|skill| {
            // Create context-aware transformation matrix
            let dim = skill.vector.len();
            let mut transform = DMatrix::identity(dim, dim);
            
            // Apply context parameters as scaling factors
            for (param_name, param_value) in &context.parameters {
                if let Ok(idx) = param_name.parse::<usize>() {
                    if idx < dim {
                        transform[(idx, idx)] *= param_value;
                    }
                }
            }
            
            // Apply transformation
            let adapted_vector = &transform * &skill.vector;
            
            Ok(Skill {
                id: Uuid::new_v4(),
                name: format!("{}_adapted", skill.name),
                vector: adapted_vector,
                dependencies: skill.dependencies.clone(),
                metadata: {
                    let mut meta = skill.metadata.clone();
                    meta.insert("context_id".to_string(), context.id.to_string());
                    meta
                },
            })
        }).collect()
    }
    
    /// Apply evolution transformation to skills
    fn apply_evolution(&self, skills: &[Skill], evolution: &EvolutionPath) -> Result<Vec<Skill>, String> {
        skills.iter().map(|skill| {
            // Ensure dimensions match
            if evolution.transformation_matrix.nrows() != skill.vector.len() {
                return Err("Evolution matrix dimension mismatch".to_string());
            }
            
            // Apply evolution transformation
            let evolved_vector = &evolution.transformation_matrix * &skill.vector;
            
            Ok(Skill {
                id: Uuid::new_v4(),
                name: format!("{}_evolved", skill.name),
                vector: evolved_vector,
                dependencies: skill.dependencies.clone(),
                metadata: {
                    let mut meta = skill.metadata.clone();
                    meta.insert("evolution_id".to_string(), evolution.id.to_string());
                    meta
                },
            })
        }).collect()
    }
    
    /// Synthesize multiple skills into one through kernel weaving
    /// Reference: SWML Paper Algorithm 3.1
    fn synthesize_skills(&self, skills: &[Skill]) -> Result<Skill, String> {
        if skills.is_empty() {
            return Err("Cannot synthesize empty skill set".to_string());
        }
        
        let dim = skills[0].vector.len();
        let mut woven_vector = DVector::zeros(dim);
        let mut total_weight = 0.0;
        
        // Kernel-weighted combination
        for (i, skill_i) in skills.iter().enumerate() {
            let mut skill_weight = 0.0;
            
            for (j, skill_j) in skills.iter().enumerate() {
                if i != j {
                    let kernel_value = (self.kernel)(skill_i, skill_j);
                    skill_weight += kernel_value;
                }
            }
            
            // Normalize and accumulate
            if skill_weight > 0.0 {
                woven_vector += skill_weight * &skill_i.vector;
                total_weight += skill_weight;
            }
        }
        
        // Normalize the final vector
        if total_weight > 0.0 {
            woven_vector /= total_weight;
        } else {
            // Fallback to simple average
            for skill in skills {
                woven_vector += &skill.vector;
            }
            woven_vector /= skills.len() as f64;
        }
        
        // Apply regularization
        let regularization_term = self.regularization * woven_vector.norm();
        woven_vector *= 1.0 / (1.0 + regularization_term);
        
        // Collect all dependencies
        let mut all_dependencies = Vec::new();
        for skill in skills {
            all_dependencies.extend(skill.dependencies.clone());
        }
        all_dependencies.sort();
        all_dependencies.dedup();
        
        Ok(Skill {
            id: Uuid::new_v4(),
            name: "woven_skill".to_string(),
            vector: woven_vector,
            dependencies: all_dependencies,
            metadata: {
                let mut meta = std::collections::HashMap::new();
                meta.insert("weaving_method".to_string(), "kernel".to_string());
                meta.insert("source_skills".to_string(), skills.len().to_string());
                meta
            },
        })
    }
    
    /// Calculate weaving metrics
    fn calculate_metrics(&self, woven: &Skill, original: &[Skill], context: &Context) -> WeavingMetrics {
        // Coherence: How well the skills fit together
        let coherence = self.calculate_coherence(woven, original);
        
        // Stability: How robust the transformation is
        let stability = self.calculate_stability(woven);
        
        // Information preserved: Ratio of information retained
        let information_preserved = self.calculate_information_preservation(woven, original);
        
        // Cost: Computational complexity (simplified)
        let cost = (original.len() as f64) * context.parameters.len() as f64;
        
        WeavingMetrics {
            coherence,
            stability,
            information_preserved,
            cost,
        }
    }
    
    /// Calculate coherence metric
    fn calculate_coherence(&self, woven: &Skill, original: &[Skill]) -> f64 {
        if original.is_empty() {
            return 0.0;
        }
        
        let mut sum = 0.0;
        for skill in original {
            sum += (self.kernel)(woven, skill);
        }
        
        sum / original.len() as f64
    }
    
    /// Calculate stability metric
    fn calculate_stability(&self, woven: &Skill) -> f64 {
        // Stability based on vector norm
        let norm = woven.vector.norm();
        1.0 / (1.0 + (norm - 1.0).abs())
    }
    
    /// Calculate information preservation
    fn calculate_information_preservation(&self, woven: &Skill, original: &[Skill]) -> f64 {
        if original.is_empty() {
            return 0.0;
        }
        
        // Calculate total information in original skills
        let original_info: f64 = original.iter()
            .map(|s| s.vector.norm())
            .sum();
        
        // Information in woven skill
        let woven_info = woven.vector.norm();
        
        (woven_info / original_info).min(1.0)
    }
}

/// Trait for custom skill weaving strategies
pub trait SkillWeaving {
    /// Weave multiple skills into one
    fn weave(&self, skills: &[Skill], context: &Context, evolution: &EvolutionPath) -> Result<WeavingResult, String>;
    
    /// Get the name of the weaving strategy
    fn name(&self) -> &str;
}

impl SkillWeaving for OmegaFunction {
    fn weave(&self, skills: &[Skill], context: &Context, evolution: &EvolutionPath) -> Result<WeavingResult, String> {
        self.weave(skills, context, evolution)
    }
    
    fn name(&self) -> &str {
        "Kernel-based Omega Function"
    }
}

/// Initialize the Omega function
pub fn initialize_omega() -> Result<(), Box<dyn std::error::Error>> {
    log::info!("Initializing Omega skill weaving function");
    
    let omega = OmegaFunction::new();
    log::debug!("Omega function initialized with learning rate: {}", omega.learning_rate);
    log::debug!("Regularization parameter: {}", omega.regularization);
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spaces::{Context, EvolutionPath};
    use std::collections::HashMap;
    
    fn create_test_skill(name: &str, dim: usize) -> Skill {
        Skill {
            id: Uuid::new_v4(),
            name: name.to_string(),
            vector: DVector::from_element(dim, 1.0),
            dependencies: vec![],
            metadata: HashMap::new(),
        }
    }
    
    fn create_test_context() -> Context {
        Context {
            id: Uuid::new_v4(),
            name: "test_context".to_string(),
            parameters: {
                let mut params = HashMap::new();
                params.insert("0".to_string(), 1.5);
                params.insert("1".to_string(), 0.8);
                params
            },
            constraints: vec![],
        }
    }
    
    fn create_test_evolution(dim: usize) -> EvolutionPath {
        EvolutionPath {
            id: Uuid::new_v4(),
            from_skill: Uuid::new_v4(),
            to_skill: Uuid::new_v4(),
            transformation_matrix: DMatrix::identity(dim, dim) * 1.1,
            timestamp: chrono::Utc::now(),
        }
    }
    
    #[test]
    fn test_omega_weaving() {
        let omega = OmegaFunction::new();
        let skills = vec![
            create_test_skill("skill1", 5),
            create_test_skill("skill2", 5),
        ];
        let context = create_test_context();
        let evolution = create_test_evolution(5);
        
        let result = omega.weave(&skills, &context, &evolution);
        assert!(result.is_ok());
        
        let weaving = result.unwrap();
        assert!(weaving.confidence > 0.0 && weaving.confidence <= 1.0);
        assert_eq!(weaving.skill.vector.len(), 5);
    }
    
    #[test]
    fn test_empty_skill_weaving() {
        let omega = OmegaFunction::new();
        let skills = vec![];
        let context = create_test_context();
        let evolution = create_test_evolution(5);
        
        let result = omega.weave(&skills, &context, &evolution);
        assert!(result.is_err());
    }
}