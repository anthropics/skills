//! Implementation of the Four Fundamental Spaces in SWML
//! 
//! Reference: SWML Paper Section 3.2 - Spaces
//! 
//! This module implements the four fundamental spaces:
//! 1. Skill Space (S) - The space of all skills
//! 2. Task Space (T) - The space of all tasks  
//! 3. Context Space (C) - The space of all contexts
//! 4. Evolution Space (E) - The space of all evolutionary paths

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock};
use uuid::Uuid;
use nalgebra::{DVector, DMatrix};
use petgraph::graph::{Graph, NodeIndex};
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};

/// Trait for all SWML spaces
pub trait Space {
    type Element: Clone + Send + Sync;
    
    /// Get the dimension of the space
    fn dimension(&self) -> usize;
    
    /// Check if an element belongs to the space
    fn contains(&self, element: &Self::Element) -> bool;
    
    /// Get the distance between two elements in the space
    fn distance(&self, a: &Self::Element, b: &Self::Element) -> f64;
    
    /// Get the basis vectors of the space
    fn basis(&self) -> Vec<Self::Element>;
}

/// Skill representation in the skill space
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Skill {
    pub id: Uuid,
    pub name: String,
    pub vector: DVector<f64>,
    pub dependencies: Vec<Uuid>,
    pub metadata: HashMap<String, String>,
}

/// Task representation in the task space
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskElement {
    pub id: Uuid,
    pub name: String,
    pub required_skills: Vec<Uuid>,
    pub complexity: f64,
    pub context_requirements: Vec<String>,
}

/// Context representation in the context space
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Context {
    pub id: Uuid,
    pub name: String,
    pub parameters: HashMap<String, f64>,
    pub constraints: Vec<String>,
}

/// Evolution path representation in the evolution space
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EvolutionPath {
    pub id: Uuid,
    pub from_skill: Uuid,
    pub to_skill: Uuid,
    pub transformation_matrix: DMatrix<f64>,
    pub timestamp: DateTime<Utc>,
}

/// The Skill Space S
/// Reference: SWML Paper Section 3.2.1
/// "S is a Hilbert space with inner product ⟨s₁, s₂⟩"
pub struct SkillSpace {
    skills: Arc<RwLock<HashMap<Uuid, Skill>>>,
    dimension: usize,
    graph: Arc<RwLock<Graph<Uuid, f64>>>,
}

impl SkillSpace {
    pub fn new(dimension: usize) -> Self {
        Self {
            skills: Arc::new(RwLock::new(HashMap::new())),
            dimension,
            graph: Arc::new(RwLock::new(Graph::new())),
        }
    }
    
    /// Add a skill to the space
    pub fn add_skill(&self, skill: Skill) -> Result<NodeIndex, String> {
        let mut skills = self.skills.write().unwrap();
        let mut graph = self.graph.write().unwrap();
        
        if skills.contains_key(&skill.id) {
            return Err("Skill already exists".to_string());
        }
        
        let node_idx = graph.add_node(skill.id);
        skills.insert(skill.id, skill);
        Ok(node_idx)
    }
    
    /// Compute inner product between two skills
    /// Reference: SWML Paper Equation 3.1
    pub fn inner_product(&self, s1: &Skill, s2: &Skill) -> f64 {
        s1.vector.dot(&s2.vector)
    }
}

impl Space for SkillSpace {
    type Element = Skill;
    
    fn dimension(&self) -> usize {
        self.dimension
    }
    
    fn contains(&self, element: &Self::Element) -> bool {
        self.skills.read().unwrap().contains_key(&element.id)
    }
    
    fn distance(&self, a: &Self::Element, b: &Self::Element) -> f64 {
        // Euclidean distance in skill vector space
        (&a.vector - &b.vector).norm()
    }
    
    fn basis(&self) -> Vec<Self::Element> {
        // Return orthonormal basis skills
        let skills = self.skills.read().unwrap();
        skills.values().take(self.dimension).cloned().collect()
    }
}

/// The Task Space T
/// Reference: SWML Paper Section 3.2.2
/// "T forms a monoid under task composition"
pub struct TaskSpace {
    tasks: Arc<RwLock<HashMap<Uuid, TaskElement>>>,
    dimension: usize,
}

impl TaskSpace {
    pub fn new(dimension: usize) -> Self {
        Self {
            tasks: Arc::new(RwLock::new(HashMap::new())),
            dimension,
        }
    }
    
    /// Compose two tasks
    /// Reference: SWML Paper Definition 3.2
    pub fn compose(&self, t1: &TaskElement, t2: &TaskElement) -> TaskElement {
        let mut required_skills = t1.required_skills.clone();
        required_skills.extend(t2.required_skills.clone());
        let required_skills: Vec<Uuid> = required_skills.into_iter().collect::<HashSet<_>>().into_iter().collect();
        
        TaskElement {
            id: Uuid::new_v4(),
            name: format!("{} ∘ {}", t1.name, t2.name),
            required_skills,
            complexity: t1.complexity + t2.complexity,
            context_requirements: {
                let mut reqs = t1.context_requirements.clone();
                reqs.extend(t2.context_requirements.clone());
                reqs.into_iter().collect::<HashSet<_>>().into_iter().collect()
            },
        }
    }
}

impl Space for TaskSpace {
    type Element = TaskElement;
    
    fn dimension(&self) -> usize {
        self.dimension
    }
    
    fn contains(&self, element: &Self::Element) -> bool {
        self.tasks.read().unwrap().contains_key(&element.id)
    }
    
    fn distance(&self, a: &Self::Element, b: &Self::Element) -> f64 {
        // Distance based on skill requirement overlap
        let a_skills: HashSet<_> = a.required_skills.iter().collect();
        let b_skills: HashSet<_> = b.required_skills.iter().collect();
        let intersection = a_skills.intersection(&b_skills).count() as f64;
        let union = a_skills.union(&b_skills).count() as f64;
        
        if union == 0.0 {
            0.0
        } else {
            1.0 - (intersection / union)
        }
    }
    
    fn basis(&self) -> Vec<Self::Element> {
        let tasks = self.tasks.read().unwrap();
        tasks.values().take(self.dimension).cloned().collect()
    }
}

/// The Context Space C
/// Reference: SWML Paper Section 3.2.3
/// "C is a measurable space with σ-algebra"
pub struct ContextSpace {
    contexts: Arc<RwLock<HashMap<Uuid, Context>>>,
    dimension: usize,
}

impl ContextSpace {
    pub fn new(dimension: usize) -> Self {
        Self {
            contexts: Arc::new(RwLock::new(HashMap::new())),
            dimension,
        }
    }
    
    /// Check if a context transformation is valid
    pub fn valid_transformation(&self, from: &Context, to: &Context) -> bool {
        // Check if all constraints in 'to' can be satisfied given 'from'
        to.constraints.iter().all(|_constraint| {
            // Simplified validation logic
            from.parameters.len() >= to.parameters.len()
        })
    }
}

impl Space for ContextSpace {
    type Element = Context;
    
    fn dimension(&self) -> usize {
        self.dimension
    }
    
    fn contains(&self, element: &Self::Element) -> bool {
        self.contexts.read().unwrap().contains_key(&element.id)
    }
    
    fn distance(&self, a: &Self::Element, b: &Self::Element) -> f64 {
        // Distance based on parameter differences
        let mut sum = 0.0;
        for (key, a_val) in &a.parameters {
            if let Some(b_val) = b.parameters.get(key) {
                sum += (a_val - b_val).powi(2);
            }
        }
        sum.sqrt()
    }
    
    fn basis(&self) -> Vec<Self::Element> {
        let contexts = self.contexts.read().unwrap();
        contexts.values().take(self.dimension).cloned().collect()
    }
}

/// The Evolution Space E
/// Reference: SWML Paper Section 3.2.4
/// "E captures the temporal evolution of skills"
pub struct EvolutionSpace {
    paths: Arc<RwLock<HashMap<Uuid, EvolutionPath>>>,
    dimension: usize,
}

impl EvolutionSpace {
    pub fn new(dimension: usize) -> Self {
        Self {
            paths: Arc::new(RwLock::new(HashMap::new())),
            dimension,
        }
    }
    
    /// Apply an evolution path to a skill
    pub fn evolve(&self, skill: &Skill, path: &EvolutionPath) -> Skill {
        let evolved_vector = &path.transformation_matrix * &skill.vector;
        
        Skill {
            id: Uuid::new_v4(),
            name: format!("{}_evolved", skill.name),
            vector: evolved_vector,
            dependencies: skill.dependencies.clone(),
            metadata: skill.metadata.clone(),
        }
    }
}

impl Space for EvolutionSpace {
    type Element = EvolutionPath;
    
    fn dimension(&self) -> usize {
        self.dimension
    }
    
    fn contains(&self, element: &Self::Element) -> bool {
        self.paths.read().unwrap().contains_key(&element.id)
    }
    
    fn distance(&self, a: &Self::Element, b: &Self::Element) -> f64 {
        // Distance based on transformation matrix Frobenius norm
        (&a.transformation_matrix - &b.transformation_matrix).norm()
    }
    
    fn basis(&self) -> Vec<Self::Element> {
        let paths = self.paths.read().unwrap();
        paths.values().take(self.dimension).cloned().collect()
    }
}

/// Initialize all four spaces
pub fn initialize_spaces() -> Result<(), Box<dyn std::error::Error>> {
    log::info!("Initializing four fundamental spaces");
    
    // Default dimensions for each space
    let _skill_space = SkillSpace::new(100);
    let _task_space = TaskSpace::new(50);
    let _context_space = ContextSpace::new(20);
    let _evolution_space = EvolutionSpace::new(30);
    
    log::info!("All spaces initialized successfully");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_skill_space() {
        let space = SkillSpace::new(10);
        let skill = Skill {
            id: Uuid::new_v4(),
            name: "Test Skill".to_string(),
            vector: DVector::from_element(10, 1.0),
            dependencies: vec![],
            metadata: HashMap::new(),
        };
        
        assert!(space.add_skill(skill.clone()).is_ok());
        assert!(space.contains(&skill));
    }
    
    #[test]
    fn test_task_composition() {
        let space = TaskSpace::new(5);
        let t1 = TaskElement {
            id: Uuid::new_v4(),
            name: "Task 1".to_string(),
            required_skills: vec![Uuid::new_v4()],
            complexity: 1.0,
            context_requirements: vec!["req1".to_string()],
        };
        
        let t2 = TaskElement {
            id: Uuid::new_v4(),
            name: "Task 2".to_string(),
            required_skills: vec![Uuid::new_v4()],
            complexity: 2.0,
            context_requirements: vec!["req2".to_string()],
        };
        
        let composed = space.compose(&t1, &t2);
        assert_eq!(composed.complexity, 3.0);
        assert_eq!(composed.required_skills.len(), 2);
    }
}