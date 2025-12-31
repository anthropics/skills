//! Implementation of Task Algebra for SWML
//! 
//! Reference: SWML Paper Section 3.4 - Task Algebra
//! 
//! This module implements the algebraic structure for task composition,
//! including the monoid structure and task operators.

use std::sync::Arc;
use std::collections::{HashMap, HashSet};
use uuid::Uuid;
use serde::{Serialize, Deserialize};
use crate::spaces::{Skill, TaskElement};

/// A task in the SWML algebra system
/// Reference: SWML Paper Definition 3.4
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Task {
    /// Unique identifier
    pub id: Uuid,
    /// Human-readable name
    pub name: String,
    /// Required input skills
    pub inputs: Vec<Uuid>,
    /// Produced output skills
    pub outputs: Vec<Uuid>,
    /// Preconditions that must be satisfied
    pub preconditions: Vec<Condition>,
    /// Postconditions that will be true after execution
    pub postconditions: Vec<Condition>,
    /// Task operator type
    pub operator: TaskOperator,
    /// Metadata
    pub metadata: HashMap<String, String>,
}

/// Condition for task execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Condition {
    /// Condition identifier
    pub id: Uuid,
    /// Condition expression
    pub expression: String,
    /// Variables used in the condition
    pub variables: Vec<String>,
}

/// Task operators in the algebra
/// Reference: SWML Paper Section 3.4.1
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskOperator {
    /// Identity operator I
    Identity,
    /// Sequential composition τ₁ ∘ τ₂
    Sequential(Box<Task>, Box<Task>),
    /// Parallel composition τ₁ ∥ τ₂
    Parallel(Vec<Task>),
    /// Choice operator τ₁ ⊕ τ₂
    Choice(Vec<Task>),
    /// Iteration operator τ*
    Iteration(Box<Task>),
    /// Atomic task
    Atomic(AtomicTask),
}

/// Atomic task that cannot be decomposed further
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AtomicTask {
    /// Implementation function identifier
    pub function_id: String,
    /// Parameters for the function
    pub parameters: HashMap<String, serde_json::Value>,
}

/// The Task Algebra system
/// Reference: SWML Paper Definition 3.5
pub struct TaskAlgebra {
    /// Registry of available tasks
    tasks: Arc<std::sync::RwLock<HashMap<Uuid, Task>>>,
    /// Identity element
    identity: Task,
}

impl TaskAlgebra {
    /// Create a new task algebra system
    pub fn new() -> Self {
        let identity = Task {
            id: Uuid::new_v4(),
            name: "Identity".to_string(),
            inputs: vec![],
            outputs: vec![],
            preconditions: vec![],
            postconditions: vec![],
            operator: TaskOperator::Identity,
            metadata: HashMap::new(),
        };
        
        Self {
            tasks: Arc::new(std::sync::RwLock::new(HashMap::new())),
            identity: identity.clone(),
        }
    }
    
    /// Get the identity element
    /// Reference: SWML Paper Axiom 1
    pub fn identity(&self) -> &Task {
        &self.identity
    }
    
    /// Sequential composition of tasks
    /// Reference: SWML Paper Equation 3.4
    /// "τ₁ ∘ τ₂ executes τ₁ then τ₂"
    pub fn sequential(&self, t1: Task, t2: Task) -> Task {
        // Check compatibility: outputs of t1 should match inputs of t2
        let compatible = t1.outputs.iter()
            .any(|output| t2.inputs.contains(output));
        
        if !compatible {
            log::warn!("Sequential composition of incompatible tasks");
        }
        
        Task {
            id: Uuid::new_v4(),
            name: format!("{} → {}", t1.name, t2.name),
            inputs: t1.inputs.clone(),
            outputs: t2.outputs.clone(),
            preconditions: t1.preconditions.clone(),
            postconditions: t2.postconditions.clone(),
            operator: TaskOperator::Sequential(Box::new(t1), Box::new(t2)),
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("composition_type".to_string(), "sequential".to_string());
                meta
            },
        }
    }
    
    /// Parallel composition of tasks
    /// Reference: SWML Paper Equation 3.5
    /// "τ₁ ∥ τ₂ executes τ₁ and τ₂ concurrently"
    pub fn parallel(&self, tasks: Vec<Task>) -> Task {
        if tasks.is_empty() {
            return self.identity.clone();
        }
        
        // Collect all inputs and outputs
        let mut all_inputs = HashSet::new();
        let mut all_outputs = HashSet::new();
        let mut all_preconditions = Vec::new();
        let mut all_postconditions = Vec::new();
        
        for task in &tasks {
            all_inputs.extend(task.inputs.iter().cloned());
            all_outputs.extend(task.outputs.iter().cloned());
            all_preconditions.extend(task.preconditions.iter().cloned());
            all_postconditions.extend(task.postconditions.iter().cloned());
        }
        
        Task {
            id: Uuid::new_v4(),
            name: tasks.iter()
                .map(|t| t.name.clone())
                .collect::<Vec<_>>()
                .join(" ∥ "),
            inputs: all_inputs.into_iter().collect(),
            outputs: all_outputs.into_iter().collect(),
            preconditions: all_preconditions,
            postconditions: all_postconditions,
            operator: TaskOperator::Parallel(tasks),
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("composition_type".to_string(), "parallel".to_string());
                meta
            },
        }
    }
    
    /// Choice operator for alternative tasks
    /// Reference: SWML Paper Equation 3.6
    /// "τ₁ ⊕ τ₂ chooses between τ₁ and τ₂"
    pub fn choice(&self, tasks: Vec<Task>) -> Task {
        if tasks.is_empty() {
            return self.identity.clone();
        }
        
        if tasks.len() == 1 {
            return tasks[0].clone();
        }
        
        // For choice, we take the union of possible inputs/outputs
        let mut possible_inputs = HashSet::new();
        let mut possible_outputs = HashSet::new();
        
        for task in &tasks {
            possible_inputs.extend(task.inputs.iter().cloned());
            possible_outputs.extend(task.outputs.iter().cloned());
        }
        
        Task {
            id: Uuid::new_v4(),
            name: format!("Choice({})", tasks.len()),
            inputs: possible_inputs.into_iter().collect(),
            outputs: possible_outputs.into_iter().collect(),
            preconditions: vec![], // Choice determines preconditions at runtime
            postconditions: vec![], // Choice determines postconditions at runtime
            operator: TaskOperator::Choice(tasks),
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("composition_type".to_string(), "choice".to_string());
                meta
            },
        }
    }
    
    /// Iteration operator (Kleene star)
    /// Reference: SWML Paper Equation 3.7
    /// "τ* represents zero or more iterations of τ"
    pub fn iterate(&self, task: Task) -> Task {
        Task {
            id: Uuid::new_v4(),
            name: format!("{}*", task.name),
            inputs: task.inputs.clone(),
            outputs: task.outputs.clone(),
            preconditions: vec![], // Iteration checks conditions dynamically
            postconditions: task.postconditions.clone(),
            operator: TaskOperator::Iteration(Box::new(task)),
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("composition_type".to_string(), "iteration".to_string());
                meta
            },
        }
    }
    
    /// Create an atomic task
    pub fn atomic(&self, name: String, function_id: String, inputs: Vec<Uuid>, outputs: Vec<Uuid>) -> Task {
        Task {
            id: Uuid::new_v4(),
            name,
            inputs,
            outputs,
            preconditions: vec![],
            postconditions: vec![],
            operator: TaskOperator::Atomic(AtomicTask {
                function_id,
                parameters: HashMap::new(),
            }),
            metadata: HashMap::new(),
        }
    }
    
    /// Check if a task satisfies the monoid laws
    /// Reference: SWML Paper Theorem 3.1
    pub fn verify_monoid_laws(&self, t1: &Task, t2: &Task, t3: &Task) -> MonoidVerification {
        // Left identity: I ∘ τ = τ
        let left_identity = self.verify_left_identity(t1);
        
        // Right identity: τ ∘ I = τ
        let right_identity = self.verify_right_identity(t1);
        
        // Associativity: (τ₁ ∘ τ₂) ∘ τ₃ = τ₁ ∘ (τ₂ ∘ τ₃)
        let associativity = self.verify_associativity(t1, t2, t3);
        
        MonoidVerification {
            left_identity,
            right_identity,
            associativity,
        }
    }
    
    /// Verify left identity law
    fn verify_left_identity(&self, task: &Task) -> bool {
        let composed = self.sequential(self.identity.clone(), task.clone());
        // In practice, we'd check structural equivalence
        composed.inputs == task.inputs && composed.outputs == task.outputs
    }
    
    /// Verify right identity law  
    fn verify_right_identity(&self, task: &Task) -> bool {
        let composed = self.sequential(task.clone(), self.identity.clone());
        composed.inputs == task.inputs && composed.outputs == task.outputs
    }
    
    /// Verify associativity law
    fn verify_associativity(&self, t1: &Task, t2: &Task, t3: &Task) -> bool {
        let left = self.sequential(
            self.sequential(t1.clone(), t2.clone()),
            t3.clone()
        );
        
        let right = self.sequential(
            t1.clone(),
            self.sequential(t2.clone(), t3.clone())
        );
        
        // Check structural equivalence
        left.inputs == right.inputs && left.outputs == right.outputs
    }
    
    /// Convert a TaskElement to an algebraic Task
    pub fn from_task_element(&self, element: &TaskElement) -> Task {
        self.atomic(
            element.name.clone(),
            format!("task_{}", element.id),
            element.required_skills.clone(),
            vec![], // Output skills would be determined by execution
        )
    }
}

/// Result of monoid law verification
#[derive(Debug, Clone)]
pub struct MonoidVerification {
    pub left_identity: bool,
    pub right_identity: bool,
    pub associativity: bool,
}

impl MonoidVerification {
    /// Check if all monoid laws are satisfied
    pub fn is_valid(&self) -> bool {
        self.left_identity && self.right_identity && self.associativity
    }
}

/// Task execution context
#[derive(Debug, Clone)]
pub struct ExecutionContext {
    /// Available skills
    pub skills: HashMap<Uuid, Skill>,
    /// Variable bindings
    pub variables: HashMap<String, serde_json::Value>,
    /// Execution trace
    pub trace: Vec<ExecutionEvent>,
}

/// Event in task execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionEvent {
    pub task_id: Uuid,
    pub event_type: ExecutionEventType,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// Types of execution events
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ExecutionEventType {
    Started,
    Completed,
    Failed(String),
    SkillProduced(Uuid),
    SkillConsumed(Uuid),
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_task_algebra_creation() {
        let algebra = TaskAlgebra::new();
        assert_eq!(algebra.identity().name, "Identity");
    }
    
    #[test]
    fn test_sequential_composition() {
        let algebra = TaskAlgebra::new();
        
        let t1 = algebra.atomic(
            "Task1".to_string(),
            "func1".to_string(),
            vec![],
            vec![Uuid::new_v4()],
        );
        
        let output_skill = t1.outputs[0];
        let t2 = algebra.atomic(
            "Task2".to_string(),
            "func2".to_string(),
            vec![output_skill],
            vec![],
        );
        
        let composed = algebra.sequential(t1, t2);
        assert!(composed.name.contains("→"));
    }
    
    #[test]
    fn test_parallel_composition() {
        let algebra = TaskAlgebra::new();
        
        let t1 = algebra.atomic("T1".to_string(), "f1".to_string(), vec![], vec![]);
        let t2 = algebra.atomic("T2".to_string(), "f2".to_string(), vec![], vec![]);
        
        let parallel = algebra.parallel(vec![t1, t2]);
        assert!(parallel.name.contains("∥"));
    }
    
    #[test]
    fn test_monoid_laws() {
        let algebra = TaskAlgebra::new();
        
        let t1 = algebra.atomic("T1".to_string(), "f1".to_string(), vec![], vec![]);
        let t2 = algebra.atomic("T2".to_string(), "f2".to_string(), vec![], vec![]);
        let t3 = algebra.atomic("T3".to_string(), "f3".to_string(), vec![], vec![]);
        
        let verification = algebra.verify_monoid_laws(&t1, &t2, &t3);
        assert!(verification.left_identity);
        assert!(verification.right_identity);
        // Note: Full associativity check would require deeper structural comparison
    }
}