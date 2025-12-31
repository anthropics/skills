//! Integration tests for SWML Core

use swml_core::{initialize, PhaseExecutor, Phase, phases::PhaseInput};

#[tokio::test]
async fn test_full_pipeline() {
    // Initialize system
    initialize().expect("Failed to initialize SWML");
    
    // Create executor
    let executor = PhaseExecutor::new();
    
    // Test parsing phase
    let input = PhaseInput::Raw("test swml content".to_string());
    let result = executor.execute_phase(Phase::Parsing, input).await;
    
    assert!(result.is_ok());
    let phase_result = result.unwrap();
    assert!(phase_result.success);
}

#[test]
fn test_axiom_system() {
    use swml_core::axioms::{AxiomSystem, AxiomContext};
    use uuid::Uuid;
    use chrono::Utc;
    
    let system = AxiomSystem::new();
    assert_eq!(system.axioms().len(), 5);
    
    // Test validation
    let context = AxiomContext {
        task: Some(Uuid::new_v4()),
        skills: vec![Uuid::new_v4(), Uuid::new_v4()],
        context: "test".to_string(),
        timestamp: Utc::now(),
    };
    
    let results = system.validate(&context);
    assert_eq!(results.len(), 5);
    
    // All axioms should pass with valid context
    for (name, valid) in results {
        assert!(valid, "Axiom {} failed", name);
    }
}

#[test]
fn test_skill_weaving() {
    use swml_core::spaces::{Skill, Context, EvolutionPath};
    use swml_core::omega::OmegaFunction;
    use nalgebra::DVector;
    use uuid::Uuid;
    use std::collections::HashMap;
    
    let omega = OmegaFunction::new();
    
    // Create test skills
    let skill1 = Skill {
        id: Uuid::new_v4(),
        name: "Skill 1".to_string(),
        vector: DVector::from_vec(vec![1.0; 10]),
        dependencies: vec![],
        metadata: HashMap::new(),
    };
    
    let skill2 = Skill {
        id: Uuid::new_v4(),
        name: "Skill 2".to_string(),
        vector: DVector::from_vec(vec![0.5; 10]),
        dependencies: vec![],
        metadata: HashMap::new(),
    };
    
    let context = Context {
        id: Uuid::new_v4(),
        name: "Test Context".to_string(),
        parameters: HashMap::new(),
        constraints: vec![],
    };
    
    let evolution = EvolutionPath {
        id: Uuid::new_v4(),
        from_skill: skill1.id,
        to_skill: skill2.id,
        transformation_matrix: nalgebra::DMatrix::identity(10, 10),
        timestamp: chrono::Utc::now(),
    };
    
    let result = omega.weave(&[skill1, skill2], &context, &evolution);
    assert!(result.is_ok());
    
    let weaving = result.unwrap();
    assert!(weaving.confidence > 0.0);
    assert!(weaving.confidence <= 1.0);
}

#[test]
fn test_task_algebra() {
    use swml_core::algebra::TaskAlgebra;
    use uuid::Uuid;
    
    let algebra = TaskAlgebra::new();
    
    // Test identity
    let identity = algebra.identity();
    assert_eq!(identity.name, "Identity");
    
    // Test task creation
    let task = algebra.atomic(
        "Test Task".to_string(),
        "test_func".to_string(),
        vec![],
        vec![Uuid::new_v4()],
    );
    
    assert_eq!(task.name, "Test Task");
    assert_eq!(task.outputs.len(), 1);
    
    // Test sequential composition
    let task2 = algebra.atomic(
        "Task 2".to_string(),
        "func2".to_string(),
        task.outputs.clone(),
        vec![],
    );
    
    let composed = algebra.sequential(task, task2);
    assert!(composed.name.contains("→"));
}