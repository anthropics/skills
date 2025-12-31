//! Basic usage example of SWML Core

use swml_core::{initialize, PhaseExecutor, Phase, phases::PhaseInput};
use nalgebra::DVector;
use uuid::Uuid;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logging
    env_logger::init();
    
    println!("=== SWML Core Basic Usage Example ===\n");
    
    // Initialize SWML system
    println!("1. Initializing SWML system...");
    initialize()?;
    println!("   ✓ System initialized\n");
    
    // Create phase executor
    println!("2. Creating phase executor...");
    let executor = PhaseExecutor::new();
    println!("   ✓ Executor created\n");
    
    // Execute parsing phase
    println!("3. Executing parsing phase...");
    let swml_input = r#"
        <swml version="1.0">
            <task name="data_analysis">
                <requires>python_skills</requires>
                <requires>statistics_knowledge</requires>
                <produces>analysis_report</produces>
            </task>
        </swml>
    "#;
    
    let parse_result = executor.execute_phase(
        Phase::Parsing,
        PhaseInput::Raw(swml_input.to_string())
    ).await?;
    
    println!("   ✓ Parsing completed");
    println!("   - Duration: {}ms", parse_result.metrics.duration_ms);
    println!("   - Success: {}\n", parse_result.success);
    
    // Demonstrate skill creation and weaving
    println!("4. Creating and weaving skills...");
    
    use swml_core::spaces::{Skill, Context, EvolutionPath};
    use swml_core::omega::OmegaFunction;
    
    // Create sample skills
    let skill1 = Skill {
        id: Uuid::new_v4(),
        name: "Python Programming".to_string(),
        vector: DVector::from_vec(vec![1.0, 0.8, 0.6, 0.9, 0.7]),
        dependencies: vec![],
        metadata: HashMap::new(),
    };
    
    let skill2 = Skill {
        id: Uuid::new_v4(),
        name: "Data Analysis".to_string(),
        vector: DVector::from_vec(vec![0.7, 1.0, 0.8, 0.6, 0.9]),
        dependencies: vec![skill1.id],
        metadata: HashMap::new(),
    };
    
    // Create context
    let context = Context {
        id: Uuid::new_v4(),
        name: "Research Project".to_string(),
        parameters: {
            let mut params = HashMap::new();
            params.insert("complexity".to_string(), 0.8);
            params.insert("time_constraint".to_string(), 0.6);
            params
        },
        constraints: vec!["academic_rigor".to_string()],
    };
    
    // Create evolution path
    let evolution = EvolutionPath {
        id: Uuid::new_v4(),
        from_skill: skill1.id,
        to_skill: skill2.id,
        transformation_matrix: nalgebra::DMatrix::identity(5, 5) * 1.1,
        timestamp: chrono::Utc::now(),
    };
    
    // Perform skill weaving
    let omega = OmegaFunction::new();
    let weaving_result = omega.weave(&[skill1.clone(), skill2.clone()], &context, &evolution)?;
    
    println!("   ✓ Skills woven successfully");
    println!("   - Woven skill: {}", weaving_result.skill.name);
    println!("   - Confidence: {:.2}", weaving_result.confidence);
    println!("   - Coherence: {:.2}", weaving_result.metrics.coherence);
    println!("   - Stability: {:.2}\n", weaving_result.metrics.stability);
    
    // Demonstrate task algebra
    println!("5. Demonstrating task algebra...");
    
    use swml_core::algebra::TaskAlgebra;
    
    let algebra = TaskAlgebra::new();
    
    // Create atomic tasks
    let task1 = algebra.atomic(
        "Load Data".to_string(),
        "load_csv".to_string(),
        vec![],
        vec![Uuid::new_v4()], // produces data skill
    );
    
    let task2 = algebra.atomic(
        "Analyze Data".to_string(),
        "run_analysis".to_string(),
        task1.outputs.clone(), // requires data skill
        vec![Uuid::new_v4()], // produces analysis skill
    );
    
    // Compose tasks sequentially
    let composed = algebra.sequential(task1.clone(), task2.clone());
    println!("   ✓ Sequential composition: {}", composed.name);
    
    // Compose tasks in parallel
    let parallel = algebra.parallel(vec![task1.clone(), task2.clone()]);
    println!("   ✓ Parallel composition: {}", parallel.name);
    
    // Create iterative task
    let iterative = algebra.iterate(task1.clone());
    println!("   ✓ Iterative task: {}\n", iterative.name);
    
    // Verify monoid laws
    let task3 = algebra.atomic(
        "Export Results".to_string(),
        "export_csv".to_string(),
        vec![],
        vec![],
    );
    
    let verification = algebra.verify_monoid_laws(&task1, &task2, &task3);
    println!("   ✓ Monoid law verification:");
    println!("     - Left identity: {}", verification.left_identity);
    println!("     - Right identity: {}", verification.right_identity);
    println!("     - Associativity: {}", verification.associativity);
    
    println!("\n=== Example completed successfully ===");
    
    Ok(())
}