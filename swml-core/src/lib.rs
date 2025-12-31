//! SWML Core - Implementation of Skill-Web Markup Language Theoretical Foundation
//! 
//! This crate implements the mathematical and theoretical foundations of SWML
//! as described in the SWML research paper.
//! 
//! # Architecture
//! 
//! The implementation is organized into the following modules:
//! - `axioms`: Five fundamental axioms (Section 3.1)
//! - `spaces`: Four fundamental spaces (Section 3.2)
//! - `omega`: Skill weaving function Ω (Section 3.3)
//! - `algebra`: Task algebra and operations (Section 3.4)
//! - `phases`: Six-phase execution model (Section 4)

#![warn(missing_docs)]

pub mod axioms;
pub mod spaces;
pub mod omega;
pub mod algebra;
pub mod phases;

/// Re-export commonly used types
pub use axioms::{Axiom, AxiomSystem};
pub use spaces::{SkillSpace, Space};
pub use omega::{OmegaFunction, SkillWeaving};
pub use algebra::{Task, TaskAlgebra};
pub use phases::{Phase, PhaseExecutor};

/// SWML version information
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Initialize the SWML system
pub fn initialize() -> Result<(), Box<dyn std::error::Error>> {
    log::info!("Initializing SWML Core v{}", VERSION);
    
    // Initialize axiom system
    axioms::initialize_axiom_system()?;
    
    // Initialize spaces
    spaces::initialize_spaces()?;
    
    // Initialize omega function
    omega::initialize_omega()?;
    
    log::info!("SWML Core initialized successfully");
    Ok(())
}