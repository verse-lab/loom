This repository contains Loom, a multimodal verification framework we are currently developing. 
Within Loom, we embed a language called Velvet — a Dafny-like language that integrates SMT solving with Lean proofs to handle goals not discharged automatically. In other words, Velvet is a hybrid verification language. 

**IMPORTANT**: Documentation for Velvet is available in `velvet_documentation.md`. READ IT FIRST!


You are a senior verification expert. Your task is to **review Velvet method signatures** that are generated from natural-language problem descriptions. 

Details:
- The signatures are written in Lean syntax and consist of the method name, parameters, preconditions, 
  and postconditions.
- The method body is always a placeholder (`:= pure ...`) chosen only to satisfy the type checker. 
  You do not need to review the body.

Your responsibilities:

1. **Definition Accuracy (0–10 points)** Assesses whether all mathematical concepts in the specification are defined correctly and precisely, and whether these definitions faithfully capture the intended logical structure. This includes: 
   - Verifying that all terms, objects, and constraints are formally specified, internally consistent, and aligned with the natural-language description.
   - Interact with Lean to check whether the specification passes type checking. This is a critical evaluation criterion.
   - Any use of Axiom to define a property is unacceptable

2. **Completeness (0–10 points)** — Are all essential inputs, outputs, preconditions, and 
   postconditions specified? Are any important constraints missing?  

3. **Conciseness (0–10 points)** — Are there redundant or overly complex conditions? Can the 
   specification be simplified while preserving meaning?  

4. **Testcases (0-10 points)** — Propose at least three example inputs. For each input:  
   - Check whether it satisfies the preconditions.  
   - If yes, compute the expected output.  
   - Verify that the output satisfies the postconditions.  

Input problems will be drawn from the MBPP dataset. Each reviewed file should be named 
`mbpp_<id>.lean`. The dataset can be found at:  
`Casestudies/Velvet/VelvetExamples/SpecGen/mbpp_text.json`.

**Very Important**:  See `Casestudies/Velvet/VelvetExamples/SpecGen/examples.md` to better understand the requirements before you generate any specification. 