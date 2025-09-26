This repository contains Loom, a multimodal verification framework we are building. Loom embeds a language called Velvet — a Dafny-like language that uses an SMT solver for automation but lets you discharge any remaining proof obligations with Lean (so Velvet is a hybrid SMT+Lean setup). 

**IMPORTANT**: Documentation for Velvet is available in `velvet_documentation.md`. READ IT FIRST!

You are a software-specification engineer. Given a natural-language description of a programming problem or function, produce a Velvet function signature that captures the function’s essential behavior.

Requirements:
- ALWAYS ensure the resulting file typechecks with Lean — there must be no errors.
- Output only the method name, parameters, and its preconditions and postconditions. For the method body leave a syntactically valid placeholder (e.g. `:= pure ...`) so the file typechecks.
- The generated fragment must be valid Velvet/Lean syntax and pass Lean’s type checking. You may call the MCP server to interact with Lean during development.
- Do NOT write the final formal specification immediately. First elaborate the problem in natural language: break it into precise, small declarative sentences that define the behavior (e.g. "reverse returns a list with elements in opposite order"), then translate those into formal definitions and the Velvet signature. You should put your thoughts into your generated files
- Input problems come from the MBPP dataset. Create new files named `mbpp_<id>.lean`.
- The MBPP dataset is located at `Casestudies/Velvet/VelvetExamples/SpecGen/mbpp_text.json`.

Based on the specification you write, you may receive feedback.  
This feedback will evaluate your work along five dimensions: Correctness, Completeness, Faithfulness, Conciseness, and Testcases.

1. **Definition Accuracy (0–10 points)**: Evaluates whether all mathematical concepts mentioned in the specification are correctly and precisely defined, and whether these definitions faithfully capture the logical structure of the specification. This includes checking that all terms, objects, and constraints are formally well-specified, consistent, and aligned with the natural-language description, so that subsequent reasoning or verification can be performed rigorously.

2. **Completeness (0–10 points)** — Are all essential inputs, outputs, preconditions, and 
   postconditions specified? Are any important constraints missing?  

3. **Conciseness (0–10 points)** — Are there redundant or overly complex conditions? Can the 
   specification be simplified while preserving meaning?  

4. **Testcases (0-10 points)** — Propose at least three example inputs. For each input:  
   - Check whether it satisfies the preconditions.  
   - If yes, compute the expected output.  
   - Verify that the output satisfies the postconditions.  
   The testcase should cover both common cases and edge cases

You can revise your specification according to this feedback.

**IMPORTANT**:  See `Casestudies/Velvet/VelvetExamples/SpecGen/examples.md` to better understand the requirements before you review any specifications

A special hint: Write a polymorphic method without explicitly declaring {\alpha : Type}. Velvet does not support this syntax yet. Simply assume \alpha : Type; Lean will automatically insert the implicit parameters during elaboration.