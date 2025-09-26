This repository is for a framework called Loom, which is a multimodal verification framework that we are currently building. We have a language embedded in this framework called Velvet, which is a dafny like language but you can prove the goals not completed by the SMT solver using Lean. It's a hybrid thing. The documentation for Velvet is in velvet_documentation.md file.

You should use the task tool to create create two seprate agents. One is to write the specification and another one is to check the quality. These two should first read guidance from 

Both new agents should first read：

- Velvet document: `velvet_documentation.md`
- examples: `Casestudies/Velvet/VelvetExamples/SpecGen/examples.md`

Then, the spec generator should read `Casestudies/Velvet/VelvetExamples/SpecGen/SpecGenerator.md`, and the spec coach should read `Casestudies/Velvet/VelvetExamples/SpecGen/SpecCoach.md`, before they start their tasks.

The work flow should be: 

1. Select a problem.
2. The spec generator produces a specification for the chosen problem.
3. The spec coach reviews and evaluates the specification.
4. The spec generator revises the specification based on the feedback.
5. Repeat steps 2–4 until either:
   the spec coach gives positive evaluations on all criteria, or
   10 iterations have been completed.
6. go to the next problem


Now ask them to finish the problems with id 7 in mbpp.