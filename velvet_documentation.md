# Velvet Language Documentation

### Introduction

Velvet is a language for writing programs with specifications, shallowly embedded in Lean. It allows you to prove the correctness of your programs with respect to their specifications using Lean's proof capabilities. The syntax is inspired by Dafny.

### The Velvet Advantage: Hybrid Verification

The primary strength of Velvet is its nature as a **shallowly embedded language** within Lean. This enables a powerful hybrid verification workflow that combines automated SMT solving with the full power of Lean's interactive theorem proving.

1.  **Automated Proof with SMT:** The `loom_solve` tactic is the first line of attack. It attempts to automatically prove the correctness of the method by translating the proof goals into SMT queries. For many methods, this is all that is needed.

2.  **Interactive Proving:** If `loom_solve` fails to completely prove the method, you are not stuck. Because you are in the Lean environment, you can seamlessly add interactive Lean tactics to the `prove_correct` block to finish the proof. This allows you to handle complex proofs that are beyond the scope of SMT solvers, while still benefiting from automation for the parts that can be automated.

**Example: Falling back to interactive tactics**

In some cases, `loom_solve` may not be able to solve all proof goals. Here, we can add interactive tactics like `grind` to complete the proof.

```lean
prove_correct cbrt by
  dsimp [cbrt]
  loom_solve
  -- SMT failed to discharge one goal, but grind succeeds
  grind
```

**Example: Guiding the SMT solver**

Another way to interact with the proof system is to provide hints to the SMT solver. In the `LastDigit` example, a `solverHint` is provided to help `loom_solve` with the modulo arithmetic.

```lean
attribute [local solverHint] Nat.mod_lt

prove_correct LastDigit by
  unfold LastDigit
  loom_solve
```

This combination of automated and interactive proving makes Velvet a flexible and powerful tool for writing verified software.

### Setup

A typical Velvet file starts with a set of imports and options to configure the environment and the SMT solver.

**Example Setup:**
```lean
import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"
```

### Method Definition

Methods are the basic unit of programs in Velvet. They are defined using the `method` keyword. The signature includes the method name, typed arguments, and named, typed return values.

**Syntax:**
```lean
method <method_name> (<arg1>: <Type1>, ...) return (<ret_val_name>: <Type>)
```

**Example:**
```lean
method Minimum (a: Int) (b: Int) return (minValue: Int)
```

### Pre- and Post-conditions

You can specify preconditions and postconditions for your methods using `require` and `ensures` clauses.

**Syntax:**
```lean
method <method_name> (...)
    require <precondition>
    ensures <postcondition1>
    ensures <postcondition2>
```

**Example:**
```lean
method CubeSurfaceArea (size: Int) return (area: Int)
    require size > 0
    ensures area = 6 * size * size
```

### Data Types

Velvet uses Lean's data types. The most common ones observed are:

*   **`Int`**: Signed integers.
*   **`Nat`** or **`ℕ`**: Non-negative integers.
*   **`Array <Type>`**: Lean's native array type (e.g., `Array Int`).
*   **`Unit`**: The unit type, for methods that don't return a value.

### Method Body

The implementation of a method goes inside a `do` block.

*   **Variable Declaration**: Mutable local variables are declared with `let mut`.
    **Example:**
    ```lean
    let mut i := 0
    ```

*   **Control Flow**: Standard `if/then/else` is supported.
    **Example:**
    ```lean
    if a <= b then
        minValue := a
    else
        minValue := b
    ```

*   **Loops**: `while` loops are used for iteration. For verification, they can be annotated with `invariant` clauses (conditions that are true at the start of each iteration) and a `done_with` clause (a condition that is true upon loop termination).

    **Syntax:**
    ```lean
    while <condition>
        invariant <invariant1>
        done_with <termination_condition>
    do
        -- loop body
    ```
    **Example:**
    ```lean
    let mut i := 0
    while i < a.size
        invariant cubedArray.size = a.size
        invariant 0 ≤ i ∧ i ≤ a.size
        done_with i = a.size
    do
        cubedArray := Array.set! cubedArray i (a[i]! * a[i]! * a[i]!)
        i := i + 1
    ```

*   **Array Operations**: For `Array <Type>`:
    *   **Creation**: `Array.replicate <size> <default_value>`
    *   **Size**: `<array>.size`
    *   **Access**: `<array>[<index>]!` (Note the `!`)
    *   **Update**: `Array.set! <array> <index> <value>`, which returns a new array.

    **Example:**
    ```lean
    let mut cubedArray := Array.replicate a.size 0
    cubedArray := Array.set! cubedArray i (a[i]! * a[i]! * a[i]!)
    ```

*   **Return Statement**: The `return` keyword is used to return a value from a method.
    **Example:**
    ```lean
    return cubedArray
    ```

### Verification

The correctness of a Velvet method with respect to its specification is proven in a `prove_correct` block.

**Syntax:**
```lean
prove_correct <method_name> by
  <tactic1>
  <tactic2>
  ...
```

**Common Tactics:**

*   **`unfold <method_name>`**: Unfolds the definition of the method.
*   **`loom_solve`**: An automated tactic to solve the proof obligations.

**Example:**
```lean
prove_correct CubeElements by
  unfold CubeElements
  loom_solve
```

### Differences from Dafny

While Velvet's syntax is inspired by Dafny, there are several key differences in how constructs are expressed.

| Feature             | Dafny                               | Velvet                                        |
| ------------------- | ----------------------------------- | --------------------------------------------- |
| **Method Body**     | `{ ... }`                           | `do` block                                    |
| **Variable Decl.**  | `var x := 0;`                       | `let mut x := 0`                              |
| **Loops**           | `for`, `while`                      | `while` (no `for` loop construct)             |
| **Array Type**      | `array<int>`                        | `Array Int`                                   |
| **Array Creation**  | `new int[size]`                     | `Array.replicate size defaultValue`           |
| **Array Access**    | `a[i]`                              | `a[i]!` (Note the `!`)                        |
| **Array Update**    | `a[i] := value;`                    | `a := Array.set! a i value`                   |
| **Loop Post-cond.** | `ensures` on `while` (less common)  | `done_with` clause for `while`                |

#### Example: `for` loop translation

A Dafny `for` loop must be translated into a `while` loop in Velvet.

**Dafny:**
```dafny
for i := 0 to a.Length {
    // loop body
}
```

**Velvet:**
```lean
let mut i := 0
while i < a.size do
    -- loop body
    i := i + 1
```
