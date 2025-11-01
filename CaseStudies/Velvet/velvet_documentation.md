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
  loom_solve
  -- SMT failed to discharge one goal, but grind succeeds
  grind
```

**Example: Guiding the SMT solver**

Another way to interact with the proof system is to provide hints to the SMT solver. In the `LastDigit` example, a `solverHint` is provided to help `loom_solve` with the modulo arithmetic.

```lean
attribute [local solverHint] Nat.mod_lt

prove_correct LastDigit by
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
method <method_name> (<arg1>: <Type1>) (<arg2>: <Type2>) ... return (<ret_val_name>: <Type>)
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

    **Note on nested conditionals**: Velvet has issues with `if/else if/then` syntax. Instead, nest the second `if` inside the `else` block:
    ```lean
    -- Don't use: if/else if/then
    -- if m = 0 then ... else if n = 0 then ...

    -- Use: nested if inside else
    if m = 0 then
        return n + 1
    else
        if n = 0 then
            return something
        else
            return something_else
    ```

*   **Loops**: `while` loops are used for iteration. For verification, they can be annotated with `invariant` clauses (conditions that are true at the start of each iteration) and a `done_with` clause (a condition that is true upon loop termination).

    Note: `done_with` clause can be omitted, in this case it becomes negation of the loop condition. 
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

*   **Non-deterministic operations**: syntax `let <name> :| <cond>` is used to assign a value using non-determinism.
    **Example:**
    ```lean
    let ans :| ans > inp + 200
    ```
    You can choose the type of non-determinism by switching between `AngelicChoice` and `DemonicChoice`.
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

*   **Call of another method**: Use Lean's monadic computation syntax to call another method.
    **Example:**
    ```lean
    let pre_res ← pickGreaterN (n - 1)
    ```

*   **Return Statement**: The `return` keyword is used to return a value from a method.
    **Example:**
    ```lean
    return cubedArray
    ```

### Testing
Velvet `method`s are executable definitions in Lean, therefore you can do property based testing before attempting verification. For an example on how to do testing for `insertionSort`, please refer to `VelvetExamples/Examples.lean`. 
You can execute programs with Lean commands as well:
```lean
#eval (insertionSort #[9,3,1,5]).run
--output: DivM.res ⟨(), ⟨#[1, 3, 5, 9], ()⟩⟩
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
*   **`loom_solve!`**: Similar to `loom_solve`, but also highlights all places which caused automation to fail (related `ensures`/`require`/`invariant`/`decreasing`). Please note that highlighting remains after completing the proof manually and the intended way is to use `loom_solve` for proofs that involve manual part.
*   **`grind`**: A general-purpose tactic for finishing proofs after SMT fails.
*   **`simp_all`**: Simplifies all hypotheses and the goal.
*   **`aesop`**: A tableau-based proof search tactic.

**Advanced Tactics**
*   **`loom_auto`**: SMT tactic customizable with hints (more in **`Solver Hints`** section).
*   **`loom_solver`**: Customizable tactic used by `loom_solve` to discharge goals automatically. Default is `loom_auto`.
*   **`loom_goals_intro`**: Tactic that introduces raw goals. Might be helpful in case where user needs to manually inspect generated goals before running automation.
*   **`loom_unfold`**: Tactic that can be used to unfold `WithName` constructs after `loom_goals_intro`.

**`loom_solver`** customization example:
```lean
macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try simp at *
  try grind
  try lean_auto))
```
If you need to inspect how goals are generated, please refer to `loom_goals_intro` and `wpgen` tactics implementation.

**Example:**
```lean
prove_correct CubeElements by
  loom_solve
```

#### Solver Hints

When `loom_solve` fails to complete a proof due to missing mathematical knowledge, you can provide **solver hints** using the `attribute [local solverHint]` declaration. These hints guide the SMT solver by making relevant lemmas available.

**Example with modulo arithmetic:**
```lean
attribute [local solverHint] Nat.mod_lt

prove_correct LastDigit by
  loom_solve
```

**Example with array operations:**
```lean
attribute [local solverHint] Array.size_replicate Array.size_set

prove_correct CubeElements by
  loom_solve
```

#### Interactive Proof Strategies

For complex proofs that `loom_solve` cannot handle completely, you can combine automated and interactive tactics:

**Pattern 1: Fallback to interactive tactics**
```lean
prove_correct method_name by
  loom_solve
  -- SMT failed on remaining goals, use interactive tactics
  grind
```

**Pattern 2: Manual proof after automation**
```lean
prove_correct method_name by
  loom_solve <;> simp_all
  -- Handle remaining subgoals manually
  { intros k hk
    by_cases h : k = i <;> simp_all }
```

To assist the user in interactive mode, Velvet supports:
* convenient naming for hypotheses produced by `invariant`/`ensures`/`require`.
* increnemental mode (that is, automation won't rerun on each proof change)
  To ensure that incremental mode works as expected, we suggest using `{ subgoal_proof }` pattern in manual proofs


**Pattern 3: Helper lemmas**
When proofs are complex, define helper lemmas and use them as solver hints:
```lean
-- Define helper lemma
lemma adjacent_to_global_sorted (a : Array Int) :
    (∀ k, 0 ≤ k ∧ k < a.size - 1 → a[k]! ≤ a[k+1]!) →
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!) := by
  -- proof here

-- Use as solver hint
attribute [local solverHint] adjacent_to_global_sorted

prove_correct IsSorted by
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
| **Boolean Equivalence** | `<==>`                         | `↔`                                           |
| **Logical And/Or**  | `&&`, `\|\|`                        | `∧`, `∨`                                      |
| **Existential**     | `exists`                            | `∃`                                           |
| **Universal**       | `forall`                            | `∀`                                           |

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

### Pattern Matching and Recursion

Velvet provides support for pattern matching with `match` expressions and recursive method calls.

#### Match Expressions

Velvet supports pattern matching on data constructors using `match` expressions.

**Basic Pattern Matching:**
```lean
method test1 (n : Nat) return (res : Nat)
  ensures n = res
  do
    match n with
    | .zero => pure 0
    | .succ k =>
      let b ← test1 k
      pure (Nat.succ b)
```

**Multiple Parameter Matching:**
```lean
method test2 (n : β) (l : List α) return (res : Nat)
  ensures res = l.length
  do
    match l, n with
    | [], _ => pure 0
    | _ :: k, _ =>
      let b ← test2 n k
      pure b.succ
```

**Match in Function Definitions:**
```lean
def get_cnt_sum (l: List Encoding) :=
  match l with
  | List.nil => 0
  | List.cons x xs => x.cnt + get_cnt_sum xs
```

**Note:** Pattern matching is a newer feature in Velvet and may have issues with more complicated constructs.

#### Recursion

**Simple Recursion:**
```lean
method simple_recursion (x : Nat) return (res: Nat)
  require True
  ensures res = x
  do
    if x = 0 then
      return 0
    else
      let pre_res ← simple_recursion (x - 1)
      return pre_res + 1
```

**Structural Recursion:**
```lean
method SimpleList (li: List Nat) return (res: Nat)
  ensures res > 0
  do
    match li with
    | x :: xs =>
      let prev ← SimpleList xs
      return (prev.1 + x)
    | [] =>
      return 1
```

**Verification with Recursion:**
```lean
prove_correct simple_recursion by
  loom_solve  -- Often sufficient for simple recursive methods
```

**Termination Handling:**
Velvet supports `decreasing_by` and `termination_by` clauses similar to Lean, which can be added at the end of method definitions and `prove_correct` commands:

```lean
method gcd (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  do
    if b = 0 then
      return a
    else
      let remainder := a % b
      let result ← gcd b remainder
      return result.1
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    grind -- proof that a % b < b

prove_correct gcd
termination_by b
decreasing_by all_goals(
  apply Nat.mod_lt
  grind)
by
  loom_solve
```

**Note:** Recursion is also a newer feature in Velvet and may have issues with more complex recursive patterns.

### Advanced Features

#### `triple`s and definitions

After `method` declaration it becomes a regular Lean 4 definition of a monadic computation with the same name and parameters as `method` and with return type `VelvetM`.
You can use it as a Lean definition if needed, for example, to run it with `#eval`.

`prove_correct ...` command creates a Lean 4 statement about the related `method`, which has the form of:
```lean
lemma method_name_correct: triple preconditions (method_name args) postconditions
```
It can be further used as a Lean 4 definition if needed. 
For an example on how to do 2 layer proofs using `triple`s produced by Velvet, please refer to `VelvetExamples/SpMSpV_Example.lean`.

You can also use `#print method_name_correct` to inspect the generated triple.

#### Total correctness

Velvet can be used to reason about terminating loops. In this case, each loop should be annotated with `decreasing <term>` clause, and a goal about the `<term>` being decreased will be generated.

Velvet provides support for proving termination and functional correctness separately by combining `triple`s of different `method`s.
For an example on how to prove functional correctness from partial correctness and termination, please refer to `VelvetExample/Total_Partial_example.lean`.


#### Custom Data Types and Structures

Velvet supports defining custom data structures using Lean's `structure` syntax:

```lean
structure Encoding where
  cnt: Nat
  c: Char
  deriving Inhabited
```

These structures can be used in method signatures and arrays:
```lean
method encodeStr (str: Array Char) return (res: Array Encoding)
```

#### Complex Loop Invariants

For more sophisticated algorithms, you may need complex invariants that track multiple properties:

```lean
while j < high
invariant low <= i ∧ i <= j ∧ j <= high
invariant arrayToMultiset arr = arrayToMultiset oldArr
invariant (forall k, low <= k -> k < i -> arr[k]! < pivotVal)
invariant (forall k , i <= k -> k < j -> arr[k]! >= pivotVal)
invariant arr[high]! = oldArr[high]!
do
    -- loop body
```

#### Mutable Parameters

Methods can take mutable parameters using the `mut` keyword:

```lean
method qsortPartition (mut arr: Array Int) (low: Nat) (high: Nat)
  return (pivotIndex: Nat)
```

The modified array is automatically available as `arrNew` in postconditions:
```lean
ensures arrNew[pivotIndex]! = arr[high]!
```

#### Compound Loop Conditions

While loops can have compound conditions that help with termination:

```lean
while i < a.size - 1 ∧ sorted
    invariant 0 ≤ i ∧ i ≤ a.size - 1
    invariant sorted = true → (∀ k, 0 ≤ k ∧ k < i → a[k]! ≤ a[k+1]!)
    invariant sorted = false → ∃ k, 0 ≤ k ∧ k < a.size - 1 ∧ a[k]! > a[k+1]!
    done_with (i = a.size - 1 ∨ sorted = false)
```

#### Helper Functions and Lemmas

For complex verification, define helper functions and prove lemmas about them:

```lean
def get_cnt_sum (l: List Encoding) :=
  match l with
  | List.nil => 0
  | List.cons x xs => x.cnt + get_cnt_sum xs

lemma get_cnt_sum_append l1 l2:
    get_cnt_sum (l1 ++ l2) = get_cnt_sum l1 + get_cnt_sum l2 := by
  induction l1 with
  | nil => simp; rfl
  | cons e l1' ih =>
    simp [ih]
    grind
```

Use these in specifications:
```lean
method decodeStr' (encoded_str: Array Encoding)
   return (res: Array Char)
   ensures (res.size = get_cnt_sum encoded_str.toList)
```

### Common Porting Patterns

When porting from Dafny to Velvet, several patterns emerge frequently:

#### Type Translations

**Integer types**: Dafny's `int` typically becomes `Int` in Velvet, but consider using `Nat` for non-negative values to get better SMT support:

```lean
-- Dafny: method LastDigit(n: int) requires n >= 0
-- Velvet: better to use Nat directly
method LastDigit (n: Nat) return (d: Nat)
```

**Precondition simplification**: When using `Nat`, non-negativity constraints become unnecessary:
```lean
-- Dafny: requires n >= 0 && size > 0
-- Velvet: just require size > 0 (if n is Nat)
```

#### Loop Invariant Translation

**Basic pattern**: Maintain the logical structure but adapt to Velvet syntax:
```lean
-- Dafny:
-- invariant 0 <= i <= a.Length
-- invariant forall k :: 0 <= k < i ==> result[k] == transform(a[k])

-- Velvet:
invariant 0 ≤ i ∧ i ≤ a.size
invariant ∀ k, 0 ≤ k ∧ k < i → result[k]! = transform a[k]!
```

**Array size invariants**: Always include size preservation invariants:
```lean
invariant result.size = a.size  -- often needed for verification
```

#### Complex Proof Strategies

**For simple methods**: Start with `loom_solve`:
```lean
prove_correct SimpleMethod by
  loom_solve
```

**For arithmetic-heavy methods**: Add relevant mathematical lemmas as hints:
```lean
attribute [local solverHint] Nat.mod_lt Nat.div_le_iff_le_mul_right

prove_correct ArithmeticMethod by
  loom_solve
```

**For complex methods**: Use the hybrid approach with interactive tactics:
```lean
prove_correct ComplexMethod by
  loom_solve <;> simp_all
  -- Handle remaining goals manually
  intros; by_cases <;> grind
```

#### Common Verification Challenges

**Issue**: SMT solver cannot handle modular arithmetic
**Solution**: Add `Nat.mod_lt` as a solver hint

**Issue**: Array size properties not automatically proven
**Solution**: Add explicit size invariants and use `Array.size_replicate`, `Array.size_set` hints

**Issue**: Complex logical equivalences in specifications
**Solution**: Break down into helper lemmas and prove them separately

#### Best Practices for Porting

1. **Start simple**: Port the basic structure first, then add complexity
2. **Use typed signatures**: Prefer `Nat` over `Int` when values are non-negative
3. **Keep original code**: Comment out original Dafny code for reference
4. **Incremental verification**: Get basic structure verified before adding complex invariants
5. **Name your lemmas**: Use `have` statements with descriptive names instead of relying on auto-generated names
6. **Test solver hints**: Add mathematical lemmas as hints when SMT solving fails

### Complete Examples from Porting

#### Example 1: Simple Arithmetic Method

**Original Dafny (task_id_435):**
```dafny
method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
    d := n % 10;
}
```

**Velvet Translation:**
```lean
method LastDigit (n: Nat) return (d: Nat)
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10

attribute [local solverHint] Nat.mod_lt

prove_correct LastDigit by
  loom_solve
```

**Key insights:**
- Used `Nat` instead of `Int` to eliminate non-negativity precondition
- Added `Nat.mod_lt` hint for modular arithmetic
- Direct return statement instead of assignment

#### Example 2: Array Processing with Loop

**Original Dafny (task_id_447):**
```dafny
method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures cubed.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{
    var cubedArray := new int[a.Length];
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant cubedArray.Length == a.Length
        invariant forall k :: 0 <= k < i ==> cubedArray[k] == a[k] * a[k] * a[k]
    {
        cubedArray[i] := a[i] * a[i] * a[i];
    }
    return cubedArray;
}
```

**Velvet Translation:**
```lean
method CubeElements (a: Array Int) return (cubed: Array Int)
    ensures cubed.size = a.size
    ensures ∀ i, 0 ≤ i ∧ i < a.size → cubed[i]! = a[i]! * a[i]! * a[i]!
    do
    let mut cubedArray := Array.replicate a.size 0
    let mut i := 0
    while i < a.size
    invariant cubedArray.size = a.size
    invariant 0 ≤ i ∧ i ≤ a.size
    invariant ∀ k, 0 ≤ k ∧ k < i → cubedArray[k]! = a[k]! * a[k]! * a[k]!
    do
        cubedArray := cubedArray.set! i (a[i]! * a[i]! * a[i]!)
        i := i + 1
    return cubedArray

attribute [local solverHint] Array.size_replicate Array.size_set

prove_correct CubeElements by
  loom_solve <;> simp_all
  -- Additional interactive proving for complex array reasoning
```

**Key insights:**
- `for` loop became `while` loop with manual increment
- Array creation uses `Array.replicate` with default value
- Array update uses `Array.set!` with reassignment
- Added array size hints for verification
- Used both automated and interactive proving strategies
