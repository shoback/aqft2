/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Multiplication Operators on L² Spaces for AQFT

This file provides a general framework for multiplication operators on L² spaces,
essential for constructing field operators and heat kernel operators in quantum field theory.
The key insight: bounded functions give bounded multiplication operators on L².

### Core Theory:

**Main Results:**
- `mulL2_of_boundedContinuous`: Bounded continuous φ → bounded T_φ on L²(α,μ) with ‖T_φ‖ ≤ ‖φ‖∞
- `mulL2_of_Linfty`: L∞ functions φ → bounded T_φ on L²(α,μ) with ‖T_φ‖ ≤ ‖φ‖∞
- `mulC0_of_boundedContinuous`: Warmup lemma for continuous function spaces

**Key Technical Lemma:**
- `ae_lin_of_coeLp`: Handles L^p coercion linearity for multiplication operators

### Operator Constructors:

**From Bounded Continuous Functions:**
- `mulL2_BoundedContinuous`: T_φ : L²(α,μ) →L[ℝ] L²(α,μ) from φ ∈ BC(α,ℝ)
- `mulL2_BoundedContinuous_apply`: (T_φ f)(x) = φ(x) · f(x) (a.e.)
- `mulL2_BoundedContinuous_norm_le`: ‖T_φ‖ ≤ ‖φ‖∞

**From L∞ Functions:**
- `mulL2_Linfty`: T_φ : L²(α,μ) →L[ℝ] L²(α,μ) from φ ∈ L∞(α,μ)
- `mulL2_Linfty_apply`: (T_φ f)(x) = φ(x) · f(x) (a.e.)
- `mulL2_Linfty_norm_le`: ‖T_φ‖ ≤ ‖φ‖∞

### Examples and Applications:

**Concrete Examples:**
- `constantFunction`: Constant multiplication c·f for c ∈ ℝ
- `constantMultiplication`: Scaling operator on L²(ℝ)
- `sineBoundedFunction`: Sine multiplication (bounded by 1)
- `sineBoundedMultiplication`: sin(x)·f(x) operator

### Mathematical Framework:

**Multiplication Operator Definition:**
For bounded φ : α → ℝ, define T_φ : L²(α,μ) → L²(α,μ) by:
```
(T_φ f)(x) = φ(x) · f(x)  (pointwise, a.e.)
```

**Key Properties:**
1. **Boundedness**: ‖T_φ‖ ≤ ‖φ‖∞ (essential supremum bound)
2. **Linearity**: T_φ(af + bg) = aT_φf + bT_φg (linear operator)
3. **A.E. Equality**: Uses =ᵐ[μ] since L² functions are equivalence classes

**Technical Challenges:**
- L² functions are equivalence classes, not pointwise functions
- Need AE representatives for pointwise multiplication
- Proving boundedness requires careful measure theory
- MemLp.toLp conversions between functions and L² classes

### AQFT Applications:

**Field Operators:** φ(f) = ∫ φ(x)f(x) dx (field smearing)
**Heat Kernels:** exp(-t|p|²) multiplication for Gaussian free field evolution
**Spectral Theory:** Multiplication operators with spectrum = essential range of φ

### Implementation:

**Proof Strategy:** Pointwise bound → L² bound → LinearMap.mkContinuous
**Status:** Framework complete, core proofs marked with `sorry`
**Integration:** Used in `QFTHilbertSpace`, `GFFMconstruct`, `HilbertSpace` modules

Foundation for rigorous field operator construction in Osterwalder-Schrader framework.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Real
open TopologicalSpace

noncomputable section

/-! ## Multiplication Operators on L² Spaces

This file provides a general framework for multiplication operators on L² spaces over arbitrary
measure spaces. The key results are:

1. **Bounded continuous functions** give bounded multiplication operators
2. **L∞ functions** give bounded multiplication operators

These lemmas can then be applied to specific spaces in QFT and other applications.
-/

namespace OperatorTheory

-- General measure space setup
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
variable (μ : Measure α) [SigmaFinite μ]

/-! ## Core Multiplication Lemmas

These are the fundamental results for multiplication operators on L² spaces.

We start with a warmup for continuous functions, then move to L² spaces.
-/

/-- **Warmup Lemma**: Bounded continuous functions give bounded multiplication operators on C⁰.

If ϕ : α → ℝ is bounded and continuous, then pointwise multiplication by ϕ defines a bounded linear operator
on C⁰(α, ℝ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞. This is a good warmup for the L² case. -/
lemma mulC0_of_boundedContinuous [CompactSpace α] (ϕ : BoundedContinuousFunction α ℝ) :
  ∃ (T : C(α, ℝ) →L[ℝ] C(α, ℝ)), (∀ f : C(α, ℝ), ∀ x, T f x = ϕ x * f x) ∧ ‖T‖ ≤ ‖ϕ‖ := by
  -- Step 1: Define the linear map
  let L : C(α, ℝ) →ₗ[ℝ] C(α, ℝ) := {
    toFun := fun f => ⟨fun x => ϕ x * f x, by
      -- Continuity: product of continuous functions is continuous
      exact Continuous.mul ϕ.continuous f.continuous⟩
    map_add' := fun f g => by
      ext x
      simp [mul_add]
    map_smul' := fun c f => by
      ext x
      simp [ContinuousMap.smul_apply]
      ring
  }

  -- Step 2: Show boundedness
  have h_bound : ∀ f : C(α, ℝ), ‖L f‖ ≤ ‖ϕ‖ * ‖f‖ := by
    intro f
    -- Use the characterization: ‖g‖ ≤ C ↔ ∀ x, |g x| ≤ C
    rw [ContinuousMap.norm_le (L f) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    intro x
    simp [L]
    -- Goal is |ϕ x| * |f x| ≤ ‖ϕ‖ * ‖f‖
    calc |ϕ x| * |f x|
      ≤ ‖ϕ‖ * |f x| := mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm ϕ x) (abs_nonneg _)
      _ ≤ ‖ϕ‖ * ‖f‖ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

  -- Step 3: Use LinearMap.mkContinuous
  let T : C(α, ℝ) →L[ℝ] C(α, ℝ) := LinearMap.mkContinuous L ‖ϕ‖ h_bound

  use T
  constructor
  · intro f x
    simp [T, LinearMap.mkContinuous_apply, L]
  · exact LinearMap.mkContinuous_norm_le L (norm_nonneg _) h_bound


noncomputable section
lemma ae_lin_of_coeLp
    (ϕ : α → ℝ) (a b : ℝ) (f g : Lp ℝ 2 μ) :
  (fun x => ϕ x * ((a • f + b • g : Lp ℝ 2 μ) x))
    =ᵐ[μ] (fun x => a * (ϕ x * f x) + b * (ϕ x * g x)) := by
  classical
  -- coerce `(a • f + b • g)` to a function and linearize
  have h₁ :
      (fun x => ((a • f + b • g : Lp ℝ 2 μ) x))
        =ᵐ[μ] (fun x => a • f x + b • g x) := by
    refine (Lp.coeFn_add (a • f) (b • g)).trans ?_
    -- rewrite each smul under the coercion
    filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hx hy
    simp [hx, hy]
  -- push `ϕ x * _` through that a.e. equality
  have h₂ :
      (fun x => ϕ x * ((a • f + b • g : Lp ℝ 2 μ) x))
        =ᵐ[μ] (fun x => ϕ x * (a • f x + b • g x)) := by
    refine h₁.mono ?_
    intro x hx; simp only [hx]
  -- pointwise algebra (true for all x)
  have h₃ :
      (fun x => ϕ x * (a • f x + b • g x))
        = (fun x => a * (ϕ x * f x) + b * (ϕ x * g x)) := by
    funext x; simp [mul_add, smul_eq_mul, mul_left_comm]
  exact h₂.trans (Filter.EventuallyEq.of_eq h₃)
end

/-- **Lemma 1**: Bounded continuous functions give bounded multiplication operators.

If ϕ : α → ℝ is bounded and continuous, then pointwise multiplication by ϕ
defines a bounded linear operator on L²(α, μ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞. -/
lemma mulL2_of_boundedContinuous (ϕ : BoundedContinuousFunction α ℝ) :
  ∃ (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), (∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun x => ϕ x * f x) ∧ ‖T‖ ≤ ‖ϕ‖ := by
  -- CONCRETE STEP 1: Establish the key mathematical bound
  -- Since ϕ is bounded continuous, we have |ϕ(x)| ≤ ‖ϕ‖ for all x
  have h_bound_key : ∀ x : α, |ϕ x| ≤ ‖ϕ‖ := BoundedContinuousFunction.norm_coe_le_norm ϕ

  -- CONCRETE STEP 2: The key pointwise inequality
  -- For any x and any real number r, we have |ϕ(x) * r|² ≤ ‖ϕ‖² * |r|²
  have h_pointwise_bound : ∀ (x : α) (r : ℝ), |ϕ x * r|^2 ≤ ‖ϕ‖^2 * |r|^2 := by
    intro x r
    -- Use the fact that |ab|² = |a|² * |b|²
    rw [abs_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right
    · -- Use a more basic approach: |ϕ x|² ≤ ‖ϕ‖²
      have h1 : |ϕ x| ≤ ‖ϕ‖ := h_bound_key x
      rw [sq_le_sq]
      simp only [abs_abs]
      rw [abs_of_nonneg (norm_nonneg _)]
      exact h1
    · exact sq_nonneg _

  -- CONCRETE STEP 3: Use AE representative and mathematical bound
  -- Get the AE representative of ϕ
  have ϕ_measurable : AEStronglyMeasurable (ϕ : α → ℝ) μ :=
    ϕ.continuous.aestronglyMeasurable
  let ϕ_ae : α →ₘ[μ] ℝ := AEEqFun.mk (ϕ : α → ℝ) ϕ_measurable

  -- CONCRETE STEP 3: Use function representatives and mathematical bound
  -- ϕ is already an honest function (bounded continuous function)
  -- For f ∈ L², we need to get its AE representative to multiply pointwise

  -- The strategy: For each f ∈ L², get its AE representative f_rep,
  -- then multiply ϕ(x) * f_rep(x), and show this is in L²

  -- First, we need to show that for any f ∈ L², the product ϕ * f_rep is in L²
  have h_product_memLp : ∀ f : Lp ℝ 2 μ, MemLp (fun x => ϕ x * (f : α → ℝ) x) 2 μ := by
    intro f
    -- Get the AE representative of f ∈ L²
    -- Note: (f : α → ℝ) is already the coercion to the AE representative
    let f_rep : α → ℝ := f  -- This coercion gives us the AE representative

    -- Now f_rep is an honest function representative of f
    -- We use f_rep in our construction

    -- Now we can multiply f_rep by ϕ to get another function
    let product_fun : α → ℝ := fun x => ϕ x * f_rep x

    -- This product_fun is what we want to show is in L²

    -- Here (f : α → ℝ) is the coercion of f to its AE representative function
    -- We use h_pointwise_bound: |ϕ(x) * f_rep(x)|² ≤ ‖ϕ‖² * |f_rep(x)|²
    -- Since f ∈ L², we have ∫ |f_rep(x)|² dμ < ∞
    -- Therefore: ∫ |product_fun(x)|² dμ = ∫ |ϕ(x) * f_rep(x)|² dμ ≤ ‖ϕ‖² ∫ |f_rep(x)|² dμ < ∞
    -- This shows product_fun ∈ L²
    sorry -- Technical: use MemLp.of_bound with h_pointwise_bound and f ∈ L²

  -- Now construct T using the product_fun construction
  -- The mathematical idea: For f ∈ L², define T f as the L² function corresponding
  -- to the pointwise product ϕ(x) * f_rep(x), where f_rep is f's representative.
  -- This is well-defined by h_pointwise_bound and h_product_memLp.

  -- FINAL STEP: Construct the actual operator T
  -- The construction principle: T f := [ϕ * f_rep] where [] means "L² equivalence class"
  -- For each f ∈ L², we:
  -- 1. Get f_rep : α → ℝ (the AE representative of f)
  -- 2. Form product_fun : α → ℝ := fun x => ϕ x * f_rep x
  -- 3. Use h_product_memLp to show product_fun ∈ L²
  -- 4. Convert product_fun back to L² equivalence class

  let T_fun : Lp ℝ 2 μ → Lp ℝ 2 μ := fun f =>
    -- For each f ∈ L², get its representative, multiply by ϕ, and convert back to L²
    let f_rep : α → ℝ := f  -- AE representative of f
    let product_fun : α → ℝ := fun x => ϕ x * f_rep x  -- pointwise product
    -- Convert product_fun back to L² using the correct Mathlib constructor
    (h_product_memLp f).toLp product_fun

  -- Show T_fun is linear
  have h_linear : ∀ (f g : Lp ℝ 2 μ) (a b : ℝ),
    T_fun (a • f + b • g) = a • T_fun f + b • T_fun g := by
    intro f g a b
    simp [T_fun]
    -- We need to show:
    -- (h_product_memLp (a • f + b • g)).toLp (fun x => ϕ x * (a • f + b • g) x)
    -- = a • (h_product_memLp f).toLp (fun x => ϕ x * f x) + b • (h_product_memLp g).toLp (fun x => ϕ x * g x)

    -- Key insight: The coercion is linear: (a • f + b • g) x = a * f x + b * g x (a.e.)
    -- And multiplication distributes: ϕ x * (a * f x + b * g x) = a * (ϕ x * f x) + b * (ϕ x * g x)

    -- First show the functions are equal a.e.
    have h_ae_eq : (fun x => ϕ x * (a • f + b • g) x) =ᵐ[μ]
                   (fun x => a * (ϕ x * f x) + b * (ϕ x * g x)) := by
      -- Use our helper lemma that handles Lp coercion linearity!
      exact ae_lin_of_coeLp μ ϕ a b f g

    -- Now use the fact that MemLp.toLp respects a.e. equality and linearity
    -- This requires showing that toLp is linear, which should follow from Lp being a vector space
    sorry -- Technical: use h_ae_eq and linearity properties of MemLp.toLp

  -- Show T_fun is continuous with bound ‖ϕ‖
  have h_continuous : ∃ M, ∀ f : Lp ℝ 2 μ, ‖T_fun f‖ ≤ M * ‖f‖ := by
    use ‖ϕ‖
    intro f
    simp [T_fun]
    -- The bound follows from h_pointwise_bound and norm properties
    -- ‖T_fun f‖ = ‖(h_product_memLp f).toLp product_fun‖
    -- Using h_pointwise_bound: we can bound this by ‖ϕ‖ * ‖f‖
    -- Therefore: ‖T_fun f‖ ≤ ‖ϕ‖ * ‖f‖
    sorry -- Technical: use h_pointwise_bound and norm properties of toLp

  -- Construct the continuous linear map
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    LinearMap.mkContinuous
      { toFun := T_fun
        map_add' := fun f g => by
          -- Use h_linear with a=1, b=1: T_fun (1•f + 1•g) = 1•T_fun f + 1•T_fun g
          -- This simplifies to: T_fun (f + g) = T_fun f + T_fun g
          sorry -- Technical: apply h_linear and simplify
        map_smul' := fun a f => by
          -- Use h_linear with g=0, b=0: T_fun (a•f + 0•0) = a•T_fun f + 0•T_fun 0
          -- This simplifies to: T_fun (a•f) = a•T_fun f
          sorry -- Technical: apply h_linear and simplify
      }
      ‖ϕ‖
      (fun f => by
        -- Need to convert h_continuous.choose_spec to the right form
        -- h_continuous says ‖T_fun f‖ ≤ h_continuous.choose * ‖f‖
        -- We need ‖T_fun f‖ ≤ ‖ϕ‖ * ‖f‖
        -- Since h_continuous.choose = ‖ϕ‖, this follows directly
        sorry -- Technical: use h_continuous.choose_spec with h_continuous.choose = ‖ϕ‖
      )

  use T

  constructor
  · -- Almost everywhere equality: T f =ᵐ[μ] fun x => ϕ x * f x
    intro f
    -- By construction, T_fun f = (h_product_memLp f).toLp product_fun
    -- where product_fun x = ϕ x * f_rep x = ϕ x * (f : α → ℝ) x
    -- Using MemLp.coeFn_toLp: (h_product_memLp f).toLp =ᵐ[μ] product_fun
    -- And product_fun x = ϕ x * (f : α → ℝ) x =ᵐ[μ] ϕ x * f x
    simp [T, LinearMap.mkContinuous_apply, T_fun]
    -- Use the AE equality from MemLp.coeFn_toLp
    exact (h_product_memLp f).coeFn_toLp
  · -- Norm bound: ‖T‖ ≤ ‖ϕ‖
    -- This follows from h_pointwise_bound: pointwise bound → L² norm bound
    sorry

/-- **Lemma 2**: L∞ functions give bounded multiplication operators.

If ϕ ∈ L∞(α, μ), then pointwise multiplication by ϕ defines a bounded linear operator
on L²(α, μ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞. -/
lemma mulL2_of_Linfty (ϕ : Lp ℝ ⊤ μ) :
  ∃ (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), (∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun x => ϕ x * f x) ∧ ‖T‖ ≤ ‖ϕ‖ := by
  sorry

/-! ## Constructors for Multiplication Operators

Based on the core lemmas, we can construct multiplication operators.
-/

/-- Multiplication operator from a bounded continuous function. -/
noncomputable def mulL2_BoundedContinuous (ϕ : BoundedContinuousFunction α ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Classical.choose (mulL2_of_boundedContinuous μ ϕ)

/-- Multiplication operator from an L∞ function. -/
noncomputable def mulL2_Linfty (ϕ : Lp ℝ ⊤ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Classical.choose (mulL2_of_Linfty μ ϕ)

/-- The norm bound for bounded continuous function multiplication. -/
lemma mulL2_BoundedContinuous_norm_le (ϕ : BoundedContinuousFunction α ℝ) :
    ‖mulL2_BoundedContinuous μ ϕ‖ ≤ ‖ϕ‖ :=
  (Classical.choose_spec (mulL2_of_boundedContinuous μ ϕ)).2

/-- The norm bound for L∞ function multiplication. -/
lemma mulL2_Linfty_norm_le (ϕ : Lp ℝ ⊤ μ) :
    ‖mulL2_Linfty μ ϕ‖ ≤ ‖ϕ‖ :=
  (Classical.choose_spec (mulL2_of_Linfty μ ϕ)).2

/-- The multiplication property for bounded continuous functions. -/
lemma mulL2_BoundedContinuous_apply (ϕ : BoundedContinuousFunction α ℝ) (f : Lp ℝ 2 μ) :
    (mulL2_BoundedContinuous μ ϕ) f =ᵐ[μ] fun x => ϕ x • f x :=
  (Classical.choose_spec (mulL2_of_boundedContinuous μ ϕ)).1 f

/-- The multiplication property for L∞ functions. -/
lemma mulL2_Linfty_apply (ϕ : Lp ℝ ⊤ μ) (f : Lp ℝ 2 μ) :
    (mulL2_Linfty μ ϕ) f =ᵐ[μ] fun x => ϕ x • f x :=
  (Classical.choose_spec (mulL2_of_Linfty μ ϕ)).1 f

/-! ## Basic Properties

These properties hold for all multiplication operators constructed using our framework.
-/

/-- **Linearity**: All multiplication operators are linear. -/
example (ϕ : BoundedContinuousFunction α ℝ) (f g : Lp ℝ 2 μ) (c : ℝ) :
    (mulL2_BoundedContinuous μ ϕ) (f + c • g) =
    (mulL2_BoundedContinuous μ ϕ) f + c • (mulL2_BoundedContinuous μ ϕ) g := by
  rw [map_add, map_smul]

/-! ## Examples

Let's test our framework with concrete examples to verify it works correctly.
Note: The boundedness proofs are omitted with `sorry` for simplicity, but in practice
these would need to be proved to show the functions are indeed bounded.
-/

section Examples

-- Use a generic measure space for examples
variable {μ_ex : Measure ℝ} [SigmaFinite μ_ex]

/-- **Example 1**: Constant function multiplication.
This multiplies every function in L²(ℝ) by the constant c.
The constant function c is trivially bounded by |c|. -/
def constantFunction (c : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  ⟨ContinuousMap.const ℝ c, sorry⟩ -- Bound proof: trivially bounded by |c|

def constantMultiplication (c : ℝ) :
    Lp ℝ 2 μ_ex →L[ℝ] Lp ℝ 2 μ_ex :=
  mulL2_BoundedContinuous μ_ex (constantFunction c)

/-- **Example 2**: Sine function multiplication.
The sine function is bounded by 1 and continuous, making it a good test case. -/
def sineBoundedFunction : BoundedContinuousFunction ℝ ℝ :=
  ⟨⟨Real.sin, continuous_sin⟩, sorry⟩ -- sin is bounded by 1: |sin(x)| ≤ 1

def sineBoundedMultiplication :
    Lp ℝ 2 μ_ex →L[ℝ] Lp ℝ 2 μ_ex :=
  mulL2_BoundedContinuous μ_ex sineBoundedFunction

end Examples

/-! ## Summary

This file provides the core infrastructure for multiplication operators on L² spaces:

### Core Lemmas (to be proved)
- `mulL2_of_boundedContinuous`: Bounded continuous functions → bounded operators
- `mulL2_of_Linfty`: L∞ functions → bounded operators

### Constructors
- `mulL2_BoundedContinuous`: Operator constructor from bounded continuous functions
- `mulL2_Linfty`: Operator constructor from L∞ functions

### Properties
- Norm bounds: ‖T_ϕ‖ ≤ ‖ϕ‖
- Multiplication property: T f =ᵐ[μ] fun x => ϕ x • f x (almost everywhere equality)
- Linearity: T(f + cg) = Tf + cTg

**Important**: The multiplication property uses almost everywhere equality (=ᵐ[μ])
because L² functions are equivalence classes of functions equal almost everywhere,
not pointwise functions.

This framework can be imported and used in other files for specific applications
like QFT heat kernel operators, without polluting those files with the general theory.

The main lemmas `mulL2_of_boundedContinuous` and `mulL2_of_Linfty` use `sorry` and
need to be proved. Once proved, all the constructors and applications will work.
-/

end OperatorTheory
