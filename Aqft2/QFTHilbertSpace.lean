/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## QFT Hilbert Space Construction for AQFT

This file applies the multiplication operator framework from `Operators` to construct
concrete L² Hilbert spaces for quantum field theory. The focus is on spatial slices
and heat kernel operators essential for the Glimm-Jaffe reflection positivity argument.

### Spatial Geometry:

**Spatial Coordinates:**
- `SpatialCoords`: ℝ^(d-1) (space without time dimension)
- `SpatialL2`: L²(ℝ^(d-1)) space for spatial functions
- `spatialPart`: Extract spatial coordinates from spacetime
- `timeSlice`: Extract spatial function at fixed time t

### Energy Functions (Mass m > 0):

**Energy Operators:**
- `Esq`: E²(k) = ‖k‖² + m² (squared energy in momentum space)
- `E`: E(k) = √(‖k‖² + m²) (energy function)
- `E_pos`: E(k) > 0 for all k (positive energy)
- `E_bounded_below`: E(k) ≥ m (mass gap)
- `E_continuous`: Continuity of energy function
- `E_squared`: (E(k))² = E²(k) relationship

### Heat Kernel Framework:

**Heat Kernel Functions (for Reflection Positivity):**
- `heatKernel`: e^(-tE(k)) (basic exponential decay)
- `heatKernelInt`: E(k)⁻¹ e^(-tE(k)) (integrated version)
- `heatKernel_bounded`: |e^(-tE(k))| ≤ 1 for t ≥ 0
- `heatKernelInt_bounded`: |E⁻¹ e^(-tE)| ≤ m⁻¹ for t ≥ 0
- `heatKernel_continuous`: Continuity properties

**Heat Kernel Operators:**
- `heatKernelOperator`: e^(-tE) as bounded operator on SpatialL2
- `heatKernelIntOperator`: E⁻¹ e^(-tE) as bounded operator on SpatialL2
- `heatKernelOperator_norm_bound`: ‖e^(-tE)‖ ≤ 1
- `heatKernelIntOperator_norm_bound`: ‖E⁻¹ e^(-tE)‖ ≤ m⁻¹

### Multiplication Operators on Spatial Slices:

**Constructors (using OperatorTheory framework):**
- `mulSpatialL2_BoundedContinuous`: φ ∈ BC(ℝ^(d-1)) → T_φ on SpatialL2
- `mulSpatialL2_Linfty`: φ ∈ L∞(ℝ^(d-1)) → T_φ on SpatialL2
- `spatialConstantMultiplication`: Constant scaling c·f on spatial slices

### Mathematical Foundation:

**Glimm-Jaffe Application:**
Heat kernels e^(-tE) and E⁻¹ e^(-tE) provide reflection positivity (OS-3):
exponential decay dominates polynomial growth, preserving positivity under time reflection.

**Energy Spectrum:** σ(E) = [m, ∞) with mass gap m > 0 preventing zero modes.

### Integration:

**AQFT Connections:** Links to `Basic` (fields), `Operators` (framework), `Euclidean` (symmetries),
`Schwinger` (correlations), `GFFMconstruct` (Gaussian realization), `OS_Axioms` (verification).

**Physical Role:** SpatialL2 = field state space, E(k) = energy spectrum, heat kernels =
Euclidean time evolution for constructive QFT in Osterwalder-Schrader framework.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace

import Mathlib.Topology.MetricSpace.Isometry

-- Import our basic definitions
import Aqft2.Basic
import Aqft2.Operators

open MeasureTheory Complex Real
open TopologicalSpace OperatorTheory

noncomputable section

/-! ## Multiplication Operators on L² Spaces

This file formulates general lemmas for multiplication operators on L² spaces over arbitrary
measure spaces, then applies them to QFT Hilbert spaces.

**Key Lemmas** (to be proved elsewhere):
1. Bounded continuous functions give bounded multiplication operators
2. L∞ functions give bounded multiplication operators

**Applications**: SpatialCoords (spatial slices for Glimm-Jaffe arguments)
-/

-- General measure space setup
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
variable {μ : Measure α} [SigmaFinite μ]

/-! ## General Multiplication Lemmas

These are imported from Aqft2.Operators and available via the OperatorTheory namespace.
We can use them directly without redefinition.
-/

-- Note: mulL2_of_boundedContinuous and mulL2_of_Linfty are now available from OperatorTheory
-- Example usage: OperatorTheory.mulL2_of_boundedContinuous ϕ

/-! ## Using OperatorTheory: Clean Calling Conventions

We import and use the operators from OperatorTheory directly. This demonstrates
the clean calling convention and avoids redefining everything locally.
-/

-- Example: Direct use of the imported lemma
example (ϕ : BoundedContinuousFunction α ℝ) :
  ∃ (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), (∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun x => ϕ x * f x) ∧ ‖T‖ ≤ ‖ϕ‖ :=
  OperatorTheory.mulL2_of_boundedContinuous μ ϕ

-- Example: Direct use of the constructor
example (ϕ : BoundedContinuousFunction α ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  OperatorTheory.mulL2_BoundedContinuous μ ϕ

-- Example: Direct use of the norm bound
example (ϕ : BoundedContinuousFunction α ℝ) :
  ‖OperatorTheory.mulL2_BoundedContinuous μ ϕ‖ ≤ ‖ϕ‖ :=
  OperatorTheory.mulL2_BoundedContinuous_norm_le μ ϕ

/-! ## Applications to QFT Hilbert Spaces

Now we apply the general lemmas to specific spaces used in QFT, particularly
spatial coordinates for the Glimm-Jaffe argument.
-/

/-- Spatial coordinates: ℝ^{d-1} (space without time) -/
abbrev SpatialCoords := Fin (STDimension - 1) → ℝ

/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 := Lp ℝ 2 (volume : Measure SpatialCoords)

/-- Extract spatial part of spacetime coordinate -/
def spatialPart (x : SpaceTime) : SpatialCoords :=
  fun i => x ⟨i.val + 1, by simp [STDimension]; omega⟩

/-- Time slice: given time t, extract the spatial function -/
def timeSlice (t : ℝ) (f : SpaceTime → ℝ) : SpatialCoords → ℝ :=
  fun x_spatial => f (fun i => if i.val = 0 then t else
    have h_pos : i.val - 1 < STDimension - 1 := by
      cases' i with val h_val
      simp at h_val
      cases val with
      | zero => simp
      | succ n => simp [STDimension] at h_val ⊢; omega
    x_spatial ⟨i.val - 1, h_pos⟩)

-- Mass parameter assumption: m > 0
variable {m : ℝ} [Fact (0 < m)]

/-! ## Spatial Energy Operators

Following the pattern from Covariance.lean, we define the squared energy operator
E²(k) = ‖k‖² + m² and its square root E(k) = √(‖k‖² + m²) in spatial momentum space.
These act as multiplication operators on L²(ℝ^{d-1}).

We require m² > 0 for the mass parameter.
-/

/-- The squared energy function E²(k) = ‖k‖² + m² on spatial momentum space -/
def Esq (m : ℝ) (k : SpatialCoords) : ℝ :=
  ‖k‖^2 + m^2

/-- The energy function E(k) = √(‖k‖² + m²) on spatial momentum space -/
def E (m : ℝ) (k : SpatialCoords) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)

/-- The squared energy function is always positive for m > 0 -/
lemma Esq_pos {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  0 < Esq m k := by
  unfold Esq
  apply add_pos_of_nonneg_of_pos
  · exact sq_nonneg ‖k‖
  · exact pow_pos (Fact.out : 0 < m) 2

/-- The energy function E is always positive for m > 0 -/
lemma E_pos {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  0 < E m k := by
  unfold E
  apply Real.sqrt_pos.mpr
  exact Esq_pos k

/-- The squared energy function is bounded below by m² -/
lemma Esq_bounded_below {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  m^2 ≤ Esq m k := by
  unfold Esq
  apply le_add_of_nonneg_left
  exact sq_nonneg ‖k‖

/-- The energy function E is bounded below by m -/
lemma E_bounded_below {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  m ≤ E m k := by
  unfold E
  -- Since ‖k‖² + m² ≥ m², we have √(‖k‖² + m²) ≥ √(m²) = m
  have h1 : m^2 ≤ ‖k‖^2 + m^2 := by linarith [sq_nonneg ‖k‖]
  have h2 : Real.sqrt (m^2) = m := Real.sqrt_sq (le_of_lt (Fact.out : 0 < m))
  calc m
    = Real.sqrt (m^2) := h2.symm
    _ ≤ Real.sqrt (‖k‖^2 + m^2) := Real.sqrt_le_sqrt h1

/-- The energy function E is continuous -/
lemma E_continuous {m : ℝ} [Fact (0 < m)] :
  Continuous (E m) := by
  unfold E
  apply Continuous.comp Real.continuous_sqrt
  apply Continuous.add
  · exact continuous_norm.comp continuous_id |>.pow _
  · exact continuous_const

/-- Relationship: E² = (E)² -/
lemma E_squared {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  (E m k)^2 = Esq m k := by
  unfold E Esq
  exact Real.sq_sqrt (le_of_lt (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos (Fact.out : 0 < m) 2)))

/-! ## Heat Kernel Functions for Glimm-Jaffe

For the Glimm-Jaffe reflection positivity argument, we need:

1. **Basic heat kernel**: e^{-tμ} where μ = E(k) = √(‖k‖² + m²)
2. **Integrated heat kernel**: μ⁻¹ e^{-tμ} (from integrating ∫₀^∞ e^{-sμ} ds = μ⁻¹)

The integrated version is bounded on L² because the exponential decay e^{-tμ}
dominates the polynomial growth of μ⁻¹.
-/

/-- Basic heat kernel function: e^{-tμ} where μ = E(k) -/
def heatKernel (m : ℝ) (t : ℝ) (k : SpatialCoords) : ℝ :=
  Real.exp (-(t * E m k))

/-- Integrated heat kernel function: μ⁻¹ e^{-tμ} where μ = E(k)
    This represents ∫₀^∞ e^{-sμ} ds * e^{-tμ} = μ⁻¹ e^{-tμ} -/
def heatKernelInt (m : ℝ) (t : ℝ) (k : SpatialCoords) : ℝ :=
  (E m k)⁻¹ * Real.exp (-(t * E m k))

/-- The basic heat kernel function is bounded by 1 for t ≥ 0 -/
lemma heatKernel_bounded {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  ∃ C > 0, ∀ k : SpatialCoords, |heatKernel m t k| ≤ C := by
  -- For t ≥ 0, e^{-tμ} ≤ 1 since μ > 0
  use 1
  constructor
  · norm_num
  · intro k
    unfold heatKernel
    rw [Real.abs_exp]
    -- exp(-t * E m k) ≤ exp(0) = 1 for t ≥ 0 and E m k > 0
    rw [← Real.exp_zero]
    apply Real.exp_monotone
    have h_pos_E : 0 < E m k := E_pos k
    have : t * E m k ≥ 0 := mul_nonneg ht (le_of_lt h_pos_E)
    linarith

/-- The integrated heat kernel function is bounded for t ≥ 0 -/
lemma heatKernelInt_bounded {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  ∃ C > 0, ∀ k : SpatialCoords, |heatKernelInt m t k| ≤ C := by
  -- For t ≥ 0, e^{-tμ}/μ is bounded because exponential decay dominates polynomial growth
  -- The key insight: μ⁻¹ ≤ m⁻¹ and e^{-tμ} ≤ 1 for t ≥ 0, so μ⁻¹e^{-tμ} ≤ m⁻¹

  have h_pos_m : 0 < m := Fact.out

  use m⁻¹  -- The bound C = 1/m works
  constructor
  · exact inv_pos.mpr h_pos_m
  · intro k
    have h_pos_E : 0 < E m k := E_pos k

    unfold heatKernelInt
    rw [abs_mul]
    -- Now we have |(E m k)⁻¹| * |Real.exp (-(t * E m k))| ≤ m⁻¹

    -- Key ingredients:
    -- 1. E(k) ≥ m, so (E(k))⁻¹ ≤ m⁻¹
    -- 2. exp(-t*E(k)) ≤ 1 for t ≥ 0

    have h_exp_le_one : Real.exp (-(t * E m k)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_monotone
      -- For t ≥ 0 and E(k) > 0, we have -t*E(k) ≤ 0
      have : t * E m k ≥ 0 := mul_nonneg ht (le_of_lt h_pos_E)
      linarith

    have h_inv_bound : (E m k)⁻¹ ≤ m⁻¹ := by
      -- This follows from m ≤ E m k and the fact that inverse reverses inequalities
      have h_bound : m ≤ E m k := E_bounded_below k
      -- For 0 < a ≤ b, we have b⁻¹ ≤ a⁻¹
      rw [← one_div, ← one_div]
      rwa [one_div_le_one_div h_pos_E h_pos_m]

    -- Combine the bounds: |(E m k)⁻¹| * |exp(-t * E m k)| ≤ m⁻¹ * 1 = m⁻¹
    have h_step1 : |(E m k)⁻¹| * |Real.exp (-(t * E m k))| ≤ m⁻¹ * |Real.exp (-(t * E m k))| := by
      apply mul_le_mul_of_nonneg_right
      · rwa [abs_inv, abs_of_pos h_pos_E]
      · exact abs_nonneg _
    have h_step2 : m⁻¹ * |Real.exp (-(t * E m k))| ≤ m⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rwa [Real.abs_exp]
      · exact inv_nonneg.mpr (le_of_lt h_pos_m)
    have h_step3 : m⁻¹ * 1 = m⁻¹ := by rw [mul_one]

    -- Chain the inequalities
    calc |(E m k)⁻¹| * |Real.exp (-(t * E m k))|
      ≤ m⁻¹ * |Real.exp (-(t * E m k))| := h_step1
      _ ≤ m⁻¹ * 1 := h_step2
      _ = m⁻¹ := h_step3

/-- The basic heat kernel function is continuous for t ≥ 0 -/
lemma heatKernel_continuous {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  Continuous (heatKernel m t) := by
  unfold heatKernel
  -- Real.exp (-(t * E m k)) is continuous
  apply Continuous.comp Real.continuous_exp
  apply Continuous.neg
  apply Continuous.mul
  · exact continuous_const
  · exact E_continuous.comp continuous_id

/-- The integrated heat kernel function is continuous for t ≥ 0 -/
lemma heatKernelInt_continuous {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  Continuous (heatKernelInt m t) := by
  unfold heatKernelInt
  apply Continuous.mul
  · -- (E m k)⁻¹ is continuous where E m k > 0
    apply Continuous.inv₀
    exact E_continuous.comp continuous_id
    intro k
    exact ne_of_gt (E_pos k)
  · -- Real.exp (-(t * E m k)) is continuous
    apply Continuous.comp Real.continuous_exp
    apply Continuous.neg
    apply Continuous.mul
    · exact continuous_const
    · exact E_continuous.comp continuous_id

/-- **Application**: Basic heat kernel as a bounded operator on spatial L².

This constructs the basic heat kernel operator e^{-tμ} as a bounded linear operator on L²(SpatialCoords).
Uses the general `OperatorTheory.mulL2_of_boundedContinuous` framework. -/
noncomputable def heatKernelOperator (m : ℝ) [Fact (0 < m)] (t : ℝ) (ht : 0 ≤ t) :
    SpatialL2 →L[ℝ] SpatialL2 :=
  -- The basic heat kernel e^{-tμ} is bounded and continuous, so we can use the operator theory
  let ϕ_heat : BoundedContinuousFunction SpatialCoords ℝ := by
    -- We construct the bounded continuous function from heatKernel
    -- Continuity follows from heatKernel_continuous, boundedness from heatKernel_bounded
    exact ⟨⟨heatKernel m t, heatKernel_continuous ht⟩, sorry⟩ -- bound proof to be filled later
  OperatorTheory.mulL2_BoundedContinuous (volume : Measure SpatialCoords) ϕ_heat

/-- The basic heat kernel operator has norm bound ≤ 1. -/
lemma heatKernelOperator_norm_bound (m : ℝ) [Fact (0 < m)] (t : ℝ) (ht : 0 ≤ t) :
    ‖heatKernelOperator m t ht‖ ≤ 1 := by
  -- This follows from heatKernel_bounded
  sorry

/-- **Main Application**: Integrated heat kernel as a bounded operator on spatial L².

This uses our general multiplication lemma to construct the heat kernel operator
μ⁻¹ e^{-(s+t)μ} as a bounded linear operator on L²(SpatialCoords). -/
noncomputable def heatKernelIntOperator (m : ℝ) [Fact (0 < m)] (t : ℝ) (ht : 0 ≤ t) :
    SpatialL2 →L[ℝ] SpatialL2 := by
  -- For now, we use the general multiplication lemma structure
  -- The proof that the integrated heat kernel gives a bounded continuous function
  -- will be completed when we prove the general lemmas
  sorry

/-- The integrated heat kernel operator has the expected norm bound. -/
lemma heatKernelIntOperator_norm_bound (m : ℝ) [Fact (0 < m)] (t : ℝ) (ht : 0 ≤ t) :
    ‖heatKernelIntOperator m t ht‖ ≤ m⁻¹ := by
  -- This follows from our general norm bound and the heat kernel bound
  sorry

/-! ## Applications to Real-Valued Spatial L² -/

/-- **Application 1**: Multiplication by bounded continuous functions on spatial slices. -/
def mulSpatialL2_BoundedContinuous (ϕ : BoundedContinuousFunction SpatialCoords ℝ) :
    SpatialL2 →L[ℝ] SpatialL2 :=
  OperatorTheory.mulL2_BoundedContinuous (volume : Measure SpatialCoords) ϕ

/-- **Application 2**: Multiplication by L∞ functions on spatial slices. -/
def mulSpatialL2_Linfty (ϕ : Lp ℝ ⊤ (volume : Measure SpatialCoords)) :
    SpatialL2 →L[ℝ] SpatialL2 :=
  OperatorTheory.mulL2_Linfty (volume : Measure SpatialCoords) ϕ

/-- **Example**: Constant function multiplication on spatial slices. -/
def spatialConstantMultiplication (c : ℝ) :
    SpatialL2 →L[ℝ] SpatialL2 :=
  let ϕ_const : BoundedContinuousFunction SpatialCoords ℝ :=
    ⟨ContinuousMap.const SpatialCoords c, |c|, fun x => by simp⟩
  mulSpatialL2_BoundedContinuous ϕ_const

/-! ## Properties and Examples -/

/-- **Property**: Constant multiplication has the expected norm bound. -/
example (c : ℝ) :
    ‖spatialConstantMultiplication c‖ ≤ |c| := by
  -- This follows from the general norm bound lemma
  sorry

/-- **Linearity**: All multiplication operators are linear. -/
example (ϕ : BoundedContinuousFunction SpatialCoords ℝ) (f g : SpatialL2) (c : ℝ) :
    (mulSpatialL2_BoundedContinuous ϕ) (f + c • g) =
    (mulSpatialL2_BoundedContinuous ϕ) f + c • (mulSpatialL2_BoundedContinuous ϕ) g := by
  rw [map_add, map_smul]
