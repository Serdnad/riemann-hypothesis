module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentiableAtOrbit
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharacters
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceStabUFromIntegralUnipotentIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellLieAlg

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (P : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hP : ∀ X, X ∈ lieOf S ↔ X ∈ P) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE S ↔ unrealify x ∈ P := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have e : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
        ext i j; rfl
      show unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ P
      rw [e]; exact (hP X).1 hX
    | zero =>
      have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.zero_mem
    | add x y _ _ hx hy =>
      have e : unrealify (x + y) = unrealify x + unrealify y := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.add_mem hx hy
    | smul c x _ hx =>
      have e : unrealify (c • x) = c • unrealify x := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.smul_mem c hx
  · intro hx
    refine Submodule.subset_span ⟨unrealify x, (hP _).2 hx, ?_⟩
    ext ⟨i, j, b⟩
    cases b <;> rfl

open scoped Matrix.Norms.Operator in
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  apply GlobalTheory.OmegaFrobenius.mem_lieOf_UH <;> assumption

open scoped Matrix.Norms.Operator in
theorem exp_mul_eq_iff {N : ℕ} (X E : Matrix (Fin N) (Fin N) ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • X) * E = E) ↔ X * E = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * E)
      (NormedSpace.exp (t • X) * X * E) t := fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).mul_const E
  constructor
  · intro h
    have h0 := hd 0
    rw [show (fun t : ℝ => NormedSpace.exp (t • X) * E) = fun _ => E from funext h] at h0
    simpa using h0.unique (hasDerivAt_const _ _)
  · intro h t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => by rw [(hd t).deriv, Matrix.mul_assoc, h, Matrix.mul_zero]) t 0
    simpa using this

theorem mul_single_eq_iff {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    g * Matrix.single j j (1 : ℂ) = h * Matrix.single j j (1 : ℂ) ↔ g *ᵥ bvec j = h *ᵥ bvec j := by
  simp only [bvec, Matrix.mulVec_single_one]
  constructor
  · intro e
    funext i
    simpa using congrFun (congrFun e i) j
  · intro e
    ext i l
    by_cases hl : l = j
    · subst hl
      simpa using congrFun e i
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]

theorem exp_fix_iff {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) ↔ ∀ i, X i j = 0 := by
  have h1 := exp_mul_eq_iff X (Matrix.single j j (1 : ℂ))
  have h2 := mul_single_eq_iff X 0 j
  rw [Matrix.zero_mul] at h2
  rw [h2] at h1
  have h3 : X *ᵥ bvec j = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ bvec j ↔ ∀ i, X i j = 0 := by
    simp [bvec, funext_iff]
  rw [← h3, ← h1]
  refine forall_congr' fun t => ?_
  have h4 := mul_single_eq_iff (NormedSpace.exp (t • X)) 1 j
  rw [Matrix.one_mul, Matrix.one_mulVec] at h4
  rw [h4, Complex.coe_smul]

theorem rows_zero {k r : ℕ} {X : Mat k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0)
    (hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0)
    (i : Fin (2 * r + k + 1)) (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) : X i j = 0 := by
  have hil := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hv : i'.val = 2 * r + k - i.val := rfl
  have h := congrFun (congrFun hX i') j
  have h1 : (Xᴴ * Hpk k r) i' j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.conjTranspose_apply, hc i' (by omega) l, star_zero, zero_mul]
  have h2 : (Hpk k r * X) i' j = X i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · have : Hpk k r i' i = 1 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, one_mul]
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun e => hl (Fin.ext e)
      have : Hpk k r i' l = 0 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · simp
  rw [Matrix.add_apply, h1, h2, zero_add] at h
  exact h

theorem mem_lieOf_UWb (k r : ℕ) (X : Mat k r) :
    X ∈ lieOf (Formalism.FourierDecayAlt.B2.UWb k r) ↔ (Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0) := by
  have hH := (hpkFacts k r).2.1
  constructor
  · intro h
    have hX := (mem_lieOf_UH _ hH X).1 fun t => (h t).1
    have hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0 := by
      intro j hj
      have hjl := j.isLt
      by_cases hr : j.val < r
      · exact (exp_fix_iff X j).1 fun t => ((h t).2 ⟨j.val, hr⟩).1
      · have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rw [← e]
        exact (exp_fix_iff X _).1 fun t => ((h t).2 _).2
    refine ⟨hX, fun i j hij => ?_⟩
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · exact hc j (fun hj => hij ⟨hi, hj⟩) i
    · exact rows_zero hX hc i hi j
  · rintro ⟨hX, h0⟩ t
    refine ⟨(mem_lieOf_UH _ hH X).2 hX t, fun a => ⟨?_, ?_⟩⟩
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.1; have := a.isLt
      simp only [eI] at *; omega
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.2; have := a.isLt
      simp only [esI] at *; omega

def skewSub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    have ha' : aᴴ * H + H * a = 0 := ha
    have hb' : bᴴ * H + H * b = 0 := hb
    show (a + b)ᴴ * H + H * (a + b) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' c a ha := by
    have ha' : aᴴ * H + H * a = 0 := ha
    show (c • a)ᴴ * H + H * (c • a) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha', smul_zero]

def midSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {a b} ha hb := fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha := fun i j h => by rw [Matrix.smul_apply, ha i j h, smul_zero]

theorem lie_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  intro k r x
  have h2 := mem_lieE_iff (S := Formalism.FourierDecayAlt.B2.UWb k r) (skewSub (Hpk k r) ⊓ midSub k r) (mem_lieOf_UWb k r) x
  refine ⟨mem_lieE_iff (skewSub (Hpk k r)) (mem_lieOf_UH _ (hpkFacts k r).2.1) x, h2, fun hx => ?_⟩
  have h := (mem_lieOf_UWb k r _).2 (h2.1 hx) 1
  simpa using h

end GlobalTheory.CellLieAlg
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarTransport

theorem isMatGroup_UH_of_sq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  apply GlobalTheory.OmegaFrobenius.isMatGroup_UH <;> assumption

theorem haar_transport : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r),
    IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  intro k r μG ε P hμ hP hH
  have hce := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hP
  have hm := hce.continuous.measurable
  have hme := hce.measurableEmbedding
  have hG : PI.IsMatGroup (GG k r) := isMatGroup_UH_of_sq _ (hpkFacts k r).2.1
  have hmem : ∀ y, Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∈ GG k r := fun y =>
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH _).1 ⟨y, rfl⟩
  have hν : PI.IsHaarOnM (GG k r) ((Formalism.REAL.muG ε).map (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P)) := by
    refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
    · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 (NeZero.ne _)
    · have hcl : IsClosed {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r} := hG.1
      show (Measure.map _ _) {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = 0
      rw [Measure.map_apply hm hcl.measurableSet.compl]
      have : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ⁻¹' {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = ∅ := by
        ext y; simpa using hmem y
      rw [this, measure_empty]
    · intro a ha
      obtain ⟨u, hu⟩ := (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH a).2 ha
      subst hu
      have hl : Measurable (PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)) :=
        (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_cont (k := k) (r := r) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)).measurable
      rw [Measure.map_map hl hm]
      have e : PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u) ∘ Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P =
          Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ∘ (fun v => u * v) := by
        funext v; exact Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u v
      rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  obtain ⟨c, -, hct, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ μG hG hμ').1 _ hν
  refine ⟨c, hct.ne, fun φ hφ => ?_⟩
  have h1 : ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) =
      ∫⁻ y, φ (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∂(Formalism.REAL.muG ε) := rfl
  rw [h1, ← lintegral_map hφ hm, hc, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.HaarTransport

end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem stepBoundAt_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ)
    (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B Cg n₀ d p q b hn₀ hC
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  have hK := countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hC
  obtain ⟨hD, -, -, -, -, -, -, -, hlam, -⟩ := hC
  refine GlobalTheory.StepGlob.stepBoundAt_of_local B b (fun v => ?_)
  obtain ⟨hpar, hds, -, -⟩ := hD v
  have hU : IsURepOn (UJset (B.I.ε v)) (B.σ v) := hds.2.2.1
  have h120v : 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hrk v]; exact h120
  have heig := GlobalTheory.T.lowestKType_infinitesimalChar_large_gap B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hpar hds h (hgap v) h120v
  exact ⟨hU, GlobalTheory.StepBoundOneRep.stepBound_of_eigen B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) b hU
    (hK v) heig (hlam v)⟩

end GlobalTheory.Dec
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem zOf_coeff_mem {G : Type} [Group G] [Fintype G] (K : IntermediateField ℚ ℂ) (χ : G → ℂ)
    (h : ∀ x, χ x ∈ K) (y : G) : (zOf χ).coeff y ∈ K := by
  unfold zOf
  refine Finset.sum_induction _ (fun a : MonoidAlgebra ℂ G => a.coeff y ∈ K) ?_ ?_ ?_
  · intro a b ha hb
    have := K.add_mem ha hb
    simpa using this
  · simp
  · intro x _
    have h1 : χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ ∈ K :=
      K.mul_mem (K.div_mem (h 1) (natCast_mem K _)) (h _)
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact h1
    · exact K.zero_mem

theorem isSer_eSerC (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) (r N : ℕ) (hN : 0 < N)
    (hd : Nat.card (GL (Fin r) (ZMod g)) ∣ N) : GlobalTheory.MemN.IsSer r g N (eSerC L r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L hg hG r
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · intro f
    refine ⟨fun h0 hf => GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero g L hG r f hf.1 hf.2.1 hf.2.2 h0, h4 f⟩
  · intro f x
    unfold eSerC
    refine finsum_mem_induction (fun a : MonoidAlgebra ℂ (Gn g r) => a.coeff x ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}) ?_ ?_ ?_
    · simp
    · intro a b ha hb
      have := add_mem ha hb
      simpa using this
    · intro χ hχ
      obtain ⟨⟨V, _, hV⟩, _⟩ := hχ
      exact zOf_coeff_mem _ χ (GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin (Gn g r) χ N hN hd ⟨V, hV⟩) x

end GlobalTheory.GLm
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k), ∃ κ : UPts cm.sig J (Ad F), κ.1 ∈ stabGL (hat F S.Lb) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.St.G.LvlZero.level_conj_frame | exact GlobalTheory.St.G.LvlZero.level_conj_frame | (intros; apply GlobalTheory.St.G.LvlZero.level_conj_frame <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.FixedForm

theorem sum_le_orbit {G α ι : Type} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞)
    (t : Finset ι) (x : ι → α) (hQ : ∀ i ∈ t, ∀ ρ : G, Q (ρ • x i) ∧ w (ρ • x i) = w (x i))
    (hd : ∀ i ∈ t, ∀ i' ∈ t, (∃ ρ : G, ρ • x i = x i') → i = i') :
    ∑ i ∈ t, w (x i) ≤ ∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0 := by
  let q : ι → MulAction.orbitRel.Quotient G α := fun i => Quotient.mk _ (x i)
  have hinj : ∀ i ∈ t, ∀ i' ∈ t, q i = q i' → i = i' := by
    intro i hi i' hi' h
    have h1 : (MulAction.orbitRel G α) (x i') (x i) := Quotient.exact h.symm
    rw [MulAction.orbitRel_apply] at h1
    exact hd i hi i' hi' h1
  have h1 : ∑ i ∈ t, w (x i) = ∑ o ∈ t.image q, if Q o.out then w o.out else 0 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 : (MulAction.orbitRel G α) (q i).out (x i) := Quotient.exact (Quotient.out_eq (q i))
    rw [MulAction.orbitRel_apply] at h2
    obtain ⟨ρ, hρ⟩ := h2
    have hρ' : ρ • x i = (q i).out := hρ
    rw [← hρ', if_pos (hQ i hi ρ).1, (hQ i hi ρ).2]
  rw [h1]
  exact ENNReal.sum_le_tsum _

theorem nD_nonneg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (l : ℕ) :
    0 ≤ N.nD l := by
  unfold NF.nD
  split_ifs
  · positivity
  · exact le_rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ₀ ι s Λ hg h0 hs hd
  set B : ℝ := (N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hB
  have hDel : 0 ≤ N.Del := nD_nonneg N _
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => nD_nonneg N l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hom := (GlobalTheory.DegAsm.WeightInf.main K V H hK r).1 N g
  let f : ι → Submodule (𝓞 K) V := fun i => latL N.F' N.F (Λ i)
  have hcard : ((s.image f).card : ℝ) ≤ N.NT ^ 2 := by
    have h1 := GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm K V H hK r N g Λ₀ hg h0
    have h2 : ((s.image f : Finset _) : Set (Submodule (𝓞 K) V)) ⊆ {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ₀} := by
      intro L hL
      rw [Finset.mem_coe, Finset.mem_image] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact ⟨Λ i, (hs i hi).1, rfl, (hs i hi).2.2.1⟩
    have h3 := (ENat.toENNReal_le.2 (Set.encard_le_encard h2)).trans h1
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hfib : ∀ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) ≤ B := by
    intro L hL
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hL
    have h1 := GlobalTheory.T.hermFrame_weightSum_sameDatum_le K V H hK r N g (Λ i₀) hg (hs i₀ hi₀).1
    have hgI : N.gI g (Λ i₀) = N.gI g Λ₀ := by
      unfold NF.gI latLa flagPairDefinitePartLattice
      rw [(hs i₀ hi₀).2.1, (hs i₀ hi₀).2.2.2]
    rw [hgI, ← hB] at h1
    have h2 := sum_le_orbit (G := N.R) (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g (Λ i₀) Λ')
      (fun Λ' => ENNReal.ofReal (N.om Λ')) (s.filter fun i => f i = f i₀) Λ
      (by
        intro i hi ρ
        obtain ⟨hi, hfi⟩ := Finset.mem_filter.1 hi
        obtain ⟨a1, ⟨a2, a3, a4⟩, -⟩ := GlobalTheory.DegCnt.StabInv.main K V H hK r N g (Λ i) hg (hs i hi).1 ρ.1 ρ.2
        refine ⟨⟨a1, a2.trans ((hs i hi).2.1.trans (hs i₀ hi₀).2.1.symm), a3.trans hfi,
          a4.trans ((hs i hi).2.2.2.trans (hs i₀ hi₀).2.2.2.symm)⟩, ?_⟩
        exact congrArg ENNReal.ofReal ((hom (Λ i) hg (hs i hi).1).2 ρ.1 ρ.2))
      (by
        rintro i hi i' hi' ⟨ρ, hρ⟩
        exact hd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 ⟨ρ.1, ρ.2, hρ⟩)
    have h3 : ∑ i ∈ s with f i = f i₀, ENNReal.ofReal (N.om (Λ i)) ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h1
      unfold NF.omSum
      convert h2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      (hom (Λ i) hg (hs i (Finset.mem_filter.1 hi).1).1).1.le), ENNReal.ofReal_le_ofReal_iff hB0] at h3
    exact h3
  calc ∑ i ∈ s, N.om (Λ i) = ∑ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ ≤ (s.image f).card • B := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = ((s.image f).card : ℝ) * B := nsmul_eq_mul _ _
    _ ≤ N.NT ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0

end GlobalTheory.DegAsm.FixedForm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  first | exact @GlobalTheory.AdaptedExists.exists_isAdapted | exact GlobalTheory.AdaptedExists.exists_isAdapted | (intros; apply GlobalTheory.AdaptedExists.exists_isAdapted <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruence_stabU_from_integral_unipotent_isometry : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ (∏ τ, ‖embS D τ (Gval (lf D F0) F')‖) ^ 4 * ∏ τ, ‖embS D τ (Dr1 (lf D F0) F')‖ ^ 2 ∧ ∀ a ∈ GlobalTheory.LoopV.stabU (ZhatL (lf D F0) F'), GlobalTheory.LoopV.EntIn I (a - 1) → ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∀ c, n (frame F' c) = ∑ i, a i c • frame F' i := by
  first | exact @GlobalTheory.LoopV.Cong.congruence_mem | exact GlobalTheory.LoopV.Cong.congruence_mem | (intros; apply GlobalTheory.LoopV.Cong.congruence_mem <;> assumption)
end
