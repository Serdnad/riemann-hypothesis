module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalDualModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

namespace ColHigh

variable {ι : Type} {m n : ℕ}

def der (m : ℕ) (τ : ι) (k l : Fin n) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ i : Fin m, (X (τ, i, k) : Pol ι m n) • pderiv (τ, i, l)

theorem der_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) : der m τ k l P = colLie m τ k l P := by
  have h (S : Finset (Fin m)) (D : Fin m → Derivation ℂ (Pol ι m n) (Pol ι m n)) :
      (∑ i ∈ S, D i) P = ∑ i ∈ S, D i P := by
    rw [← Finset.sum_apply]
    exact congrFun (map_sum Derivation.coeFnAddMonoidHom D S) P
  simp [der, h, colLie_apply]

theorem der_X [DecidableEq ι] (t t' : ι) (k l j : Fin n) (a : Fin m) :
    der m t k l (X (t', a, j)) = if t' = t ∧ j = l then X (t, a, k) else 0 := by
  rw [der_apply, colLie_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [pderiv_X, Pi.single_apply]
  · have (a' : Fin m) : ((t', a, j) : ι × Fin m × Fin n) ≠ (t, a', l) := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [pderiv_X, this]

theorem comm [DecidableEq ι] (t t' : ι) (i k l : Fin n) (P : Pol ι m n) :
    colLie m t i i (colLie m t' k l P) - colLie m t' k l (colLie m t i i P) =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        colLie m t' k l P := by
  have : ⁅der m t i i, der m t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        der m t' k l := by
    refine MvPolynomial.derivation_ext fun ⟨s, a, j⟩ => ?_
    rw [Derivation.commutator_apply, Derivation.smul_apply]
    simp only [der_X, apply_ite (der m t i i), apply_ite (der m t' k l), map_zero]
    by_cases h1 : s = t' ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases h2 : s = t
      · subst h2
        by_cases h3 : i = k <;> by_cases h4 : i = j <;> simp [h3, h4, eq_comm, sub_smul] <;>
          (try split_ifs) <;> simp_all
      · simp [h2, Ne.symm h2]
    · simp only [if_neg h1, smul_zero, zero_sub, neg_eq_zero]
      split_ifs with h2 h3
      · exact absurd ⟨h2.1.trans h3.1, h2.2.trans h3.2⟩ h1
      · rfl
      · rfl
  have := DFunLike.congr_fun this P
  rw [Derivation.commutator_apply, Derivation.smul_apply] at this
  simpa only [der_apply] using this

theorem diag_monomial (t : ι) (k : Fin n) (s : ι × Fin m × Fin n →₀ ℕ) (c : ℂ) :
    colLie m t k k (monomial s c) = ((∑ a, (s (t, a, k) : ℤ) : ℤ) : ℂ) • monomial s c := by
  simp only [colLie_apply, X_mul_pderiv_monomial, Int.cast_sum,
    Int.cast_natCast, Finset.sum_smul, Nat.cast_smul_eq_nsmul]

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (a b : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) : X a * pderiv b P ∈ restrictTotalDegree σ ℂ d := by
  classical

  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · rw [mem_restrictTotalDegree] at hP ⊢
    have h1 : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hP
    have h2 : s - Finsupp.single b 1 + Finsupp.single b 1 = s :=
      Finsupp.sub_add_single_one_cancel h
    have h3 : ((s - Finsupp.single b 1).sum fun _ e => e) + 1 = s.sum fun _ e => e := by
      conv_rhs => rw [← h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    refine (totalDegree_mul _ _).trans ?_
    have h4 := totalDegree_monomial_le (s - Finsupp.single b 1) (AddMonoidAlgebra.coeff P s * (s b : ℂ))
    rw [totalDegree_X]
    have h5 : ((s - Finsupp.single b 1).sum fun _ => id) = (s - Finsupp.single b 1).sum fun _ e => e := rfl
    omega

theorem colLie_mem (d : ℕ) (t : ι) (k l : Fin n) (P : Pol ι m n)
    (hP : P ∈ restrictTotalDegree _ ℂ d) : colLie m t k l P ∈ restrictTotalDegree _ ℂ d := by
  rw [colLie_apply]
  exact Submodule.sum_mem _ fun i _ => X_mul_pderiv_mem d _ _ P hP

theorem exists_bound {σ X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (Φ : X →ₗ[ℂ] MvPolynomial σ ℂ) : ∃ d, ∀ x, Φ x ∈ restrictTotalDegree σ ℂ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun i => (Φ (b i)).totalDegree, fun x => ?_⟩

  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_restrictTotalDegree]
  exact Finset.le_sup (f := fun i => (Φ (b i)).totalDegree) (Finset.mem_univ i)

end ColHigh


open ColHigh in
theorem exists_colHighest (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)) (hU0 : U ≠ ⊥)
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) :
    ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧
      ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  classical
  have hL : ∀ τ k l, ∀ Φ ∈ U, colLie m τ k l ∘ₗ Φ ∈ U := by
    intro τ k l Φ hΦ
    obtain ⟨d, hd⟩ := exists_bound Φ
    obtain ⟨s, c, h⟩ := GlobalTheory.T.colLieOperator_eq_sum_colUnitaryAction_bddDegree ι m n d τ k l
    have : colLie m τ k l ∘ₗ Φ = ∑ g ∈ s, c g • (colSub m τ g ∘ₗ Φ) := by
      ext1 x
      rw [LinearMap.comp_apply, ← h _ ((mem_restrictTotalDegree _ _ _).1 (hd x))]
      simp [LinearMap.sum_apply]
    rw [this]
    exact U.sum_mem fun g _ => U.smul_mem _ (hU Φ hΦ τ g)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨d, hd⟩ := exists_bound Φ₀
  let R : Submodule ℂ (Pol ι m n) := restrictTotalDegree _ ℂ d
  let B : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range (LinearMap.llcomp ℂ X R _ R.subtype : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n))
  have hB : ∀ Φ, Φ ∈ B ↔ ∀ x, Φ x ∈ R := by
    intro Φ
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  have : FiniteDimensional ℂ B := inferInstance
  have : FiniteDimensional ℂ (U ⊓ B : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_right
  let e : ι → Fin n → Fin n → Module.End ℂ (X →ₗ[ℂ] Pol ι m n) :=
    fun τ k l => LinearMap.llcomp ℂ X _ _ (colLie m τ k l)
  have he : ∀ τ k l Φ, e τ k l Φ = colLie m τ k l ∘ₗ Φ := fun _ _ _ _ => rfl
  obtain ⟨Φ, hΦ, h0, h1, μ, h2⟩ := GlobalTheory.exists_highest_vector e (by
      intro t t' i k l
      refine LinearMap.ext fun Φ => LinearMap.ext fun x => ?_
      exact comm t t' i k l (Φ x))
    (by
      rw [eq_top_iff]
      intro Φ _
      let b := Module.finBasis ℂ X
      have : Φ = ∑ i, ∑ s ∈ (Φ (b i)).support, (b.coord i).smulRight (monomial s (AddMonoidAlgebra.coeff (Φ (b i)) s)) := by
        refine LinearMap.ext fun x => ?_

        conv_lhs => rw [← b.sum_repr x, map_sum]
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, ← Finset.smul_sum, map_smul,
          ← as_sum, Module.Basis.coord_apply]
      rw [this]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun s _ => ?_
      refine Submodule.mem_iSup_of_mem (fun t k => ∑ a, (s (t, a, k) : ℤ)) ?_
      simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro t k
      refine LinearMap.ext fun x => ?_
      rw [he, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        diag_monomial, smul_comm])
    (U ⊓ B) (fun τ k l Φ hΦ => ⟨hL τ k l Φ hΦ.1,
      (hB _).2 fun x => colLie_mem d τ k l _ ((hB _).1 hΦ.2 x)⟩)
    ((Submodule.ne_bot_iff _).2 ⟨Φ₀, ⟨hΦ₀, (hB _).2 hd⟩, hne⟩)
  exact ⟨Φ, hΦ.1, h0, h1, μ, h2⟩

end GlobalTheory.DefLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.WordCont

theorem continuous_apply_family {Y L E : Type} [TopologicalSpace Y] [AddCommGroup L] [Module ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Y → L →ₗ[ℝ] E) (hW : ∀ x, Continuous fun y => W y x)
    {f : Y → L} (hf : Continuous f) : Continuous fun y => W y (f y) := by
  let b := Module.finBasis ℝ L
  have e : (fun y => W y (f y)) = fun y => ∑ i, b.coord i (f y) • W y (b i) := by
    funext y

    conv_lhs => rw [← b.sum_repr (f y), map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp hf).smul (hW _)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.UnitaryLieAlgebra.unitaryLie G

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_word [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {Y : Type} [TopologicalSpace Y] (l : List (Y → Matrix (Fin n) (Fin n) ℂ))
    (hc : ∀ f ∈ l, Continuous f) (hm : ∀ f ∈ l, ∀ y, f y ∈ lieG G) :
    ∀ w ∈ smSub G (trRep σ P), Continuous fun y => word (trRep σ P) (l.map fun f => f y) w := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  induction l using List.reverseRecOn with
  | nil => intro w _; exact continuous_const
  | append_singleton l f ih =>
    intro w hw
    have hc' : ∀ f ∈ l, Continuous f := fun g hg => hc g (by simp [hg])
    have hm' : ∀ f ∈ l, ∀ y, f y ∈ lieG G := fun g hg => hm g (by simp [hg])
    have hl : ∀ y, ∀ X ∈ l.map (fun f => f y), X ∈ lieG G := fun y X hX => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg y
    obtain ⟨hadd, hsm⟩ := GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ w hw
    let W : Y → lieSub G →ₗ[ℝ] H := fun y =>
      { toFun := fun X => word (trRep σ P) (l.map fun f => f y) (dRep (trRep σ P) X w)
        map_add' := fun X Z => by
          rw [Submodule.coe_add, hadd _ X.2 _ Z.2,
            word_add hG hπ (hl y) (dRep_mem hG hπ hw X.2) (dRep_mem hG hπ hw Z.2)]
        map_smul' := fun a X => by
          rw [Submodule.coe_smul, hsm a _ X.2, word_smul hG hπ (hl y) _ (dRep_mem hG hπ hw X.2)]
          simp }
    have hf : Continuous fun y => (⟨f y, hm f (by simp) y⟩ : lieSub G) :=
      (hc f (by simp)).subtype_mk _
    have := continuous_apply_family W (fun X => ih hc' hm' _ (dRep_mem hG hπ hw X.2)) hf
    simp only [List.map_append, word_append, List.map_cons, List.map_nil, word_cons, word_nil]
    exact this

theorem word_rep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    {w : H} (hw : w ∈ smSub G π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    word π l (π g w) = π g (word π (l.map fun X => g⁻¹ * X * g) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hm : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ lieG G := fun Y hY => by
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lieG hG hg (hl' Z hZ)
    rw [word_cons, ih hl', dRep_rep hG hπ (word_mem hG hπ hm hw) hg (hl X (by simp))]
    rfl

theorem continuous_sigma (hσ : IsURepOn (UJset ε) σ) {u : Formalism.REAL.UJ ε → H} (hu : Continuous u) :
    Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (u g) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g => σ (umat g) (u g) - σ (umat g) (u g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun g : Formalism.REAL.UJ ε => ‖σ (umat g) (u g) - σ (umat g) (u g₀)‖) = fun g => ‖u g - u g₀‖ := by
      funext g
      rw [← map_sub, hσ.2.1 _ g.2]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt
  have h2 := h1.add (continuous_orbit hσ (u g₀)).continuousAt
  simpa [ContinuousAt] using h2

theorem continuous_word_translate : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hmem : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ Formalism.QuantumDeterminants.UH G := fun g => conj_mem_UH hP h g.2
  have hinv : ∀ g : Formalism.REAL.UJ ε, (P⁻¹ * umat g * P)⁻¹ = P⁻¹ * umat g⁻¹ * P := fun g => by
    apply Matrix.inv_eq_right_inv
    have e : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    calc P⁻¹ * umat g * P * (P⁻¹ * umat g⁻¹ * P) = P⁻¹ * (umat g * (P * P⁻¹) * umat g⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hd, Matrix.mul_one, e, Matrix.mul_one, nonsing_inv_mul _ hd]
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const
  have c2 : Continuous fun g : Formalism.REAL.UJ ε => (P⁻¹ * umat g * P)⁻¹ := by
    simp only [hinv]
    exact c1.comp continuous_inv
  have hc := continuous_word hP h hσ
    (l.map fun X (g : Formalism.REAL.UJ ε) => (P⁻¹ * umat g * P)⁻¹ * X * (P⁻¹ * umat g * P))
    (fun f hf => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hf
      exact (c2.matrix_mul continuous_const).matrix_mul c1)
    (fun f hf g => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_mem_lieG hG (hmem g) (hl X hX)) w hw
  convert continuous_sigma hσ hc using 2 with g
  have := word_rep hG hπ hw (hmem g) hl
  rw [trRep_conj hP] at this
  rw [this, List.map_map]
  rfl

end GlobalTheory.SmVec.WordCont
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PureVirt

variable {ι : Type} [Fintype ι] {m : ι → ℕ} {S : Type} [CommRing S] [Algebra ℝ S]

def Virt (m : ι → ℕ) (g : ℕ → Mat m S → S) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ),
    ∀ (A : Mat m S) (b : ℕ), ∑ j, c j • (ρ j).ptr b A = g b A

theorem virt_smul (r : ℝ) {g : ℕ → Mat m S → S} (hg : Virt m g) : Virt m (fun b A => r • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J, inferInstance, ρ, fun j => r * c j, fun A b => ?_⟩
  simp only [← hc, Finset.smul_sum, smul_smul]

theorem virt_fsum {α : Type} [Fintype α] (g : α → ℕ → Mat m S → S) (hg : ∀ a, Virt m (g a)) :
    Virt m (fun b A => ∑ a, g a b A) := by
  choose J hJ ρ c hc using hg
  refine ⟨Σ a, J a, inferInstance, fun x => ρ x.1 x.2, fun x => c x.1 x.2, fun A b => ?_⟩
  rw [Fintype.sum_sigma]
  simp only [hc]

theorem ptr_tensor_sub_wedge2 (ρ : PolyRep m) (A : Mat m S) (b : ℕ) :
    (ρ.tensor ρ).ptr b A - 2 * ρ.wedge2.ptr b A = 2 ^ b * ρ.ptr b A := by
  have h := GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow (ρ.lie A) b
  have e1 : (ρ.tensor ρ).ptr b A = ((kron (ρ.lie A) 1 + kron 1 (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ ρ A)
  have e2 : ρ.wedge2.ptr b A = ((wedge2Lie (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare ρ A)
  have e3 : ρ.ptr b A = ((ρ.lie A) ^ b).trace := rfl
  linear_combination e1 - 2 * e2 - h - 2 ^ b * e3

theorem virt_double {g : ℕ → Mat m S → S} (hg : Virt m g) :
    Virt m (fun b A => (2 : ℝ) ^ b • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J ⊕ J, inferInstance, Sum.elim (fun j => (ρ j).tensor (ρ j)) (fun j => (ρ j).wedge2),
    Sum.elim c (fun j => -2 * c j), fun A b => ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ptr_tensor_sub_wedge2 (ρ j) A b
  simp only [Algebra.smul_def, map_mul, map_neg, map_pow, map_ofNat]
  linear_combination (algebraMap ℝ S (c j)) * h

theorem virt_proj (τ : ι) : Virt m (fun b (A : Mat m S) => ((A τ) ^ b).trace) := by
  refine ⟨Unit, inferInstance, fun _ => proj m τ, fun _ => 1, fun A b => ?_⟩
  simp only [PolyRep.ptr, lie_proj_model, one_smul, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem virt_pow (τ : ι) (a : ℕ) :
    Virt m (fun b (A : Mat m S) => ((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
  induction a with
  | zero => simpa using virt_proj (m := m) (S := S) τ
  | succ a ih =>
    have e : (fun b (A : Mat m S) => ((2 : ℝ) ^ (a + 1)) ^ b • ((A τ) ^ b).trace)
        = fun b A => (2 : ℝ) ^ b • (((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
      funext b A
      rw [smul_smul, pow_succ, mul_pow, mul_comm]
    rw [e]
    exact virt_double ih

theorem exists_vandermonde_solution (n i : ℕ) : ∃ x : Fin (n + 1) → ℝ, ∀ b : Fin (n + 1),
    ∑ a, x a * ((2 : ℝ) ^ (a : ℕ)) ^ (b : ℕ) = if (b : ℕ) = i then 1 else 0 := by
  set V := Matrix.vandermonde (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) with hV
  have hinj : Function.Injective (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) := by
    intro a a' h
    exact Fin.ext ((pow_right_strictMono₀ one_lt_two).injective h)
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set δ : Fin (n + 1) → ℝ := fun b => if (b : ℕ) = i then 1 else 0 with hδ
  refine ⟨δ ᵥ* V⁻¹, fun b => ?_⟩
  have h : (δ ᵥ* V⁻¹) ᵥ* V = δ := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  exact congrFun h b

theorem exists_pure_power_trace {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S]
    [Algebra ℝ S] (τ : ι) (i : ℕ) (_hi : 1 ≤ i) :
    ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n →
      ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  obtain ⟨x, hx⟩ := exists_vandermonde_solution n i
  obtain ⟨J, hJ, ρ, c, hc⟩ := virt_fsum (m := m) (S := S)
    (fun a : Fin (n + 1) => fun b A => x a • (((2 : ℝ) ^ (a : ℕ)) ^ b • ((A τ) ^ b).trace))
    (fun a => virt_smul (x a) (virt_pow τ a))
  refine ⟨J, hJ, ρ, c, fun A b hb => ?_⟩
  rw [hc]
  have h := hx ⟨b, Nat.lt_succ_of_le hb⟩
  simp only [smul_smul, ← Finset.sum_smul] at h ⊢
  rw [h]
  split_ifs with hbi
  · subst hbi; exact one_smul ℝ _
  · exact zero_smul ℝ _

end GlobalTheory.GoodMetric.PureVirt

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo



theorem omDat_updFW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ nW FW i Tp tup O
  refine ⟨{ O with }, rfl, rfl, fun h => ?_, fun cc ph h => h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end GlobalTheory.RealGeo
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_harmonicCoefficientMap_at_weights : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  first | exact @GlobalTheory.CoefMapRecord.exists_io_record | exact GlobalTheory.CoefMapRecord.exists_io_record | (intros; apply GlobalTheory.CoefMapRecord.exists_io_record <;> assumption)
end
