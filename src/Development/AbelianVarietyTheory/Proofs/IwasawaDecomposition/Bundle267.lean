module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle217
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle220
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobGarding

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) :
    ∃ φ', IsTest φ' ∧ ∀ w, word (trRep σ P) l (gard ε σ φ w) = gard ε σ φ' w := by
  induction l with
  | nil => exact ⟨φ, hφ, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨φ', h1, h2⟩ := ih fun Y hY => hl Y (by simp [hY])
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ' h1
    exact ⟨ψ X, (hψ X).1, fun w => by rw [word_cons, h2, (hψ X).2 (hl X (by simp))]⟩

theorem inner_word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G (trRep σ P)) (a : H) :
    ⟪a, word (trRep σ P) l (gard ε σ φ w)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪a, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hc := GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ l hl w hw
  have key : ∀ y : H, ⟪y, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • word (trRep σ P) l (σ (umat g) w) ∂(Formalism.REAL.muG ε)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    intro y
    rw [← integral_inner (hφ.integrable hc)]
    congr 1
    funext g
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
  rw [← key]
  congr 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint (gram_unit hP h) (isURepOn_trRep hP h hσ) hl hu
  rw [key, h2 _ (gard_mem hP h hσ hφ w), inner_gard hσ hφ]
  congr 1
  funext g
  rw [h2 _ (sigma_mem hP h hσ hw g.2)]

theorem sobCont_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ hℓ
  obtain ⟨m, ls, a, hls, hrep⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner n ε H σ P G hP h hσ ℓ hℓ
  refine ⟨fun φ hφ => ?_, fun w hw => ?_⟩
  · choose ψ _ hψ using fun i => word_gard hP h hσ hφ (ls i) (hls i)
    refine ⟨∑ i, ‖a i‖ * ∫ g : Formalism.REAL.UJ ε, |ψ i (umat g)| ∂(Formalism.REAL.muG ε), fun w => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hψ, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_gard_le hσ _ w) (norm_nonneg _))
  · have e : ∀ g : Formalism.REAL.UJ ε, ℓ (σ (umat g) w) = ∑ i, ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun g => hrep _ (sigma_mem hP h hσ hw g.2)
    have hc : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun i => continuous_const.inner (GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ (ls i) (hls i) w hw)
    simp only [e]
    refine ⟨continuous_finsetSum _ fun i _ => hc i, fun φ hφ => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w)]
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ fun i _ => hφ.integrable (hc i)]
    exact Finset.sum_congr rfl fun i _ => inner_word_gard hP h hσ hφ (ls i) (hls i) hw (a i)

end GlobalTheory.SobGarding
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.GelfScalar

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def LinAdjOn (D : Submodule ℂ H) (f : H → H) : Prop :=
  (∀ w ∈ D, f w ∈ D) ∧ (∀ v ∈ D, ∀ w ∈ D, f (v + w) = f v + f w) ∧ (∀ (c : ℂ), ∀ w ∈ D, f (c • w) = c • f w) ∧
    ∀ u ∈ D, ∃ u' ∈ D, ∀ w ∈ D, ⟪u, f w⟫_ℂ = ⟪u', w⟫_ℂ

variable {D : Submodule ℂ H}

theorem linAdjOn_id : LinAdjOn D fun w => w := ⟨fun _ hw => hw, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun u hu => ⟨u, hu, fun _ _ => rfl⟩⟩

theorem linAdjOn_zero : LinAdjOn D fun _ => 0 := by
  refine ⟨fun _ _ => D.zero_mem, fun _ _ _ _ => (add_zero 0).symm, fun c _ _ => (smul_zero c).symm,
    fun _ _ => ⟨0, D.zero_mem, fun w _ => ?_⟩⟩
  simp

theorem LinAdjOn.comp {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f (g w) := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => hf1 _ (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show f (g (v + w)) = f (g v) + f (g w)
    rw [hg2 v hv w hw, hf2 _ (hg1 v hv) _ (hg1 w hw)]
  · show f (g (c • w)) = c • f (g w)
    rw [hg3 c w hw, hf3 c _ (hg1 w hw)]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u₁ hu₁
    exact ⟨u₂, hu₂, fun w hw => (h₁ _ (hg1 w hw)).trans (h₂ w hw)⟩

theorem LinAdjOn.add {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f w + g w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => D.add_mem (hf1 w hw) (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_,
    fun u hu => ?_⟩
  · show f (v + w) + g (v + w) = (f v + g v) + (f w + g w)
    rw [hf2 v hv w hw, hg2 v hv w hw]
    abel
  · show f (c • w) + g (c • w) = c • (f w + g w)
    rw [hf3 c w hw, hg3 c w hw, smul_add]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u hu
    refine ⟨u₁ + u₂, D.add_mem hu₁ hu₂, fun w hw => ?_⟩
    show ⟪u, f w + g w⟫_ℂ = ⟪u₁ + u₂, w⟫_ℂ
    rw [inner_add_right, inner_add_left, h₁ w hw, h₂ w hw]

theorem LinAdjOn.smul {f : H → H} (hf : LinAdjOn D f) (a : ℂ) : LinAdjOn D fun w => a • f w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  refine ⟨fun w hw => D.smul_mem a (hf1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show a • f (v + w) = a • f v + a • f w
    rw [hf2 v hv w hw, smul_add]
  · show a • f (c • w) = c • a • f w
    rw [hf3 c w hw, smul_comm]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    refine ⟨(starRingEnd ℂ a) • u₁, D.smul_mem _ hu₁, fun w hw => ?_⟩
    show ⟪u, a • f w⟫_ℂ = ⟪(starRingEnd ℂ a) • u₁, w⟫_ℂ
    rw [inner_smul_right, inner_smul_left, h₁ w hw, Complex.conj_conj]

theorem linAdjOn_sum {ι : Type} (s : Finset ι) {f : ι → H → H} (hf : ∀ i, LinAdjOn D (f i)) :
    LinAdjOn D fun w => ∑ i ∈ s, f i w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact linAdjOn_zero
  · intro i s hi ih
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih

theorem linAdjOn_foldr (l : List (H → H)) (hl : ∀ f ∈ l, LinAdjOn D f) :
    LinAdjOn D fun w => l.foldr (fun f acc => f acc) w := by
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    exact linAdjOn_id
  | cons f l ih =>
    simp only [List.foldr_cons]
    exact (hl f (by simp)).comp (ih fun g hg => hl g (by simp [hg]))

theorem LinAdjOn.exists_extend {f : H → H} (hf : LinAdjOn D f) : ∃ A : H →ₗ[ℂ] H, ∀ w ∈ D, A w = f w := by
  obtain ⟨-, hf2, hf3, -⟩ := hf
  let g : D →ₗ[ℂ] H :=
    { toFun := fun x => f x
      map_add' := fun x y => hf2 x x.2 y y.2
      map_smul' := fun c x => hf3 c x x.2 }
  obtain ⟨A, hA⟩ := LinearMap.exists_extend g
  refine ⟨A, fun w hw => ?_⟩
  have key := LinearMap.congr_fun hA ⟨w, hw⟩
  exact key

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem linAdjOn_dRep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : LinAdjOn (smSub G π) (dRep π X) := by
  refine ⟨fun w hw => dRep_mem hG hπ hw hX, fun v hv w hw => dRep_add hv hw hX,
    fun c w hw => dRep_smul c hw hX, fun u hu => ⟨-dRep π X u, neg_mem (dRep_mem hG hπ hu hX), fun w hw => ?_⟩⟩
  rw [inner_dRep hG hπ hu hw hX, inner_neg_left]

theorem linAdjOn_dRepC (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (Z : Matrix (Fin n) (Fin n) ℂ) : LinAdjOn (smSub G π) (dRepC G π Z) := by
  obtain ⟨h₁, h₂⟩ := parts_mem hG hh Z
  exact (linAdjOn_dRep hG hπ h₁).add ((linAdjOn_dRep hG hπ h₂).smul Complex.I)

theorem linAdjOn_gelfH (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) :
    LinAdjOn (smSub G π) (gelfH G π k) := by
  show LinAdjOn (smSub G π) fun w => ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC G π (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
      (fun f acc => f acc) w
  refine linAdjOn_sum Finset.univ fun idx => linAdjOn_foldr _ fun g hg => ?_
  rw [List.mem_ofFn] at hg
  obtain ⟨a, rfl⟩ := hg
  exact linAdjOn_dRepC hG hh hπ _

end

theorem gelfH_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  intro n ε H _ _ _ σ P G hP hPG hσ hirr k
  have hGu : IsUnit G := gram_unit hP hPG
  have hh : Gᴴ = G := gram_herm hPG
  have hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isURepOn_trRep hP hPG hσ
  have hirr' : IsIrredOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isIrredOn_trRep hP hPG hirr
  have hL := linAdjOn_gelfH hGu hh hπ k
  obtain ⟨A, hA⟩ := hL.exists_extend
  obtain ⟨-, -, -, hadj⟩ := hL
  have hnorm : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ v : H, ‖trRep σ P g v‖ = ‖v‖ := fun g hg v => hπ.2.1 g hg v
  have hAg : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      A (trRep σ P g w) = trRep σ P g (A w) := by
    intro g hg w hw
    rw [hA _ (rep_mem hGu hπ hw hg), hA w hw]
    exact GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth n ε H σ P G hP hPG hσ k g hg w hw
  have h₁ : ∀ (i : Formalism.QuantumDeterminants.UH G) (v : H), ‖trRep σ P i.1 v‖ = ‖v‖ := fun i v => hnorm i.1 i.2 v
  have h₂ : ∀ i : Formalism.QuantumDeterminants.UH G, ∃ j : Formalism.QuantumDeterminants.UH G,
      (∀ v, trRep σ P j.1 (trRep σ P i.1 v) = v) ∧ ∀ v, trRep σ P i.1 (trRep σ P j.1 v) = v := by
    intro i
    have hu : IsUnit i.1.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mem_UH hGu i.2)
    refine ⟨⟨i.1⁻¹, inv_mem_UH hGu i.2⟩, fun v => ?_, fun v => ?_⟩
    · rw [← rep_mul hπ (inv_mem_UH hGu i.2) i.2, Matrix.nonsing_inv_mul _ hu, rep_one hπ]
    · rw [← rep_mul hπ i.2 (inv_mem_UH hGu i.2), Matrix.mul_nonsing_inv _ hu, rep_one hπ]
  have h₃ : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ S, trRep σ P i.1 v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hinv => hirr' S hS fun g hg v hv => hinv ⟨g, hg⟩ v hv
  have h₄ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ smSub G (trRep σ P), trRep σ P i.1 v ∈ smSub G (trRep σ P) :=
    fun i v hv => rep_mem hGu hπ hv i.2
  have h₅ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), ‖A (trRep σ P i.1 w)‖ = ‖A w‖ := by
    intro i w hw
    rw [hAg i.1 i.2 w hw, hnorm i.1 i.2]
  have h₆ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ‖(LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)‖ = ‖(LinearMap.id : H →ₗ[ℂ] H) w‖ := by
    intro i w _
    simp only [LinearMap.id_apply]
    exact hnorm i.1 i.2 w
  have h₇ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ⟪A (trRep σ P i.1 w), (LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)⟫_ℂ =
        ⟪A w, (LinearMap.id : H →ₗ[ℂ] H) w⟫_ℂ := by
    intro i w hw
    simp only [LinearMap.id_apply]
    rw [hAg i.1 i.2 w hw, rep_inner hπ i.2]
  have h₈ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f hu hu0 hAu
    apply eq_zero_of_inner_smooth hP hPG hσ
    intro v hv
    obtain ⟨v', -, hvv⟩ := hadj v hv
    have t₁ : Tendsto (fun i => ⟪v, A (u i)⟫_ℂ) atTop (𝓝 ⟪v, f⟫_ℂ) := tendsto_const_nhds.inner hAu
    have t₂ : Tendsto (fun i => ⟪v', u i⟫_ℂ) atTop (𝓝 ⟪v', (0 : H)⟫_ℂ) :=
      tendsto_const_nhds.inner hu0
    rw [inner_zero_right] at t₂
    refine tendsto_nhds_unique t₁ (t₂.congr fun i => ?_)
    rw [hA _ (hu i), hvv _ (hu i)]
  have h₉ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => (LinearMap.id : H →ₗ[ℂ] H) (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f _ hu0 hu
    simp only [LinearMap.id_apply] at hu
    exact tendsto_nhds_unique hu hu0
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (Formalism.QuantumDeterminants.UH G) H H (fun i => trRep σ P i.1) (smSub G (trRep σ P))
    h₁ h₂ h₃ h₄ A LinearMap.id h₅ h₆ h₇ h₈ h₉
  refine ⟨starRingEnd ℂ c, fun w hw => ?_⟩
  rw [← hA w hw]
  apply ext_inner_smooth hP hPG hσ
  intro u hu
  have e₁ : ⟪A w, u⟫_ℂ = ⟪starRingEnd ℂ c • w, u⟫_ℂ := by
    have e := hc w hw u hu
    rw [LinearMap.id_apply] at e
    rw [e, inner_smul_left, Complex.conj_conj]
  rw [← inner_conj_symm, e₁, inner_conj_symm]

end GlobalTheory.SmVec.GelfScalar
end

section

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

variable {ι : Type} [Fintype ι] {m : ι → ℕ}

theorem charpolyRev_neg_lie_nsum (ρ : PolyRep m) (k : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    Matrix.charpolyRev (-((ρ.nsum k).lie A)) = (Matrix.charpolyRev (-(ρ.lie A))) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.charpolyRev]
    haveI : IsEmpty (Fin (ρ.nsum 0).M) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty
  | succ k ih =>
    rw [pow_succ, ← ih, ← GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix]
    exact congrArg (fun L => Matrix.charpolyRev (-L)) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum (ρ.nsum k) ρ A)

theorem chern_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n) ∈ Reach m n S :=
  Submodule.subset_span ⟨ρ, rfl⟩

theorem ptr_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => ρ.ptr n A) ∈ Reach m n S := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := (Reach m 0 S).smul_mem (ρ.M : ℝ) (chern_mem_reach 0 S ρ)
    convert h using 1
    funext A
    have h0 : (Matrix.charpolyRev (-(ρ.lie A))).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [PolyRep.ptr, h0, Algebra.smul_def]
  · obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_pow_eq_sum_smul_coeff_charpolyRev n hn
    have h := (Reach m n S).sum_mem (t := Finset.range (n + 1))
      (fun k _ => (Reach m n S).smul_mem (c k) (chern_mem_reach n S (ρ.nsum k)))
    convert h using 1
    funext A
    rw [Finset.sum_apply, PolyRep.ptr, ← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, charpolyRev_neg_lie_nsum]

theorem ptr_tensor (ρ σ : PolyRep m) (N : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    (ρ.tensor σ).ptr N A =
      ∑ a ∈ Finset.range (N + 1), (N.choose a : S) * ρ.ptr a A * σ.ptr (N - a) A := by
  simp only [PolyRep.ptr]
  rw [← GlobalTheory.T.trace_pow_finProdKronecker_add_binomial]
  exact congrArg (fun L => (L ^ N).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ σ A)

theorem ptr_mul_trProd_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)) :
    (∀ x ∈ l, 1 ≤ x.2) → ∀ r : ℕ, r + (l.map Prod.snd).sum = n → ∀ ρ : PolyRep m,
      (fun A : Mat m S => ρ.ptr r A * trProd l A) ∈ Reach m n S := by
  induction l with
  | nil =>
    intro _ r hr ρ
    have hr' : r = n := by simpa using hr
    subst hr'
    simpa [trProd] using ptr_mem_reach r S ρ
  | cons x l ih =>
    obtain ⟨τ, i⟩ := x
    intro hl r hr ρ
    have hi : 1 ≤ i := hl (τ, i) (by simp)
    have hr' : (r + i) + (l.map Prod.snd).sum = n := by
      simp only [List.map_cons, List.sum_cons] at hr
      omega
    obtain ⟨J, _, σ, c, hσ⟩ := GlobalTheory.T.exists_polyRep_combination_pure_power_trace m n S τ i hi
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (r + i) hr'
    have h := (Reach m n S).smul_mem (((r + i).choose r : ℝ)⁻¹)
      ((Reach m n S).sum_mem (t := Finset.univ)
        (fun j _ => (Reach m n S).smul_mem (c j) (ih' (ρ.tensor (σ j)))))
    convert h using 1
    funext A
    have hne : (((r + i).choose r : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right r i)).ne'
    have key : ∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A =
        (((r + i).choose r : ℕ) : ℝ) • (ρ.ptr r A * ((A τ) ^ i).trace) := by
      simp only [ptr_tensor, Finset.smul_sum]
      rw [Finset.sum_comm]
      have e : ∀ a ∈ Finset.range (r + i + 1),
          ∑ j, c j • ((((r + i).choose a : ℕ) : S) * ρ.ptr a A * (σ j).ptr (r + i - a) A) =
            (((r + i).choose a : ℕ) : S) * ρ.ptr a A *
              (if r + i - a = i then ((A τ) ^ i).trace else 0) := by
        intro a _
        rw [← hσ A (r + i - a) (by omega), Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
      rw [Finset.sum_congr rfl e, Finset.sum_eq_single r]
      · rw [if_pos (by omega), Algebra.smul_def, map_natCast, mul_assoc]
      · intro a ha har
        rw [Finset.mem_range] at ha
        rw [if_neg (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    simp only [Pi.smul_apply, Finset.sum_apply]
    have e2 : ∑ j, c j • ((ρ.tensor (σ j)).ptr (r + i) A * trProd l A) =
        (∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A) * trProd l A := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm
    rw [e2, key, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hne, one_smul]
    simp only [trProd, List.map_cons, List.prod_cons, mul_assoc]

theorem trProd_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (l : List (ι × ℕ)) (hl : ∀ x ∈ l, 1 ≤ x.2) (hs : (l.map Prod.snd).sum = n) :
    (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  have h := ptr_mul_trProd_mem_reach n S l hl 0 (by simpa using hs) (PolyRep.triv m)
  convert h using 2 with A
  have : (PolyRep.triv m).ptr 0 A = 1 := by
    rw [PolyRep.ptr, pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact Nat.cast_one
  rw [this, one_mul]

end GlobalTheory.GoodMetric.ChernSpan
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

theorem IsAmpleLB.tens_of_isNef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, GlobalTheory.IsAmpleLB A → (letI := GlobalTheory.algebraΓOfHom f; GlobalTheory.IsNef k N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens A N) := by
  intro h k _ X f hf A N hA hN
  letI := GlobalTheory.algebraΓOfHom f
  refine IsAmpleLB.tens_of_forall_isPsEff k X f hf A N hA hN.isLB fun Z hZ => ?_
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := f) fun _ => rfl]
  have hp' : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  exact IsNef.isPsEff h k _ hp' _ (hN.pull_of_isClosedImmersion (redι Z) hi)

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem lvlE_range_iff : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  have h := congrArg (fun s : Set S.Forms => f ∈ s) (GlobalTheory.Mem.LiftForms.range_lvlForm S r P ψ)
  simp only [Set.mem_range, GlobalTheory.Mem.LiftForms.lvlForm_apply] at h
  rw [h]
  rfl

end GlobalTheory.TopSpan
end
