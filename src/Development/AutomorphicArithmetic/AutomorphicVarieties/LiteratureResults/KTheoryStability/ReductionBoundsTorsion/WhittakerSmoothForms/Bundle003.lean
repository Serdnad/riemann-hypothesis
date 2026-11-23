module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem eta_zero {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (σ : ℕ → Γ) :
    eta A φ c 0 σ = fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := rfl

theorem eta_succ {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ) :
    eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) := rfl

theorem psi_contDiffAt (H : Hyp U A φ) (γ : Γ) {h : V} (hh : h ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psi A φ γ) h := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) φ (A γ⁻¹ h) :=
    H.smooth.contDiffAt (H.isOpen.mem_nhds (H.mapsTo _ h hh))
  exact h1.comp h (A γ⁻¹).contDiff.contDiffAt

theorem Kf_contDiffOn (hL : PLoc U A φ) (H : Hyp U A φ) {q : ℕ}
    (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (hβ : ∀ τ, ContDiffOn ℝ (⊤ : ℕ∞) (β τ) U) (σ : ℕ → Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ β σ) U := by
  intro h hh
  obtain ⟨s, W, hW, hWU, hz⟩ := hL H h hh
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ∑ γ ∈ s, psi A φ γ x • β (cons γ σ) x) h := by
    apply ContDiffAt.sum
    intro γ _
    exact (psi_contDiffAt U A φ H γ hh).smul ((hβ _).contDiffAt (H.isOpen.mem_nhds hh))
  refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW] with x hx
  show (∑ᶠ γ, psi A φ γ x • β (cons γ σ) x) = _
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  by_contra hn
  apply hγ
  simp [hz γ hn x hx]

theorem extDeriv_contDiffOn (H : Hyp U A φ) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U) : ContDiffOn ℝ (⊤ : ℕ∞) (extDeriv ω) U := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ ω) U := hω.fderiv_of_isOpen H.isOpen (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn hd

theorem pSmooth (hL : PLoc U A φ) : PSmooth U A φ := by
  intro H k c j σ
  have key : ∀ (i : ℕ) (τ : ℕ → Γ), ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c i τ) U := by
    intro i
    induction i with
    | zero =>
      intro τ
      rw [eta_zero]
      exact contDiffOn_const
    | succ i ih =>
      intro τ
      rw [eta_succ]
      exact extDeriv_contDiffOn U A φ H (Kf_contDiffOn U A φ hL H _ ih τ)
  exact ⟨key j σ, Kf_contDiffOn U A φ hL H _ (key j) σ⟩

theorem pClosed (hS : PSmooth U A φ) : PClosed U A φ := by
  intro H k c j σ h hh
  cases j with
  | zero =>
    rw [eta_zero]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | succ j =>
    rw [eta_succ]
    exact extDeriv_extDeriv_apply ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds hh))
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        first
        | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
        | (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.2 le_top)
        | simp)

theorem pDep : PDep A φ := by
  intro k c j
  induction j with
  | zero =>
    intro σ σ' hσ
    rw [eta_zero, eta_zero]
    have e : (fun i : Fin (k + 2) => σ i) = fun i : Fin (k + 2) => σ' i := by
      funext i
      have := i.isLt
      exact hσ i (by omega)
    rw [e]
  | succ j ih =>
    intro σ σ' hσ
    rw [eta_succ, eta_succ]
    have e : Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
      funext x
      simp only [Kf]
      congr 1
      funext γ
      rw [ih (cons γ σ) (cons γ σ')]
      intro n hn
      cases n with
      | zero => rfl
      | succ m => exact hσ m (by omega)
    rw [e]

end PositivityTheory.KB.WhittakerCocycle

end
end

section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem skip_zero_cons (γ : Γ) (σ : ℕ → Γ) : skip 0 (cons γ σ) = σ := by
  funext n; simp [skip, cons]

theorem skip_succ_cons (i : ℕ) (γ : Γ) (σ : ℕ → Γ) : skip (i + 1) (cons γ σ) = cons γ (skip i σ) := by
  funext n
  cases n with
  | zero => simp [skip, cons]
  | succ m => simp [skip, cons]

theorem delG_cons (n : ℕ) {X : Type} [AddCommGroup X] [Module ℝ X] (β : (ℕ → Γ) → X) (γ : Γ)
    (σ : ℕ → Γ) : delG (n + 1) β (cons γ σ) = β σ - delG n (fun τ => β (cons γ τ)) σ := by
  simp only [delG]
  rw [Finset.sum_range_succ', skip_zero_cons]
  simp only [skip_succ_cons, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    pow_zero, one_smul]
  abel

theorem skip_succAbove {m : ℕ} (σ : ℕ → Γ) (i : Fin (m + 2)) (l : Fin (m + 1)) :
    skip (i : ℕ) σ (l : ℕ) = σ ((i.succAbove l : Fin (m + 2)) : ℕ) := by
  rw [skip]
  rcases lt_or_ge (l : ℕ) (i : ℕ) with hl | hl
  · rw [if_pos hl, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hl)]
    simp
  · rw [if_neg (not_lt.mpr hl), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hl)]
    simp

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem pLoc : PLoc U A φ := by
  intro H h hh
  obtain ⟨t, ht, hfin⟩ := H.locFin ⟨h, hh⟩
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype U ⟨h, hh⟩ t).mp ht
  refine ⟨hfin.toFinset, u ∩ U, inter_mem hu (H.isOpen.mem_nhds hh), inter_subset_right, ?_⟩
  intro γ hγ x hx
  by_contra hne
  apply hγ
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨x, hx.2⟩, hne, hut hx.1⟩

theorem finsum_psi (hL : PLoc U A φ) (H : Hyp U A φ) {h : V} (hh : h ∈ U) :
    ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧ ∀ x ∈ W, (∑ γ ∈ s, psi A φ γ x = 1) ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℝ M] (F : Γ → M),
        ∑ᶠ γ, psi A φ γ x • F γ = ∑ γ ∈ s, psi A φ γ x • F γ := by
  obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
  refine ⟨s, W, hW, hWU, fun x hx => ⟨?_, ?_⟩⟩
  · have h1 := H.sum_one x (hWU hx)
    rw [finsum_eq_sum_of_support_subset (s := s)] at h1
    · exact h1
    · intro γ hγ
      by_contra hγs
      exact hγ (hs γ hγs x hx)
  · intro M _ _ F
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs x hx]

theorem pHom (hL : PLoc U A φ) : PHom U A φ := by
  intro H q n β σ h hh
  obtain ⟨s, W, hW, hWU, hs⟩ := finsum_psi U A φ hL H hh
  obtain ⟨h1, hF⟩ := hs h (mem_of_mem_nhds hW)
  have hK : ∀ (β' : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) τ,
      Kf A φ β' τ h = ∑ γ ∈ s, psi A φ γ h • β' (cons γ τ) h :=
    fun β' τ => hF (fun γ => β' (cons γ τ) h)
  rw [hK (delG (n + 1) β)]
  simp only [delG_cons, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1,
    one_smul, sub_sub_cancel]
  simp only [delG, Finset.sum_apply, Pi.smul_apply, hK, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

end PositivityTheory.KB.WhittakerCocycle

end
end
