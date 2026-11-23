module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.schwartzBruhat_comp_affine_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by
  first | exact @GlobalTheory.AffineSB.mem_SB_comp_affine | exact GlobalTheory.AffineSB.mem_SB_comp_affine | (intros; apply GlobalTheory.AffineSB.mem_SB_comp_affine <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SliceIntegral

theorem integral_slice_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂]
    (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) :
    (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  haveI := t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro (IsCompact.image Φ.2.2 continuous_fst) fun x hx => ?_⟩
  · have ht : Filter.Tendsto (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
        (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
          (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have := hc.tendsto x
      rwa [sub_self, ← Prod.zero_eq_mk, ← Prod.zero_eq_mk] at this
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with x' hx'
    congr 1
    funext a
    have := hx' (x, 0, a)
    simpa using this
  · have h0 : ∀ a, Φ.1 (x, 0, a) = 0 := fun a =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [h0]

end GlobalTheory.SliceIntegral
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory

theorem typeFrame_conj_symm_rowE_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  intro k _ κ t _ _ _ _ ϖ j c l h p hp u a b
  set ord := stdOrd κ t j c h with hord
  have hbas : (typeFrame ϖ ord).bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
    change fromBlocks 1 0 0 _ = _
    congr 1
  have hinv : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hbas]
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have hM : ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val =
      fromBlocks 1 0 (Matrix.of fun (i : Fin c) y => if i.val = p then ((ϖ : k) ^ (p + 1))⁻¹ * u y else 0) 1 := by
    rw [Units.val_mul, Units.val_mul, hinv, hbas]
    change fromBlocks _ _ _ _ * fromBlocks 1 0 _ 1 * _ = _
    simp only [fromBlocks_multiply]
    congr 1 <;> ext i y <;> simp [diagonal_apply]
    by_cases hi : (i : ℕ) = p <;> simp [hi]
  have e : ((typeFrame ϖ ord).conj.symm (rowE c (p + 1) u)).val =
      ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val.submatrix ord ord := rfl
  rw [e, submatrix_apply, hM]
  have haux : ord (Sum.inl (Sum.inr ⟨p, by omega⟩)) = Sum.inr ⟨p, hp⟩ := standardOrderExtendedBasis_apply_low_block κ t j c h ⟨p, hp⟩
  have hcond : a = Sum.inl (Sum.inr ⟨p, by omega⟩) ↔ ord a = Sum.inr ⟨p, hp⟩ := by
    rw [← haux]; exact ord.apply_eq_iff_eq.symm
  have h1 : (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b =
      (1 : Matrix (XIx κ t j ⊕ Fin c) (XIx κ t j ⊕ Fin c) k) (ord a) (ord b) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [ord.apply_eq_iff_eq]
  rw [h1]
  simp only [hcond]
  generalize ord a = x
  generalize ord b = y
  rcases x with x | i <;> rcases y with y | i' <;> simp [Matrix.one_apply, Fin.ext_iff]

end GlobalTheory
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.StepData

theorem det_eq_one_of_one_row {k n : Type*} [Field k] [Fintype n] [DecidableEq n] (M : Matrix n n k) (i : n)
    (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b) (hii : M i i = 1) : M.det = 1 := by
  have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) * replicateRow Unit (M i - Pi.single i (1 : k)) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = a
      · subst hb; simp [Matrix.mul_apply, hii]
      · simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
  rw [e, det_one_add_replicateCol_mul_replicateRow]
  simp [hii]

theorem iter_lam_one_row (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum (k := k) (a := r))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) : ∀ (h : (P.iter t μ hμ j).J),
    (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) →
    (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 →
    ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧
      (P.iter t μ hμ j).lam h = P.lam g := by
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    set Q := P.iter t μ hμ j with hQ
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val = (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b; rw [Q.corner_val]; rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e; apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ → (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by rw [ec]; exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]; ext x y; exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]; exact det_eq_one_of_one_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_one_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp

end GlobalTheory.StepData
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum (k := k) (a := r)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) (h : (P.iter t μ hμ j).J), (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) → (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 → ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (P.iter t μ hμ j).lam h = P.lam g := by
  have det_eq_one_of_row {k n : Type} [Field k] [Fintype n] [DecidableEq n]
      (M : Matrix n n k) (i : n)
      (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b)
      (hii : M i i = 1) : M.det = 1 := by
    have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) *
        replicateRow Unit (M i - Pi.single i (1 : k)) := by
      ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = a
        · subst hb
          simp [Matrix.mul_apply, hii]
        · simp [Matrix.mul_apply, hb, Ne.symm hb]
      · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
    rw [e, det_one_add_replicateCol_mul_replicateRow]
    simp [hii]
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j r₀
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    let Q := P.iter t μ hμ j
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val =
        (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b
      rw [Q.corner_val]
      rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e
      apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ →
        (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by
      rw [ec]
      exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      ext x y
      exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_eq_one_of_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp [Q]
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.linearMap_killing_partialEvalIntegralKernel_translation_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  first | exact @GlobalTheory.FlatFactor.kerRed_translate_invariant | exact GlobalTheory.FlatFactor.kerRed_translate_invariant | (intros; apply GlobalTheory.FlatFactor.kerRed_translate_invariant <;> assumption)
end

section

noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩

theorem mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem eventually_invariant {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm

theorem invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']

theorem exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩

theorem sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩

end GlobalTheory.LocMod.Inhab
end
end

section

open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxCharComb

open GlobalTheory.LocMod.Inhab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_box_superset {K : Set (Matrix Y Y' k)} (hK : IsCompact K) :
    ∃ R : kˣ, ∀ x ∈ K, x ∈ box Y Y' R := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ (box Y Y' (1 : kˣ) : Set (Matrix Y Y' k))) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually
        ((isOpen_box (Y := Y) (Y' := Y') (1 : kˣ)).mem_nhds (box Y Y' 1).zero_mem)
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s⁻¹, fun x hx r q => ?_⟩
  have h1 : valuation k (((s : k) • x) r q) ≤ valuation k ((1 : kˣ) : k) :=
    hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) x hx r q
  have e : x r q = (s : k)⁻¹ * (((s : k) • x) r q) := by
    rw [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ s.ne_zero]
  rw [e, map_mul, Units.val_inv_eq_inv_val]
  exact mul_le_of_le_one_right' (by simpa only [Units.val_one, map_one] using h1)

end GlobalTheory.BoxCharComb
end
end

section


theorem _root_.GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  first | exact @GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | exact GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | (intros; apply GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one <;> assumption)
end
