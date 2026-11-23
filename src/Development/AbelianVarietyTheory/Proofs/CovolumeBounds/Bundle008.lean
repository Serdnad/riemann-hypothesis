module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

@[expose] public section

section

noncomputable section

open Module Submodule

namespace GlobalTheory

section General

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}

theorem mem_span_of_lt_succMinOf {v : Fin n → V} (hv : LinearIndependent K v) (hS : ∀ j, v j ∈ S)
    (hN : ∀ j : Fin n, N (v j) ≤ succMinOf K N S (j + 1)) {i : ℕ} (hi : i ≤ n) {x : V}
    (hx : x ∈ S) (hx0 : 0 ≤ N x) (h : N x < succMinOf K N S (i + 1)) :
    x ∈ span K (v '' {j | (j : ℕ) < i}) := by
  have hrank : (n : Cardinal) ≤ Module.rank K (span K S) :=
    natCast_le_rank_span_iff.2 ⟨v, hv, hS⟩
  have key : ∀ i ≤ n, succMinOf K N S i ≤ N x → N x < succMinOf K N S (i + 1) →
      x ∈ span K (v '' {j | (j : ℕ) < i}) := by
    intro i hi h1 h2
    by_contra hx'
    have hw : LinearIndependent K (fun j : Fin i => v (Fin.castLE hi j)) :=
      hv.comp _ (Fin.castLE_injective hi)
    have hr : Set.range (fun j : Fin i => v (Fin.castLE hi j)) = v '' {j | (j : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    have hli : LinearIndependent K
        (Fin.cons x (fun j : Fin i => v (Fin.castLE hi j)) : Fin (i + 1) → V) :=
      linearIndependent_finCons.2 ⟨hw, by rwa [hr]⟩
    refine absurd (succMinOf_le_of_linearIndependent (N := N) (S := S) (i := i + 1) hli (by simp)
      hx0 ?_ ?_) (not_le.2 h2)
    · intro k
      refine Fin.cases hx (fun j => hS _) k
    · intro k
      refine Fin.cases le_rfl (fun j => ?_) k
      exact (hN _).trans ((succMinOf_mono (show (j : ℕ) + 1 ≤ i from j.2)
        ((Nat.cast_le.2 hi).trans hrank)).trans h1)
  induction i with
  | zero => exact key 0 hi (succMinOf_zero.le.trans hx0) h
  | succ m ih =>
    rcases lt_or_ge (N x) (succMinOf K N S (m + 1)) with h1 | h1
    · have hsub : {j : Fin n | (j : ℕ) < m} ⊆ {j : Fin n | (j : ℕ) < m + 1} :=
        fun j hj => Nat.lt_succ_of_lt hj
      exact span_mono (Set.image_mono hsub) (ih (Nat.le_of_succ_le hi) h1)
    · exact key (m + 1) hi h1 h

theorem exists_linearIndependent_eq_succMinOf (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hS, hvN⟩ := ih ((Nat.cast_le.2 (Nat.le_succ m)).trans hn)
    obtain ⟨-, w, hw, hwS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hn)
    obtain ⟨k, hk⟩ : ∃ k, w k ∉ span K (Set.range v) := by
      by_contra! h
      have h1 : span K (Set.range w) ≤ span K (Set.range v) :=
        span_le.2 (Set.range_subset_iff.2 h)
      have : Module.Finite K (span K (Set.range v)) :=
        Module.Finite.span_of_finite K (Set.finite_range v)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at h2
      simp at h2
    have hk' : N (w k) = succMinOf K N S (m + 1) := by
      refine le_antisymm (hwS k).2 (not_lt.1 fun h => hk ?_)
      exact span_mono (Set.image_subset_range _ _)
        (mem_span_of_lt_succMinOf hv hS (fun j => (hvN j).le) le_rfl (hwS k).1
          (hN _ (hwS k).1) h)
    refine ⟨Fin.snoc v (w k), linearIndependent_finSnoc.2 ⟨hv, hk⟩, fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using (hwS k).1
      · simpa using hS j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hk'
      · simpa using hvN j

end General

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}

theorem mem_span_of_norm_lt_succMin {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : ‖x‖ < succMin L (i + 1)) : x ∈ span ℝ (v '' {j | (j : ℕ) < i}) :=
  mem_span_of_lt_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E)) hv hL hN hi hx
    (norm_nonneg x) h

theorem succMin_le_norm_of_notMem_span {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ :=
  not_lt.1 fun h' => h (mem_span_of_norm_lt_succMin hv hL hN hi hx h')

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem exists_linearIndependent_norm_eq_succMin (hn : n ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin n → E, LinearIndependent ℝ v ∧ (∀ j, v j ∈ L) ∧
      ∀ j : Fin n, ‖v j‖ = succMin L (j + 1) :=
  exists_linearIndependent_eq_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E))
    (finite_mem_and_norm_le L) (fun x _ => norm_nonneg x) (natCast_le_rank_of_le_finrank hn)

variable (L) [IsZLattice ℝ L]

theorem exists_basis_norm_eq_succMin :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ j, b j ∈ L) ∧
      ∀ j : Fin (finrank ℝ E), ‖b j‖ = succMin L (j + 1) := by
  obtain ⟨v, hv, hL, hN⟩ :=
    exists_linearIndependent_norm_eq_succMin (L := L) (finrank_span_of_isZLattice L).ge
  have htop : ⊤ ≤ span ℝ (Set.range v) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  exact ⟨Basis.mk hv htop, by simpa using hL, by simpa using hN⟩

end Normed

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} {L : Submodule ℤ V}
  {n : ℕ}

end Quadratic

end GlobalTheory
end
end

section

open MvPolynomial Matrix Topology Filter
open GlobalTheory.MvPoly

namespace GlobalTheory.Harm

section Adjoint

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem pderiv_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (i : σ) (Q : MvPolynomial τ R) :
    pderiv i (G Q) = ∑ j, M i j • G (pderiv j Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have h1 : pderiv i (G (X k)) = C (M i k) := by
      simp [hG, pderiv_X, Pi.single_apply, smul_eq_C_mul]
    have h2 : ∑ j, M i j • G (P * pderiv j (X k)) = G P * C (M i k) := by
      rw [Finset.sum_eq_single k]
      · simp [smul_eq_C_mul, mul_comm]
      · intro j _ hj
        simp [pderiv_X, Pi.single_apply, hj.symm]
      · simp
    rw [map_mul, Derivation.leibniz, hP, h1, smul_eq_mul, smul_eq_mul, ← h2, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, map_add (f := _), smul_add, smul_eq_mul, smul_eq_mul, map_mul G (X k),
      mul_smul_comm]


omit [Fintype τ] in
theorem constantCoeff_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (Q : MvPolynomial τ R) :
    constantCoeff (G Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP => simp [hG, smul_eq_C_mul]

theorem fockInner_algHom_of_linear (F : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (G : MvPolynomial τ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (M : σ → τ → ℂ)
    (hF : ∀ i, F (X i) = ∑ j, M i j • X j) (hG : ∀ j, G (X j) = ∑ i, star (M i j) • X i)
    (P : MvPolynomial σ ℂ) (Q : MvPolynomial τ ℂ) : fockInner (F P) Q = fockInner P (G Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C r =>
    have := constantCoeff_algHom_of_linear G _ hG Q
    rw [constantCoeff_eq] at this
    rw [algHom_C, algebraMap_eq, C_apply, C_apply, fockInner_monomial_left,
      fockInner_monomial_left, this]
    simp [constantCoeff_eq]
  | add P P' hP hP' => rw [map_add (f := _), fockInner_add_left, fockInner_add_left, hP, hP']
  | mul_X P k hP =>

    rw [mul_comm P, fockInner_X_mul_left, pderiv_algHom_of_linear G _ hG, map_mul, hF,
    Finset.sum_mul, ← fockInnerₛₗ_apply, ← fockInnerₛₗ_apply, map_sum, map_sum,
    LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fockInnerₛₗ_apply, fockInnerₛₗ_apply, smul_mul_assoc, fockInner_smul_left,
      fockInner_smul_right, fockInner_X_mul_left, hP]
    simp

variable {T κ : Type*} [Fintype T] [Fintype κ] {p q : ℕ}

theorem fockInner_colSubst (A B : T → Matrix κ κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colSubst A B P) Q =
      fockInner P (colSubst (fun t => (A t)ᴴ) (fun t => (B t)ᴴ) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _ (fun v w => if v.1 = w.1 ∧ v.2.1 = w.2.1 then
    Sum.elim (fun _ => A v.1 v.2.2 w.2.2) (fun _ => B v.1 w.2.2 v.2.2) v.2.1 else 0) ?_ ?_ P Q
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]

theorem fockInner_colAct [DecidableEq κ] (g : T → GL κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colAct ℂ T p q κ g P) Q = fockInner P (colAct ℂ T p q κ (star g) Q) := by
  rw [colAct_apply, colAct_apply, fockInner_colSubst]
  rfl

theorem exists_fockInner_sub_eq_zero {σ : Type*} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) :
    ∃ Q ∈ W, ∀ w ∈ W, fockInner (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : MvPolynomial σ ℂ →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    LinearMap.pi fun i => (fockInnerₛₗ σ ℂ).flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : fockInner P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)

    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this

    rw [← this, ← fockInnerₛₗ_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, fockInnerₛₗ_apply, fockInner_smul_right]
    exact mul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have := hL x hx x x.2
    rw [fockInner_self] at this
    exact Subtype.ext (fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp this))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

end Adjoint

section Triangular

variable {R : Type*} [CommRing R] {T : Type*} [Fintype T] {p q n : ℕ}

end Triangular

section Density

variable {T κ : Type*} [Fintype κ] {p q n : ℕ}

end Density

end GlobalTheory.Harm
end

section

open scoped InnerProductSpace
open Module Submodule Matrix

namespace GlobalTheory

section Gram

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem det_gram_real_sum_smul (e : ι → E) (m : Matrix ι ι ℝ) :
    (gram ℝ (fun j => ∑ i, m i j • e i)).det = m.det ^ 2 * (gram ℝ e).det := by
  simpa using Hadamard.re_det_gram_sum_smul (𝕜 := ℝ) e m

end Gram

section Def

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem free_of_fg {V : Type*} [AddCommGroup V] [Module ℝ V] {L : Submodule ℤ V} (h : L.FG) :
    Module.Free ℤ L := by
  have : Module.Finite ℤ L := .of_fg h
  have : HasUniqueDiv V := .of_isTorsionFree ℝ V
  infer_instance


open Classical in
noncomputable def spanCovol (L : Submodule ℤ E) : ℝ :=
  letI : Decidable L.FG := Classical.propDecidable _
  if h : L.FG then
    haveI : Module.Finite ℤ L := .of_fg h
    haveI : Module.Free ℤ L := free_of_fg h
    √(gram ℝ fun i => (finBasis ℤ L i : E)).det
  else 0

theorem sqrt_det_gram_eq_relIndex_mul {L' L : Submodule ℤ E} (h : L' ≤ L) (b' : Basis ι ℤ L')
    (b : Basis ι ℤ L) :
    √(gram ℝ fun i => (b' i : E)).det =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * √(gram ℝ fun i => (b i : E)).det := by
  let w : ι → L := fun j => ⟨b' j, h (b' j).2⟩
  have h1 : L'.toAddSubgroup.relIndex L.toAddSubgroup = (b.det w).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b
  have h2 : (fun j => (b' j : E)) =
      fun j => ∑ i, ((b.toMatrix w).map (Int.cast : ℤ → ℝ)) i j • (b i : E) := by
    funext j
    have := congrArg (fun x : L => (x : E)) (b.sum_repr (w j))
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    simp only [map_apply, Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
    exact this.symm
  rw [h2, det_gram_real_sum_smul, h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ← Int.cast_det, Nat.cast_natAbs, Int.cast_abs, Basis.det_apply]

theorem spanCovol_eq_sqrt_det_gram {L : Submodule ℤ E} (b : Basis ι ℤ L) :
    spanCovol L = √(gram ℝ fun i => (b i : E)).det := by
  have hf : Module.Finite ℤ L := .of_basis b
  have hfg : L.FG := Module.Finite.iff_fg.1 hf
  have : Module.Free ℤ L := .of_basis b
  let e := (finBasis ℤ L).indexEquiv b
  rw [spanCovol, dite_eq_left hfg, sqrt_det_gram_eq_relIndex_mul le_rfl b ((finBasis ℤ L).reindex e),
    AddSubgroup.relIndex_self, Nat.cast_one, one_mul, ← Hadamard.det_gram_comp_equiv _ e]
  congr 3
  ext i
  simp

theorem spanCovol_span {v : ι → E} (hv : LinearIndependent ℤ v) :
    spanCovol (span ℤ (Set.range v)) = √(gram ℝ v).det := by
  rw [spanCovol_eq_sqrt_det_gram (Basis.span hv)]
  simp

theorem spanCovol_map_linearIsometry {L : Submodule ℤ E} (hL : L.FG) (T : E →ₗᵢ[ℝ] F) :
    spanCovol (L.map (T.toLinearMap.restrictScalars ℤ)) = spanCovol L := by
  have : Module.Finite ℤ L := .of_fg hL
  have : Module.Free ℤ L := free_of_fg hL
  let b := finBasis ℤ L
  rw [spanCovol_eq_sqrt_det_gram
    (b.map (L.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective)),
    spanCovol_eq_sqrt_det_gram b]
  congr 2
  ext i j
  exact T.inner_map_map _ _

end Def

section Discrete

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem discreteTopology_of_le {N L : Submodule ℤ V} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion h)
    (continuous_inclusion h) (Set.inclusion_injective h)

variable [FiniteDimensional ℝ V]

theorem fg_of_discrete (L : Submodule ℤ V) [DiscreteTopology L] : L.FG :=
  Module.Finite.iff_fg.1 inferInstance

theorem exists_basis_range_subset {ι : Type*} {v : ι → V} (hv : LinearIndependent ℝ v) :
    ∃ β : Basis (Fin (finrank ℝ V)) ℝ V, Set.range v ⊆ Set.range β := by
  let β := Basis.extend hv.linearIndepOn_id
  refine ⟨β.reindex (β.indexEquiv (finBasis ℝ V)), ?_⟩
  rw [Basis.range_reindex, Basis.range_extend]
  exact Basis.subset_extend _

theorem discreteTopology_span_of_linearIndependent {ι : Type*} {v : ι → V}
    (hv : LinearIndependent ℝ v) : DiscreteTopology (span ℤ (Set.range v)) := by
  obtain ⟨β, hβ⟩ := exists_basis_range_subset hv
  exact discreteTopology_of_le (span_mono hβ)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem span_range_coe_basis {ι : Type*} {L : Submodule ℤ V} (b : Basis ι ℤ L) :
    span ℤ (Set.range fun i => (b i : V)) = L := by
  have := congrArg (Submodule.map L.subtype) b.span_eq
  rwa [Submodule.map_span, ← Set.range_comp, map_subtype_top] at this

theorem linearIndependent_real_coe_basis {ι : Type*} [Fintype ι] {L : Submodule ℤ V}
    [DiscreteTopology L] (b : Basis ι ℤ L) : LinearIndependent ℝ fun i => (b i : V) :=
  linearIndependent_real_of_int_of_discrete L (fun i => (b i).2)
    (b.linearIndependent.map' L.subtype (ker_subtype L))

end Discrete

section Main

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem spanCovol_eq_covolume [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : spanCovol L = ZLattice.covolume L := by
  rw [spanCovol_eq_sqrt_det_gram (finBasis ℤ L), covolume_eq_sqrt_det_gram L (finBasis ℤ L)]

instance discreteTopology_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Submodule ℝ E) : DiscreteTopology (ZLattice.comap ℝ L S.subtype) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val S.injective_subtype

instance isZLattice_comap_subtype_span (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) :=
  ⟨span_span_coe_preimage⟩

theorem spanCovol_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L] (S : Submodule ℝ E)
    (h : (L : Set E) ⊆ S) : spanCovol (ZLattice.comap ℝ L S.subtype) = spanCovol L := by
  rw [← spanCovol_map_linearIsometry (fg_of_discrete _) S.subtypeₗᵢ]
  congr 1
  exact map_comap_eq_self fun x hx => ⟨⟨x, h hx⟩, rfl⟩

theorem spanCovol_eq_covolume_comap_span [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    spanCovol L = ZLattice.covolume (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) := by
  rw [← spanCovol_eq_covolume, spanCovol_comap_subtype L _ subset_span]

end Main

end GlobalTheory
end
