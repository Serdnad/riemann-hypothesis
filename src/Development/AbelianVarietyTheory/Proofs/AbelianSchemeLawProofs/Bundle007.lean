module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]

def ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* Γ(P, W) :=
  (p.appLE U W h).hom

theorem rs_ap (p : P ⟶ X) {U : X.Opens} {W W' : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W' ≤ W) (x : Γ(X, U)) :
    rs P h' (ap p h x) = ap p (h'.trans h) x :=
  congr($(p.appLE_map h (homOfLE h').op).hom x)

theorem ap_rs (p : P ⟶ X) {U U' : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U') (h' : U' ≤ U) (x : Γ(X, U)) :
    ap p h (rs X h' x) = ap p (h.trans fun _ hy => h' hy) x :=
  congr($(p.map_appLE h (homOfLE h').op).hom x)

theorem basicOpen_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (x : Γ(X, U)) :
    P.basicOpen (ap p h x) = W ⊓ p ⁻¹ᵁ X.basicOpen x :=
  Scheme.basicOpen_appLE p W U h x

theorem ap_cst (p : P ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {W : P.Opens}
    (h : W ≤ p ⁻¹ᵁ U) (r : R) : ap p h (cst f U r) = cst (p ≫ f) W r := by
  refine (ap_rs p h le_top _).trans ?_
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rs X h u.val := rfl

theorem le_pre (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W ≤ p ⁻¹ᵁ V) :
    W ≤ p ⁻¹ᵁ (U ⊓ V) := fun _ hy => ⟨h hy, h' hy⟩

theorem pre_left (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ U := fun _ hy => (h hy).1

theorem pre_right (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ V := fun _ hy => (h hy).2

def box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) : LB P :=
  ⟨H.ι × K.ι, fun a => p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2, fun a b =>
    Units.map (ap p (le_pre p (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).toMonoidHom
      (H.g a.1 b.1) *
    Units.map (ap q (le_pre q (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).toMonoidHom
      (K.g a.2 b.2)⟩

variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem rs_mul {U : X.Opens} {V : Y.Opens} {W W' : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V)
    (h : W' ≤ W) (x : Γ(X, U)) (y : Γ(Y, V)) :
    rs P h (ap p h₁ x * ap q h₂ y) = ap p (h.trans h₁) x * ap q (h.trans h₂) y := by
  rw [map_mul, rs_ap, rs_ap]

theorem ap_g_self (hH : H.IsLB) (i : H.ι) {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U i)) :
    ap p h (H.g i i).val = 1 := by
  have h₁ := congrArg (fun u => ap p (pre_left p h) u.val) (hH.g_self i)
  simpa only [val_res, ap_rs, Units.val_one, map_one] using h₁

theorem ap_cocycle (hH : H.IsLB) (i j k : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j))
    (h₂ : W ≤ p ⁻¹ᵁ (H.U j ⊓ H.U k)) (h₃ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U k)) :
    ap p h₃ (H.g i k).val = ap p h₁ (H.g i j).val * ap p h₂ (H.g j k).val := by
  have e := congrArg (fun u => ap p (le_pre p h₁ (pre_right p h₂)) u.val) (hH.cocycle i j k)
  simp only [val_res, ap_rs, Units.val_mul, map_mul] at e
  exact e.symm

theorem ap_ratio {U V : X.Opens} {x y : Γ(X, V)} {r : Γ(X, U)}
    (e : rs X (inf_le_right : U ⊓ V ≤ V) x =
      rs X (inf_le_left : U ⊓ V ≤ U) r * rs X (inf_le_right : U ⊓ V ≤ V) y)
    {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ p ⁻¹ᵁ V) :
    ap p h₂ x = ap p h₁ r * ap p h₂ y := by
  have e' := congrArg (ap p (le_pre p h₁ h₂)) e
  simpa only [ap_rs, map_mul] using e'

theorem ap_compat (s : LB.Sec H) (i j : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ H.U i) (h₂ : W ≤ p ⁻¹ᵁ H.U j)
    (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j)) :
    ap p h₁ (s.f i) = ap p h (H.g i j).val * ap p h₂ (s.f j) := by
  have e : rs X inf_le_left (s.f i) = (H.g i j).val * rs X inf_le_right (s.f j) := s.compat i j
  have e' := congrArg (ap p h) e
  simpa only [ap_rs, map_mul] using e'

theorem isLB_box (hH : H.IsLB) (hK : K.IsLB) : (box p q H K).IsLB := by
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, K.U i by rw [hK.cover]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  · intro a
    refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
    rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
  · intro a b c
    refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
      (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
    exact (mul_mul_mul_comm _ _ _ _).trans
      (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)

def boxSec (s : LB.Sec H) (t : LB.Sec K) : LB.Sec (box p q H K) where
  f := fun a => ap p (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_left (s.f a.1) *
    ap q (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_right (t.f a.2)
  compat := fun a b => by
    refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (rs_mul p q _ _ _ _ _).symm))
    exact (congrArg₂ (· * ·) (ap_compat p s a.1 b.1 _ _ _) (ap_compat q t a.2 b.2 _ _ _)).trans
      (mul_mul_mul_comm _ _ _ _)

theorem nonzeroLocus_boxSec (s : LB.Sec H) (t : LB.Sec K) :
    nonzeroLocus (boxSec p q s t) = p ⁻¹ᵁ nonzeroLocus s ⊓ q ⁻¹ᵁ nonzeroLocus t := by
  have key : ∀ a : H.ι × K.ι, P.basicOpen ((boxSec p q s t).f a) =
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ p ⁻¹ᵁ X.basicOpen (s.f a.1)) ⊓
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ q ⁻¹ᵁ Y.basicOpen (t.f a.2)) := fun a =>
    (P.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (basicOpen_ap p _ _) (basicOpen_ap q _ _))
  ext y
  constructor
  · intro h
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have ha := (key a).le ha
    exact ⟨TopologicalSpace.Opens.mem_iSup.2 ⟨a.1, ha.1.2⟩, TopologicalSpace.Opens.mem_iSup.2 ⟨a.2, ha.2.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ k, X.basicOpen (s.f k) from h₁)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ k, Y.basicOpen (t.f k) from h₂)
    have hy : y ∈ p ⁻¹ᵁ H.U i ⊓ q ⁻¹ᵁ K.U j := ⟨X.basicOpen_le _ hi, Y.basicOpen_le _ hj⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (key (i, j)).ge ⟨⟨hy, hi⟩, hy, hj⟩⟩

theorem ratio_self (s : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) : r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k => X.basicOpen (s.f k)) (nonzeroLocus s)
    (fun k => homOfLE (le_iSup (fun k => X.basicOpen (s.f k)) k)) le_rfl r 1 fun k => ?_
  have hle : X.basicOpen (s.f k) ≤ nonzeroLocus s ⊓ H.U k :=
    le_inf (le_iSup (fun k => X.basicOpen (s.f k)) k) (X.basicOpen_le _)
  have e := congrArg (rs X hle) (h k)
  simp only [map_mul, rs_rs] at e
  have u : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) := X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  have e' : rs X (hle.trans inf_le_left) r = 1 := u.mul_right_cancel (e.symm.trans (_root_.one_mul _).symm)
  exact e'.trans (map_one (rs X (hle.trans inf_le_left))).symm

theorem isProjBy_of_isPullback {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (sq : IsPullback p q f g) (hf : IsProjBy f) (hg : IsProjBy g) : IsProjBy (p ≫ f) := by
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  obtain ⟨K, hK, n, t, ht, ht'⟩ := hg
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨box p q H K, isLB_box p q hH hK, m * n + m + n,
    fun a => boxSec p q (s (e a).1) (t (e a).2), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

end GlobalTheory.AbLaw.Segre

theorem GlobalTheory.AbLaw.isProjBy_tensor : ∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))),
    IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom := fun _ _ X Y hX hY =>
  GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback _ _ (IsPullback.of_hasPullback X.hom Y.hom) hX hY
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TrivLocus

theorem exists_ker_iff_minors {K : Type} [Field K] {a b : ℕ} (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔ ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩ σ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    funext i
    exact congrFun h (σ i)
  · intro h
    by_contra hn
    have hinj : Function.Injective D.mulVec := by
      intro v w e
      by_contra hvw
      exact hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩
    have hcol : LinearIndependent K D.col := Matrix.mulVec_injective_iff.1 hinj
    have hrank : D.rank = a := by
      rw [← Matrix.rank_transpose]
      have := LinearIndependent.rank_matrix (M := D.transpose) hcol
      simpa using this
    obtain ⟨κ, e, -, hspan, hli⟩ := exists_linearIndependent' K D.row
    have : Finite κ := hli.finite
    let _ : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]
    let ε : Fin a ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent K (D.submatrix (e ∘ ε) id).row := hli.comp ε ε.injective
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')
    exact hu.ne_zero (h _)

theorem nontrivial_ker_iff {R K : Type} [CommRing R] [Field K] (g : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map g).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker g := by
  have h := exists_ker_iff_minors (D.map g)
  have h' : ∀ σ : Fin a → Fin b, ((D.map g).submatrix σ id).det = g (D.submatrix σ id).det := fun σ => by
    rw [RingHom.map_det]; rfl
  simp only [h'] at h
  simp only [RingHom.mem_ker]
  rw [← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]
  exact ⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩,
    fun ⟨v, hv, e⟩ => ⟨⟨v, e⟩, fun e' => hv (congrArg Subtype.val e')⟩⟩

variable {X Y : Scheme.{0}}

def zeroSec (N : LB X) : LB.Sec N where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem nontrivial_sec_iff (N : LB X) : Nontrivial (LB.Sec N) ↔ ∃ (s : LB.Sec N) (i : N.ι), s.f i ≠ 0 := by
  rw [nontrivial_iff_exists_ne (zeroSec N)]
  refine exists_congr fun s => ?_
  obtain ⟨sf, hs⟩ := s
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have : sf = fun _ => 0 := funext hn
    subst this
    exact h rfl
  · rintro ⟨i, hi⟩ h
    exact hi (congrArg (fun s => s.f i) h)

theorem pull_pw (M : LB X) (π : Y ⟶ X) (t : ℤ) : (pw M t).pull π = pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow (G := Γ(Y, LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

theorem rs_ne_zero [IsIntegral X] {U V : X.Opens} (h : V ≤ U) (hV : (V : Set X).Nonempty) {x : Γ(X, U)}
    (hx : x ≠ 0) : rs X h x ≠ 0 := by
  have : Nonempty V := hV.to_subtype
  intro e
  exact hx (map_injective_of_isIntegral X (homOfLE h) (e.trans (map_zero _).symm))

theorem nonempty_of_ne_zero {U : X.Opens} {x : Γ(X, U)} (hx : x ≠ 0) : (U : Set X).Nonempty := by
  by_contra h
  have : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h)
  subst this
  exact hx (Subsingleton.elim _ _)

theorem triv_iff [IsIntegral X] (hX : IsField Γ(X, ⊤)) (N : LB X) (hN : ⨆ i, N.U i = ⊤) :
    Triv N ↔ Nontrivial (LB.Sec N) ∧ Nontrivial (LB.Sec (pw N (-1))) := by
  rw [nontrivial_sec_iff, nontrivial_sec_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have : Nonempty (N.U i) := ⟨⟨x, hi⟩⟩
    refine ⟨⟨⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩, i, (t.s i).ne_zero⟩,
      ⟨⟨fun i => ((t.s i)⁻¹).val, fun i j => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    rw [← zpow_neg_one (N.g i j)] at h
    exact congrArg Units.val h
  · rintro ⟨⟨s, i, hi⟩, ⟨s'', j, hj⟩⟩
    let s' : ∀ k : N.ι, Γ(X, N.U k) := s''.f
    change N.ι at j
    change s' j ≠ 0 at hj
    have hc : ∀ k l, rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k * s' k) =
        rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l * s' l) := by
      intro k l
      have h₁ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k) =
        (N.g k l).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l) := s.compat k l
      have h₂ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s' k) =
        (N.g k l ^ (-1 : ℤ)).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s' l) := s''.compat k l
      rw [map_mul, map_mul, h₁, h₂, _root_.mul_mul_mul_comm, ← Units.val_mul, zpow_neg_one, mul_inv_cancel,
        Units.val_one, _root_.one_mul]
    obtain ⟨h, hh, -⟩ := X.sheaf.existsUnique_gluing' N.U ⊤ (fun _ => homOfLE le_top) hN.ge
      (fun k => s.f k * s' k) hc
    change Γ(X, ⊤) at h
    have hh' : ∀ k, rs X (le_top : N.U k ≤ ⊤) h = s.f k * s' k := hh
    have hne : (↑(N.U i ⊓ N.U j) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen (nonempty_of_ne_zero hi) (nonempty_of_ne_zero hj)
    have hsj : s.f j ≠ 0 := by
      intro e
      have h₁ : rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i) =
        (N.g i j).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j) := s.compat i j
      rw [e, map_zero, mul_zero] at h₁
      exact rs_ne_zero _ hne hi h₁
    have : Nonempty (N.U j) := (nonempty_of_ne_zero hsj).to_subtype
    have h0 : h ≠ 0 := by
      intro e
      have := hh' j
      rw [e, map_zero] at this
      exact mul_ne_zero hsj hj this.symm
    have hu : IsUnit h := by
      obtain ⟨c, hc⟩ := hX.mul_inv_cancel h0
      exact IsUnit.of_mul_eq_one c hc
    have hs : ∀ k, IsUnit (s.f k) := fun k =>
      isUnit_of_mul_isUnit_left (hh' k ▸ hu.map (rs X (le_top : N.U k ≤ ⊤)))
    exact ⟨⟨fun k => (hs k).unit⟩, fun k l => Units.ext (s.compat k l)⟩

theorem triv_fibre_iff {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (hM : M.IsLB)
    (P : Perf f M) (Q : Perf f (pw M (-1))) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (g : R →+* K) {X' : Scheme.{0}} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Triv (M.pull π) ↔ (∀ σ : Fin P.a → Fin P.b, (P.D₀.submatrix σ id).det ∈ RingHom.ker g) ∧
      ∀ σ : Fin Q.a → Fin Q.b, (Q.D₀.submatrix σ id).det ∈ RingHom.ker g := by
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ h
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  obtain ⟨E, -⟩ := P.sec K g X' π f' h
  obtain ⟨E', -⟩ := Q.sec K g X' π f' h
  rw [triv_iff (isField_of_universallyClosed K f') _ (LB.isLB_linComb hM _ _).cover, ← pull_pw,
    ← nontrivial_ker_iff, ← nontrivial_ker_iff, E.nontrivial_congr, E'.nontrivial_congr]

theorem isClosed_trivLocus :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
  rintro R _ X f M hM ⟨P⟩ ⟨Q⟩ _ _
  convert PrimeSpectrum.isClosed_zeroLocus
    ((Set.range fun σ : Fin P.a → Fin P.b => (P.D₀.submatrix σ id).det) ∪
      Set.range fun σ : Fin Q.a → Fin Q.b => (Q.D₀.submatrix σ id).det)
  rename_i p
  change _ ↔ p ∈ PrimeSpectrum.zeroLocus _
  rw [PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · rintro ⟨K, _, g, X', π, f', hg, h, ht⟩
    rw [← hg]
    exact (triv_fibre_iff hM P Q g h).1 ht
  · intro hp
    have hk : RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal := Ideal.ker_algebraMap_residueField _
    refine ⟨p.asIdeal.ResidueField, inferInstance, algebraMap R _, _, _, _, hk, IsPullback.of_hasPullback _ _, ?_⟩
    refine (triv_fibre_iff hM P Q _ (IsPullback.of_hasPullback _ _)).2 ?_
    rw [hk]
    exact hp

end GlobalTheory.TrivLocus
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem formallyUnramified_mulA (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulA G n).left := by
  have h : mulN G n = mulA G n :=
    (Category.id_comp _).symm.trans (MulUnramified.comp_mulN G (𝟙 G) n)
  rw [← h]
  exact formallyUnramified_mulN S G n hn

end GlobalTheory
end
