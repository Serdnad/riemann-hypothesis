module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem mul_single_mul_apply (M N : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ) * N) i j = M i i₀ * N i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · congr 1
    simp [Matrix.mul_apply, Matrix.single_apply]
  · intro b _ hb
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hb]
  · simp

theorem mul_single_apply' (M : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ)) i j = if j = i₀ then M i i₀ else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
  · by_cases h : j = i₀
    · subst h; simp
    · simp [Matrix.single_apply, Ne.symm h, h]
  · intro b _ hb
    simp [Matrix.single_apply, Ne.symm hb]
  · simp

theorem Tens.xe_xi (T : Tens D D' W) (i₀ : Fin r) (y : D.X) :
    T.xe (T.xi i₀ y) = Pi.single i₀ y := by
  simp [Tens.xi]

theorem Tens.xe_smul_xi (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (i₀ : Fin r) (y : D.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • T.xi i₀ y) i = TensO.mat s a i i₀ • y := by
  letI := T.mod s
  rw [Tens.xe_smul]
  simp only [Tens.xe_xi]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem TensO.mat_star_idem_mul_binv {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀) * TensO.binv s) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 := by
  change TensO.mat s (star (TensO.idem s i₀)) * TensO.mat s (TensO.binv s) = _
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one]

theorem TensO.mat_star_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀)) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) := by
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single]

theorem SymUnit.inv_col_ne {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    ∃ i, ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 := congrFun (congrFun (Units.mul_inv s.1) i₀) i₀
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun k _ => by rw [h k, mul_zero]), Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

theorem tens_factor_latt : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s;
    (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧
    Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧
    ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  intro R _ _ D D' r W T s i₀
  letI := T.mod s
  have key : ∀ y i, T.xe (star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) i =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ • y := by
    intro y i
    rw [← mul_smul, Tens.xe_smul_xi, TensO.mat_star_idem_mul_binv, mul_single_apply']
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    show T.xe (T.xi i₀ y) i₀ = y
    rw [Tens.xe_xi]; simp
  · intro z
    apply T.xe.injective
    funext i
    rw [Tens.xe_xi, Tens.xe_smul]
    show Pi.single (M := fun _ => D.X) i₀ (T.xe z i₀) i = _
    simp only [TensO.idem, TensO.ofMat, TensO.mat, Matrix.single_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  · intro y y' h
    obtain ⟨i, hi⟩ := SymUnit.inv_col_ne s i₀
    have h' := congrArg (fun z => T.xe z i) h
    simp only [key] at h'
    exact smul_right_injective D.X hi h'
  · intro z
    refine ⟨∑ j, (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ j • T.xe z j, ?_⟩
    apply T.xe.injective
    funext i
    rw [key, Tens.xe_smul, TensO.mat_star_idem, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_single_mul_apply, mul_smul]
end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem sumForm_add {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x = ∑ m, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ y = ∑ m, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x + y = ∑ m, gc (c m) * gk (b m) := by
  first
  | exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | (apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)

theorem isAffineOpen_Sp_field (K : Type) [Field K] (V : (Sp K).Opens) : IsAffineOpen V := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases h : (V : Set (Sp K)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    rw [this]; exact isAffineOpen_top _
  · have : V = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [this]; exact isAffineOpen_bot _

theorem eq_sum_of_isIntegral_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU f hf
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have hf' : IsIntegral Γ(G.left, W) f := hf
  have hx : IsIntegral Γ(G.left, W) (e.symm f) := hf'.map e.symm.toAlgHom
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W))
    (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩
  have hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _)) := by
    rw [congrArg Subtype.val hy]; exact (e.apply_symm_apply f).symm
  rw [hfy]
  clear hfy hy
  induction y with
  | tmul c b =>
    refine ⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩
    rw [Fin.sum_univ_one]
    exact Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))
  | add u v hu hv =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _)]
    exact sumForm_add _ _ _ hu hv

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Over S}
variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

def lamLeft (z : X ⟶ G) : (X ⟶ G) →* Multiplicative (Pic X.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_prod_left {κ : Type} [Fintype κ] (x : κ → (X ⟶ G)) (n : κ → ℤ) (z : X ⟶ G) :
    lam (cls L hL) (∏ i, x i ^ n i) z = ∑ i, n i • lam (cls L hL) (x i) z := by
  have h := congrArg Multiplicative.toAdd (map_prod (lamLeft hL hΘ z) (fun i => x i ^ n i) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  exact h

theorem lam_prod_right {κ : Type} [Fintype κ] (x : X ⟶ G) (z : κ → (X ⟶ G)) (n : κ → ℤ) :
    lam (cls L hL) x (∏ i, z i ^ n i) = ∑ i, n i • lam (cls L hL) x (z i) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ (z _) x]

theorem lam_mul_right (x y z : X ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

end Bilinear

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def pairP (T : Tens D D' W) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j)

theorem cls_tens (T : Tens D D' W) :
    cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (T.pr i) (T.pr j) := by
  have hC := LB.isLB_linComb D.P.isLB (tensφ T.pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨T.w, T.w_gen⟩).trans ?_
  rw [cls_linComb D.P.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_tens (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairP T W h h := by

  rw [cls_tens T, pairP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

end Tensor

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Tensor2

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pairP_mul (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairP T W (u * v) (u * v) = pairP T W u u + pairP T W v v + pairP T (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ T.pr i = u ≫ T.pr i * v ≫ T.pr i := fun i => by
    haveI := T.pr_hom i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (v ≫ T.pr i) (u ≫ T.pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairP, hm, lam_mul_left D.P.isLB hΘ, lam_mul_right D.P.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

def pre {X Y Z : Over (Spec (CommRingCat.of R))} [GrpObj Z] (u : X ⟶ Y) : (Y ⟶ Z) →* (X ⟶ Z) where
  toFun f := u ≫ f
  map_one' := by simp [Hom.one_def]
  map_mul' f g := MonObj.comp_mul u f g

theorem comp_act_pr (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ T.act m) ≫ T.pr i = ∏ k, (u ≫ T.pr k) ^ m i k := by
  rw [Category.assoc, Tens.act_pr]
  exact (map_prod (pre (Z := D.P.A) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := D.P.A) u) _ _)

theorem pairP_act_left (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M (u ≫ T.act m) v = pairP T (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_left D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairP_act_right (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M u (v ≫ T.act m) = pairP T (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_right D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end Tensor2

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem symUnit_mul_star (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    (W + W.transpose) * TensO.mat _ (star a) = (TensO.mat _ a).transpose * (W + W.transpose) := by
  have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show (W + W.transpose) * ((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)) = _
  rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem rosatiAdj_core (T : Tens D D' W) (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    RosatiAdj D'.P.A D'.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := T.act (TensO.mat _ a)
  let g := T.act (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_tens T]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairP_mul, pairP_mul]
    rw [pairP_act_left T (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairP_act_right T (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by

        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.RosatiTens


open GlobalTheory.Mum.RosatiTens in
theorem GlobalTheory.Mum.rosatiAdj_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact rosatiAdj_core T h a
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.MumFam

theorem lbIso_lam_retract_adj : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  intro S G G' G₀ _ _ _ _ _ _ L L' L₀ hL hL' hL₀ inc u u' E E' Fm hinc hu hE huu hA hB hLL
  haveI := hinc
  haveI := hu
  have key : inc ≫ u ≫ u' = inc ≫ Fm ≫ E' := by
    rw [huu, ← Category.assoc inc E, hE]
  let P : G2 G ⟶ G2 G' := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm)
  let Q : G2 G ⟶ G' ⊗ G₀ := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ u)
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hLam' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff hLam (pull_isLB hLam' _)).1 ?_
  rw [cls_pull hLam']
  have c1 : cls (abelian₂ G L) hLam =
      GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] (cls L₀ hL₀) := by
    have e0 : cls L hL = CechPic.pull (inc ≫ u).left (cls L₀ hL₀) := (cls_eq_iff hL (pull_isLB hL₀ _)).2 hLL
    have hp : GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (CechPic.pull (inc ≫ u).left (cls L₀ hL₀)) =
        GlobalTheory.ZH.EndoExtend.cubeCls G₀ (fun i => x2 G i ≫ (inc ≫ u)) (cls L₀ hL₀) := by
      unfold GlobalTheory.ZH.EndoExtend.cubeCls
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← CechPic.pull_comp, ← Over.comp_left]
      have he := psum_hom (MonoidHom.mk' (fun z : G2 G ⟶ G => z ≫ (inc ≫ u))
        fun a b => MonObj.mul_comp a b (inc ≫ u)) (x2 G) I.down
      change psum G (x2 G) I.down ≫ (inc ≫ u) =
        psum G₀ (fun i => x2 G i ≫ (inc ≫ u)) I.down at he
      rw [he]
    rw [show cls (abelian₂ G L) hLam = GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (cls L hL) from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ hL, e0, hp]
    congr 1
    ext i
    fin_cases i <;> simp [x2]
  have c2 : CechPic.pull P.left (cls (abelian₂ G' L') hLam') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] (cls L' hL') := by
    rw [show cls (abelian₂ G' L') hLam' = GlobalTheory.ZH.EndoExtend.cubeCls G' (x2 G') (cls L' hL') from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL']
    exact GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ _ _ (fun i => by fin_cases i <;> simp [x2, P]) _
  have a1 : GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G' G₀ ≫ u, snd G' G₀] (cls L₀ hL₀) =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G₀, snd G' G₀ ≫ u'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₀ _ hL₀).symm.trans
      (((cls_eq_iff _ _).2 hA).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b1 := congrArg (CechPic.pull Q.left) a1
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G₀ _ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] Q
      (fun i => by fin_cases i <;> simp [Q]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] Q
      (fun i => by fin_cases i <;> simp [Q, key])] at b1
  have a2 : GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G' ≫ E, snd G' G'] (cls L' hL') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G', snd G' G' ≫ E'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL').symm.trans
      (((cls_eq_iff _ _).2 hB).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b2 := congrArg (CechPic.pull P.left) a2
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] P
      (fun i => by fin_cases i <;> simp [P, hE]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] P
      (fun i => by fin_cases i <;> simp [P])] at b2
  exact c1.trans (b1.trans (b2.symm.trans c2.symm))

end GlobalTheory.MumFam
end
end
