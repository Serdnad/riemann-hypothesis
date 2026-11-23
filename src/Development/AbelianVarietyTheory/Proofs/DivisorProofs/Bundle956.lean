module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CechPic

theorem squareZero_localUnit_difference_ring_identity {R : Type*} [CommRing R] {Tj Tk Nj Nk H G G' Sj Sk Pj Pk Pj' Pk' M : R}
    (hT : Tj = G' * Tk) (hS : Sj = G * G * Sk) (hP : Pj = G' * G' * Pk) (hj' : Pj * Pj' = 1)
    (hk' : Pk * Pk' = 1) (hNj : Nj = Sj * Pj' - 1) (hNk : Nk = Sk * Pk' - 1) (hNj2 : Nj * Nj = 0)
    (hNk2 : Nk * Nk = 0) (hH : 2 * H = 1)
    (hM : M = Tj * (1 + Nj * H) - G * (Tk * (1 + Nk * H))) (hM2 : M * M = 0) :
    M * (G * (Tk * (1 + Nk * H))) = 0 := by
  have e1 : (Tj * (1 + Nj * H)) ^ 2 = Tj ^ 2 * Sj * Pj' := by
    linear_combination Tj ^ 2 * Nj * hH + Tj ^ 2 * H ^ 2 * hNj2 + Tj ^ 2 * hNj
  have e2 : (G * (Tk * (1 + Nk * H))) ^ 2 = G ^ 2 * Tk ^ 2 * Sk * Pk' := by
    linear_combination G ^ 2 * Tk ^ 2 * Nk * hH + G ^ 2 * Tk ^ 2 * H ^ 2 * hNk2 + G ^ 2 * Tk ^ 2 * hNk
  have e4 : Pj' * (G' * G') = Pk' := by
    linear_combination (-(Pj' * (G' * G'))) * hk' + Pk' * hj' - Pk' * Pj' * hP
  have e5 : (Tj * (1 + Nj * H)) ^ 2 = (G * (Tk * (1 + Nk * H))) ^ 2 := by
    rw [e1, e2, hT, hS]
    linear_combination G ^ 2 * Tk ^ 2 * Sk * e4
  linear_combination H * e5 - H * hM2 +
    H * (Tj * (1 + Nj * H) + G * (Tk * (1 + Nk * H)) + M) * hM - M * (G * (Tk * (1 + Nk * H))) * hH

end GlobalTheory.CechPic


open GlobalTheory.SmallExtLift in
theorem GlobalTheory.CechPic.eq_zero_of_sqZero_retract : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  intro X X' i q e hiq h2 hsq c hc hc2
  obtain ⟨Q, hQ, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  rw [two_nsmul, ← GlobalTheory.CechPic.cls_tens hQ hQ (GlobalTheory.CechPic.isLB_tens hQ hQ),
    GlobalTheory.CechPic.cls_eq_zero_iff] at hc2
  obtain ⟨s, hs⟩ := hc2
  rw [← GlobalTheory.CechPic.cls_pull hQ i (pull_isLB hQ i), GlobalTheory.CechPic.cls_eq_zero_iff] at hc
  obtain ⟨t₀, ht₀⟩ := hc
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hQ).2 ?_

  have genLaw : ∀ {M : LB X'} (t : LB.Gen M), t.IsGen → ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z)
      (a b : M.ι) (ha : f z ∈ M.U a) (hb : f z ∈ M.U b),
      gr f z _ ha (t.s a).val = gr f z (M.U a ⊓ M.U b) ⟨ha, hb⟩ (M.g a b).val * gr f z _ hb (t.s b).val := by
    intro M t ht Z f z a b ha hb
    have hm : f z ∈ M.U a ⊓ M.U b := ⟨ha, hb⟩
    have := congrArg (fun u => gr f z _ hm u.val) (ht a b)
    simp only [Units.val_mul, map_mul] at this
    exact (gr_res f z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) rfl (gr_res f z _ hm _)))
  let W : Q.ι → X.Opens := fun j => (Q.pull i).U (fun _ => j)
  have hσ : ∀ j, Q.U j ≤ (q ≫ i) ⁻¹ᵁ Q.U j := fun j x hx => by
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hiq]; exact hx
  have hW : ∀ j, Q.U j ≤ q ⁻¹ᵁ W j := fun j x hx => pull_le Q i j le_rfl (hσ j hx)
  have hσf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → ((f ≫ q) ≫ i) z ∈ Q.U j := by
    intro j Z f z hz
    simp only [Scheme.Hom.comp_apply, hiq]; exact hz
  have hWf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → (f ≫ q) z ∈ W j :=
    fun j Z f z hz => hW j hz
  let sj : ∀ j, Γ(X', Q.U j)ˣ := fun j => res (le_inf le_rfl le_rfl) (s.s (j, j))
  let u : ∀ j, Γ(X', Q.U j) := fun j => (q.appLE (W j) (Q.U j) (hW j)).hom (t₀.s fun _ => j).val
  let σi : ∀ j, Γ(X', Q.U j) := fun j => ((q ≫ i).appLE (Q.U j) (Q.U j) (hσ j)).hom (sj j)⁻¹.val
  let n : ∀ j, Γ(X', Q.U j) := fun j => (sj j).val * σi j - 1
  let hh : ∀ j, Γ(X', Q.U j) := fun j => (X'.presheaf.map (homOfLE le_top).op).hom h2.unit⁻¹.val
  let t : ∀ j, Γ(X', Q.U j) := fun j => u j * (1 + n j * hh j)
  have gn : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (n j) = gr f z _ hz (sj j).val * gr ((f ≫ q) ≫ i) z (Q.U j) (hσf j f z hz) (sj j)⁻¹.val - 1 := by
    intro Z f z j hz
    simp only [n, σi, map_sub, map_mul, map_one]
    rw [gr_appLE]
    exact congrArg (fun w => _ * w - 1) (gr_congr (Category.assoc f q i).symm z _ _ _)
  have gt : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (t j) = gr (f ≫ q) z (W j) (hWf j f z hz) (t₀.s fun _ => j).val *
        (1 + gr f z _ hz (n j) * gr f z ⊤ trivial h2.unit⁻¹.val) := by
    intro Z f z j hz
    simp only [t, u, hh, map_mul, map_add (f := _), map_one]
    rw [gr_appLE, gr_res]
  have E1 : (𝟙 X ≫ i) ≫ q = 𝟙 X := by rw [Category.assoc, e, Category.id_comp]
  have E2 : ((𝟙 X ≫ i) ≫ q) ≫ i = 𝟙 X ≫ i := by rw [E1]
  have hn0 : ∀ j, (i.app (Q.U j)).hom (n j) = 0 := fun j => gr_ext fun y hy => by
    rw [gr_app, map_zero, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv,
      map_one, sub_self]
  have hn2 : ∀ j, n j * n j = 0 := fun j => hsq _ _ _ (hn0 j) (hn0 j)
  have gti : ∀ j y (hy : (𝟙 X ≫ i) y ∈ Q.U j),
      gr (𝟙 X ≫ i) y _ hy (t j) = gr ((𝟙 X ≫ i) ≫ q) y (W j) (hWf j _ y hy) (t₀.s fun _ => j).val := by
    intro j y hy
    rw [gt (𝟙 X ≫ i) y j hy, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv, map_one, sub_self, zero_mul,
      add_zero, mul_one]
  let m : ∀ j k, Γ(X', Q.U j ⊓ Q.U k) := fun j k =>
    (X'.presheaf.map (homOfLE inf_le_left).op).hom (t j) -
      (Q.g j k).val * (X'.presheaf.map (homOfLE inf_le_right).op).hom (t k)
  have gm' : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j k (hz : f z ∈ Q.U j ⊓ Q.U k),
      gr f z _ hz (m j k) = gr f z _ hz.1 (t j) - gr f z _ hz (Q.g j k).val * gr f z _ hz.2 (t k) := by
    intro Z f z j k hz
    simp only [m, map_sub, map_mul]
    rw [gr_res, gr_res]
  have hm0 : ∀ j k, (i.app _).hom (m j k) = 0 := fun j k => gr_ext fun y hy => by
    rw [gr_app, map_zero, gm' (𝟙 X ≫ i) y j k hy, gti j y hy.1, gti k y hy.2, sub_eq_zero]
    have := gr_gen ht₀ ((𝟙 X ≫ i) ≫ q) y (hσf j _ y hy.1) (hσf k _ y hy.2)
    exact this.trans (congrArg (· * _) (gr_congr E2 y _ _ _))
  have gS : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) a b (ha : f z ∈ Q.U a) (hb : f z ∈ Q.U b),
      gr f z _ ha (sj a).val = gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val *
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z _ hb (sj b).val := by
    intro Z f z a b ha hb
    have hS := genLaw s hs f z (a, a) (b, b) ⟨ha, ha⟩ ⟨hb, hb⟩
    have hm : f z ∈ (Q.U a ⊓ Q.U a) ⊓ (Q.U b ⊓ Q.U b) := ⟨⟨ha, ha⟩, ⟨hb, hb⟩⟩
    have hg : gr f z _ hm ((GlobalTheory.CechPic.tens Q Q).g (a, a) (b, b)).val =
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val := by
      show gr f z _ hm (res _ (Q.g a b) * res _ (Q.g a b)).val = _
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)
    refine (gr_res f z (le_inf le_rfl le_rfl : Q.U a ≤ Q.U a ⊓ Q.U a) ha (s.s (a, a)).val).trans (hS.trans ?_)
    exact congrArg₂ (· * ·) hg (gr_res f z (le_inf le_rfl le_rfl : Q.U b ≤ Q.U b ⊓ Q.U b) hb (s.s (b, b)).val).symm
  refine gen_of_refine hQ Q.U hQ.cover id (fun _ => le_rfl) t
    (fun j => ((Units.isUnit _).map _).mul (isUnit_one_add (hn2 j) _)) fun a b x ha hb => ?_
  have hab : (𝟙 X') x ∈ Q.U a ⊓ Q.U b := ⟨ha, hb⟩
  have hmx := gm' (𝟙 X') x a b hab
  have hm := hmx
  rw [gt (𝟙 X') x a ha, gt (𝟙 X') x b hb] at hm
  have hmm := congrArg (gr (𝟙 X') x _ hab) (hsq _ _ _ (hm0 a b) (hm0 a b))
  rw [map_mul, map_zero] at hmm
  have hT := gr_gen ht₀ (𝟙 X' ≫ q) x (hσf a _ x ha) (hσf b _ x hb)
  have hSx := gS (𝟙 X') x a b ha hb
  have hPx := gS ((𝟙 X' ≫ q) ≫ i) x a b (hσf a _ x ha) (hσf b _ x hb)
  have hj' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hk' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hNa := gn (𝟙 X') x a ha
  have hNb := gn (𝟙 X') x b hb
  have hNa2 := congrArg (gr (𝟙 X') x _ ha) (hn2 a)
  have hNb2 := congrArg (gr (𝟙 X') x _ hb) (hn2 b)
  rw [map_mul, map_zero] at hNa2 hNb2
  have hH : 2 * gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val = 1 := by
    have := congrArg (gr (𝟙 X') x ⊤ trivial) h2.val_inv_mul
    rw [map_mul, map_one, map_ofNat] at this
    linear_combination this
  have key := GlobalTheory.CechPic.squareZero_localUnit_difference_ring_identity hT hSx hPx hj' hk' hNa hNb hNa2 hNb2 hH hm hmm
  have hB := ((Units.isUnit (Q.g a b)).map (gr (𝟙 X') x (Q.U a ⊓ Q.U b) hab)).mul
    (((Units.isUnit (t₀.s fun _ => b)).map (gr (𝟙 X' ≫ q) x (W b) (hWf b _ x hb))).mul (isUnit_one_add hNb2 (gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val)))
  have h0 := hB.mul_left_eq_zero.1 key
  rw [hmx] at h0
  exact sub_eq_zero.1 h0
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.LBDescent

theorem exists_finite_subextension_cls (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B X : Scheme.{0}) (pB : B ⟶ Sp K) [QuasiCompact pB]
    [QuasiSeparated pB] (p : X ⟶ Sp Ω) (φ : X ⟶ B)
    (hX : IsPullback φ p pB (spMap (algebraMap K Ω))) (L : LB X) (hL : L.IsLB) :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp F) (φ₁ : X₁ ⟶ B),
        IsPullback φ₁ p₁ pB (spMap (algebraMap K F)) →
        ∀ j : X ⟶ X₁, j ≫ φ₁ = φ → j ≫ p₁ = p ≫ spMap (algebraMap F Ω) →
          ∃ x : CechPic.Pic X₁, CechPic.pull j x = CechPic.cls L hL := by
  obtain ⟨R, M, ρ, ⟨T, hT⟩, hM, h1, h2, hI⟩ := exists_fg_lb pB p φ hX L hL
  let F : IntermediateField K Ω := IntermediateField.adjoin K (T : Set Ω)
  have hle : R ≤ F.toSubalgebra := by
    rw [← hT]
    exact IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨F, IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), ?_⟩
  intro X₁ p₁ φ₁ hX₁ j hj1 hj2
  let ι : R →+* F := (Subalgebra.inclusion hle).toRingHom
  have e1 : spMap ι ≫ spMap (algebraMap K R) = spMap (algebraMap K F) := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have e2 : spMap (algebraMap F Ω) ≫ spMap ι = spMap R.val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  let q : X₁ ⟶ Limits.pullback pB (spMap (algebraMap K R)) :=
    Limits.pullback.lift φ₁ (p₁ ≫ spMap ι) (by rw [Category.assoc, e1, hX₁.w])
  have hq : j ≫ q = ρ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, hj1, h1]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, hj2, Category.assoc, e2, h2]
  refine ⟨CechPic.pull q (CechPic.cls M hM), ?_⟩
  rw [← CechPic.pull_comp, hq, ← CechPic.cls_pull hM ρ (pull_isLB hM ρ), eq_comm, CechPic.cls_eq_iff]
  exact hI

end GlobalTheory.LBDescent
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

end GlobalTheory.AmpleRigid
end
end

section

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace TensorProduct GlobalTheory.AnPer

namespace GlobalTheory.TaylorHom

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)}

theorem eventually_mem {w : Fin g → ℂ} (h : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, w) : Tot I g) ∈ W := by
  have hc : Continuous fun z : I → ℂ ↦ ((z, w) : Tot I g) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds h)

theorem analyticAt_slice (h : Hol W) {w : Fin g → ℂ} (hw : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    AnalyticAt ℂ (fun z : I → ℂ ↦ h.fn (z, w)) 0 := by
  have hp : AnalyticAt ℂ (fun z : I → ℂ ↦ ((z, w) : Tot I g)) 0 :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := h.fn) (f := fun z : I → ℂ ↦ ((z, w) : Tot I g)) (h.analytic _ hw) hp

def coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W) : Hol W₀ :=
  Hol.mk (fun p ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v) fun p hp ↦
    AnalyticAt.comp (g := fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) (f := Prod.snd)
      (GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v (h.analytic _ (hW p hp))).1 analyticAt_snd

theorem fn_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    {p : Tot I₀ g} (hp : p ∈ W₀) : (coef hW k v h).fn p = iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v := by
  unfold coef
  exact Hol.fn_mk _ _ hp

theorem dw_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    (a : Fin g) : dw a (coef hW k v h) = coef hW k v (dw a h) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hH : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hG'⟩ := GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v hH

  have hL : (dw a (coef hW k v h)).fn p =
      fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) p.2 (Pi.single a 1) := by
    rw [show dw a (coef hW k v h) =
        Hol.der ((0, Pi.single a 1) : Tot I₀ g) (coef hW k v h) from rfl, Hol.fn_der _ _ hp,
      Hol.fderiv_fn_congr (F := fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) _
        (fun q hq ↦ fn_coef hW k v h hq) hp]
    have hc := (hG.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p))).fderiv
    rw [show (fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) =
        (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) ∘ Prod.snd from rfl, hc]
    rfl
  have hR : (coef hW k v (dw a h)).fn p =
      iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1)) 0 v := by
    rw [fn_coef hW k v (dw a h) hp]
    have hev : (fun z : I → ℂ ↦ (dw a h).fn (z, p.2)) =ᶠ[𝓝 0]
        fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1) := by
      filter_upwards [eventually_mem (hW p hp)] with z hz
      exact Hol.fn_der _ _ hz
    exact congrFun (congrArg DFunLike.coe ((hev.iteratedFDeriv (𝕜 := ℂ) k).eq_of_nhds)) v
  rw [hL, hR]
  exact hG' _

variable [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D]

def poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W) : D ⊗[ℂ] Hol W₀ :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ • ∏ a, t (s a)) ⊗ₜ[ℂ] coef hW k (fun a ↦ Pi.single (s a) 1) h

theorem ev_poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W)
    (p : Tot I₀ g) (hp : p ∈ W₀) :
    Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
      (poly hW N t h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2) := by

  simp only [poly, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
  Algebra.ofId_apply, Hol.ev_apply, fn_coef hW _ _ h hp, GlobalTheory.PeriodFamily.taylor]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

theorem exists_taylor_algHom : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot I₀ g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∃ Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : Tot I₀ g) (hp : p ∈ W₀),
      Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
        (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) ∧
      ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h) := by
  intro I I₀ _ _ _ g D _ _ N t ht W W₀ hW

  have slice_eq : ∀ {p : Tot I₀ g} (_ : p ∈ W₀) {F : (I → ℂ) → ℂ} (x : Hol W),
      (∀ z, ((z, p.2) : Tot I g) ∈ W → x.fn (z, p.2) = F z) →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ x.fn (z, p.2)) = GlobalTheory.PeriodFamily.taylor N t F := by
    intro p hp F x hx
    apply GlobalTheory.PeriodFamily.taylor_congr_germ
    filter_upwards [eventually_mem (hW p hp)] with z hz
    exact hx z hz
  have hconst : ∀ c : ℂ, poly hW N t (algebraMap ℂ (Hol W) c) = algebraMap ℂ (D ⊗[ℂ] Hol W₀) c := by
    intro c
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [ev_poly, AlgHom.commutes, slice_eq hp (F := fun _ ↦ c) _ fun z hz ↦ Hol.fn_algebraMap c hz,
      GlobalTheory.PeriodFamily.taylor_const_fun]
  have hadd : ∀ x y : Hol W, poly hW N t (x + y) = poly hW N t x + poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_add (f := _), ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) + y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_add x y hz,
      GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  have hmul : ∀ x y : Hol W, poly hW N t (x * y) = poly hW N t x * poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_mul, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) * y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_mul x y hz,
      GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  refine ⟨{ toFun := poly hW N t
            map_one' := by simpa only [map_one] using hconst 1
            map_mul' := hmul
            map_zero' := by simpa only [map_zero] using hconst 0
            map_add' := hadd
            commutes' := hconst }, fun h p hp ↦ ev_poly hW N t h p hp, fun a h ↦ ?_⟩
  show poly hW N t (dw a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (poly hW N t h)

  simp only [poly, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← dw_coef]
  rfl

end GlobalTheory.TaylorHom
end
end

section

open NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory

theorem isIntegral_inv_of_pow_eq_one {K : Type} [Field K] {u : K} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    IsIntegral ℤ u⁻¹ := by
  refine IsIntegral.of_pow hn ?_
  rw [inv_pow, hu, inv_one]
  exact isIntegral_one

theorem matLat_smul_le_of_isIntegral {K : Type} [Field K] [NumberField K] {a b : ℕ} (c : K) (hc : IsIntegral ℤ c)
    (A : Matrix (Fin a) (Fin b) K) (M : Submodule (𝓞 K) (Fin b → K)) :
    Formalism.DivisionValues.matLat (c • A) M ≤ Formalism.DivisionValues.matLat A M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hmem : A.mulVec y ∈ Formalism.DivisionValues.matLat A M := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have h2 := (Formalism.DivisionValues.matLat A M).smul_mem (⟨c, hc⟩ : 𝓞 K) hmem
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  exact h2

theorem finitePlaceBound_inv_rootOfUnity_smul {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}
    {Df : DefSide Bs} (O : FunData K Df) (ze : Bs.Tup → K) (μ : Formalism.PairingDivisionLocalBalance.Pl K → Bs.Tup) (C b : ℝ)
    (hze : ∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) (h : LeafFP O μ C b) :
    LeafFP { O with vmu := fun t => (ze t)⁻¹ • O.vmu t } μ C b := by
  obtain ⟨ha, hb, hc⟩ := h
  refine ⟨fun w => ?_, hb, hc⟩
  obtain ⟨n, hn, hu⟩ := hze (μ w)
  exact le_trans (localization_mono _
    (matLat_smul_le_of_isIntegral _ (isIntegral_inv_of_pow_eq_one hn hu) _ _)) (ha w)

end GlobalTheory
end
