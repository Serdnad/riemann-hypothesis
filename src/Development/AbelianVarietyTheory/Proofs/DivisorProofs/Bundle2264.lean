module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerUnram

theorem formallyUnramified_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  intro K _ _ B f hf H
  have hfin : IsFinite (Hom.hom f).left := hf.1
  set Z := pullback (Hom.hom f).left η[B.X].left with hZ
  set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp
  have : IsFinite p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hnat := Scheme.isoSpec_hom_naturality p
  have hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom := by
    rw [← hnat]; simp
  have hfinS : IsFinite (Spec.map p.appTop) := by rw [hS]; infer_instance
  have hfinR : p.appTop.hom.Finite := (IsFinite.SpecMap_iff _).1 hfinS
  let ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  let _ : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have h : ψ.hom.Finite := by
      show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
      exact hfinR.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    exact h
  have hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ := by simp [ψ]
  have : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp',
    CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]
  show Algebra.FormallyUnramified K Γ(Z, ⊤)
  refine GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_

  let q : Sp (DualNumber K) ⟶ Z := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv
  have hq : q ≫ p = spMap (algebraMap K (DualNumber K)) := by
    have e := Scheme.isoSpec_inv_naturality p
    simp only [q, Category.assoc]
    rw [← e, Scheme.isoSpec_Spec]
    simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact φ.commutes a
  have hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p := by
    intro T g
    rw [Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, Over.w η[B.X]]
    rfl
  let v : epsPtR (𝟙 (Sp K)) ⟶ B.X := Over.homMk (q ≫ pullback.fst _ _) (by
    rw [hfst, hq]; exact (Category.comp_id _).symm)
  have hv : v ≫ Hom.hom f = 1 := by
    ext1
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    simp only [v, Over.homMk_left, Category.assoc]
    rw [pullback.condition, ← Category.assoc q, hq]
    rfl

  let T₀ : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let red : T₀ ⟶ epsPtR (𝟙 (Sp K)) := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1)
  let bas : epsPtR (𝟙 (Sp K)) ⟶ T₀ := Over.homMk (spMap (algebraMap K (DualNumber K))) rfl
  have hrb : red ≫ bas = 𝟙 T₀ := by
    ext1
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let w : epsPtR (𝟙 (Sp K)) ⟶ B.X := v * (bas ≫ red ≫ v)⁻¹
  have hw₀ : red ≫ w = 1 := by
    simp only [w]
    rw [comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]
  have hwf : w ≫ Hom.hom f = 1 := by
    simp only [w]
    rw [mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one,
      _root_.mul_one]
  have hw : w = 1 := H w (by
    have := congrArg Over.Hom.left hw₀
    rw [Over.comp_left] at this
    exact this) hwf
  have hvc : v = bas ≫ red ≫ v := mul_inv_eq_one.mp hw
  have hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q := by
    refine pullback.hom_ext ?_ ?_
    · have := congrArg Over.Hom.left hvc
      simpa [v, red, bas] using this
    · change q ≫ p = _ ≫ _ ≫ q ≫ p
      rw [hq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
  simp only [q, ← Category.assoc] at hq2
  rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hq2
  have := congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KerUnram
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_left_origin {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) : f.hom.left A.origin = B.origin := by
  have e : (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X) ≫ f.hom = 1 := by
    rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  unfold origin
  rw [← e, Over.comp_left]
  rfl

theorem exists_sec_pull_ample_vanish_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧
      cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  intro K _ A B f d hd hf
  obtain ⟨L, hL, amp, rfl⟩ := hd
  obtain ⟨N, hN, M, t, h0, h1⟩ := GlobalTheory.T.exists_ampleSections_vanishing_origin_separating K B L hL amp
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_apply_ne_origin' K A B f hf
  let ιB := (B.X.hom ⁻¹ᵁ ⊤).ι
  let h : A.X.left ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift ιB f.hom.left (by
    rw [Scheme.Opens.range_ι]; intro x _; trivial)
  have hh : h ≫ ιB = f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ x, ιB (h x) = f.hom.left x := fun x => by rw [← hh]; rfl
  obtain ⟨j, hj⟩ := h1 (h a) (by rw [hpt]; exact ha)
  let s := ReciprocityTheory.ChartRestriction.G.DVR.pullSec L (fun _ : Fin N => ιB) (fun _ => 1) (t j) h
  have hs : Out.nonzeroLocus s = h ⁻¹ᵁ Out.nonzeroLocus (t j) := GlobalTheory.nonzeroLocus_pullSec _ _ (t j) h
  refine ⟨N, _, LB.isLB_linComb hL _ _, s, hN, ?_, ?_, ?_⟩
  · rw [cls_linComb hL]
    simp only [hh, one_zsmul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro e
    have : a ∈ Out.nonzeroLocus s := by rw [hs]; exact hj
    rw [e] at this; exact this
  · intro ho
    rw [hs] at ho
    exact h0 j (h A.origin) (by rw [hpt, hom_left_origin]) ho

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_zsmul_of_symm : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  intro K _ B A c hc f n
  have bil := GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X

  have h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0 := by
    have e := (bil 1 1 1 0).2.1
    simp only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e
    exact e

  have hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c := by
    intro y
    have hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c := hc
    rw [show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']

  have hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c =
      AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c := by
    intro y z
    simp only [AbVar.lam]
    abel
  set x := f.hom with hx
  have key : AbVar.lam c x x = 2 • CechPic.pull x.left c := by
    have e := (bil x x 1 (-1)).2.2.2.2
    rw [zpow_neg_one] at e
    have e2 := hmul x x⁻¹
    rw [_root_.mul_inv_cancel, h1, hinv, e] at e2
    have e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c =
        -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c) := by module
    rw [← sub_eq_zero, e3, ← e2, neg_zero]
  refine ⟨key, ?_⟩
  have step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c =
      CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c := by
    intro m
    rw [zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]
    module
  change CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, h1]; simp
  | succ m ih =>
    rw [step, ih]
    module
  | pred m ih =>
    have e := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at e
    rw [eq_sub_of_add_eq e.symm]
    module

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  first | exact @GlobalTheory.AV.DimLe.dim_le | exact GlobalTheory.AV.DimLe.dim_le | (intros; apply GlobalTheory.AV.DimLe.dim_le <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  first | (exact @GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (exact GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (intros; apply GlobalTheory.AV.AmpleTopPos.inter_top_pos  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  first | exact @GlobalTheory.AV.isAmpleCls_add | exact GlobalTheory.AV.isAmpleCls_add | (intros; apply GlobalTheory.AV.isAmpleCls_add <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  first | exact @GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | exact GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | (intros; apply GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cancel_of_surjective_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left → ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  first | exact @GlobalTheory.AV.AbVar.cancel_of_surjective | exact GlobalTheory.AV.AbVar.cancel_of_surjective | (intros; apply GlobalTheory.AV.AbVar.cancel_of_surjective <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_factorisation_through_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | exact GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | (intros; apply GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup : ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i → IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  first | (exact @GlobalTheory.AV.AbVar.exists_quotient_finite) | (exact GlobalTheory.AV.AbVar.exists_quotient_finite) | (intros; apply GlobalTheory.AV.AbVar.exists_quotient_finite  <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

open GlobalTheory.HeckeUOps

theorem levelLe_one_two {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

theorem exists_betaInv_heckeU {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (_hL : L.Is μ₀) (G : GridData L sc)
    (i j : Fin D.R.m) : ∃ χ : HeckeU D (botBig D i j), ∀ x, χ.f x = (betaH G i j)⁻¹.1 (finIdl D x) := by
  classical
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  choose! qf hqf using GlobalTheory.T.exists_prime_notInert_place_of_mem G.pl
  have hS : ∀ q ∈ G.pl.S0.image qf, q.Prime ∧ ¬ InertQ D q := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨(hqf v hv).1, (hqf v hv).2.1⟩
  have hlev : ∀ v, (G.ch.chiH (D.R.m - i)).UnrAt v ∨ ∃ q ∈ G.pl.S0.image qf, Formalism.L2.Host.OverP D.host q v ∧
      (G.ch.chiH (D.R.m - i)).LevelLe v 2 := by
    intro PP
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · refine Or.inr ⟨qf _, Finset.mem_image_of_mem _ h, ?_, ?_⟩
      · have := (hqf _ h).2.2
        simpa [HeightOneSpectrum.under, Formalism.L2.Host.OverP] using this
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
        · exact levelLe_one_two (G.ch.lev0 _ k1 k2 PP h0).1
        · exact (G.ch.lev1 _ k1 k2 PP h1).1
    · exact Or.inl (G.ch.unr _ k1 k2 PP h)
  have hcu := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ k1 k2)
  have hci : (G.ch.chiH (D.R.m - i)).HasInf (embT D) (fun τ => 2 * cen D sc.cGap τ (D.R.m - i)) := G.ch.inf _ k1 k2
  let χc : HeckeU D 0 := ofChar 0 _ _ hcu hci (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ _ 2 (fun q hq => (hS q hq).1) hlev)
    (GlobalTheory.T.heckeCharacter_bounded_conductor_kills_idele_norms D _ _ _ 2 (G.ch.triv _ k1 k2) hci (fun q hq => (hS q hq).1) hlev)
    (fun τ => by simp) (GlobalTheory.T.heckeCharacter_nonInert_bounded_level_kills_units D _ _ 2 hS hlev)
  have he := L.C.isEta
  have hei : L.C.eta.HasInf (embT D) (fun _ => 1) := fun a => by
    rw [he.inf a, ← D.eTau.prod_comp]
    rfl
  let χe : HeckeU D 1 := ofChar 1 L.C.eta _ he.unitary hei (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
    (GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm D _ he) (fun τ => by simp) (GlobalTheory.T.heckeCharacter_nonInert_bounded_level_kills_units D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
  have hr : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have hx := (ranks_exact D i j).1
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨w, hw⟩ := odd_sLen D
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨inv _ χc (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_zero, mul_one, inv_f]
    rfl
  · refine ⟨inv _ (mul 1 χc χe (by decide)) (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_one, inv_f, mul_f]
    rfl

end GlobalTheory.FunObj.SqNum
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerField

variable {X : Scheme.{0}} {W : X.Opens} {d : Fld X} {x : X}

theorem germ_field_congr (hd : IsField W d) {O O' : X.Opens} (hO : x ∈ O) (hO' : x ∈ O')
    (hOW : O ≤ W) (hO'W : O' ≤ W) (f : Γ(X, O)) (f' : Γ(X, O'))
    (h : (X.presheaf.germ O x hO).hom f = (X.presheaf.germ O' x hO').hom f') :
    (X.presheaf.germ O x hO).hom (d O f) = (X.presheaf.germ O' x hO').hom (d O' f') := by
  obtain ⟨V, hV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hO hO' f f' h
  have h1 : (X.presheaf.germ O x hO).hom (d O f) =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iU) f)) := by
    rw [hd.2.2 O V (leOfHom iU) hOW f]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iU x hV _).symm
  have h2 : (X.presheaf.germ O' x hO').hom (d O' f') =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iV) f')) := by
    rw [hd.2.2 O' V (leOfHom iV) hO'W f']
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iV x hV _).symm
  have e' : resG X (leOfHom iU) f = resG X (leOfHom iV) f' := e
  rw [h1, h2, e']

theorem exists_rep (hxW : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f : Γ(X, O)), (X.presheaf.germ O x hO).hom f = t := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine ⟨U ⊓ W, ⟨m, hxW⟩, inf_le_right, resG X (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
  rw [← hs]
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨m, hxW⟩ s

theorem exists_rep₂ (hxW : x ∈ W) (t t' : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f f' : Γ(X, O)),
      (X.presheaf.germ O x hO).hom f = t ∧ (X.presheaf.germ O x hO).hom f' = t' := by
  obtain ⟨O₁, h₁, hW₁, f₁, e₁⟩ := exists_rep hxW t
  obtain ⟨O₂, h₂, hW₂, f₂, e₂⟩ := exists_rep hxW t'
  refine ⟨O₁ ⊓ O₂, ⟨h₁, h₂⟩, inf_le_left.trans hW₁, resG X (inf_le_left : O₁ ⊓ O₂ ≤ O₁) f₁,
    resG X (inf_le_right : O₁ ⊓ O₂ ≤ O₂) f₂, ?_, ?_⟩
  · rw [← e₁]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨h₁, h₂⟩ f₁
  · rw [← e₂]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨h₁, h₂⟩ f₂

def germMap (hxW : x ∈ W) (t : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (X.presheaf.germ _ x (exists_rep hxW t).choose_spec.choose).hom
    (d _ (exists_rep hxW t).choose_spec.choose_spec.choose_spec.choose)

theorem germMap_germ (hd : IsField W d) (hxW : x ∈ W) {O : X.Opens} (hO : x ∈ O) (hOW : O ≤ W)
    (f : Γ(X, O)) :
    germMap (d := d) hxW ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  have hs := (exists_rep hxW ((X.presheaf.germ O x hO).hom f)).choose_spec.choose_spec
  exact germ_field_congr hd _ hO hs.choose hOW _ f hs.choose_spec.choose_spec

end GlobalTheory.StalkDerField


open GlobalTheory.StalkDerField in
theorem GlobalTheory.StalkDerField.exists_stalk_derivation : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  intro X W d hd x hxW
  let g : X.presheaf.stalk x →+ X.presheaf.stalk x := AddMonoidHom.mk' (germMap (d := d) hxW) (by
    intro t t'
    obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
    rw [← map_add (f := _), germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
      germMap_germ hd hxW hO hOW, hd.1 O hOW f f', map_add])
  refine ⟨Derivation.mk' g.toIntLinearMap ?_, fun O hO hOW f => germMap_germ hd hxW hO hOW f⟩
  intro t t'
  obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
  show germMap hxW _ = _ • germMap hxW _ + _ • germMap hxW _
  rw [← map_mul, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
    germMap_germ hd hxW hO hOW, hd.2.1 O hOW f f', smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
end
end
