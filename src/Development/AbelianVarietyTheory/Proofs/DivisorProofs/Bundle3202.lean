module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle020
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.PullAutConst

theorem gm_pullChart {X Z T : Scheme.{0}} (L : LB X) (F : Z ⟶ X) (f : T ⟶ Z) (y : T) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y _ ((L.pull F).g (fun _ => j) (fun _ => j')) = gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem exists_glued {X Y B : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β))
    (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hL : L.IsLB) (hM : M₀.IsLB)
    (hF : PGen wF) (hw : PGen w) (hβ : π₁ ≫ β = π₂ ≫ β) :
    ∃ s : Γ(B, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (j₀ : M₀.ι) (j₁ j₂ : L.ι),
      β (π₁ (f z)) ∈ M₀.U j₀ → π₁ (f z) ∈ L.U j₁ → π₂ (f z) ∈ L.U j₂ →
      gm f z ⊤ s = gw wF (f ≫ π₂) z j₀ j₂ * gw w f z j₂ (fun _ => j₁) * (gw wF (f ≫ π₁) z j₀ j₁)⁻¹ := by
  have hpt : ∀ x, β (π₁ x) = β (π₂ x) := fun x => congrArg (fun g : B ⟶ Y => g x) hβ
  obtain ⟨W, hW⟩ : ∃ W : M₀.ι × L.ι × L.ι → B.Opens, ∀ t x,
      x ∈ W t ↔ β (π₁ x) ∈ M₀.U t.1 ∧ π₁ x ∈ L.U t.2.1 ∧ π₂ x ∈ L.U t.2.2 :=
    ⟨fun t => π₁ ⁻¹ᵁ (β ⁻¹ᵁ M₀.U t.1) ⊓ (π₁ ⁻¹ᵁ L.U t.2.1 ⊓ π₂ ⁻¹ᵁ L.U t.2.2), fun _ _ => Iff.rfl⟩
  have l₂ : ∀ t, W t ≤ π₂ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.2) := fun t x hx =>
    ⟨mem_pull.2 (show β (π₂ x) ∈ _ by rw [← hpt]; exact ((hW t x).1 hx).1), ((hW t x).1 hx).2.2⟩
  have lw : ∀ t, W t ≤ (L.pull π₂).U (fun _ => t.2.2) ⊓ (L.pull π₁).U (fun _ => t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).2.2, mem_pull.2 ((hW t x).1 hx).2.1⟩
  have l₁ : ∀ t, W t ≤ π₁ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).1, ((hW t x).1 hx).2.1⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ t, Γ(B, W t)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t : M₀.ι × L.ι × L.ι), f z ∈ W t →
      gm f z (W t) (u t) =
        gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ :=
    ⟨fun t => res (l₂ t) (pullU π₂ _ (wF.s (fun _ => t.1, t.2.2))) * res (lw t) (w.s (fun _ => t.2.2, fun _ => t.2.1)) *
        (res (l₁ t) (pullU π₁ _ (wF.s (fun _ => t.1, t.2.1))))⁻¹, fun Z f z t hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res f z (l₂ t) hz _).trans (gm_pull f π₂ z _ (l₂ t hz) _)) (gm_res f z (lw t) hz _)))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ t) hz _).trans (gm_pull f π₁ z _ (l₁ t hz) _)))))⟩
  have indep : ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t t' : M₀.ι × L.ι × L.ι), f z ∈ W t → f z ∈ W t' →
      gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ =
      gw wF (f ≫ π₂) z t'.1 t'.2.2 * gw w f z t'.2.2 (fun _ => t'.2.1) * (gw wF (f ≫ π₁) z t'.1 t'.2.1)⁻¹ := by
    rintro Z f z ⟨a, b, c⟩ ⟨a', b', c'⟩ h h'
    obtain ⟨ha, hb, hc⟩ := (hW _ _).1 h
    obtain ⟨ha', hb', hc'⟩ := (hW _ _).1 h'
    have e₂ := hF Z (f ≫ π₂) z a a' c c' (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha)
      (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha') hc hc'
    have e₁ := hF Z (f ≫ π₁) z a a' b b' ha ha' hb hb'
    have ew := hw Z f z c c' (fun _ => b) (fun _ => b') hc hc' (mem_pull.2 hb) (mem_pull.2 hb')
    rw [gm_pullChart L π₁ f z b b' hb hb'] at ew
    have hg : gm ((f ≫ π₂) ≫ β) z _ (M₀.g a a') = gm ((f ≫ π₁) ≫ β) z _ (M₀.g a a') := by
      simp only [Category.assoc, hβ]
    dsimp only
    rw [e₂, e₁, ew, hg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j₁, h₁⟩ := exists_chart hL (π₁ x)
      obtain ⟨j₂, h₂⟩ := exists_chart hL (π₂ x)
      obtain ⟨j₀, h₀⟩ := exists_chart hM (β (π₁ x))
      exact Opens.mem_iSup.2 ⟨(j₀, j₁, j₂), (hW _ x).2 ⟨h₀, h₁, h₂⟩⟩) u
    (fun t t' x hx => (hu _ (𝟙 B) x t hx.1).trans ((indep _ (𝟙 B) x t t' hx.1 hx.2).trans (hu _ (𝟙 B) x t' hx.2).symm))
  refine ⟨s, fun Z f z j₀ j₁ j₂ h₀ h₁ h₂ => ?_⟩
  have hz : f z ∈ W (j₀, j₁, j₂) := (hW _ _).2 ⟨h₀, h₁, h₂⟩
  exact (gm_res f z le_top hz s).symm.trans ((congrArg (gm f z _) (hs _)).trans (hu Z f z _ hz))

theorem exists_unit : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  intro A _ B' _ hB X Y L M₀ β wF π₁ π₂ w hL hM hwF hw hβ
  obtain ⟨s, hs⟩ := exists_glued L M₀ β wF π₁ π₂ w hL hM ((isGen_iff wF).1 hwF) ((isGen_iff w).1 hw) hβ
  have hbij := GlobalTheory.globalFns_holds _ B' hB
  let e := RingEquiv.ofBijective B'.hom.appTop.hom hbij
  let a : Γ(Sp A, ⊤)ˣ := Units.map e.symm.toMonoidHom s
  have ha : Units.map B'.hom.appTop.hom.toMonoidHom a = s := by
    ext
    exact e.apply_symm_apply _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a, ?_⟩
  intro p hp zz J J₀ hJ hJ₀
  have hua : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a) = a := by
    ext
    simp [unitOn]
  have k₁ := gm_pull p B'.hom zz ⊤ trivial a
  rw [hp] at k₁
  have key : gm p zz ⊤ s = gm (𝟙 _) zz ⊤ a := by
    rw [← ha]
    exact k₁
  have hs' := hs (Sp A) p zz (J₀ (p ≫ π₁ ≫ β)) (J (p ≫ π₁)) (J (p ≫ π₂)) (hJ₀ _) (hJ _) (hJ _)
  rw [hua, ← key, show p ≫ π₂ ≫ β = p ≫ π₁ ≫ β by rw [hβ], hs']
  exact (inv_mul_cancel_right _ _).symm

end GlobalTheory.PullAutConst
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.PsiZero

theorem psi_zero_mul_rigK : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  intro V _ _ D hB Z r z J hJ

  let T : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (TK V).hom)
  let ρ : T ⟶ TK V := Over.homMk r rfl
  have hcub : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) r z J = 1 := by
    have e := val_cub D.cub ρ hJ (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0)
    refine e.trans ?_
    rw [GlobalTheory.Poinc.ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face 1 1
  have hc := (val_mul hJ _ _ r).symm.trans ((val_corr hJ (hB 0 0 0) r).trans (val_mul hJ _ _ r))
  rw [hcub, _root_.mul_one,
    congrArg (fun w => val (D.tau w 0) r z J) (add_zero (0 : D.X))] at hc
  have ht : val (D.tau 0 0) r z J = 1 := (mul_eq_left.1 hc.symm)
  unfold DegPre.tau at ht
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) r z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul] at ht
  rw [← mul_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.Poinc.Sep.PsiZero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_qk_over_cF : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  intro V _ _ D hB F _ _ _ k hk y x hx
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk y x hx

end GlobalTheory.UCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USep

open GlobalTheory.TorsFrame

theorem isTorsFrame_sq : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S)
    (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
    IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  intro S P rig n T x τ ⟨hx, hτ, α, hα, hN, hC⟩
  have hL := P.isLB
  have eN : (mulA P.A n).left ≫ (mulA P.A n).left = (mulA P.A (n ^ 2)).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← sq]
  have ex : x.left ≫ (mulA P.A n).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx, one_left]
  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, eN]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (mulA P.A n).left) (GeneratorPullback.powGen P.L _ _ α (n ^ 2)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.powGen_isGen _ _ _ _ hα _))
  have vα₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
      val α' r z J = val α (r ≫ (mulA P.A n).left) z J * val α r z J ^ (n ^ 2) := fun Z r z J hJ => by
    rw [vα' _ _ z J hJ, val_mul hJ, val_pull hJ, val_powGen]
  refine ⟨by rw [sq, pow_mul, hx, one_pow], hτ, α', hα', corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · have h0 := val_corr hJ hN (𝟙 (𝟙_ (Over S)).left)
    rw [val_pull hJ, val_mul hJ, val_inv] at h0 ⊢
    rw [vα₂ _ _ z J hJ, Category.assoc, eSec_mulA, h0]
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) (𝟙 (𝟙_ (Over S)).left) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig (𝟙 (𝟙_ (Over S)).left) z J ^ k := fun k => map_zpow _ _ _
    rw [hp, hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module
  · have h1 := val_corr hJ hC (𝟙 T.left)
    have h2 := val_corr hJ hN T.hom
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) T.hom z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J ^ k := fun k => map_zpow _ _ _
    have hf : ∀ k : ℤ, val (powFrame P.A P.L x τ k) (𝟙 T.left) z J = val τ (𝟙 T.left) z J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, val_inv, hp] at h2
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ] at h1
    simp only [Category.id_comp] at h1
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ]
    simp only [Category.id_comp]
    rw [vα₂ _ _ z J hJ, ex, h2]
    have ha : val α x.left z J = val τ (𝟙 T.left) z J ^ ((n : ℤ) ^ 2) *
        (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J)⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    rw [ha]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module

end GlobalTheory.USep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  first | exact @GlobalTheory.TInj.qkPt_g_eq_of_equiv | exact GlobalTheory.TInj.qkPt_g_eq_of_equiv | (intros; apply GlobalTheory.TInj.qkPt_g_eq_of_equiv <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  first | exact @GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | exact GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | (intros; apply GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff <;> assumption)
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.psi_zero_mul_rigidificationK_eq_one : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK | exact GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK | (intros; apply GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  first | exact @GlobalTheory.PullAutConst.exists_unit | exact GlobalTheory.PullAutConst.exists_unit | (intros; apply GlobalTheory.PullAutConst.exists_unit <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_divisionPoint_pair_over_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  first | exact @GlobalTheory.UCanon.exists_qk_over_cF | exact GlobalTheory.UCanon.exists_qk_over_cF | (intros; apply GlobalTheory.UCanon.exists_qk_over_cF <;> assumption)

end
end
