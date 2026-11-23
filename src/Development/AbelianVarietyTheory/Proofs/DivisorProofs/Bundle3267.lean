module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenPackage

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'}

theorem jK_sq (hρ : Function.Injective ρ) : jK R' ≫ spMap ρ =
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem exists_genericMap (hρ : Function.Injective ρ) {G : Over (Sp R)} {G₁ : Over (Sp R')} {β : G₁.left ⟶ G.left}
    (w : β ≫ G.hom = G₁.hom ≫ spMap ρ) : ∃ κ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R),
      κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β := by
  refine ⟨pullback.lift _ (pullback.snd _ _ ≫
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, jK_sq hρ]

theorem isGrpPullback_generic (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ := by
  have hsq := jK_sq hρ
  have hmono : Mono (jK R) := EvenDesc.mono_jK R
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  exact (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w

theorem exists_square_extLam (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] [IsCommMonObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left) (hL : L.IsLB) (hExt : ExtLam G L PP) :
    ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ExtLam G₁ (L.pull κ₁) (PP.pull β₂) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨β₂, hsqβ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G G₁ β hβ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨β₂, hsqβ, pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have hN := pull_isLB hL κ₁
  have H1 := Hκ L (L.pull κ₁) _ PP g₂ hL hN hExt.1 (GlobalTheory.PolBaseChange.lbIso_refl hN) (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_generic_pol (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (hgen : IsMonHom gen.hom) :
    ∃ (A' : PolAV (Sp (FractionRing R'))) (gen' : (Over.pullback (jK R')).obj G₁ ≅ A'.A), IsMonHom gen'.hom ∧
      LBIso (A'.L.pull gen'.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  obtain ⟨A', gA, pA, -, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _
    (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) gA :=
    ⟨pA, fun T x y x₀ y₀ hx hy => by
      have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
      have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
      rw [e₁, e₂, ← mA]; rfl⟩
  have tA' : LBIso (A.L.pull gA) A'.L := tA
  obtain ⟨e, he, hee⟩ := grpPullback_iso ((hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl) gpA
  refine ⟨A', e, he, ?_⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso tA'.symm e.hom.left hee.symm)
    (GlobalTheory.GenSpread.lbIso_pull_pull A.isLB κ₁ rfl)

end GlobalTheory.Mum.EvenPackage



open GlobalTheory.Mum.EvenPackage in
theorem GlobalTheory.Mum.exists_even_package_of_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW
    R₃ _ _ _ ρ₃ G₃ _ _ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃ hL₃ hL₃g
  have hR₃ : Base R₃ := by
    haveI := hR.2
    exact ⟨hρ₃.1, charZero_of_injective_ringHom hρ₃.2.1⟩
  have hG₃ : IsSemiAbelian G₃ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ₃ hG
  obtain ⟨R₉, i1, i2, i3, ρ₄, G₉, i4, i5, β₄, X, i6, i7, i8, hρ₄, hβ₄, hTQ⟩ :=
    exists_finExt_tq_closedFibre R₃ hR₃ G₃ hG₃
  have hρ : FinExt (ρ₄.comp ρ₃) := ⟨hρ₄.1, hρ₄.2.1.comp hρ₃.2.1, hρ₄.2.2.comp hρ₃.2.2⟩
  have hβ : IsGrpPullback G₉ G (spMap (ρ₄.comp ρ₃)) (β₄ ≫ β₃) :=
    (hβ₄.comp hβ₃).congr (TraitExt.spMap_comp _ _) rfl
  have hG₉ : IsSemiAbelian G₉ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ hG
  obtain ⟨κ₄, hκ₄⟩ := exists_genericMap hρ₄.2.1 hβ₄.1.w
  have hκ₉ : (κ₄ ≫ κ₃) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₄ ≫ β₃ := by
    rw [Category.assoc, hκ₃, ← Category.assoc, hκ₄, Category.assoc]
  have hN : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have hL₉ : (L₃.pull β₄).IsLB := pull_isLB hL₃ _
  have hL₉g : LBIso ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) ((A.L.pull gen.hom.left).pull (κ₄ ≫ κ₃)) :=
    LBIso.trans (pull_isLB hL₉ _) (pull_isLB hL₃ _) (pull_isLB hN _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hL₃ (pullback.fst G₉.hom (jK R₉)) rfl).symm
      (GlobalTheory.GenSpread.lbIso_pull_comp κ₄ hκ₄.symm rfl hL₃g)
  obtain ⟨A₉, gen₉, hgen₉, hA₉⟩ := exists_generic_pol hρ.2.1 hβ hκ₉ A gen hgen
  have hA₉' : LBIso (A₉.L.pull gen₉.hom.left) ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) :=
    LBIso.trans (pull_isLB A₉.isLB _) (pull_isLB hN _) (pull_isLB hL₉ _) hA₉ hL₉g.symm
  have hprop : IsProper (pullback.snd G₉.hom (jK R₉)) := by
    have hi : IsIso gen₉.hom.left := ((Over.forget _).mapIso gen₉).isIso_hom
    have := A₉.isAb.proper
    have hw : pullback.snd G₉.hom (jK R₉) = gen₉.hom.left ≫ A₉.A.hom := (Over.w gen₉.hom).symm
    rw [hw]; infer_instance
  have hsym := GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen₉.hom hgen₉ _ _ A₉.isLB (pull_isLB hL₉ _) A₉.sym hA₉'
  haveI : IsNoetherianRing R₉ := hρ.1.1
  haveI : IsIntegrallyClosed R₉ := hρ.1.2.2.1
  obtain ⟨P, hP⟩ := GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R₉ G₉ hG₉ hprop _ hL₉ hsym
  obtain ⟨β₂, hsq, hE⟩ := exists_square_extLam hρ.2.1 hβ hκ₉ _ PP hN hPP
  refine ⟨R₉, i1, i2, i3, ρ₄.comp ρ₃, G₉, i4, i5, β₄ ≫ β₃, β₂, P, A₉, gen₉, hρ, hβ, hsq, hG₉, ?_, ?_, hgen₉, ?_⟩
  · rw [hP]
    exact lbIso_lam_of_extLam R₉ G₉ hG₉ _ _ _ hL₉ (pull_isLB hN _) hL₉g.symm hE
  · refine evenOn_of_trait_unif R hR G hG A gen hgen W φ GW βW DW AW UW κ hW hφi hφl hGW hκ hUW R₉ _ G₉ _ _ P hρ hβ hκ₉
      ?_ X hTQ
    rw [hP]; exact hL₉g
  · rw [hP]; exact hA₉'

end
end

section

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isPeriod_comp_isometry_symm {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ρ P) : IsPeriod D' ρ (P.comp w.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  have hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
    have := congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange
    simpa [AddMonoidHom.coe_range] using this
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [hlin]
  · intro x y hxy
    have := hinj hxy
    simpa using this
  · rw [hrange]; exact hdisc
  · rw [hrange']; exact hspan
  · have := hw (w.symm x) (w.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [him, this]

theorem unif_of_fineAt : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type)
    (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) →
    SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) →
    FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF
  have hN0 : 0 < N := by omega
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hsm
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  obtain ⟨n, Di, t, hmem, hall, hdist⟩ := GlobalTheory.T.exists_finite_markedLattice_period_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF
  have hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P) := by
    intro i P
    by_cases hP : IsPeriod (Di i) ρ P
    · exact ⟨P, hP, fun _ => rfl⟩
    · obtain ⟨Q, hQ⟩ := (hmem i).2
      exact ⟨Q, hQ, fun h => absurd h hP⟩
  choose Q hQp hQe using hQ
  have hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e :=
    fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)
  choose u ex hu using hex
  have hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P) := by
    intro i P hP
    have := hu i P
    rwa [hQe i P hP] at this
  have hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _) :=
    fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩
  have cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ))
      (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
      (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt F (RingHom.id ℂ) ρ N D'' t'' P' y' e' →
      ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        IsMarkedIsom N D' D'' t' t'' w ∧ ∀ x, P' (w x) = h (P x) := by
    intro D' D'' t' t'' P P' y y' e e' hy h1 h2
    subst hy
    obtain ⟨w, h, hw, hP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2
    exact ⟨w, h, hw, hP⟩
  refine ⟨{
      n := n
      Di := Di
      t := t
      mem := fun i => (hmem i).1
      ne := fun i => (hmem i).2
      all := hall
      distinct := hdist
      u := u
      ex := ex
      unif := hunif
      onto := ?_
      disj := ?_
      fibre := ?_
      hol := ?_
      lift := ?_ }⟩
  · intro y hy
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    refine ⟨i, _, hP', ?_⟩
    exact (hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw
      (fun x => by simp)).symm
  · intro i j P P' hP hP' huu
    obtain ⟨w, h, hw, -⟩ := cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')
    exact hdist i j w hw
  · intro i P P' hP hP'
    constructor
    · intro huu
      exact cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')
    · rintro ⟨w, h, hw, hPw⟩
      exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw
  · intro i m B P hB hHol
    exact GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm
      hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))
  · intro m B y hB hy hhol b₀ hb₀
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    have hU' := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w
      (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'
    obtain ⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'
    refine ⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩
    exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _)
      (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)

end GlobalTheory.PELU
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  first | exact @GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | exact GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | (intros; apply GlobalTheory.Mum.quotient_smooth_and_baseChange_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_galoisAction_pulledBack_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  first | exact @GlobalTheory.Mum.galAct_nonempty | exact GlobalTheory.Mum.galAct_nonempty | (intros; apply GlobalTheory.Mum.galAct_nonempty <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  first | (exact @GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (exact GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (intros; apply GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem GlobalTheory.FibreCorr.exists_correction : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ k : ℕ, ∃ e : ℕ, ∀ F : M₁.O z, (∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ G b : M₁.O z, (F : Ω) = G + b ∧ (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x') ∧ b ∈ Ideal.span {c : M₁.O z | ¬ IsUnit c} ^ k := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU _ z hz k
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  have key : ∀ k, ∃ e, GlobalTheory.FibreCorr.approxIdeal hπ U D z e ≤
      GlobalTheory.FibreCorr.fibreIdeal hπ D z ⊔ maximalIdeal (M₁.O z) ^ k := by
    refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (M₁.O z) (GlobalTheory.FibreCorr.approxIdeal hπ U D z) (GlobalTheory.FibreCorr.fibreIdeal hπ D z)
      (GlobalTheory.FibreCorr.approxIdeal_antitone U D z) (GlobalTheory.FibreCorr.pow_le_approxIdeal U D z) ?_
    intro F a ha hK
    have ha' : ∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈
        (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n := by
      intro n
      rw [← AdicCompletion.maximalIdeal_eq_map]
      exact ha n
    refine GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit o Ω M₁ M π hπ hprop hn₁ hn D z hz F a ha' ?_
    intro x' hx' hc f' hf' e
    obtain ⟨N, hN⟩ := GlobalTheory.T.approximate_germ_mem_cartier_ideal_mod_max_pow o Ω M₁ M π hπ hn U D hU z x' hx' hc f' hf' e
    exact ⟨N, fun n hn => hN n hn (a n) (hK n)⟩
  obtain ⟨e, he⟩ := key k
  refine ⟨e, fun F hF => ?_⟩
  have hF' : F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z e := hF
  obtain ⟨G, hG, b, hb, hGb⟩ := Submodule.mem_sup.1 (he hF')
  refine ⟨G, b, ?_, fun x' hx' f' hf' => hG x' hx' f' hf', ?_⟩
  · rw [← hGb]; simp
  · have hm : Ideal.span {c : M₁.O z | ¬ IsUnit c} = maximalIdeal (M₁.O z) :=
      Ideal.span_eq (maximalIdeal (M₁.O z))
    rw [hm]
    exact hb
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumCoef

theorem shift_add' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (a b : X) :
    shift h h' n j (a + b) = shift h h' n j a + shift h h' n j b := by
  simp only [shift, map_add (f := _), smul_add]; abel

theorem shift_zero' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) :
    shift h h' n j 0 = 0 := by
  simp [shift]

theorem coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ g : ∀ β, SecT D.toPre a N (-1) β, Small (maximalIdeal R) (w := id) g ∧ TFE h h' g ∧ (∀ β, β ≠ 0 → Van (maximalIdeal R) (g β) 0) ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval (g 0) (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J = sval σ₀ (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J := by
  classical
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨s₀, s, hrel, hsmall, hvan, hσ⟩ := GlobalTheory.T.exists_terms_mumfordFormalSection_translates R hB D a a' h h' hE N hN hP σ₀
  obtain ⟨F, hsum, hFs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hB D a (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s hsmall
  have hw0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := shift_zero' h h' _ _
  have hfe : TFE h h' F := by
    refine GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hB D a a' h h' hE (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s F
      (fun mu => Equiv.addRight mu) hsmall hsum ?_ ?_
    · intro mu i
      exact shift_add' h h' _ _ i mu
    · intro mu i
      exact GlobalTheory.T.twistedRelation_cocycle_in_translation R hB D a a' h h' hE (N : ℤ) (-1) i mu 0 _ _ s₀ (s i) (s (i + mu))
        (zero_add _).symm (shift_add' h h' _ _ i mu) (hrel i) (hrel (i + mu))
  have hv0 : ∀ i ∉ ({0} : Finset D.toPre.X), Van (maximalIdeal R) (s i) 0 := fun i hi =>
    hvan i (by simpa using hi)
  refine ⟨F, hFs, hfe, ?_, ?_⟩
  · intro β hβ Z x z J hJ
    rw [hsum 0 {0} hv0 β Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = β) = ∅ := by
      rw [Finset.filter_singleton, hw0, if_neg (Ne.symm hβ)]
    rw [this, Finset.sum_empty]
  · intro Z x z J hJ
    rw [hsum 0 {0} hv0 0 Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = 0) = {0} := by
      rw [Finset.filter_singleton, hw0, if_pos rfl]
    rw [this, Finset.sum_singleton]
    exact hσ Z _ z J hJ

end GlobalTheory.MumCoef
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualConFT.hasRep_of_finiteType | exact GlobalTheory.DualConFT.hasRep_of_finiteType | (intros; apply GlobalTheory.DualConFT.hasRep_of_finiteType <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧ f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  first | exact @GlobalTheory.FlatPair.flat_pair | exact GlobalTheory.FlatPair.flat_pair | (intros; apply GlobalTheory.FlatPair.flat_pair <;> assumption)
end
