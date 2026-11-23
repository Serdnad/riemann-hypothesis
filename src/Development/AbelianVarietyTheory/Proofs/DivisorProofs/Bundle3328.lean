module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3319
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3320
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TraitUnif

theorem exists_generic_fibre_pull : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), Function.Injective φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (AW : PolAV (Sp (FractionRing W))) (genW : ((Over.pullback (jK W)).obj ((Over.pullback (spMap φ)).obj G)) ≅ AW.A) (κ₁ : pullback ((Over.pullback (spMap φ)).obj G).hom (jK W) ⟶ pullback G.hom (jK R)), IsMonHom genW.hom ∧ κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst ((Over.pullback (spMap φ)).obj G).hom (jK W) ≫ pullback.fst G.hom (spMap φ) ∧ LBIso (AW.L.pull genW.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ A gen hgen
  haveI : IsMonHom gen.hom := hgen
  set gφ := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ with hgφ
  have hsq : jK W ≫ spMap φ = spMap gφ ≫ jK R := by
    simp only [hgφ, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  let GV := (Over.pullback (spMap φ)).obj G
  have hβ := isGrpPullback_pullback G (spMap φ)
  let κ₁ : pullback GV.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ)) (pullback.snd GV.hom (jK W) ≫ spMap gφ)
      (by rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ) :=
    pullback.lift_fst _ _ _
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GV).hom ≫ spMap gφ :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GV) ((Over.pullback (jK R)).obj G) (spMap gφ) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GV (jK W)).comp hβ).congr hsq hκf.symm) w
  have hκA : IsGrpPullback ((Over.pullback (jK W)).obj GV) A.A (spMap gφ) (κ₁ ≫ gen.hom.left) :=
    (hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap gφ) A
  have hP' : IsGrpPullback P'.A A.A (spMap gφ) g := by
    refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
    have ex : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]
    rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hκA hP'
  refine ⟨P', e, κ₁, he, hκf, ?_⟩
  have h1 : LBIso (P'.L.pull e.hom.left) ((A.L.pull g).pull e.hom.left) :=
    GlobalTheory.FamRep.lbIso_pull (LBIso.symm ⟨t, ht⟩) _
  have h2 : LBIso ((A.L.pull g).pull e.hom.left) (A.L.pull (e.hom.left ≫ g)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB g e.hom.left
  have h3 : LBIso ((A.L.pull gen.hom.left).pull κ₁) (A.L.pull (κ₁ ≫ gen.hom.left)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB gen.hom.left κ₁
  rw [heq] at h2
  exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB A.isLB _) _) h1
    (LBIso.trans (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) h2 h3.symm)

theorem extLam_pull_square : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)), IsGrpPullback G₁ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst G₁.hom (jK R') ≫ β → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (N : LB ((Over.pullback (jK R')).obj G₁).left) (PP : LB (G2 G).left), L.IsLB → N.IsLB → LBIso N (L.pull κ₁) → ExtLam G L PP → ExtLam G₁ N (PP.pull β₂) := by
  intro R R' _ _ _ _ _ _ ρ hρ G _ _ G₁ _ _ β β₂ κ₁ hβ hsqβ hκf L N PP hL hN hNL hExt
  have hsq : jK R' ≫ spMap ρ =
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  have hκ : IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have H1 := Hκ L N _ PP g₂ hL hN hExt.1 hNL (hExt.2 g₂ hg₂)
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

theorem exists_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  have := hR.1.1
  have := hR.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨AV, genV, κ₁, hgenV, hκ, hLV⟩ := exists_generic_fibre_pull R V φ hφ G A gen hgen
  obtain ⟨βV₂, hsqV, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G _ _ (isGrpPullback_pullback G (spMap φ))
  have hExtV := extLam_pull_square R V φ hφ G _ _ βV₂ κ₁ (isGrpPullback_pullback G (spMap φ)) hsqV hκ _ _ PP
    (pull_isLB A.isLB _) (pull_isLB AV.isLB _) hLV hPP
  have hGV : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hsq, hLam⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V hV _ hGV AV genV hgenV _ hExtV
  have hρloc : IsLocalHom ρ := RingHom.IsIntegral.isLocalHom hρ.2.2.to_isIntegral hρ.2.1
  refine ⟨R', _, _, _, ρ.comp φ, G₁, _, _, β ≫ pullback.fst G.hom (spMap φ), β₂ ≫ βV₂, D₁, A₁, U₁, hR',
    hρ.2.1.comp hφ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.isLocalHom_comp ρ φ
  · refine (hβ.comp (isGrpPullback_pullback G (spMap φ))).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsqV.1, ← Category.assoc, hsq.1, Category.assoc]
    · rw [Category.assoc, hsqV.2, ← Category.assoc, hsq.2, Category.assoc]
  · exact LBIso.trans (DVR.linComb_isLB _ U₁.LG.isLB _ _) (pull_isLB (pull_isLB hPP.1 _) _) (pull_isLB hPP.1 _) hLam
      (GlobalTheory.FamRep.lbIso_pull_pull hPP.1 βV₂ β₂)
end GlobalTheory.Mum.TraitUnif
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  first | exact @GlobalTheory.MixHt.resArch_eq_finsum_cycInt | exact GlobalTheory.MixHt.resArch_eq_finsum_cycInt | (intros; apply GlobalTheory.MixHt.resArch_eq_finsum_cycInt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.pointClosureIntegral_update_tensor_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  first | exact @GlobalTheory.Mix.cycInt_update_tens | exact GlobalTheory.Mix.cycInt_update_tens | (intros; apply GlobalTheory.Mix.cycInt_update_tens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocityDefect_add_bundleSection : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  first | exact @GlobalTheory.DefectAdd.defect_add | exact GlobalTheory.DefectAdd.defect_add | (intros; apply GlobalTheory.DefectAdd.defect_add <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocityFormula_le_semipositive : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.CycPair.side_le | exact GlobalTheory.CycPair.side_le | (intros; apply GlobalTheory.CycPair.side_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocityDefect_independent_firstMetric : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.MetricIndep.side_sub_side_addFn | exact GlobalTheory.MetricIndep.side_sub_side_addFn | (intros; apply GlobalTheory.MetricIndep.side_sub_side_addFn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithSelfIntersection_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  first | exact @GlobalTheory.HSNefMono.selfInter_mono_of_isNef | exact GlobalTheory.HSNefMono.selfInter_mono_of_isNef | (intros; apply GlobalTheory.HSNefMono.selfInter_mono_of_isNef <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem isometric_pull_id {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) :
    (L.pull (𝟙 X) (Category.id_comp p)).Isometric L := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  exact hiso.symm

theorem hasDim_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) : HasDim (genericPoint X) (D + 1) :=
  (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq

theorem hasDim_of_coheight_eq_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {z : X} (hz : Order.coheight z = 1) : HasDim z D := by
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  unfold HasDim
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  exact PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz

theorem lin_intCast {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun i => (n i : ℝ)) = ∑ i, n i • (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  simp only [lin, zsmul_eq_mul, map_intCast]

theorem arMix_of_mixHt : ArchInteg →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) →
    GlobalTheory.Published.ArMix := by
  intro hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  refine ⟨hAI k X p D hX M (comb L n) r hr, ?_⟩
  obtain ⟨T, hT⟩ := hEx k X p (isAmb_of_isArithVar hX) (D + 1)
  have hgen := hasDim_genericPoint hX
  set F' : Option ι → HermLB p := fun o => o.elim M L with hF'
  let F : (Fin (D + 1) → HermLB p) → ℝ := fun K => T (D + 1) K (genericPoint X)
  obtain ⟨Φ₀, hΦ₀, -⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK)
    (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'

  have hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) =
      Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1)) := by
    intro m
    obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT (comb F' m)
    have h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X)) :=
      ⟨g, hg, hg' _ _ hgen⟩
    have h₂ := hΦ₀ (fun _ => m)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
    rw [HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]
    exact h₂.symm
  have hpol := GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n
  rw [hpol]

  let m₀ : Option ι → ℤ := fun o => o.elim 1 0
  let m₁ : Option ι → ℤ := fun o => o.elim 0 n
  have hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none =
      ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast,
      Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]
    ring
  have hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D *
      MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X) := by
    rw [LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]
    refine hT.iso _ _ _ _ le_rfl hgen fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₀, F']
    · simp only [Fin.cons_succ]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₁, F']
  rw [hval]

  set N := comb L n
  have hrec := hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N)
    (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr
  have e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X := by simp
  rw [e₁] at hrec
  rw [hrec, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT N
  obtain rfl : h = g := hh.unique hX hg
  have e₂ : (𝟙 X : X ⟶ X) z = z := by simp
  rw [e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]

end GlobalTheory.MixHt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_indep_sec : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T,
    IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ)
    (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT N L r hr r' hr'
  haveI : IsNoetherian Y := hq.isNoetherian
  have step1 : ∀ (P : HermLB q) (t t' : P.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
      (ht' : genericPoint Y ∈ nonzeroLocus t'),
      recVal (T (e + 1) L) L P (isRatSec_ratOfSec t ht) = recVal (T (e + 1) L) L P (isRatSec_ratOfSec t' ht') := by
    intro P t t' ht ht'
    have hS := (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t) ⟨_, ht⟩).union
      (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t') ⟨_, ht'⟩)
    obtain ⟨A, s, u, hs, hu⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq (L 0) _ (hS.insert (genericPoint Y))
    have hgs : genericPoint Y ∈ nonzeroLocus s := hs (Set.mem_insert _ _)
    have hgu : genericPoint Y ∈ nonzeroLocus u := hu (Set.mem_insert _ _)
    have cs : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cs' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have cu : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cu' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have r1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t s ht hgs cs
    have r1' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t' s ht' hgs cs'
    have r2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t u ht hgu cu
    have r2' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t' u ht' hgu cu'
    have a1 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t ht) (L 0) A (Fin.tail L)
    have a1' := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t' ht') (L 0) A (Fin.tail L)
    rw [← Fin.cons_self_tail L]
    linarith
  obtain ⟨A, u, t, t', hu, ht, ht', hrel⟩ := GlobalTheory.T.exists_common_denominator_rational_sections k Y q hq N r r' hr hr'
  have v1 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r hr _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t ht) fun i j hi hj => (hrel i j hi hj).1
  have v2 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r' hr' _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t' ht') fun i j hi hj => (hrel i j hi hj).2
  have s1 := step1 (N.tens A) t t' ht ht'
  linarith

end GlobalTheory.MixHt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  first | exact @GlobalTheory.SiegOpen.level_openImmersion | exact GlobalTheory.SiegOpen.level_openImmersion | (intros; apply GlobalTheory.SiegOpen.level_openImmersion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaSetup_levelCover_every_point : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.Poinc.SetupCov.exists_setup_cov | exact GlobalTheory.Poinc.SetupCov.exists_setup_cov | (intros; apply GlobalTheory.Poinc.SetupCov.exists_setup_cov <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_linearUniformisation_pullback_localMap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  first | exact @GlobalTheory.LocalPull.exists_pelUnif_pull | exact GlobalTheory.LocalPull.exists_pelUnif_pull | (intros; apply GlobalTheory.LocalPull.exists_pelUnif_pull <;> assumption)
end
