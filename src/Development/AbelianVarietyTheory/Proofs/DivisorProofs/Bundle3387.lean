module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlue.homFix_finiteType) | (exact GlobalTheory.HomFixGlue.homFix_finiteType) | (intros; apply GlobalTheory.HomFixGlue.homFix_finiteType  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual

namespace GlobalTheory.HTLiftIso

theorem liftFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _ φ hφ x hx y hy
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl o.ab hg o.ab hg m.cart m.cart
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have CD := cupSquare_of_free ADR.1 hAB (smooth_prod hg hg)
  obtain ⟨φd, hφd⟩ := exists_isCorrForm CD o.isLB o.rig₁ o.rig₂
  obtain ⟨φ₀, hφ₀, e₀⟩ := GlobalTheory.Published.AbelianDualCrystal.exists_crystal_pairing κ m.cart m.cart m.sq.1 m.sq.2
    o.isLB o₀.isLB (LBIso.symm m.pol) hφd
  obtain rfl := hφ.unique CS o₀.isLB hφ₀
  rw [e₀]
  obtain ⟨ψ, hψ, eψ⟩ := hφd.isPolForm
  have iso := (ADR.2.2.2.2 C _ _ hAB (smooth_prod hg hg) o.P o.isLB ψ hψ).1
  have hx' : crysToDR κ m.cart x ∈ Fil o.A := hx
  have hy' : crysToDR κ m.cart y ∈ Fil o.A := hy
  have h := iso _ (push_mem_Fil (inl o.A o.A) hx') _ (push_mem_Fil (inr o.A o.A) hy')
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _)] at h
  simpa [push_id, push_one] using h

end GlobalTheory.HTLiftIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GaloisPackageDescent

theorem exists_cp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hinv
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.uniformisation_lineBundle_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  obtain ⟨rig, hrig⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local (V := R) (L.pull (eSec G))
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
  obtain ⟨c⟩ := GlobalTheory.T.exists_cubicalStructure_descendedLineBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  have hsym := GlobalTheory.T.isSymmetric_of_galoisPullback_uniformisationBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  obtain ⟨A, gen, κ, hgen, -, -⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨hLaws, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hLaws R A G hS gen hgen ⟨L, rig, hL, hrig⟩ c hsym
  refine ⟨P, ?_⟩
  rw [hP]
  exact hLi

end GlobalTheory.GaloisPackageDescent
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithHilbertSamuel_nef_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  first | exact @GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | exact GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | (intros; apply GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem archRecip_of_principalisation (hP : GlobalTheory.Published.Principalisation) : ArchRecip := by
  intro k _ Y _ _ q e hq M N L s t hs ht hcov
  have : IsNoetherian Y := hq.isNoetherian
  have : Finite (k →+* ℂ) := hq.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hcons (A : HermLB q) (σ : k →+* ℂ) :
      (fun i => MLine.ofHerm ((Fin.cons A L : Fin (e + 1) → HermLB q) i) σ) =
        Fin.cons (MLine.ofHerm A σ) (fun i => MLine.ofHerm (L i) σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, ((divOfSec A.isLB a ha).mult z : ℝ) *
          cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm B σ).logSec b) z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals hP k Y q e hq L B b z hz ((hab z hz).resolve_left hza), finsum_eq_sum_of_fintype,
        Finset.mul_sum]
  have fin (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
    D.finite_support_mult.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      simp [h] at hz
  have hside (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) :
      mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) A (isRatSec_ratOfSec a ha) +
          ∑ᶠ z, ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, side (MLine.ofHerm B σ) (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm A σ).logSec a)
          ((MLine.ofHerm B σ).logSec b) (divOfSec (MLine.ofHerm A σ).φ.isLB a ha) := by
    rw [GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k Y q (e + 1) hq, finsum_eq_sum_of_fintype, finsum_congr (key A B a b ha hab),
      finsum_sum_comm _ _ (fun σ _ => fin _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [side, ← hcons]
    rfl
  rw [hside M N s t hs hcov, hside N M t s ht fun z hz => (hcov z hz).symm]
  exact Finset.sum_congr rfl fun σ _ => GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding hP k Y q e hq σ (fun i => MLine.ofHerm (L i) σ)
    (MLine.ofHerm M σ) (MLine.ofHerm N σ) s hs t ht hcov

end GlobalTheory.MixHt
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_keyDatum_abelianLocus_point : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  first | exact @GlobalTheory.KeyDatumAb.exists_keyOn | exact GlobalTheory.KeyDatumAb.exists_keyOn | (intros; apply GlobalTheory.KeyDatumAb.exists_keyOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  first | exact @GlobalTheory.Poinc.LamBound.main | exact GlobalTheory.Poinc.LamBound.main | (intros; apply GlobalTheory.Poinc.LamBound.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_emb_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C
  obtain ⟨R₁, i₁, i₂, i₃, ρ, D₁, C₁, hρ, hD, hS⟩ := GlobalTheory.T.exists_sections_prescribed_reduction_finite_ext R hR D C
  have := hR.2
  have h₁ : Base R₁ := ⟨hρ.1, (RingHom.charZero_iff hρ.2.1).1 this⟩
  obtain ⟨C', E, hE⟩ := GlobalTheory.T.exists_closedFibre_theta_embedding_of_sections R₁ h₁ D₁ C₁ hS
  exact ⟨R₁, i₁, i₂, i₃, ρ, D₁, C', E, hρ, hD, hE⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.samePolarisedData_uniformise_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.samePol_unif_finExt | exact GlobalTheory.Mum.samePol_unif_finExt | (intros; apply GlobalTheory.Mum.samePol_unif_finExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ α₀ : D.toPre.X, ∃ mu : D.toPre.X, CongMod S.N mu α₀ ∧ (∀ α, CongMod S.N α α₀ → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧ ∃ (e : Ω) (a : M.Z.presheaf.stalk x), e ≠ 0 ∧ (∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e = S.FF T₀ c' κ / S.th x₀) ∧ M.stalkHom x a = e ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j a) r := by
  first | exact @GlobalTheory.QUnit.main | exact GlobalTheory.QUnit.main | (intros; apply GlobalTheory.QUnit.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | exact GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field <;> assumption)
end
