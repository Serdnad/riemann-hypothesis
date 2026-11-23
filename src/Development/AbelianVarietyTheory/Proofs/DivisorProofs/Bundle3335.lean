module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle697
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.canonical_ideal_weight_section : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @GlobalTheory.LogCanon.logCanon_iff | exact GlobalTheory.LogCanon.logCanon_iff | (intros; apply GlobalTheory.LogCanon.logCanon_iff <;> assumption)
end

section

namespace GlobalTheory.ChernDegree

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := fun Y Δ L r hr φ hφ =>
  ⟨(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).1, by
    rw [GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle Y L φ hφ, GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented Y Δ L r φ.isLB hr]⟩

end GlobalTheory.ChernDegree
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [GlobalTheory.T.pullback_real_polynomial_even_form_fields _ _ _ _ _ _ _ _ _ _ (GlobalTheory.T.chernForms_pullback_metric_flag_refinement F σ X Y ι m E E' φ f hf hR H hH) R,
      GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag F σ Y ι m E' _ hM, e]
    exact GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t ⊤ U v D Θ := by
  first | exact @GlobalTheory.KSExists.exists_isKS | exact GlobalTheory.KSExists.exists_isKS | (intros; apply GlobalTheory.KSExists.exists_isKS <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixMat

theorem exists_locClosed_homFix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM hrA hrB hamp hk hva hbasA hbasB
  obtain ⟨eA, heA⟩ := hrA
  obtain ⟨eB, heB⟩ := hrB
  obtain ⟨mA, bA, hbA⟩ := hbasA
  obtain ⟨mB, bB, hbB⟩ := hbasB
  have hyp : Hyps L M k bA bB eA eB := ⟨hA, hB, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩

  obtain ⟨X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest, hex, hmat⟩ :=
    GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme Rg A B L M k mA mB bA bB eA eB hyp
  refine ⟨mA * mB, X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest.1, htest.2.1, htest.2.2.1,
    htest.2.2.2, ?_⟩
  intro R _ t A' B' _ _ φA' φB' Φ' h1 h2 h3 h4
  have ht : IsTest A B L M t A' B' φA' φB' Φ' := ⟨h1, h2, h3, h4⟩

  obtain ⟨c, hc'⟩ := GlobalTheory.T.line_bundle_sections_product_base_change Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' ht
  obtain ⟨h, hh, hmatc⟩ := hex R t A' B' φA' φB' Φ' c ht hc'

  obtain ⟨A₂, g₂, B₂, g₂', φA₂, φB₂, Φ₂, ht₂, hp₂⟩ :=
    GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest Rg A B L M H (Sp R) (i ≫ cE ≫ affπ Rg (mA * mB)) h AH BH φA φB Φ htest
  have hm₂ := hmat R h A₂ B₂ φA₂ φB₂ Φ₂ ht₂ hp₂
  rw [hh, hmatc] at hm₂
  rw [hh] at ht₂

  have hpd := GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data Rg A B L M k mA mB bA bB eA eB hyp R t A₂ B₂ φA₂ φB₂ Φ₂ A' B' φA' φB' Φ' c
    ht₂ ht hm₂ hc'
  have hfin := IsPullD.comp hp₂ hpd
  rw [Category.id_comp] at hfin
  refine ⟨h, ⟨hh, hfin⟩, ?_⟩

  rintro h' ⟨hh', hpd'⟩
  have ht' : IsTest A B L M (h' ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' := by
    rw [hh']; exact ht
  have hm' := hmat R h' A' B' φA' φB' Φ' ht' hpd'
  rw [hh'] at hm'
  have heq : matOf (h' ≫ i ≫ cE) = c :=
    GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' _ _ ht hm' hc'
  have hg : h' ≫ i ≫ cE = h ≫ i ≫ cE := by
    apply hom_ext_affine
    · simp only [Category.assoc]
      rw [hh', hh]
    · intro n
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective n
      exact congrFun (congrFun (heq.trans hmatc.symm) p.1) p.2
  have hg' : h' ≫ i = h ≫ i := by
    rw [← cancel_mono cE]
    simpa only [Category.assoc] using hg
  exact (cancel_mono i).1 hg'

end GlobalTheory.HomFixMat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FormalFunctions

theorem exists_of_thick : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  intro A _ _ I hI X hX f hf

  let Z : Over (Sp A) := Over.mk (𝔸(Unit; Sp A) ↘ Sp A)
  have hZs : IsSeparated Z.hom := by dsimp [Z]; infer_instance
  have hZl : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  have hZq : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let F : ∀ e, (thickObj A I e X).left ⟶ Z.left := fun e =>
    AffineSpace.homOfVector (pullback.fst X.hom (thick A I e) ≫ X.hom) (fun _ => f e)
  have hβ : ∀ e, thickMap A I e X ≫ pullback.fst X.hom (thick A I (e + 1)) =
      pullback.fst X.hom (thick A I e) := by
    intro e
    unfold thickMap
    first
      | (simp only [pullback.map, pullback.lift_fst, Category.comp_id]; done)
      | exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      | simp [pullback.map]
  have hF₁ : ∀ e, F e ≫ Z.hom = (thickObj A I e X).hom ≫ thick A I e := by
    intro e
    dsimp [F, Z]
    rw [AffineSpace.homOfVector_over]
    exact pullback.condition
  have hF₂ : ∀ e, thickMap A I e X ≫ F (e + 1) = F e := by
    intro e
    dsimp [F]
    rw [AffineSpace.comp_homOfVector, ← Category.assoc, hβ e]
    congr 1
    funext _
    exact hf e
  obtain ⟨g, hg, -⟩ := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms A I hI X Z hX hZs hZl hZq
    (fun e => thickObj A I e X) (fun e => thickMap A I e X) (fun e => pullback.fst X.hom (thick A I e))
    (fun e => IsPullback.of_hasPullback _ _) hβ F hF₁ hF₂
  refine ⟨g.left.appTop (AffineSpace.coord (Sp A) ()), fun e => ?_⟩
  have h := congrArg (fun φ => φ.appTop (AffineSpace.coord (Sp A) ())) (hg e)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [h]
  exact AffineSpace.homOfVector_appTop_coord _ _ _

end GlobalTheory.FormalFunctions
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AlgConn

namespace GlobalTheory.ZariskiConn

theorem preconnectedSpace_of_isLocalRing (Y : Scheme.{0}) [IsLocalRing Γ(Y, ⊤)] : PreconnectedSpace Y := by
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen Y U hU
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ε with h | h
  · right
    rw [← hεU, Y.basicOpen_of_isUnit h]
    rfl
  · left
    have h0 : ε = 0 := by
      have h1 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, he, sub_self]
      exact (h.mul_right_eq_zero).1 h1
    rw [← hεU, h0, Scheme.basicOpen_zero]
    rfl

theorem range_thick (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (thick O (maximalIdeal O) n) = {closedPoint O} := by
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have key : ∀ Q : PrimeSpectrum (O ⧸ maximalIdeal O ^ (n + 1)),
      thick O (maximalIdeal O) n Q = closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal O
    have hp : (Q.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal O ^ (n + 1)))).IsPrime := inferInstance
    refine le_antisymm (le_maximalIdeal hp.ne_top) (hp.le_of_pow_le (n := n + 1) fun a ha => ?_)
    change Ideal.Quotient.mk _ a ∈ Q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.asIdeal.zero_mem
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ maximalIdeal O ^ (n + 1))
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem isPreconnected_closedFibre (O : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hI : IsAdicComplete (maximalIdeal O) O) (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [hP : IsProper f]
    [PreconnectedSpace Y] : _root_.IsPreconnected (f ⁻¹' {closedPoint O}) := by
  let ι : ∀ n, pullback f (thick O (maximalIdeal O) n) ⟶ Y := fun n => pullback.fst _ _
  have hTn : ∀ n, Set.range (ι n) = f ⁻¹' {closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (thick O (maximalIdeal O) n)
    rw [range_thick] at h
    exact h
  refine isPreconnected_closed_iff.2 fun A B hA hB hcov ⟨u, hu, huA⟩ ⟨u', hu', hu'B⟩ => ?_
  by_contra hcon
  have hdis : ∀ y, y ∈ f ⁻¹' {closedPoint O} → y ∈ A → y ∈ B → False :=
    fun y h1 h2 h3 => hcon ⟨y, h1, h2, h3⟩
  have hAB : ∀ n, (ι n ⁻¹' A)ᶜ = ι n ⁻¹' B := by
    intro n
    ext x
    have hx : ι n x ∈ f ⁻¹' {closedPoint O} := by rw [← hTn n]; exact ⟨x, rfl⟩
    exact ⟨fun h => (hcov hx).resolve_left h, fun h h' => hdis _ hx h' h⟩
  have hclo : ∀ n, IsClopen (ι n ⁻¹' A) := fun n =>
    ⟨hA.preimage (ι n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (ι n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen O _
    (ι n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have htr : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ ι (n + 1) = ι n := fun n =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hc : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen O _ _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ≫ ·) (hhp (n + 1))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ f) (htr n)).trans (hhp n).symm
    · refine TopologicalSpace.Opens.ext ?_
      refine Eq.trans ?_ (hhU n).symm
      refine Eq.trans (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ⁻¹' ·) (hhU (n + 1))) ?_
      rw [← htr n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
    GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : ι 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      ι 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  rw [← hTn 0] at hu hu'
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨x', rfl⟩ := hu'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ ι 0 ⁻¹' A := huA
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ ι 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    exact hdis _ (by rw [← hTn 0]; exact ⟨x', rfl⟩) hxA hu'B

theorem exists_complete_flat (X : Scheme.{0}) [IsAffine X] [IsLocallyNoetherian X] (x : X) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsNoetherianRing O) (_ : IsLocalRing O),
      IsAdicComplete (maximalIdeal O) O ∧ ∃ g : Spec (.of O) ⟶ X, Flat g ∧ g (closedPoint O) = x := by
  let B : Type := X.presheaf.stalk x
  let O : Type := AdicCompletion (maximalIdeal B) B
  haveI : IsNoetherianRing O := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B _
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of O := CommRingCat.ofHom (algebraMap B O)
  haveI : IsLocalHom φ.hom := inferInstanceAs (IsLocalHom (algebraMap B O))
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _)
  haveI : Flat (X.fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X x
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map φ ≫ X.fromSpecStalk x, inferInstance, ?_⟩
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans Scheme.fromSpecStalk_closedPoint

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X]
    [IsLocallyNoetherian X], Function.Bijective f.appTop →
    ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  intro X Y f _ _ _ hf x
  obtain ⟨O, _, _, _, hO, g, hg, hx⟩ := exists_complete_flat X x
  haveI : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hf
  have H := IsPullback.of_hasPullback f g
  haveI : IsIso (pullback.snd f g).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsLocalRing Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (.of O)).symm ≪≫ asIso (pullback.snd f g).appTop).commRingCatIsoToRingEquiv.isLocalRing
  haveI := preconnectedSpace_of_isLocalRing (pullback f g)
  have hc := isPreconnected_closedFibre O hO _ (pullback.snd f g)
  have hw : ∀ y, f (pullback.fst f g y) = g (pullback.snd f g y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : pullback.fst f g '' (pullback.snd f g ⁻¹' {closedPoint O}) = f.base ⁻¹' {x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : pullback.snd f g y = closedPoint O := hy
      change f (pullback.fst f g y) = x
      rw [hw, hy', hx]
    · intro hz
      have h1 : f z = g (closedPoint O) := (show f z = x from hz).trans hx.symm
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      exact ⟨y, hy2, hy1⟩
  rw [← hR]
  exact hc.image _ (pullback.fst f g).continuous.continuousOn

end GlobalTheory.ZariskiConn
end
end
