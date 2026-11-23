module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

theorem _root_.GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (A B : PAT H (Sp ℂ)) (p q : ℕ), p + q = 1 → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) := by
  first | exact @GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure | exact GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure | (intros; apply GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem _root_.GlobalTheory.T.height_birationalImage_eq_tuple_height : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), IsTotallyComplex F → T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → T.IsHeight (CompHt.imageHeight Nm W ev T.D) := by
  first | exact @GlobalTheory.HSCore.isHeight_imageHeight | exact GlobalTheory.HSCore.isHeight_imageHeight | (intros; apply GlobalTheory.HSCore.isHeight_imageHeight <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.ImageDegree

theorem imageDeg_eq_del : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → (CompHt.imageDeg ev T.D : ℤ) = T.del := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hG hB hP
  obtain ⟨-, hdeg, hdim⟩ := GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt hQ F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F T.N T.D T.imageIdeal T.toLinSys.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hG.alg.variety) hdim
  rw [hP.imageDeg_eq hf]
  exact hdeg

end GlobalTheory.HSCore.ImageDegree
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.LogPair TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem smooth_quotient_of_isEtCoord (Y : Scheme.{0}) (q : Y ⟶ Sp ℂ) (n : ℕ) (U : Y.Opens) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n))
    (hE : IsEtCoord q U z) :
    ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  let A := MvPolynomial (Fin n) ℂ
  let B := Γ(Y, U)
  let φ : A →+* B := MvPolynomial.eval₂Hom (cstOn q U) z
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.Etale A B := RingHom.etale_algebraMap.1 hE
  let I : Ideal A := Ideal.span (MvPolynomial.X '' (J : Set (Fin n)))
  have hI : I.map (algebraMap A B) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [Ideal.map_span, Set.image_image]
    congr 1
    ext x
    simp only [RingHom.algebraMap_toAlgebra, φ, Set.mem_image, Finset.mem_coe]
    constructor <;> rintro ⟨j, hj, rfl⟩ <;> exact ⟨j, hj, by rw [MvPolynomial.eval₂Hom_X']⟩
  have h1 : (algebraMap ℂ (A ⧸ I)).Smooth := by
    rw [RingHom.smooth_algebraMap]
    haveI : Algebra.Smooth ℂ (MvPolynomial {x // x ∉ (J : Set (Fin n))} ℂ) := ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv (quotientSpanXEquiv ℂ (J : Set (Fin n))).symm
  have h2 : (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).Smooth := by
    rw [RingHom.smooth_algebraMap]; infer_instance
  let e : ((A ⧸ I) ⊗[A] B) ≃+* B ⧸ Ideal.span (z '' (J : Set (Fin n))) :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have h12 : ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I))).Smooth :=
    RingHom.Smooth.comp h1 h2
  have h3 : (e.toRingHom.comp ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I)))).Smooth :=
    have he : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
    RingHom.Smooth.comp h12 he
  convert h3 using 1
  ext c
  simp only [RingHom.comp_apply]
  have k1 : algebraMap ℂ (A ⧸ I) c = Ideal.Quotient.mk I (MvPolynomial.C c) := rfl
  have k2 : algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I (MvPolynomial.C c)) =
      (1 : A ⧸ I) ⊗ₜ[A] (algX q U c) := by
    have hm : Ideal.Quotient.mk I (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hm,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    congr 1
    simp [RingHom.algebraMap_toAlgebra, φ]
    rfl
  have k3 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm (algX q U c ⊗ₜ[A] (1 : A ⧸ I)) =
      Ideal.Quotient.mk _ (algX q U c) := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [k1, k2]
  simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul, k3,
    Ideal.quotEquivOfEq_mk]

theorem smooth_coordStratum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  intro Y _ _ q n _ U z hF J
  exact smooth_quotient_of_isEtCoord Y q n U z J (GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame ℂ Y q n U z hF).2

end GlobalTheory.PairStep
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens), ∃ (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)) (ω : Fin g → Ω[Sec (str A) U.1⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) ∧ (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) ∧ (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) ∧ (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) ∧ ∀ a ξ, ∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ (Pi.single a 1) = val u.ex U.1 ((d a).liftKaehlerDifferential ξ) z := by
  first | exact @GlobalTheory.CechPer.kaehler_frame | exact GlobalTheory.CechPer.kaehler_frame | (intros; apply GlobalTheory.CechPer.kaehler_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  first | exact @GlobalTheory.biIso_of_weil | exact GlobalTheory.biIso_of_weil | (intros; apply GlobalTheory.biIso_of_weil <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.diag_form_two_smul_and_ker_alt : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.SymBirig.diag_form_two_smul_and_ker | exact GlobalTheory.SymBirig.diag_form_two_smul_and_ker | (intros; apply GlobalTheory.SymBirig.diag_form_two_smul_and_ker <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' K L σ A _ _ _ hpb
  have hB := @GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @GlobalTheory.T.structure_h1_rank_descends_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @GlobalTheory.T.primitive_axes_descend_field K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @GlobalTheory.T.wedge_property_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS (E := E) (a := a) S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS (E := E) (a := a) S)
    (hy : y ∈ supS (E := E) (a := a) S) : x * y ∈ supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_field_unit_mem_open_archimedean_units E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS (E := E) (a := (m + 1)) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.same_lam_iff_locally_triv | exact GlobalTheory.TwistFlat.same_lam_iff_locally_triv | (intros; apply GlobalTheory.TwistFlat.same_lam_iff_locally_triv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) := by
  first | exact @GlobalTheory.CoreFive.shift_phase_conj | exact GlobalTheory.CoreFive.shift_phase_conj | (intros; apply GlobalTheory.CoreFive.shift_phase_conj <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  first | exact @GlobalTheory.GenRepD.genRepD | exact GlobalTheory.GenRepD.genRepD | (intros; apply GlobalTheory.GenRepD.genRepD <;> assumption)
end
