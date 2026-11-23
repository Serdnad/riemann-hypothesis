module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle006
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle002
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsGrpObjIsAddLawHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory

theorem exists_grpObj_weierstrass : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ (η[schemeOver W].left = zero W ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) (hT : IsUnimodularSol (W.map ρ) T), (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧ Proportional T (diagXYZ (W.map ρ).toProjective P Q)) → ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP → y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P), ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN)) :=
  fun _ _ W h => by
    letI : W.IsElliptic := ⟨h⟩
    exact GlobalTheory.WeierstrassCurve.exists_grpObj_isAddLawHom W h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.exists_weierstrass_coordinates_on_line : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  first | exact @GlobalTheory.UnifCoord.exists_coord_on_line | exact GlobalTheory.UnifCoord.exists_coord_on_line | (intros; apply GlobalTheory.UnifCoord.exists_coord_on_line <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

theorem _root_.GlobalTheory.T.cmPoint_lower_bound_of_coefficient_bound : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.cmLowerBound_of_coeffBound | exact GlobalTheory.cmLowerBound_of_coeffBound | (intros; apply GlobalTheory.cmLowerBound_of_coeffBound <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem thetaLine_lower_bound_of_degree :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)) → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hD K _ _ x T abelian₂ ℓ U H La logOm V _ c G μ n S Rr hT hL hloc harch hℓ hdne hLa hH hn hlocU hsq hnd
    hcf hmem hS hRr hev
  have hdeg := hD K x T abelian₂ hT hL hloc harch
  have hHad := hadamard_local_base K x.P.g abelian₂ ℓ U H La hL.1 hℓ hdne (by linarith) hH hn hlocU hsq
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  have hd := finrank_pos_real K
  have hnd' : T.dual.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (x.P.g : ℝ) / 4 * Real.log (2 * Real.pi) := by
    apply le_of_eq
    simp only [MLine.ndeg]
    rw [hdeg]
    field_simp
  exact lambda_number_base K x.P.g abelian₂ ℓ T.dual La logOm V c G μ n S Rr ⟨hL, hℓ, hTd, hLa, hHad, hnd, hnd'⟩ hcf hmem hS
    hRr hev

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoFinite

theorem eq_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (g : ℕ) (hX : SmoothOfRelativeDimension g (f ≫ p))
    (hY : SmoothOfRelativeDimension g p) (x : X) (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f x) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ U) (x := x) hxU
  have hVU : V ≤ f ⁻¹ᵁ U := hVU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  let φ := f.appLE U V hVU
  have sq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ f := hU.SpecMap_appLE_fromSpec f hV hVU
  algebraize [α.hom, φ.hom, φ.hom.comp α.hom]
  have t₁ : Algebra.trdeg K Γ(Y, U) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K Y p g hY Γ(Y, U) hU.fromSpec inferInstance hα.symm
  have t₂ : Algebra.trdeg K Γ(X, V) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ p) g hX Γ(X, V) hV.fromSpec inferInstance (by
      rw [← Category.assoc, ← sq, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  obtain ⟨q, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have gU : hU.fromSpec (genericPoint (Spec Γ(Y, U))) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have gV : hV.fromSpec (genericPoint (Spec Γ(X, V))) = genericPoint X := genericPoint_eq_of_isOpenImmersion _
  have e : Spec.map φ q = genericPoint (Spec Γ(Y, U)) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [gU, ← hx, ← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
  rw [genericPoint_eq_bot_of_affine] at e
  have e' : q.asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) = ⊥ := congrArg PrimeSpectrum.asIdeal e
  have : FaithfulSMul Γ(Y, U) Γ(X, V) := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← e']
    exact Ideal.ker_le_comap _
  have : FaithfulSMul K Γ(Y, U) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact RingHom.injective _
  have h := trdeg_add_eq K Γ(Y, U) (A := Γ(X, V))
  rw [t₁, t₂] at h
  have h0 : Algebra.trdeg Γ(Y, U) Γ(X, V) = 0 :=
    Cardinal.eq_of_add_eq_add_left (h.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
  have halg : Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) := trdeg_eq_zero_iff.1 h0
  have hq : q.asIdeal = ⊥ := by
    by_contra hne
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact Ideal.comap_ne_bot_of_algebraic_mem ha0 ha (halg.isAlgebraic a) e'
  rw [← gV, genericPoint_eq_bot_of_affine]
  exact congrArg _ (PrimeSpectrum.ext hq)

theorem quasiFiniteAt_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] (g : ℕ)
    (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension g p) :
    f.QuasiFiniteAt (genericPoint X) := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  obtain rfl := eq_genericPoint p f g hX hY x hx
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : Subsingleton (f.fiber (f (genericPoint X))) := by
    refine (f.fiberHomeo _).toEquiv.subsingleton_congr.2 ⟨fun a b => Subtype.ext ?_⟩
    exact (eq_genericPoint p f g hX hY a.1 (a.2.trans hx)).trans
      (eq_genericPoint p f g hX hY b.1 (b.2.trans hx)).symm
  exact isOpen_discrete _

theorem isIso_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A).left := by
  have hu (t : A ⟶ A) : t ≫ toUnit A = toUnit A := toUnit_unique _ _
  suffices IsIso ((toUnit A ≫ x) * 𝟙 A) from inferInstanceAs (IsIso ((Over.forget S).map ((toUnit A ≫ x) * 𝟙 A)))
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hu, Category.comp_id, inv_mul_cancel_left,
      mul_inv_cancel_left]

theorem locallyQuasiFinite_of_quasiFiniteAt {K : Type} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B] [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [IsMonHom f] [LocallyOfFiniteType f.left] (x : A.left) (hx : f.left.QuasiFiniteAt x) :
    LocallyQuasiFinite f.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : A.left) (hy : IsClosed ({y} : Set A.left)) : ∃ u : 𝟙_ _ ⟶ A, u.left pt = y :=
    ⟨Over.homMk (pointOfClosedPoint (K := K) A.hom y hy) (pointOfClosedPoint_comp (K := K) A.hom y hy),
      pointOfClosedPoint_apply (K := K) A.hom y hy pt⟩
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)) ⟨x, hx⟩
    f.left.quasiFiniteLocus.isOpen.isLocallyClosed
  obtain ⟨u, rfl⟩ := hpt a hac
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra hne
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)ᶜ)
    (Set.nonempty_compl.2 fun h => hne (SetLike.coe_injective h))
    f.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨v, rfl⟩ := hpt b hbc
  have := isIso_transl (v * u⁻¹)
  have := isIso_transl ((v * u⁻¹) ≫ f)
  have e : ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) ≫ f = f ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul f, ← Category.assoc f, toUnit_unique (f ≫ toUnit B) (toUnit A)]
    simp only [Category.assoc, Category.id_comp, Category.comp_id]
  have e₂ : u ≫ ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) = v := by
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (𝟙 _)]
    simp
  apply hb
  have h₁ : (f.left ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B).left).QuasiFiniteAt (u.left pt) :=
    Scheme.Hom.quasiFiniteAt_comp_iff.2 ha
  rw [← Over.comp_left, ← e, Over.comp_left, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, e₂] at h₁
  exact h₁

theorem isFinite_of_surjective {K : Type} [Field K] {A B : Over (Sp K)} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g : ℕ} (dA : SmoothOfRelativeDimension g A.hom)
    (dB : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [Surjective f.left] : IsFinite f.left := by
  have := hA.proper
  have := hB.proper
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := .of_comp _ B.hom
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  have gA := isGrpPullback_pullback A t
  have gB := isGrpPullback_pullback B t
  have geomIntegralPullback (C : Over (Sp K)) [GrpObj C] (hC : IsAbelianScheme C) :
      GeometricallyIntegral ((Over.pullback t).obj C).hom := by
    have sqC := (isGrpPullback_pullback C t).1
    exact forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _
      (MorphismProperty.of_isPullback (P := @Smooth) sqC hC.smooth)
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqC hC.geomConnected)
  let f' := (Over.pullback t).map f
  have sq : IsPullback (pullback.fst A.hom t) f'.left f.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm gB.1
    rw [Over.w, Over.w]
    exact gA.1
  have : Surjective f'.left := MorphismProperty.of_isPullback (P := @Surjective) sq ‹_›
  have : IsProper f'.left := MorphismProperty.of_isPullback (P := @IsProper) sq ‹_›
  have : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Surjective (pullback.fst B.hom t) := inferInstance
  have iA := geomIntegralPullback A hA
  have iB := geomIntegralPullback B hB
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj B).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj B).hom
  have : IsProper ((Over.pullback t).obj A).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) gA.1 hA.proper
  have hq := quasiFiniteAt_genericPoint ((Over.pullback t).obj B).hom f'.left g
    (by rw [Over.w]; exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gA.1 dA)
    ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gB.1 dB)
  have : LocallyQuasiFinite f.left := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ sq ‹_›
    inferInstance inferInstance (locallyQuasiFinite_of_quasiFiniteAt f' _ hq)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.OntoFinite
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TorsionField

theorem exists_field_alg (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] : ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (φ : B →ₐ[k] ℂ) (b : B), φ b ∈ k₁ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := B)
  let S : Set ℂ := ⋃ b ∈ s, (minpoly k b).rootSet ℂ
  have hS : S.Finite := s.finite_toSet.biUnion fun b _ => Polynomial.rootSet_finite _ _
  have hint : ∀ b : B, _root_.IsIntegral k b := fun b => Algebra.IsIntegral.isIntegral b
  have hI : ∀ x ∈ S, _root_.IsIntegral k x := fun x hx => by
    simp only [S, Set.mem_iUnion] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨minpoly k b, minpoly.monic (hint b), (Polynomial.mem_rootSet.1 hb).2⟩
  have : Finite S := hS
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin hI
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', fun x hx => ?_, fun φ b => ?_⟩
  · exact (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  · change φ b ∈ IntermediateField.adjoin k S
    have hb : b ∈ Submodule.span k (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [S, Set.mem_iUnion]
      refine ⟨b, hb, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero (hint b), ?_⟩⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact IntermediateField.smul_mem _ ha

theorem exists_field_finite (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (Z : Over (Sp k)) [IsFinite Z.hom] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ y : Over.mk (spMap (algebraMap k ℂ)) ⟶ Z,
        ∃ y₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ Z,
          spMap (algebraMap k₂ ℂ) ≫ y₂.left = y.left := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of k ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k Γ(Z.left, ⊤) := h₁
  obtain ⟨k₁, hfd, hk, H⟩ := exists_field_alg k Γ(Z.left, ⊤)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ y => ?_⟩
  let y' : Sp ℂ ⟶ Z.left := y.left
  have hy : y' ≫ Z.hom = spMap (algebraMap k ℂ) := Over.w y
  let ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (y' ≫ Z.left.isoSpec.hom)
  have hψ : Spec.map ψ = y' ≫ Z.left.isoSpec.hom := Spec.map_preimage _
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap k ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  have hc' : ∀ c : k, ψ.hom (φ.hom c) = (c : ℂ) := fun c => congrArg (fun f => f.hom c) hc
  let ψa : Γ(Z.left, ⊤) →ₐ[k] ℂ := { ψ.hom with commutes' := hc' }
  let ψ₂ : Γ(Z.left, ⊤) →+* k₂ := ψ.hom.codRestrict k₂ fun b => h₁₂ (H ψa b)
  refine ⟨Over.homMk (spMap ψ₂ ≫ Z.left.isoSpec.inv) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h₂).toRingHom)
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact hc' c
  · change Spec.map (CommRingCat.ofHom (algebraMap k₂ ℂ)) ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv = y'
    rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hψ]
    rfl

end GlobalTheory.TorsionField

namespace GlobalTheory

theorem exists_numberField_torsion_points : Out.Laws → ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P : Out.PolAV (Sp k)) (n : ℕ), 0 < n → ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ x : Over.mk (spMap (algebraMap k ℂ)) ⟶ P.A, x ^ n = 1 → ∃! x₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ P.A, spMap (algebraMap k₂ ℂ) ≫ x₂.left = x.left := by
  intro _ k _ P n hn
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    have h : IsUnit (n : k) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  obtain ⟨k₁, hfd, hk, H⟩ := TorsionField.exists_field_finite k (torsion P.A n)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion P.A n x hx
  obtain ⟨y₂, hy₂⟩ := H k₂ h₂ h₁₂ y
  have : Flat (spMap (algebraMap k₂ ℂ)) := inferInstance
  have : Surjective (spMap (algebraMap k₂ ℂ)) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (spMap (algebraMap k₂ ℂ)) := Flat.epi_of_flat_of_surjective _
  refine existsUnique_of_exists_of_unique ⟨y₂ ≫ torsion.ι P.A n, ?_⟩ fun a b ha hb => ?_
  · rw [← hy, Over.comp_left, Over.comp_left, ← hy₂]
    exact (Category.assoc _ _ _).symm
  · exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap k₂ ℂ))).1 (ha.trans hb.symm))

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff_comp (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x = Chart.spMap (Chart.scaleD a) ≫ v := by
  rw [Chart.isLieComb_iff]
  simp [Chart.prodPts]

theorem isLieComb_one_iff (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left := by
  rw [isLieComb_one_iff_comp]
  exact ⟨fun h => by rw [h]; rfl, fun h => Over.OverMorphism.ext h⟩

theorem scale_add {v : epsR R ⟶ G} (hv : IsTangent v) (a b : R) :
    Chart.spMap (Chart.scaleD (a + b)) ≫ v =
      (Chart.spMap (Chart.scaleD a) ≫ v) * (Chart.spMap (Chart.scaleD b) ≫ v) := by
  rw [SqZero.scaleD_eq, SqZero.scaleD_eq, SqZero.scaleD_eq,
    ← SqZero.epsTo_add_comp ((Chart.isTan_iff _).2 hv) _ _ _ _ (TrivSqZeroExt.inr_mul_inr _ _ _)
      (by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  congr 3
  exact TrivSqZeroExt.inr_add _ _ _

theorem scaleD_comp (a b : R) : (Chart.scaleD a).comp (Chart.scaleD b) = Chart.scaleD (a * b) := by
  rw [SqZero.scaleD_eq a, SqZero.epsTo_comp_scaleD, SqZero.scaleD_eq]
  congr 1
  rw [← TrivSqZeroExt.inr_smul, smul_eq_mul, _root_.mul_comm]

theorem scaleD_one : Chart.scaleD (1 : R) = AlgHom.id R _ :=
  DualNumber.algHom_ext (by rw [SqZero.scaleD_eq, SqZero.epsTo_eps]; rfl)

theorem lieMultiple_calculus : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (v x y : epsR R ⟶ G) (a b : R), (IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left) ∧ (IsTangent v → IsLieComb ![a] ![v] x → IsLieComb ![b] ![v] y → IsLieComb ![a + b] ![v] (x * y)) ∧ (IsLieComb ![b] ![v] x → IsLieComb ![a] ![x] y → IsLieComb ![a * b] ![v] y) ∧ (∀ f : G ⟶ G', IsLieComb ![a] ![v] x → IsLieComb ![a] ![v ≫ f] (x ≫ f)) ∧ IsLieComb ![1] ![v] v ∧ (IsTangent v → IsLieComb ![0] ![v] 1) := by
  intro R _ G G' _ _ v x y a b
  refine ⟨isLieComb_one_iff a v x, fun hv hx hy => ?_, fun hx hy => ?_, fun f hx => ?_, ?_, fun hv => ?_⟩
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hx, hy]
    exact (scale_add hv a b).symm
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hy, hx, ← scaleD_comp, ← Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm
  · rw [isLieComb_one_iff_comp] at hx ⊢
    rw [hx]
    exact Category.assoc _ _ _
  · rw [isLieComb_one_iff_comp, scaleD_one, Chart.spMap_id]
    exact (Category.id_comp _).symm
  · rw [isLieComb_one_iff_comp, SqZero.scaleD_eq]
    exact (SqZero.epsTo_zero_comp ((Chart.isTan_iff _).2 hv) _ (TrivSqZeroExt.inr_zero _) _).symm

end GlobalTheory.LieMultiple
end
end
