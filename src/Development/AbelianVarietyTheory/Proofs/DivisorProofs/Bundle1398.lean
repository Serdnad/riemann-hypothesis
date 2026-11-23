module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory Matrix

namespace GlobalTheory.GLProj

theorem continuous_proj_incl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧
    Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  intro E _ _ _ a
  have hInf : Continuous (pInf E) :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
  have hFin : Continuous (pFin E) := continuous_snd
  refine ⟨Continuous.units_map _ (continuous_id.matrix_map hInf),
    Continuous.units_map _ (continuous_id.matrix_map hFin), continuous_infGL, ?_⟩
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (sFin E) 1 + x.map (sFin E))

end GlobalTheory.GLProj
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_closure_pair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  intro F _ Y K _ q₁ q₂ hq
  let ξ : Sp K ⟶ Limits.pullback Y.str Y.str := Limits.pullback.lift q₁ q₂ hq
  let x := ξ (IsLocalRing.closedPoint K)
  let i := GlobalTheory.MixHt.cloι x
  have hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str := by
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have hl : Limits.pullback.lift _ _ hw = i := by
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Limits.pullback.lift_snd _ _ _
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have hr : Set.range ξ ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩
  have hk : i.ker ≤ ξ.ker := ker_le_ker_of_range_subset_of_isReduced i ξ hr
  let ζ := IsClosedImmersion.lift i ξ hk
  have hζ : ζ ≫ i = ξ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩
  · rw [hl]; infer_instance
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_fst _ _ _
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_snd _ _ _
  · apply i.isClosedEmbedding.injective
    refine (Scheme.Hom.comp_apply ζ i _).symm.trans ?_
    rw [hζ, GlobalTheory.MixHt.cloι_genericPoint]

end GlobalTheory.FlagPush
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  first | exact @GlobalTheory.GoodTop.exists_cInf_partition | exact GlobalTheory.GoodTop.exists_cInf_partition | (intros; apply GlobalTheory.GoodTop.exists_cInf_partition <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  first | exact @GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | exact GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | (intros; apply GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_lift_valuative_criterion_varieties : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  first | exact @GlobalTheory.FlagPush.exists_lift_of_var | exact GlobalTheory.FlagPush.exists_lift_of_var | (intros; apply GlobalTheory.FlagPush.exists_lift_of_var <;> assumption)
end

section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

theorem _root_.GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  first | exact @GlobalTheory.TorsionKill.kill_torsion | exact GlobalTheory.TorsionKill.kill_torsion | (intros; apply GlobalTheory.TorsionKill.kill_torsion <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Grp
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem cont_coords : Continuous (coords : ℍ[R, a, b] → Fin 4 → R) := continuous_induced_dom
theorem cont_re : Continuous (fun x : ℍ[R, a, b] => x.re) := (continuous_apply 0).comp cont_coords
theorem cont_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) := (continuous_apply 1).comp cont_coords
theorem cont_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) := (continuous_apply 2).comp cont_coords
theorem cont_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) := (continuous_apply 3).comp cont_coords

theorem cont_of {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cont_mul : Continuous (fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2) := by
  have r1 := (cont_re (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i1 := (cont_imI (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j1 := (cont_imJ (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k1 := (cont_imK (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have r2 := (cont_re (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i2 := (cont_imI (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j2 := (cont_imJ (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k2 := (cont_imK (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  simp only [Function.comp_def] at r1 i1 j1 k1 r2 i2 j2 k2
  apply cont_of <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

theorem cont_star : Continuous (fun x : ℍ[R, a, b] => star x) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  apply cont_of <;> simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] <;> fun_prop

theorem cont_nrm : Continuous (nrm : ℍ[R, a, b] → R) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  unfold nrm
  fun_prop

theorem cont_conj (c d : ℍ[R, a, b]) : Continuous fun y : ℍ[R, a, b] => c * y * d := by
  have h1 : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := cont_mul
  have hl : Continuous fun y : ℍ[R, a, b] => c * y :=
    h1.comp (Continuous.prodMk (continuous_const : Continuous fun _ : ℍ[R, a, b] => c) continuous_id)
  exact h1.comp (Continuous.prodMk hl (continuous_const : Continuous fun _ : ℍ[R, a, b] => d))

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp
variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem supp {ε : AF F} (p q u : DA F a b) (hu : ε • u = u) : ε • (p * u * q) = p * u * q := by
  rw [← smul_mul_assoc, ← mul_smul_comm, hu]

theorem rat_inv {γ : ℍ[F, a, b]} (hγ : nrm γ = 1) :
    rat γ * rat (star γ) = 1 ∧ rat (star γ) * rat γ = 1 := by
  constructor
  · rw [← rat_mul, mul_star_eq, hγ, map_one, rat_one]
  · rw [← rat_mul, star_mul_eq, hγ, map_one, rat_one]

theorem nrm_of_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : nrm x = 1 := by
  obtain ⟨γ, hγ, h, hh, -, rfl⟩ := hx
  rw [nrm_mul, nrm_rat, hγ, hh, map_one, one_mul]

theorem mul_mem {ε : AF F} {x y : DA F a b} (hx : x ∈ H0 ε) (hy : y ∈ H0 ε) : x * y ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', hs', rfl⟩ := hy
  obtain ⟨e1, e2⟩ := rat_inv hγ'
  refine ⟨γ * γ', by rw [nrm_mul, hγ, hγ', one_mul], rat (star γ') * h * rat γ' * h', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_mul, hh, hh', nrm_rat, nrm_rat, nrm_star, hγ', map_one]; ring
  · have : rat (star γ') * h * rat γ' * h' - 1
        = rat (star γ') * (h - 1) * (rat γ' * h') + (h' - 1) := by
      rw [show rat (star γ') * (h - 1) * (rat γ' * h')
          = rat (star γ') * h * rat γ' * h' - rat (star γ') * rat γ' * h' by noncomm_ring, e2, one_mul]
      abel
    rw [this, smul_add, hs', supp _ _ _ hs]
  · rw [rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat γ') (rat (star γ')), e1, one_mul]

theorem star_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : star x ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨e1, e2⟩ := rat_inv hγ
  refine ⟨star γ, by rw [nrm_star, hγ], rat γ * star h * rat (star γ), ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_star, hh, nrm_rat, nrm_rat, nrm_star, hγ, map_one]; ring
  · have hs1 : ε • star (h - 1) = star (h - 1) := by
      rw [← QuaternionAlgebra.star_smul, hs]
    have : rat γ * star h * rat (star γ) - 1 = rat γ * star (h - 1) * rat (star γ) := by
      rw [star_sub, star_one, show rat γ * (star h - 1) * rat (star γ)
          = rat γ * star h * rat (star γ) - rat γ * rat (star γ) by noncomm_ring, e1]
    rw [this, supp _ _ _ hs1]
  · rw [star_mul, ← rat_star]
    simp only [← mul_assoc]
    rw [e2, one_mul]

theorem inv_right {δ δ' : ℍ[F, a, b]} (h : δ * δ' = 1) : δ' * δ = 1 := by
  have hn : nrm δ' * nrm δ = 1 := by rw [mul_comm, ← nrm_mul, h, nrm_one']
  have e : star δ * δ * δ' * δ = star δ * δ := by rw [mul_assoc (star δ), h, mul_one]
  rw [star_mul_eq] at e
  calc δ' * δ = algebraMap F ℍ[F, a, b] (nrm δ' * nrm δ) * (δ' * δ) := by rw [hn, map_one, one_mul]
    _ = algebraMap F ℍ[F, a, b] (nrm δ') * (algebraMap F ℍ[F, a, b] (nrm δ) * δ' * δ) := by
      rw [map_mul]; simp only [mul_assoc]
    _ = 1 := by rw [e, ← map_mul, hn, map_one]

theorem conj_mem {ε : AF F} {δ δ' : ℍ[F, a, b]} (hδ : δ * δ' = 1) {x : DA F a b} (hx : x ∈ H0 ε) :
    rat δ * x * rat δ' ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  have hδ2 := inv_right hδ
  have e1 : rat δ * rat δ' = 1 := by rw [← rat_mul, hδ, rat_one]
  have e2 : rat δ' * rat δ = 1 := by rw [← rat_mul, hδ2, rat_one]
  have hn : nrm δ * nrm δ' = 1 := by rw [← nrm_mul, hδ, nrm_one']
  refine ⟨δ * γ * δ', by rw [nrm_mul, nrm_mul, hγ, mul_one, hn], rat δ * h * rat δ', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hh, nrm_rat, nrm_rat, mul_one, ← map_mul, hn, map_one]
  · have : rat δ * h * rat δ' - 1 = rat δ * (h - 1) * rat δ' := by
      rw [show rat δ * (h - 1) * rat δ' = rat δ * h * rat δ' - rat δ * rat δ' by noncomm_ring, e1]
    rw [this, supp _ _ _ hs]
  · rw [rat_mul, rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat δ') (rat δ), e2, one_mul]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp

theorem t2Space_adeleRing_numberField (F : Type) [Field F] [NumberField F] : T2Space (AF F) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem closure_normOneProducts_subgroup_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε →
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε),
      x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε),
      rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  intro F _ _ a b ε _
  haveI := t2Space_adeleRing_numberField F
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun δ δ' hδ x hx => ?_, fun x hx => ?_⟩
  · exact map_mem_closure₂ cont_mul hx hy fun u hu v hv => mul_mem hu hv
  · exact map_mem_closure cont_star hx fun u hu => star_mem hu
  · have hc : Continuous fun y : DA F a b => rat δ * y * rat δ' := cont_conj (rat δ) (rat δ')
    have hm : Set.MapsTo (fun y : DA F a b => rat δ * y * rat δ') (H0 ε) (H0 ε) :=
      fun u hu => conj_mem hδ hu
    have key := map_mem_closure (x := x) hc hx hm
    exact key
  · have hcl : IsClosed {y : DA F a b | nrm y = 1} := isClosed_eq cont_nrm continuous_const
    exact closure_minimal (fun y hy => nrm_of_mem hy) hcl hx

end GlobalTheory.QSA.Grp
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F]

end GlobalTheory.QSA.Split

namespace GlobalTheory

theorem quaternion_split_of_isotropic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) →
    ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first
  | exact @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | (apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic ..)

end GlobalTheory
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.localNormResidueSign_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  first | exact @GlobalTheory.KSp.sgn_mul_of_isQuad | exact GlobalTheory.KSp.sgn_mul_of_isQuad | (intros; apply GlobalTheory.KSp.sgn_mul_of_isQuad <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  first | exact @GlobalTheory.PDivLat.iota_natural | exact GlobalTheory.PDivLat.iota_natural | (intros; apply GlobalTheory.PDivLat.iota_natural <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additive_picClass_of_locally_additive : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 → (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  first | exact @GlobalTheory.PicGlue.addCls_of_locally | exact GlobalTheory.PicGlue.addCls_of_locally | (intros; apply GlobalTheory.PicGlue.addCls_of_locally <;> assumption)
end
