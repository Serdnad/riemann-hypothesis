module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle025
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
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
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
open scoped LaurentSeries in
theorem _root_.GlobalTheory.ArcQ.pairE_properties : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X), (∀ (a : 𝓞 E) x, _root_.GlobalTheory.ArcQ.pairE ξ (a • x) = (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x) ∧ (∀ x y, _root_.GlobalTheory.ArcQ.pairE ξ (x + y) = _root_.GlobalTheory.ArcQ.pairE (E := E) ξ x + _root_.GlobalTheory.ArcQ.pairE ξ y) ∧ (∀ x, Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x) = ξ x) ∧ (∀ x, IsIntegral ℤ ((NumberField.discr E : E) * _root_.GlobalTheory.ArcQ.pairE ξ x)) ∧ ∀ (K : Type) [Field K] (τK : E →+* K) x, _root_.GlobalTheory.ArcQ.xiVal τK ξ x = τK (_root_.GlobalTheory.ArcQ.pairE ξ x) := by
  intro E _ _ X _ _ ξ
  classical
  set b := RingOfIntegers.basis E with hbdef
  have hB := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hB (integralBasis E) with hd
  have hP : ∀ x, _root_.GlobalTheory.ArcQ.pairE ξ x = ∑ i, d i * (ξ (b i • x) : E) := fun x => rfl
  have hexp : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = ∑ k, (b.repr y k : E) * integralBasis E k := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp [integralBasis_apply, zsmul_eq_mul, b]
  have hdual : ∀ i k, Algebra.trace ℚ E (d i * integralBasis E k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left hB _ i k
  have hL : ∀ (y : 𝓞 E) i, Algebra.trace ℚ E (d i * algebraMap (𝓞 E) E y) = (b.repr y i : ℚ) := by
    intro y i
    have e : ∀ k, d i * ((b.repr y k : E) * integralBasis E k) =
        (b.repr y k : ℚ) • (d i * integralBasis E k) := by
      intro k
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring

    rw [hexp y, Finset.mul_sum, map_sum]
    simp_rw [e, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hC : ∀ x (y : 𝓞 E), Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E y) =
      (ξ (y • x) : ℚ) := by
    intro x y
    have e : ∀ i, d i * (ξ (b i • x) : E) * algebraMap (𝓞 E) E y =
        (ξ (b i • x) : ℚ) • (d i * algebraMap (𝓞 E) E y) := by
      intro i
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring

    rw [hP, Finset.sum_mul, map_sum]
    simp_rw [e, map_smul, hL, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr y]

    simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have huniq : ∀ y y' : E, (∀ k, Algebra.trace ℚ E (y * integralBasis E k) =
      Algebra.trace ℚ E (y' * integralBasis E k)) → y = y' := by
    intro y y' h
    rw [← d.sum_repr y, ← d.sum_repr y']
    simp_rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    apply huniq
    intro k
    have e : (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x * integralBasis E k =
        _root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E (b k * a) := by
      rw [integralBasis_apply, map_mul]
      show (algebraMap (𝓞 E) E a) * _ * _ = _
      ring
    rw [e, hC, integralBasis_apply, hC, mul_smul]
  · intro x y
    simp only [hP, smul_add, map_add (f := _), Int.cast_add, mul_add, Finset.sum_add_distrib]
  · intro x
    have := hC x 1
    simpa using this
  · intro x
    rw [hP, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    have hdi : IsIntegral ℤ ((NumberField.discr E : E) * d i) := by
      have h := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
        (1 : Submodule (𝓞 E) E) (b := integralBasis E)
        (fun k => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
        (a := 1) (x := d i) (Submodule.one_le.1 le_rfl) (by
          rw [Submodule.mem_traceDual]
          intro a ha
          obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
          rw [Algebra.traceForm_apply, hL]
          exact ⟨b.repr y i, rfl⟩)
      rw [← coe_discr, Algebra.smul_def, mul_one] at h
      simpa using h
    have hξ : IsIntegral ℤ ((ξ (b i • x) : ℤ) : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ξ (b i • x)))
    rw [← mul_assoc]
    exact hdi.mul hξ
  · intro K _ τK x
    show ∑ i, τK (d i) * (ξ (b i • x) : K) = τK (_root_.GlobalTheory.ArcQ.pairE ξ x)
    rw [hP]

    simp [map_sum, map_mul, map_intCast]

end GlobalTheory.ArcQ
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frameChange_exists_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  first | exact @GlobalTheory.ArcQ.frChg_exists_unique_units | exact GlobalTheory.ArcQ.frChg_exists_unique_units | (intros; apply GlobalTheory.ArcQ.frChg_exists_unique_units <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frameChange_compose_invert_baseChange_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  first | exact @GlobalTheory.Frames.frChg_calculus | exact GlobalTheory.Frames.frChg_calculus | (intros; apply GlobalTheory.Frames.frChg_calculus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.theta_generator_eq_rootOfUnity_mul_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S] (t' : SAB H (Sp S)) (x : Sp S ⟶ Xo.X) (m m' : SABMap t' Xo.univ.t x) (w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)) (w' : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m'.φ)) (σ σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)) (s1' : LB.Sec (Xo.univ.t.PP.L.pull m'.φ)) (s : LB.Sec (PPx x)), SecGen x s → RigIso m w → RigIso m' w' → IsoMaps w σ s1 → IsoMaps w' σ' s1' → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m'.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m'.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1'.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → ∃ (ζ : S) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ∀ i, σ'.f i = constFn t'.G.hom _ ζ * σ.f i := by
  first | exact @GlobalTheory.theta_generator_eq_rootOfUnity_mul | exact GlobalTheory.theta_generator_eq_rootOfUnity_mul | (intros; apply GlobalTheory.theta_generator_eq_rootOfUnity_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.fderiv_torusCoordinateRatio_eq_zero_of_tangent : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  first | exact @GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | exact GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | (intros; apply GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.torusCoordinateRatio_differentiableAt_origin : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  first | exact @GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | exact GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | (intros; apply GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanJet

open FrameValue

theorem jet_comp_equiv {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (e : V' ≃L[ℂ] V) (F : V → ℂ) (z : V') : jet (fun w => F (e w)) z = jet F (e z) := by
  have h := e.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at h
  ext
  · simp
  · rw [snd_jet, snd_jet]
    exact congrArg (fun q : V' →L[ℂ] ℂ => q z) h

theorem valR_eq_jet {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {z : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e z v) (U : X.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR v U f = jet (fun w => valAt' (e w) U f) z := by
  ext
  · rw [fst_jet, ← hd.1]
    exact (FormalValue.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U hU f).symm
  · rw [snd_jet, ← hd.2 U hU f, valR, dite_eq_left hU]

theorem frameProd_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {n : ℕ} (u : HolUnif A L n) (j : ℕ)
    (c z : Fin n → ℂ) (k : Fin 4 → L.ι) (hk : ∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ L.U (k i)) :
    _root_.GlobalTheory.FrameValue.frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] ![k 2, k 0, k 1, k 3] *
      _root_.GlobalTheory.FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
  have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
  have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
  have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
  have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
  delta _root_.GlobalTheory.FrameValue.frameProd
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
    zpow_neg, zpow_one, zpow_natCast, add_comm z c]
  field_simp

theorem jet_sec_mul_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ g h z₀ ν j α s₀ jt hd hs hj
  have hU : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    intro y hy
    refine Set.mem_iInter.2 fun i => ?_
    have h₁ := Set.mem_iInter.1 (hj hy) (![2, 0, 1, 3] i)
    have h₂ : (![jt 2, jt 0, jt 1, jt 3] : Fin 4 → _) i = jt (![2, 0, 1, 3] i) := by fin_cases i <;> rfl
    rw [h₂]
    exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (jt (![2, 0, 1, 3] i)))
      (ConstTerm.comp_famφB a.D₀ ν.b (Λ.ε α) i)).mpr h₁
  have h0 : ⊤ ≤ (Λ.u.ex (0 : Λ.A.V).2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    have h₁ := FormalValue.top_le_comp hU (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have h₂ := hd.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at h₂
    exact h₂ ▸ h₁
  obtain ⟨ho, hh⟩ := Λ.u.hol _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  have hn : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] :=
    (ho.preimage continuous_snd).mem_nhds h0
  have lf := ConstTerm.isLift_famφB Λ.u (Λ.ct α)
  have hk : ∀ z, ⊤ ≤ (Λ.u.ex z).left ⁻¹ᵁ LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] →
      ∀ i, ⊤ ≤ (Λ.u.ex (![Λ.A.ct α + z, Λ.A.ct α, z, 0] i)).left ⁻¹ᵁ a.D₀.P.L.U (jt i) := fun z hz i => by
    have h₁ := ((lf z).le_iff _).1 hz
    fin_cases i
    exacts [add_comm z (Λ.A.ct α) ▸ h₁ 1, h₁ 2, h₁ 0, h₁ 3]
  have hg : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε α)) jt :=
    hn.mono fun v hv => ((gtHol_isLift a.D₀ Λ.u _ _ _ _ (Λ.ct α) (Λ.ex0_b v)).le_iff jt).2 (hk _ hv)
  obtain ⟨hc₁, hc₂⟩ := (analyticDictionaryExp_holomorphic_over_unif E H D l c O β b a Λ).2 (Λ.ε α) jt
  simp only [LinearEquiv.symm_apply_apply] at hc₂
  have dF : DifferentiableAt ℂ (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) 0 :=
    (hh.differentiableAt (ho.mem_nhds h0)).comp (0 : Λ.A.V) differentiableAt_snd
  have dG : DifferentiableAt ℂ (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) 0 := hc₁.differentiableAt hg
  have dfn : Differentiable ℂ (Λ.fn j α s₀) := by
    have := differentiable_secVal a.D₀.P.isLB s₀ (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact lf w)
    simp only [id, Category.comp_id] at this
    exact this
  have dP : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) 0 := by
    have : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
    exact ((dfn.comp differentiable_snd).fun_mul (this.const_mul _).cexp) 0
  have dQ : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.u.fr (jt 2) v.2) 0 :=
    ((Λ.u.fr_hol (jt 2)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds (hk _ h0 2))).comp (0 : Λ.A.V)
      differentiableAt_snd
  have e₁ := valR_eq_jet hd _ hU (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  simp only [Λ.ex0_b] at e₁
  replace e₁ := e₁.trans (jet_comp_equiv h.symm
    (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) z₀)
  have e₂ := (hs (Λ.ε α) jt hj).trans (jet_comp_equiv h.symm (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) z₀)
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  rw [← jet_mul dF dG, ← jet_pow dQ, ← jet_mul dP (dQ.fun_pow j)]
  refine jet_congr ?_ _
  filter_upwards [hn, hg] with v hv hv'
  refine (congrArg₂ (· * ·) (valAt'_sec a.D₀.P.isLB s₀ (lf v.2) hv) (hc₂ v hv')).trans ?_
  rw [← frameProd_mul Λ.u j (Λ.A.ct α) v.2 jt (hk _ hv), _root_.mul_mul_mul_comm]
  rfl

end GlobalTheory.ConstTanJet
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.polarisation_section_generates_of_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  first | exact @GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | exact GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | (intros; apply GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  first | exact @GlobalTheory.PerFlow.perFr_flow_block | exact GlobalTheory.PerFlow.perFr_flow_block | (intros; apply GlobalTheory.PerFlow.perFr_flow_block <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_latticeVector_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  first | exact @GlobalTheory.GtRep.exists_rep_and_shift | exact GlobalTheory.GtRep.exists_rep_and_shift | (intros; apply GlobalTheory.GtRep.exists_rep_and_shift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.specialisedPoints_holomorphic_quasiPeriodic : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → IsHolTo Set.univ (fun v => (Ψ.pi w v).left) ∧ (∀ la, Ψ.pi w (A.Pw w la) = 1) ∧ (∀ j, DifferentiableOn ℂ (Ψ.fr w j) {v | ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j}) ∧ ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v = Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la) := by
  first | exact @GlobalTheory.SpecHol.specPts_holomorphic | exact GlobalTheory.SpecHol.specPts_holomorphic | (intros; apply GlobalTheory.SpecHol.specPts_holomorphic <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanExp

theorem approx {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G)
    {e j : ℕ} {σ : Out.H0 U.LG.L j} {f : ∀ α : D.toPre.X, D.toPre.SecB j α} (h : U.ExpandsAt e j σ f)
    {K : Type} (q : K ≃ D.toPre.X) : ∃ F : Finset K, ∀ (S : Type) [CommRing S] [IsLocalRing S] (J : Ideal S)
      [IsAdicComplete J S] (s : Sp S ⟶ Sp R) (g : Out.GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left),
      FormalValue.IsFormalPt U J g x → ∀ (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι), ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL →
      ⊤ ≤ FormalValue.basePt g ⁻¹ᵁ D.toPre.P.L.U jM → ∀ (ω τ φ p : S) (B : K → S), IsUnit ω → IsUnit τ →
      ω * τ = (FormalValue.tau U J x jL jM).val * φ →
      (∀ α jf jt, FormalValue.CohCharts g (q α) jM jf jt →
        ω ^ j * (FormalValue.famVal g (f (q α)) jf * FormalValue.coordVal g (q α) jt) = B α * φ ^ j) →
      FormalValue.secVal U σ x jL = p * τ ^ j → p - ∑ α ∈ F, B α ∈ J ^ (e + 1) := by
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq U h
  refine ⟨F.map q.symm.toEmbedding, fun S _ _ J _ s g x hx jL jM hL hM ω τ φ p B hω hτ e₁ hB hp => ?_⟩
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  choose jf jt hc using FormalValue.exists_cohCharts g jM hM
  have e₂ := Ideal.Quotient.eq.1 ((hF S J s g x hx _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((F.map q.symm.toEmbedding).map q.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨q.symm α, Finset.mem_map_of_mem _ hα, q.apply_symm_apply α⟩) hL hM
    (fun α _ => hc α))
  rw [Finset.sum_map, hp] at e₂
  have e₃ : ω ^ j * ∑ α ∈ F.map q.symm.toEmbedding, FormalValue.famVal g (f (q α)) (jf (q α)) *
      FormalValue.coordVal g (q α) (jt (q α)) = (∑ α ∈ F.map q.symm.toEmbedding, B α) * φ ^ j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => hB α _ _ (hc _)
  rw [← Ideal.unit_mul_mem_iff_mem _ ((hω.mul hτ).pow j)]
  have e₄ := Ideal.mul_mem_left _ (ω ^ j) e₂
  have e₅ : (ω * τ) ^ j = (FormalValue.tau U J x jL jM).val ^ j * φ ^ j := by rw [e₁, mul_pow]
  refine (congrArg (· ∈ J ^ (e + 1)) ?_).mp e₄
  rw [mul_sub, mul_sub, mul_left_comm (ω ^ j) (_ ^ j)]
  refine congrArg₂ (· - ·) (by ring) ((congrArg (_ * ·) e₃).trans ?_)
  rw [e₅]
  ring

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : _root_.GlobalTheory.ArcPts.GtAn a}
  (Ξ : _root_.GlobalTheory.ArcPts.ConstPts W Λ)

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isUnit_frame (v : Λ.A.V) (k : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U k) :
    IsUnit (Ξ.τ v k) := by
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v k jM j₀ h hj)).mpr ?_)
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)

theorem differentiable_term (j : ℕ) (α : Λ.A.X) (s : a.D₀.SecB j (Λ.ε α)) :
    Differentiable ℂ fun u : Λ.A.V => Λ.fn j α s u.2 * eTwoPi (u.1 α) := by
  have h₁ := FrameValue.differentiable_secVal (u := Λ.u) a.D₀.P.isLB s (𝟙 _) (q := id) differentiable_id
    (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop)
    (fun w => by rw [id, Category.comp_id]; exact ConstTerm.isLift_famφB Λ.u (Λ.ct α) w)
  simp only [id, Category.comp_id] at h₁
  have h₂ : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
  exact (h₁.comp differentiable_snd).fun_mul (h₂.const_mul _).cexp

end Points

theorem exists_eq_mul_pow {S : Type} [CommRing S] (s : S) {t : S} (ht : IsUnit t) (j : ℕ) : ∃ p, s = p * t ^ j := by
  obtain ⟨p, hp⟩ := (ht.pow j).dvd (a := s)
  exact ⟨p, hp.trans (_root_.mul_comm _ _)⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : _root_.GlobalTheory.ArcPts.ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ g₁ v z jL jM ω φ₁ τ j σ hv hL hM hω hτ e₁ hB ⟨f, hf, hs⟩
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isAdicComplete_idealEps
  haveI := isLocalRing_dual ℂ⟦X⟧
  choose s₀ r hs using fun α : Λ.A.X => hs (Λ.ε α)
  choose F hF using fun e => approx W.P.U.toUnifPre (hf e) (Λ.ε.trans W.e).toEquiv
  have key : ∀ e u k p, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k →
      FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = p * Ξ.τ u k ^ j →
      p - ∑ α ∈ F e, r α * PowerSeries.C (Λ.fn j α (s₀ α) u.2 * eTwoPi (u.1 α)) ∈
        (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ^ (e + 1) := by
    intro e u k p hk hp
    obtain ⟨iM, i₀, hi, -⟩ := exists_charts Ξ u
    refine hF e _ _ _ (Ξ.g u) _ (Ξ.x_fm u) k iM hk (fun y hy => (hi hy).2) _ _ _ p _
      (FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g u).b.left _ hi (W.w.s (fun _ => i₀, iM)))
      (isUnit_frame Ξ u k hk) (Ξ.τ_eq u k iM i₀ hk hi) (fun α jf jt hc => ?_) hp
    refine (ConstTerm.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α (s₀ α) _ (r α) (hs α) u iM i₀ jf jt hc hi).trans ?_
    rw [map_mul, map_pow, _root_.mul_assoc]
  have hk : ∀ u, ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := fun u => by
    obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
    exact ⟨k, (top_le_iff_cpt _ _).2 hk⟩
  choose k hk using hk
  choose x hx using fun u => exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left (k u))
    (isUnit_frame Ξ u (k u) (hk u)) j
  obtain ⟨y, hy⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ v jL) hτ j
  refine ⟨x, y, isJet_of_approx fun e => ⟨_, _, IsJet.sum (F e) fun α _ =>
    (isJet_C (differentiable_term j α (s₀ α) 0) z).const_mul (r α), fun u => ?_, ?_⟩, fun u k' hk' => ?_, hy⟩
  · have := key e u _ _ (hk u) (hx u)
    rwa [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  · exact hF e _ _ _ g₁ v hv jL jM hL hM ω τ φ₁ y _ hω hτ e₁ (fun α jf jt hc => hB α (s₀ α) _ (r α) jf jt (hs α) hc) hy
  · obtain ⟨p, hp⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k')
      (isUnit_frame Ξ u k' hk') j
    rw [hp]
    refine congrArg (· * _) (FormalValue.eq_of_forall_mk_eq
      ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => ?_)
    exact (Ideal.Quotient.eq.2 (key e u _ _ hk' hp)).trans (Ideal.Quotient.eq.2 (key e u _ _ (hk u) (hx u))).symm

end GlobalTheory.ConstTanExp
end
end
