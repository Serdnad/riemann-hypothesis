module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle055
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsTheta
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamily
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
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  first | exact @GlobalTheory.ArcQ.evR_arc_isHomogeneous | exact GlobalTheory.ArcQ.evR_arc_isHomogeneous | (intros; apply GlobalTheory.ArcQ.evR_arc_isHomogeneous <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arc_framed_point_eq_of_models_over_base :
    Out.Laws → Out.Laws2 → Out.Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
      (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF)
      (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype)
      (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X)
      (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ)
      (W' : Wit Y' (a.restrict (c.V V').subtype) χ'),
    χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) →
    χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) →
    ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec),
    ThNZ th →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S)
      (y y' : FrPt Xo c S),
    IsUnit (ι PowerSeries.X) →
    GlobalTheory.ArcQ.IsArcFr W e th ι y → GlobalTheory.ArcQ.IsArcFr W' e th ι y' → y = y' :=
  @GlobalTheory.ArcQ.isArcFr_eq_of_overBase
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.ArcCM.cfOf_linear_and_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ d a' n
  have hP : ∀ F ∈ sec Xo c a' n, ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁),
      algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (absA Dw a') := fun F hF =>
    GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF
  have hcomp : ∀ a : c.F, algebraMap c.F (ArcS Dw K₁) a =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)
        (algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a) := fun _ => rfl
  have hnum : ∀ F : sec Xo c a' n,
      algebraMap _ (ArcS Dw K₁) (arcNum (evR Xo c F.1 d.yF)) = evR Xo c F.1 d.yF := fun F =>
    (hP F.1 F.2).elim fun P hP' => by
      rw [← hP'.1, LinOfPoly.arcNum_map]
  have hadd : ∀ F G : sec Xo c a' n, arcNum (evR Xo c (F + G).1 d.yF) =
      arcNum (evR Xo c F.1 d.yF) + arcNum (evR Xo c G.1 d.yF) := fun F G =>
    LinOfPoly.inj _ K₁ (by
      rw [map_add (f := _), hnum, hnum, hnum, Submodule.coe_add, LinOfPoly.evR_add])
  have hsmul : ∀ (a : c.F) (F : sec Xo c a' n), arcNum (evR Xo c (a • F).1 d.yF) =
      algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a *
        arcNum (evR Xo c F.1 d.yF) := fun a F =>
    LinOfPoly.inj _ K₁ (by
      rw [hnum, Submodule.coe_smul, LinOfPoly.evR_smul, map_mul, hnum F, hcomp])
  refine ⟨⟨{ toFun := fun F => cfOf d.yF d.μ d.jj F.1, map_add' := ?_, map_smul' := ?_ }, fun F => rfl⟩, ?_⟩
  · intro F G
    simp only [cfOf]
    rw [hadd, MvPolynomial.coeff_add, HahnSeries.coeff_add]
  · intro a F
    simp only [cfOf]
    rw [hsmul, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul, LinOfPoly.laur_alg,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, RingHom.id_apply]
    simp [Algebra.smul_def]
  · intro F hF hne
    obtain ⟨P, hP1, hP2⟩ := hP F hF
    rw [← Finsupp.degree_eq_sum]
    by_contra hd
    apply hne
    simp only [cfOf]
    rw [← hP1, LinOfPoly.arcNum_map, hP2.coeff_eq_zero hd]
    rfl
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ), letI := H.starRing; Arch.IsThNormAt a.D₀.P a.D₀.rig th em (s.Tl.n em ^ 2) ∧ (∀ i, Arch.IsLieNormAt s.xΨ.P (s.xΨ.v i) em (Real.log ((s.ℓΨ i).n em))) ∧ (∀ i, Arch.IsLieNormAt s.x'.P (s.x'.v i) em (Real.log ((s.ℓ' i).n em))) ∧ ∀ (DC : Out.DegPre ℂ) (p : Out.IsPullDeg em a.D₀ DC), (∀ thC, ThBC p th thC → Arch.IsThNormAt DC.P DC.rig thC (RingHom.id ℂ) (s.Tl.n em ^ 2)) ∧ ∀ m (u : epsR K₁ ⟶ a.D₀.P.A) (uC : epsR ℂ ⟶ DC.P.A), s.L.IsLetter m u → uC.left ≫ prj p = spMap (dualMap em) ≫ u.left → ∃ x, Arch.IsLieNormAt DC.P uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (s.L.ℓ m).n em)) := by
  first | exact @GlobalTheory.ArcCM.NormTie.lengths_eq_norms | exact GlobalTheory.ArcCM.NormTie.lengths_eq_norms | (intros; apply GlobalTheory.ArcCM.NormTie.lengths_eq_norms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.arcSection_value_at_specialised_points_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  first | exact @GlobalTheory.ArcSectionValue.section_value | exact GlobalTheory.ArcSectionValue.section_value | (intros; apply GlobalTheory.ArcSectionValue.section_value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.nonempty_chain_arc_witness_universal_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  first | exact @GlobalTheory.ArcPts.nonempty_chain | exact GlobalTheory.ArcPts.nonempty_chain | (intros; apply GlobalTheory.ArcPts.nonempty_chain <;> assumption)
end
