module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal


open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in
theorem intSec_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V')
    (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V'))
    (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (m : SABMap G' G (spMap φ)) (I : IntSec Xo V y.x y.s G)
    (hψ : ∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) (hm : FrMap ψ y y') :
    Nonempty (IntSec Xo V' y'.x y'.s G') := by
  obtain ⟨t, m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := I
  obtain ⟨hx, -, pm, hs, hf, ha⟩ := hm
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp (FractionRing V')), Nonempty (SABMap t' t (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) t
    exact ⟨_, ⟨m⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp φ :=
    RingHom.ext hψ
  have hio : spMap (algebraMap V' (FractionRing V')) ≫ spMap φ =
      spMap ψ.toRingHom ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [← FrBC.spMap_comp', ← FrBC.spMap_comp', hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (FrUniq.tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := FrUniq.tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hf (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (FrUniq.tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨w, θ', rw', iw⟩ := pull_sec G G' m θ
  have pw : PullSec m.φ θ (thfPull G.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := FrBC.exists_isoMaps_cancel m m' m2' rfl e₃ rw' r2 iw pw i2 p2
  exact ⟨⟨t', m1', m', θ', w1', w', σ', s1', _, r1, r', i1, i', fun _ _ => rfl, hg⟩⟩

theorem intSec_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun T io y => ?_, fun V V' _ _ _ _ _ _ φ ψ y y' G G' m I hψ hm =>
    intSec_baseChange φ ψ y y' G G' m I hψ hm⟩
  obtain ⟨G, t', m1, m2, -, θ, -, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := y.2.2
  exact ⟨G, ⟨⟨t', m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩⟩⟩

end GlobalTheory.EtaVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  first | exact @GlobalTheory.EtaVal.datAt_of_uniformisation | exact GlobalTheory.EtaVal.datAt_of_uniformisation | (intros; apply GlobalTheory.EtaVal.datAt_of_uniformisation <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralThetaSection_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  first | exact @GlobalTheory.EtaVal.intSec_exists_and_baseChange | exact GlobalTheory.EtaVal.intSec_exists_and_baseChange | (intros; apply GlobalTheory.EtaVal.intSec_exists_and_baseChange <;> assumption)

end
end
