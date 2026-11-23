module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle071
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle002
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSum
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
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.hasSum_sectionValue_arc_framedPoint : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (_root_.Formalism.L2.PjFree.toC (evR Xo c F yw)) := by
  first | exact @GlobalTheory.ArcQ.hasSum_evR_arc | exact GlobalTheory.ArcQ.hasSum_evR_arc | (intros; apply GlobalTheory.ArcQ.hasSum_evR_arc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arc_model_witness_extension : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), IsTypeFn H Dw.p Dw.q ty → ∀ th : a.D₀.P.L.Sec, ThNZ th → Nonempty (ThetaDat Ha th) := by
  first | exact @GlobalTheory.ArcTheta.nonempty_thetaDat | exact GlobalTheory.ArcTheta.nonempty_thetaDat | (intros; apply GlobalTheory.ArcTheta.nonempty_thetaDat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arc_framedPoint_integral_open_disc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  exact @GlobalTheory.ArcQ.integral_of_isArcFr
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_normalForm_arcDatum_framedPoint_rootOfUnity : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁), ∃ (ζ : K₁) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ((∀ τ k, GtTanR (d.e τ k)) → d.Normal ζ) ∧ ∃ (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁)) (y₀ : FrPt Xo c (ArcS Dw K₁)), (∀ τ k, GtComb (Pi.single k (1 : K₁)) (d.e τ) (e₀ τ k)) ∧ IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧ FrChg (letM Dw K₁) (GlobalTheory.ArcQ.cst Dw ζ) y₀ d.yF :=
  @GlobalTheory.ArcQ.exists_normalForm
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.isFramedPoint_of_arc_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A']
      (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A')
      (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)),
      Mono Y.j → InBC f a a' p → WitBC f p W W' →
      ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A))
        (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th',
        (∀ τ k, GlobalTheory.ArcQ.LetBC p (e τ k) (e' τ k)) → ThBC p th th' →
        ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S),
          GlobalTheory.ArcQ.IsArcFr W e th (ι'.comp (PowerSeries.map f)) y →
            GlobalTheory.ArcQ.IsArcFr W' e' th' ι' y :=
  @GlobalTheory.ArcQ.isArcFr_witBC
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_complexArcDatum_cmFibre : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (B : GlobalTheory.CM.PAT H (Sp R)) (σR : R →+* ℂ), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → l.A = 1 → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap σR) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B σR DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn aC) (hA : Λ.A = A) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left), IsPolFibre σR B.pol aC.D₀.P φ ∧ (∀ a, (aC.oa.onB.act a).left ≫ φ = φ ≫ (B.t.act.act a).left) ∧ ∀ v, Λ.toGtAn₀.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  first | exact @GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | exact GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | (intros; apply GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM


open scoped nonZeroDivisors in
theorem exists_locGen_at {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨c, hc⟩ := p.valuation_surjective K (WithZero.exp (-(FractionalIdeal.count K p I)))
  exact ⟨c, (isLocGen_iff_valuation_eq p c I).2 hc⟩

theorem cmNumbers_of_good : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)] (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La logOm : ℝ), (∀ a : 𝓞 E, star a = H.bar a) → LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → 1 ≤ La → LamDegSt H logOm → CMNumbers0 o.LamL L.ℓ o.Tl.dual La logOm := by
  intro hK E _ _ _ H _ l c nΨ n' f o La logOm hbar hG L hL hLa hDeg
  have hdeg := hDeg l c hbar nΨ n' f o La hG
  have hdet := GlobalTheory.LamF.Ind.lamInd E H l c hbar nΨ n' f o La hG L hL
  choose Hm hH hn hsq using GlobalTheory.LamF.lamLen hK.theta hK.laws E H l c hbar nΨ n' f o La hG L hL
  have hloc := GlobalTheory.LamF.letters_det_valuation_le E H l c nΨ n' f o La hG L hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, hLam, hkl, hka, -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  have hlg : ∀ k, (L.ℓ k).Good := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  have hnd : ∀ k, (L.ℓ k).ndeg = logOm / 2 := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2
  have hkey := key_deg hK.key o.K₁ o.xB o.Tl o.LamL hT hLam hkl hka
  have hHad := hadamard_local_base o.K₁ o.xB.P.g o.LamL L.ℓ L.U Hm La hLam.1 hlg hdet (by linarith) hH hn
    (fun p => by
      obtain ⟨cd, hcd⟩ := exists_locGen_at p o.LamL.I
      choose cl hcl using fun j => exists_locGen_at p (L.ℓ j).I
      exact ⟨cd, cl, hcd, hcl, hloc p cd cl hcd hcl⟩) hsq
  have hTd : o.Tl.dual.Good := (degree_algebraic o.K₁ o.Tl o.Tl hT hT).2.2.1
  have hd := finrank_pos_real o.K₁
  refine ⟨hLam, hlg, hTd, hLa, hHad, hnd, le_of_eq ?_⟩
  simp only [MLine.ndeg]
  rw [hkey]
  field_simp

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.genericPoints_constantPoints_formalSum_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  first | exact @GlobalTheory.GenericPoints.main | exact GlobalTheory.GenericPoints.main | (intros; apply GlobalTheory.GenericPoints.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  first | exact @GlobalTheory.ArcPts.WeightZero.vals_FSum | exact GlobalTheory.ArcPts.WeightZero.vals_FSum | (intros; apply GlobalTheory.ArcPts.WeightZero.vals_FSum <;> assumption)
end
