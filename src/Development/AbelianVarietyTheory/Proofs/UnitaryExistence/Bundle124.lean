module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle209
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.DataTheta
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat

theorem _root_.GlobalTheory.T.geometricallyIrreducible_components_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed (Xo := Xo') (c := c') := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A A' : DatAt Y P, (∀ χ r, PsiCoord A.U.D.toPre χ r → ((A.f r : intO ↥C.S) : ↥C.S) ≠ 0) ∧ ∃ e : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.beta a b := by
  first | exact @GlobalTheory.DatUniq.coord_ne_zero_and_exists_equiv | exact GlobalTheory.DatUniq.coord_ne_zero_and_exists_equiv | (intros; apply GlobalTheory.DatUniq.coord_ne_zero_and_exists_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

noncomputable section

namespace GlobalTheory.Member.ParExist

theorem datLaws_all (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

def parAtLevel (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datLaws_all D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datLaws_all D) j) l (datumAtLift_pq_pos D _ (datLaws_all D) j))
  eO := eOf D hF

theorem exists_par_pins_canon (D : D7) (hF : OFull D) (hz : OZeta D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ Q : Par D, Q.Pins ∧ Q.Canon ∧ (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) ∧
      Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  obtain ⟨l, hl, hb⟩ := levelPb_exists D pb hg
  refine ⟨parAtLevel D hF hz GlobalTheory.Moduli.moduli_scheme_exists l hl, ?_, ⟨rfl, fun j hj => ?_⟩, fun j => datumAtLift_pq_pos D _ (datLaws_all D) j, hb⟩
  · refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
    show IsDatW D j (datumAtLift D _ (datLaws_all D) j)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact isDatW_datumOf D _ j _ _
  · show ∃ hP hd, HEq (datumAtLift D _ (datLaws_all D) j) (datumOfRecord D j hj hP hd)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact ⟨Formalism.IndefR.Fin.factPrincipalDatum, datDom_holds D j hj _, HEq.rfl⟩

end GlobalTheory.Member.ParExist
end
end
