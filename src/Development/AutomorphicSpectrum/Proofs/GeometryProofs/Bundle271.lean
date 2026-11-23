module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareFirst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsForComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle139
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle216
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle180
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberField
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle269
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.MvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.global_snc_chart_system : GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  exact GlobalTheory.CompanionTheory.Ar.GeoModel.exists_geo
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.BdSym

theorem boundary_closed_torus_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  intro X Ω _ ξ K _ J _ y T bd hT hbd
  have key := GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT
  refine ⟨?_, ?_, ?_⟩
  · have e : ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) =
        ⋂ f ∈ bd, {w : mcPts (mCoordIdeal y) |
          MvPolynomial.eval w.1 (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext w
      have hw : w.1 ∈ mcPts (mCoordIdeal y) := w.2
      rw [Set.mem_iInter₂]
      simp only [mcPts, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
      exact ⟨fun h => h.2.2, fun h => ⟨hw, hw.1, h⟩⟩
    rw [e]
    refine isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  · rintro w ⟨hw1, hw2⟩ c hc
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc : CoordsAt ξ y z (torusSmul c w) := by
      have h' := hzw
      unfold CoordsAt at h' ⊢
      refine ⟨fun k => ?_, fun k i hu => ?_⟩
      · obtain ⟨i, hi⟩ := h'.1 k
        refine ⟨i, isUnit_iff_ne_zero.2 ?_⟩
        show c k * w ⟨k, i⟩ ≠ 0
        exact mul_ne_zero (hc k) (isUnit_iff_ne_zero.1 hi)
      · have hu' : IsUnit (w ⟨k, i⟩) := by
          refine isUnit_iff_ne_zero.2 fun h0 => isUnit_iff_ne_zero.1 hu ?_
          show c k * w ⟨k, i⟩ = 0
          rw [h0, mul_zero]
        obtain ⟨hy, hr⟩ := h'.2 k i hu'
        refine ⟨hy, fun j => ?_⟩
        obtain ⟨r, hr1, hr2⟩ := hr j
        refine ⟨r, hr1, ?_⟩
        show c k * w ⟨k, j⟩ = r * (c k * w ⟨k, i⟩)
        rw [hr2]
        ring
    exact Set.mem_inter ((key _).2 ⟨z, hz, hzc⟩) ((hbd z _ hzc).2 ((hbd z w hzw).1 hw2))
  · rintro w ⟨hw1, hw2⟩
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc := GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj hzw
    have hcz : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) = centre z := GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z
    have hz' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) := by
      rw [hcz]
      exact hz
    have hT' : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) ∉ T := by
      rw [hcz]
      exact (hbd z w hzw).1 hw2
    exact Set.mem_inter ((key (conjVec w)).2 ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z, hz', hzc⟩) ((hbd _ _ hzc).2 hT')

end GlobalTheory.CompanionTheory.Ar.BdSym
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.CoordConj

theorem centre_and_coords_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  intro X Ω _ ξ K _ J _ y z w
  exact ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z, fun h => GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj h⟩

end GlobalTheory.CompanionTheory.Ar.CoordConj
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.root_origin_compare_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → ∀ (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X) (w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) → CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) → CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) → o.𝔐.Interior z₁ → o₀.𝔐.Interior z₂ → ∀ (r : RootIx D) (v : ℂ), Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) w v → ‖v‖ * (o₀.sing r).h (fun p => w (Cmp.joinInr M.ι R.ι p)) = (o.sing r).h (fun p => w (Cmp.joinInl M.ι R.ι p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SingCmp.sing_agree | exact GlobalTheory.CompanionTheory.Ar.SingCmp.sing_agree | (intros; apply GlobalTheory.CompanionTheory.Ar.SingCmp.sing_agree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section



open GlobalTheory.CompanionTheory.Ar.FlagStep in
theorem GlobalTheory.CompanionTheory.Ar.exists_flagStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  classical
  intro E _ _ _ H D l Xo c Y Ω₀ _ _ ξ₀ K _ J _ y X ξ f cst t m Li _ _ M ρ L bd hgen hall htie hξ hcst hact hvb hLeq hsnc hbd
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  obtain ⟨X', Ω', _, _, ξ', f', N, x', b₁, htie', hall', hdom, hsm, -, hgf, hfl⟩ :=
    GlobalTheory.T.exists_model_vector_bundles X Ω₀ ξ Li ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (CMType H ⊕ CMType H) (labelRk D)
      (fun s => eigSp ρ (cst.comp (labelEmb c s))) L htie hall hvb
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω₀ Ω').injective
  have hg : IsCptGen ξ := htie.gen
  have hg' : IsCptGen ξ' := htie'.gen
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H X', Nonempty (SABMap t' t f') := by
    obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt f' t
    exact ⟨_, ⟨m₁⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H Y.X X X' Y.t t t' f f' m m₁
  obtain ⟨Li', _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t'.G Ω' ξ'
  obtain ⟨ρ', hact', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom
    t'.act.one t'.act.mul t'.act.add
  obtain ⟨j', hj₁, hj₂, hj₃, hj₄, hj₅⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M'
    hg hg' hdom
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G Ω₀ ξ₀
  have hdom₀ : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (RingHom.id Ω₀) := by
    show ξ ≫ f = _
    rw [hξ]
    simp
  obtain ⟨a₀, ha₁, ha₂, ha₃, ha₄, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t X t f m Ω₀ Ω₀ ξ₀ ξ (RingHom.id Ω₀) Li₀ Li M₀ M
    hgen hg hdom₀

  let aL : Li₀ →ₗ[Ω₀] Li := { toFun := a₀, map_add' := a₀.map_add, map_smul' := fun c e => ha₂ c e }
  have hainj : Function.Injective aL := by
    refine (injective_iff_map_eq_zero aL).2 fun e he => ?_
    by_contra hne
    have h1 := ha₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hasurj : Function.Surjective aL := by
    have : LinearMap.range aL = ⊤ := by
      rw [eq_top_iff, ← ha₄]
      exact Submodule.span_le.2 (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
    exact LinearMap.range_eq_top.1 this
  let a : Li₀ ≃ₗ[Ω₀] Li := LinearEquiv.ofBijective aL ⟨hainj, hasurj⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.tensor_equiv_of_basis_extension Ω₀ Ω' Li Li' j' hj₂ hj₃ hj₄
  have hjinj : Function.Injective j' := by
    refine (injective_iff_map_eq_zero j').2 fun e he => ?_
    by_contra hne
    have h1 := hj₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hint := GlobalTheory.T.lie_model_pullback_action_ring E H X X' t t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M' ρ ρ' j' hdom hact hact' hj₁
  have hjΦ : Φ.toLinearMap.toAddMonoidHom.comp (TensorProduct.mk Ω₀ Ω' Li 1).toAddMonoidHom = j' :=
    AddMonoidHom.ext hΦ
  let cst' : c.F →+* Ω' := (algebraMap Ω₀ Ω').comp cst
  have heig : ∀ (σ : 𝓞 E →+* Ω₀) e, j' e ∈ eigSp ρ' ((algebraMap Ω₀ Ω').comp σ) ↔ e ∈ eigSp ρ σ := by
    intro σ e
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← hint a e, RingHom.comp_apply, ← hj₂]
    exact hjinj.eq_iff
  let V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀ := fun s => (eigSp ρ (cst.comp (labelEmb c s))).comap aL
  have hgf' := GlobalTheory.T.generic_flag_under_equiv Ω₀ Ω' Li₀ Li _ Li' a _ Φ _ (labelRk D) _ V₀ b₁ 1 (fun s e => Iff.rfl) hgf
  obtain ⟨cc, u, -, -, -, -, hu1, hu0, -, halg, -, hfr⟩ := hgf
  have htop := GlobalTheory.T.unipotent_entries_field_degree Ω₀ Ω' _ (labelRk D) u hu1 hu0 hfr
  have hgf'' : IsGenericFlag (Ω' := Ω') (j'.comp aL.toAddMonoidHom) V₀ (fun s k => Φ (b₁ s k)) 1 := by
    rw [← hjΦ]
    exact hgf'
  have hg'' : IsCptGen ξ' := hg'
  have tie₁ := GlobalTheory.T.coords_added_projective X X' Ω₀ Ω' ξ ξ' f' K J y N x' hall htie htie' hdom
  have snc₁ := GlobalTheory.T.snc_model_added_coords X X' Ω₀ Ω' ξ ξ' f' K J y N x' D.dim bd _ _ hall hall' htie tie₁ hdom hsm halg htop hsnc
  rw [GlobalTheory.T.dimension_plus_flag_count E H D l c] at snc₁
  refine ⟨Ω', inferInstance, inferInstance, inferInstance, Unit ⊕ K, inferInstance, addJ J N, inferInstance,
    addY y x', X', ξ', f' ≫ f, cst', t', n, Li', inferInstance, inferInstance, M', ρ', Li₀, inferInstance,
    inferInstance, M₀, j'.comp aL.toAddMonoidHom, V₀, fun s k => Φ (b₁ s k),
    bd.map (MvPolynomial.rename (addV J N)), hall', tie₁, fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq,
    ?_, ?_, hact', ?_, ?_, ?_, ?_, snc₁, ?_⟩
  · show ξ' ≫ f' ≫ f = _
    rw [← Category.assoc, show ξ' ≫ f' = _ from hdom, Category.assoc, hξ]
  · have hd : ξ' ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap Ω₀ Ω')) ≫ ξ := hdom
    have e₁ : ξ' ≫ (f' ≫ f) ≫ Y.s = (ξ' ≫ f') ≫ f ≫ Y.s := by simp only [Category.assoc]
    rw [e₁, hd, Category.assoc, hcst]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · intro e
    rw [hn]
    show (M'.pt (j' (a₀ e))).left ≫ m₁.φ ≫ m.φ = _
    rw [← Category.assoc, hj₁, Category.assoc, ha₁, SatModel.spMap_dualMap_id, Category.id_comp]
  · intro s e
    exact (heig _ _).symm.trans Iff.rfl
  · exact hgf''
  · intro s
    have heig' : ∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
        j' e ∈ eigSp ρ' (((algebraMap Ω₀ Ω').comp cst).comp (labelEmb c s)) := by
      intro s e he
      rw [RingHom.comp_assoc]
      exact (heig _ e).2 he
    have hfl' : ∀ s, ((L s).pull ξ' f' j').IsFlagVBOn Set.univ (fun k => Φ (b₁ s k)) := by
      intro s
      rw [← hjΦ]
      exact GlobalTheory.T.flag_bundle_under_equiv X X' Ω₀ Ω' ξ ξ' f' Li _ Li' (L s) _ Φ Set.univ _ (b₁ s) (hfl s)
    have hi₀ : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc htie hsnc q hq
    have hi₁ : ∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq
    exact GlobalTheory.T.lie_model_constants_extension E H l c X X' t t' f' Ω₀ Ω' ξ ξ' cst Li Li' M M' ρ ρ' L j' (labelRk D) (fun s k => Φ (b₁ s k)) hg hg'
      hdom hact hact' hi₀ hi₁ hLeq hj₅ heig' hfl' s
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_added X X' Ω₀ Ω' ξ ξ' f' K J y N x' z w hall htie hg'' hall' hdom hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (addV J N ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [EigBase.mem_mcPts_rename (addV J N) bd w hne hne']
    exact hbd (z ≫ f') _ hw₁
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_coords_for_component : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω₀ Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) ∧ (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_eigBase | exact GlobalTheory.CompanionTheory.Ar.exists_eigBase | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_eigBase <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.flag_weighted_degree_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (τ : CMType H) (t₀ : ℝ) (c₁ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) → A.a = ∑ i, xdeg (τ, i) → (∀ w' : (Σ k, J k) → ℂ, CoordsAt 𝔐.ξ y z w' → A.h w' = ∏ i, (hx (τ, i)).h w') → CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → c₁ ≠ 0 → (∀ (hc : genPt 𝔐.ξ ⤳ centre z) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ) (α κ : Ω) (u : ℂ), (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, hc⟩ → (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, hc⟩ → 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ → 𝔐.M.GramAt 𝔐.t.PP.L z bq Δ → Γ.PosDef → Δ.PosDef → (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) = α • exteriorPower.ιMulti Ω _ bp → (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) = κ • exteriorPower.ιMulti Ω _ bq → ValAt 𝔐.ξ z (c₁ * α / κ) u → Real.log ‖u‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t₀) → ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e (τ, i))) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = Real.exp t₀ * A.h w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics | exact GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics | (intros; apply GlobalTheory.CompanionTheory.Ar.RootGram.norm_against_root_metrics <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_flag_xdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective β → Fl.RootLines xdeg e → ∀ r, ∃ A : HermLine J, A.a = xdeg r ∧ Fl.IsHodgeLine r (e r) A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | exact GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_signature_number_field : N1ab → PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q')) → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (t' : SAB H (Sp (𝓞 L'))) (tK : SAB H (Sp L')), Nonempty (SABMap tK t' (spMap (algebraMap (𝓞 L') L'))) ∧ Nonempty (SABMap tK t (spMap e)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model | exact GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model | (intros; apply GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.exists_full_torsion_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (m : ℕ), 1 ≤ m → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K) (x : Fin (m ^ (2 * D.g)) → (Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G)), (∀ i, x i ^ m = 1) ∧ ∀ (F : Type) [Field F] (f : K →+* F) (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G), b = spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) → y ^ m = 1 → ∃! i, y.left = spMap f ≫ (x i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.component_data_hodge_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.hodgeInnerProduct_blocks_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_system_hodge_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge <;> assumption)
end
