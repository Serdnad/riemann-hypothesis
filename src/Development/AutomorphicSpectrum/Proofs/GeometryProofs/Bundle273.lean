module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle271
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle265
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle190
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartHodgeComponentLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle031
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtension
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle272
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

open GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

def IsWeightAt (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (x : ℝ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
    FibreLat Or.𝔐.t z R ∧ Or.𝔐.LabVal z Or.sm σ ∧ x = R.cuspW σ

theorem IsWeightAt.unique {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x x' : ℝ} (h : IsWeightAt Or z x)
    (h' : IsWeightAt Or z x') : x = x' := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨g', Λ', i₃, i₄, R', σ', hF', hL', rfl⟩ := h'
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm ▸ rfl

theorem IsWeightAt.nonneg {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) : 0 ≤ x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, -, -, rfl⟩ := h
  exact le_max_left _ _

theorem exists_isWeightAt (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} (hz : Or.𝔐.Interior z) :
    ∃ x, IsWeightAt Or z x := by
  have hpq : 1 ≤ D.p + D.q := by
    have := Dc.two_le_N
    rw [Or.N_eq] at this
    omega
  obtain ⟨g, Λ, i₁, i₂, R, x, hF, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior hG.2.2.2.2.1 E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z hpq hz hG
    Empty (fun i => i.elim) (fun i => i.elim)
  obtain ⟨σ₀, h0, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hx : x = fun i => i.elim := funext fun i => i.elim
  subst hx
  exact ⟨_, g, Λ, i₁, i₂, R, fun τ => σ₀ (Or.sm τ), hF, fun τ a => h0 (Or.sm τ) a, rfl⟩

theorem IsWeightAt.conj {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) :
    IsWeightAt Or (spMap (starRingEnd ℂ) ≫ z) x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨-, R', hP, hH, hB, hW⟩ := GlobalTheory.T.cusp_weight_invariant_under_conjugation E g Λ (CMType H) R σ (isCMFam_of_labVal Or hL)
  have hF' : FibreLat Or.𝔐.t (spMap (starRingEnd ℂ) ≫ z) R' :=
    (GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move E H Or.𝔐.X Or.𝔐.X Or.𝔐.t Or.𝔐.t (𝟙 _) g Λ R R' z).2 hP hH
      (fun a x => by simpa using hB a (star x)) hF
  exact ⟨g, Λ, i₁, i₂, R', fun τ => (starRingEnd ℂ).comp (σ τ), hF',
    fun τ a => GlobalTheory.CompanionTheory.Ar.HodgeLine.valAt_conj (hL τ a), hW.symm⟩

def HasWeight (Or : CptOrigin Y S₀ Dc Hd) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ z : Sp ℂ ⟶ Or.𝔐.X, CoordsAt Or.𝔐.ξ Dc.y z w ∧ Or.𝔐.Interior z ∧ IsWeightAt Or z x

theorem HasWeight.unique {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x x' : ℝ} (h : HasWeight Or w x)
    (h' : HasWeight Or w x') : x = x' := by
  obtain ⟨z, hz, -, hx⟩ := h
  obtain ⟨z', hz', -, hx'⟩ := h'
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt _ _ _ K J Dc.y Or.𝔐.tie Or.𝔐.normal Or.𝔐.all z z' w hz hz'
  subst e
  exact hx.unique hx'

theorem HasWeight.torus {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) : HasWeight Or (torusSmul a w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  exact ⟨z, coordsAt_torusSmul Or.𝔐.ξ hz ha, hi, hx⟩

theorem HasWeight.conj {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) :
    HasWeight Or (conjVec w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  have hc := GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w
  refine ⟨_, hc.2 hz, ?_, hx.conj⟩
  show centre _ ∈ _
  rw [hc.1]
  exact hi

theorem exists_cuspWeight : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  classical
  let U : ((Σ k, J k) → ℂ) → ℝ := fun w => if h : ∃ x, HasWeight Or w x then h.choose else 0
  have hU : ∀ {w x}, HasWeight Or w x → U w = x := fun {w x} h => by
    have hex : ∃ x, HasWeight Or w x := ⟨x, h⟩
    simp only [U, dif_pos hex]
    exact hex.choose_spec.unique h
  have hU0 : ∀ {w}, (¬ ∃ x, HasWeight Or w x) → U w = 0 := fun {w} h => by
    simp only [U, dif_neg h]
  have hw : ∀ {z : Sp ℂ ⟶ Or.𝔐.X} {w} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
      {σ : CMType H → (𝓞 E →+* ℂ)}, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → FibreLat Or.𝔐.t z R →
      Or.𝔐.LabVal z Or.sm σ → HasWeight Or w (R.cuspW σ) := by
    intro z w g Λ i₁ i₂ R σ hz hi hF hL
    exact ⟨z, hz, hi, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩
  refine ⟨U, fun z w hz hi => ?_, fun w => ?_, fun w a ha => ?_, fun w => ?_, fun U' hU' w hX => ?_⟩
  · obtain ⟨x, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := exists_isWeightAt hG Or hi
    exact ⟨g, Λ, i₁, i₂, R, σ, hF, hL, hU (hw R hz hi hF hL)⟩
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx]
      obtain ⟨z, -, -, hz⟩ := hx
      exact hz.nonneg
    · rw [hU0 h]
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU (hx.torus ha)]
    · have h' : ¬ ∃ x, HasWeight Or (torusSmul a w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : torusSmul (fun k => (a k)⁻¹) (torusSmul a w) = w := by
          funext q
          show (a q.1)⁻¹ * (a q.1 * w q) = w q
          rw [inv_mul_cancel_left₀ (ha q.1)]
        have := hx.torus (a := fun k => (a k)⁻¹) fun k => inv_ne_zero (ha k)
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU hx.conj]
    · have h' : ¬ ∃ x, HasWeight Or (conjVec w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : conjVec (conjVec w) = w := by
          funext q
          exact Complex.conj_conj (w q)
        have := hx.conj
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hX.1
    have hi : Or.𝔐.Interior z := by
      by_contra hn
      exact hX.2 ((Or.bd z w hz).2 hn)
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU' z w hz hi
    rw [he, hU (hw R hz hi hF hL)]

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.boundary_points_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj | exact GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.conjugate_point_same_centre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | exact GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coords_with_constants_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagStep | exact GlobalTheory.CompanionTheory.Ar.exists_flagStep | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagStep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.snc_chart_hodge_component_local : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) (I : Type) [Finite I] (s : I → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), (∀ (z : Sp ℂ ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → CoordsAt 𝔐.ξ y z₀ (χ.γ t₀) → InFrameDomain y cc f (χ.γ t₀) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (σ : KA l →+* ℂ) (C : Flat.BdryChart Xo σ n a₀) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : I → Fin C.g → C.R), 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, t₀ + (ρ : ℂ) • (u ∘ π) ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π)) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at | exact GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem exists_chart_at_of_polydisc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  exact @PositivityTheory.Xgn.quotient_uniformization_chart_at

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

variable {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} {F : X' ⟶ X}

def IsMoved (w : LB.Iso M' (M.pull F)) (s : M.Sec) (s' : M'.Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : M.ι) (k : M'.ι), F (r z) ∈ M.U j → r z ∈ M'.U k →
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k)

theorem IsMoved.mem_nonzeroLocus {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (hM' : M'.IsLB) {s : M.Sec} {s' : M'.Sec}
    (h : IsMoved w s s') {y : X'} (hy : F y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  obtain ⟨k, hk⟩ := exists_chart hM' y
  have u := (mem_nonzeroLocus_iff_pull s F y hj).1 hy
  have e := h X' (𝟙 X') y j k hj hk
  rw [Category.id_comp] at e
  rw [e] at u
  exact (mem_nonzeroLocus_iff_isUnit s' hk).2 ((Units.isUnit_units_mul _ _).1 u)

variable {R R' : Type} [CommRing R] [CommRing R'] {p : X ⟶ Sp R} {p' : X' ⟶ Sp R'}

theorem IsMoved.smul {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (c : R →+* R') (hc : F ≫ p = p' ≫ spMap c) (a : R)
    {s : KeyGen.SecMod p M} {s' t' : KeyGen.SecMod p' M'} (hs : IsMoved w s s') (ht : IsMoved w (a • s : KeyGen.SecMod p M) t') :
    t' = c a • s' := by
  refine KeyGen.SecMod.ext fun k => fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  have e₁ := hs X' (𝟙 X') y j k hj hy
  have e₂ := ht X' (𝟙 X') y j k hj hy
  have hj' : (𝟙 X' ≫ F) y ∈ M.U j := by rwa [Category.id_comp]
  have hy' : (𝟙 X') y ∈ M'.U k := hy
  have ec : cst ((𝟙 X' ≫ F) ≫ p) y a = cst (𝟙 X' ≫ p') y (c a) := by
    rw [Category.assoc, hc, ← Category.assoc, cst_comp]
  rw [KeyGen.smul_f, gs_mul _ y _ hj', gs_constFn p _ _ y hj', ec, e₁, mul_left_comm] at e₂
  rw [KeyGen.smul_f, gs_mul _ y _ hy', gs_constFn p' _ _ y hy']
  exact ((Units.isUnit _).mul_right_inj.1 e₂).symm

theorem exists_moved {w : LB.Iso M' (M.pull F)} (hw : PGen w) (hM : M.IsLB) (hM' : M'.IsLB) (s : M.Sec) :
    ∃ s' : M'.Sec, IsMoved w s s' :=
  sec_pull_down hw hM hM' s

theorem exists_lift {S S' Y Y' : Scheme.{0}} {φ : Y' ⟶ Y} {q' : Y' ⟶ S'} {q : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ q' q f) (b' : S') (y : Y) (e : q y = f b') : ∃ y' : Y', q' y' = b' ∧ φ y' = y := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := f) y b' e
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← hz', ← Scheme.Hom.comp_apply, h.isoPullback_inv_snd]
  · rw [← hz, ← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open PullSec

theorem exists_pull_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  intro E _ _ _ H L _ _ D L' _ _ _ D' m
  obtain ⟨w, gw, -, -⟩ := (isPullCubical_iff m.cm D.t.cub D'.t.cub).1 m.lin
  have hM : (PowB D.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D.t.PP.L D.t.PP.isLB _ _
  have hM' : (PowB D'.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D'.t.PP.L D'.t.PP.isLB _ _
  have hex := fun s : (PowB D.t.PP.L 1).Sec => exists_moved (pGen_powIso gw 1) hM hM' s
  choose P hP using hex
  refine ⟨P, fun a s => ?_, fun s b' y e hy => ?_⟩
  · exact IsMoved.smul (p := D.t.G.hom) (p' := D'.t.G.hom) hM (algebraMap (𝓞 L) (𝓞 L')) m.cart.1.w a (hP s) (hP (a • s))
  · obtain ⟨y', h₁, h₂⟩ := exists_lift m.cart.1 b' y e
    exact ⟨y', h₁, (hP s).mem_nonzeroLocus hM hM' (by rw [h₂]; exact hy)⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.section_sup_norm_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D') (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃ s' : Out.H0 D'.t.PP.L n, (∀ M : (L →+* ℂ) → ℝ, D.SupLe s M → D'.SupLe s' fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ'), ∃ a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g, a.u.Λ = a'.u.Λ ∧ a.Hm = a'.Hm ∧ ∀ θ, a.IsFn s θ ↔ a'.IsFn s' θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | exact GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.frame_function_cm_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value | exact GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.frame_function_cm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧ (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | exact GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic <;> assumption)
end
