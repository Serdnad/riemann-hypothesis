module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle057
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle048
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle062
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle066
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.family_gives_conjugate_lie_data : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρ a = rho F.B a) ∧ ∀ i u, u ∈ D.lie i ↔ ∀ j, C.v i ((lin (F.ψ i) 1).mulVec u j) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj | exact GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_generation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | exact GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Conj.Fam GlobalTheory.CompanionTheory.Ar.Crv.Inhab

theorem mem_imLat_iff_stdLat {K : Type} [Field K] (C : ACurve K) {d : ℕ} (i : C.I)
    (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) (y : (Fin d → K) × (Fin d → K)) :
    y ∈ imLat C i T ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring T := by
  have hs : ∀ w : (Fin d → K) × (Fin d → K), w ∈ stdH C d i ↔
      ∀ j, w.1 j ∈ (C.v i).valuationSubring.toSubring ∧ w.2 j ∈ (C.v i).valuationSubring.toSubring := by
    intro w
    rw [mem_stdH]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
    exact Submodule.subset_span ⟨w, (hs w).1 hw, rfl⟩
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact (mem_imLat C).2 ⟨w, (hs w).2 hw, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
      refine (mem_imLat C).2 ⟨(a : K) • w, (hs _).2 fun j => ?_, ?_⟩
      · exact ⟨Subring.mul_mem _ a.2 ((hs w).1 hw j).1, Subring.mul_mem _ a.2 ((hs w).1 hw j).2⟩
      · rw [map_smul]
        rfl

theorem family_conj_H_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧
      ∀ i, D.H i = imLat C i (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formal_group_action_ring_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing K d O F.B
  have iso := fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ⟨(good i h).1, (good i h).2.1⟩)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi (by
              obtain ⟨g₁, g₂, g₃⟩ := good i h
              exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃))
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρH, fun _ => rfl⟩
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u
  · rw [hρ, hρH]
    exact GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y

theorem family_conj_H_lattices : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧ ∀ i y, y ∈ D.H i ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨D, h₁, h₂⟩ := family_conj_H_eq K C p d O F hI
  refine ⟨D, h₁, fun i y => ?_⟩
  rw [h₂ i]
  exact mem_imLat_iff_stdLat C i _ y

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.hausdorff_cone_ball_measure : ∀ n m : ℕ, 0 < m → m ≤ n → ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
  ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A → (∀ y ∈ A, ∀ t : ℝ, 0 < t → t • y ∈ A) →
    (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} < ⊤ →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1), cntOver (coneSet h J ∩ A) π w =
      K * (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | exact GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | (intros; apply GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure <;> assumption)
end

section


theorem _root_.GlobalTheory.T.pair_number_pullback : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | exact GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem kleimanNef_field_and_fibre : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  have hF : KleimanNefFStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefF.kleimanNef_field_of_alt (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof hF, hF⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem siuZ : SiuZStatement := by
  have hR4 := GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput
  obtain ⟨-, hVA, hSC⟩ := GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count hR4
  exact GroundTheory.Heights₂.Heights.ForSecondHalf.SiuZB.of_kodaira (GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count hVA hSC)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_line_bundle_descent : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.CompanionTheory.NormLB.exists_normLB | exact GlobalTheory.CompanionTheory.NormLB.exists_normLB | (intros; apply GlobalTheory.CompanionTheory.NormLB.exists_normLB <;> assumption)
end
