module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChart
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle025
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle026
public import Mathlib.RingTheory.RingHom.Flat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegree
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.TwModule

open GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]

def twOut {n : ℕ} (f : (Fin n → O) →ₗ[O] L) : (Fin n → O) →ₗ[O] TwMod s L where
  toFun v := (show TwMod s L from f (fun i => s (v i)))
  map_add' v w := by
    have : (fun i => s ((v + w) i)) = (fun i => s (v i)) + (fun i => s (w i)) := by
      funext i; simp
    show f (fun i => s ((v + w) i)) = f (fun i => s (v i)) + f (fun i => s (w i))
    rw [this, map_add (f := _)]
  map_smul' c v := by
    have : (fun i => s ((c • v) i)) = s c • (fun i => s (v i)) := by
      funext i; simp
    show f (fun i => s ((c • v) i)) = s c • f (fun i => s (v i))
    rw [this, map_smul]

def twIn {n : ℕ} (r : L →ₗ[O] (Fin n → O)) : TwMod s L →ₗ[O] (Fin n → O) where
  toFun x := fun i => s.symm (r (show L from x) i)
  map_add' x y := by
    funext i
    have h : r (show L from x + y) i = r (show L from x) i + r (show L from y) i :=
      congrFun (map_add r (show L from x) (show L from y)) i
    exact (congrArg s.symm h).trans (map_add s.symm _ _)
  map_smul' c x := by
    funext i
    have h : r (show L from c • x) i = s c * r (show L from x) i :=
      congrFun (map_smul r (s c) (show L from x)) i
    refine (congrArg s.symm h).trans ?_
    show s.symm (s c * r (show L from x) i) = c * s.symm (r (show L from x) i)
    rw [map_mul, s.symm_apply_apply]

theorem twOut_twIn {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (r : L →ₗ[O] (Fin n → O)) (h : f ∘ₗ r = LinearMap.id)
    (x : TwMod s L) : twOut s L f (twIn s L r x) = x := by
  have hx : f (r (show L from x)) = (show L from x) := LinearMap.congr_fun h _
  show f (fun i => s (s.symm (r (show L from x) i))) = (show L from x)
  simpa using hx

theorem twOut_surjective {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (hf : Function.Surjective f) :
    Function.Surjective (twOut s L f) := by
  intro x
  obtain ⟨v, hv⟩ := hf (show L from x)
  refine ⟨fun i => s.symm (v i), ?_⟩
  show f (fun i => s (s.symm (v i))) = (show L from x)
  simpa using hv

theorem finite_twMod [Module.Finite O L] : Module.Finite O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  exact Module.Finite.of_surjective _ (twOut_surjective s L f hf)

theorem projective_twMod [Module.Finite O L] [Module.Projective O L] : Module.Projective O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  obtain ⟨r, hr⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact Module.Projective.of_split (twIn s L r) (twOut s L f)
    (LinearMap.ext (twOut_twIn s L f r hr))

theorem rank_twMod : Module.rank O (TwMod s L) = Module.rank O L :=
  (rank_eq_of_equiv_equiv (s : O → O) (AddEquiv.refl (TwMod s L) : TwMod s L ≃+ L) s.bijective
    (fun _ _ => rfl))

theorem finrank_twMod : Module.finrank O (TwMod s L) = Module.finrank O L := by
  rw [Module.finrank, Module.finrank, rank_twMod]

end GlobalTheory.CompanionTheory.Ar.TwModule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank :
    ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]
      [Module.Finite O L] [Module.Projective O L],
      Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧
        Module.finrank O (TwMod s L) = Module.finrank O L := by
  intro O _ _ s L _ _ _ _
  exact ⟨finite_twMod s L, projective_twMod s L, finrank_twMod s L⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

theorem _root_.GlobalTheory.T.free_action_affine_chart : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens), IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W → (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V → HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | exact GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable <;> assumption)
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

def ptsOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | y ∈ S ∧ linProj π y = w}

def cntOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℝ≥0∞ :=
  (((ptsOver S π w).encard : ℕ∞) : ℝ≥0∞)

def IsScaleStable (S : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ y ∈ S, ∀ t : ℂ, t ≠ 0 → t • y ∈ S

def gaussM (m n : ℕ) : Measure (Fin m → Fin n → ℂ) :=
  (volume : Measure (Fin m → Fin n → ℂ)).withDensity matGauss

def planeMass (n e : ℕ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}

def fibrePts {e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  ptsOver S π (firstCoordVec (e + 1))

def fsSum {e : ℕ} (h : HermNorm n) (u : Fin n → ℂ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (π : Fin (e + 1) → Fin n → ℂ) : ℝ :=
  ∑ᶠ y ∈ fibrePts S π, fsLog h u (h.pointOf y)

def coefRows {e : ℕ} (h : HermNorm n) (π : Fin (e + 1) → Fin n → ℂ) : Fin e × Fin n → ℂ :=
  fun ij => ((h.mat)⁻¹ *ᵥ π ij.1.succ) ij.2


open Classical in
def logGap (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : ℝ≥0∞ :=
  if y = 0 then 0
  else if ∑ j, u j * h.pointOf y j = 0 then ⊤
  else ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y))

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_short_exact : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ N₂ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂) (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂), IsSubQuot O x E i p E₁ E₂ → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V) (EB₁ : ChartBundle O (mseg (joinCoord x z)) N₁ V₁) (EB₂ : ChartBundle O (mseg (joinCoord x z)) N₂ V₂), IsPull O x z E EB → IsPull O x z E₁ EB₁ → IsPull O x z E₂ EB₂ → IsSubQuot O (joinCoord x z) EB i p EB₁ EB₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.local_matrix_coprime_decomposition : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Split.isotropic_residue_injective_splits | exact GlobalTheory.CompanionTheory.Ar.Split.isotropic_residue_injective_splits | (intros; apply GlobalTheory.CompanionTheory.Ar.Split.isotropic_residue_injective_splits <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_contains_add_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  first | exact @PositivityTheory.HtPt.Pfib.fibre_crit_ring | exact PositivityTheory.HtPt.Pfib.fibre_crit_ring
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.graph_ideal_fibre_chart_degree : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι), P.IsPrime → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) → imageZ inlV (graphIdeal P g) = P → ∀ (G : GenFibre inlV (graphIdeal P g)) (i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k), IsChart (fibreIdeal Sum.inl G) i → ptDeg (fibreIdeal Sum.inl G) i = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg | exact GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg <;> assumption)
end
