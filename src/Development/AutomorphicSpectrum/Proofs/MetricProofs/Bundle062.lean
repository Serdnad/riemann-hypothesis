module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.WeilBound.CoreStatements.AmpleLineBundles.SlopeMaxLeOfComparableMetric
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitian
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.riemann_lattice_eigen_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | exact GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | (intros; apply GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection <;> assumption)
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem basis_slope_degree_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C :=
  @CoverDenseAlt.slopeMax_le_of_comparable_metric

end GlobalTheory.CompanionTheory.Ar
end
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.FlagPair

theorem iSup_part_degree_rank {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K}
    {Ψ : Type} [Fintype Ψ] {j k : ℕ} (A : FlagPair E Ψ j k) (h : A.IsOrthFull) :
    E.normDegree (⨆ a, A.part a) =
        ∑ τ, E.normDegree (A.W τ).top + ∑ τ, E.normDegree (A.S τ).top ∧
      E.rank (⨆ a, A.part a) = Module.finrank (𝓞 K) E.carrier := by
  unfold GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h
  obtain ⟨hort, hcard⟩ := h
  obtain ⟨hdeg, hrk⟩ := GlobalTheory.T.normalized_degree_orthogonal_sum K E (Ψ ⊕ Ψ) A.part hort
  refine ⟨?_, ?_⟩
  · rw [hdeg, Fintype.sum_sum_type]
    rfl
  · have hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j := fun τ => by
      show E.rank ((A.W τ).F (Fin.last j)) = j
      rw [(A.W τ).rank (Fin.last j), Fin.val_last]
    have hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k := fun τ => by
      show E.rank ((A.S τ).F (Fin.last k)) = k
      rw [(A.S τ).rank (Fin.last k), Fin.val_last]
    rw [hrk, Fintype.sum_sum_type, ← hcard]
    simp only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring

theorem two_sum_neg_degree_W : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull →
    -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧
      ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) →
        2 * ∑ τ, -E.normDegree (A.W τ).top ≤
          -E.normDegree ⊤ - ∑ τ, A.flatDeg τ +
            Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E Ψ _ j k A h
  obtain ⟨hdeg, hrk⟩ := iSup_part_degree_rank A h
  obtain ⟨hle, hge⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E (⨆ a, A.part a) hrk
  have hflat : ∑ τ, A.flatDeg τ =
      ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top := by
    simp only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]
  rw [hdeg] at hle
  refine ⟨?_, ?_⟩
  · rw [hflat, Finset.sum_neg_distrib]
    linarith
  · intro d hd hsub
    have hb := hge d hd hsub
    rw [hdeg] at hb
    rw [hflat, Finset.sum_neg_distrib]
    linarith

end GlobalTheory.CompanionTheory.Ar.FlagPair
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.regular_system_of_parameters_local_ring_alt : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.exists_normalized_riemann_lattice : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.log_det_eq_ball_potential : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ), t ∈ ballDom q → R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ → R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.span_standard_basis_eigenspace : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.conjugate_embeddings_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → ∀ i k : Ix Ψ j j', (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.siegel_transform_commutes_action : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.siegel_transform_symplectic_imaginary : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ), Zᵀ = Z → (∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → ∃ t, bigZe e q t = Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.siegel_normal_form_of_hermitian : ∀ {I : Type} [Fintype I] [DecidableEq I] (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ), H.IsHermitian → (∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re) → (∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) → ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧ ∀ z, L z = A (tz Z z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz <;> assumption)
end
