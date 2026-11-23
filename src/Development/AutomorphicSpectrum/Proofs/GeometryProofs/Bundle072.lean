module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AutomorphyFactorExpLinearOfCube
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeSectionFacesAndDoubling
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsGlobalFrameOfLocal
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SeriesApplyEqZeroOfFace
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartCover

private lemma eval_eq_zero_of_mem_mcPts' {K : Type} {J : K → Type}
    (P : Ideal (MRing J)) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    ∀ g ∈ pC P, MvPolynomial.eval z g = 0 := by
  intro g hg
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) := by
    unfold pC
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact RingHom.mem_ker.mpr (hz.2 f hf)
  exact RingHom.mem_ker.mp (hle hg)

private lemma torusSmul_mem_mcPts' {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (P : Ideal (MRing J)) (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P))
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    torusSmul c z ∈ mcPts P := by
  have hv := eval_eq_zero_of_mem_mcPts' P z hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz ⊢
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hmem : MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P := by
      unfold pC
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hP c z hv _ hmem

theorem mcPts_finite_cover_up_to_torus :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  intro K _ J _ P hP C O hO hcov
  classical
  set S : Set ((Σ k, J k) → ℂ) :=
    {w | (∀ k, ∑ i, ‖w ⟨k, i⟩‖ ^ 2 = 1) ∧
      ∀ f ∈ P, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} with hS
  have hSsub : S ⊆ mcPts P := by
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hw.2⟩
    by_contra h
    push Not at h
    have h1 := hw.1 k
    simp [h] at h1
  have hScl : IsClosed S := by
    rw [hS]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun k => ?_)
      (isClosed_iInter fun f => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
        (continuous_norm.comp (continuous_apply _)).pow 2) continuous_const
    · exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, J k) → ℂ)) (r := 1)).subset ?_
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    have h2 : ‖w ⟨k, i⟩‖ ^ 2 ≤ 1 := by
      rw [← hw.1 k]
      exact Finset.single_le_sum (f := fun j => ‖w ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (w ⟨k, i⟩)]
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover O hO
    (fun w hw => Set.mem_iUnion.2 (hcov w (hSsub hw)))
  refine ⟨t.card, fun a => (t.equivFin.symm a : C), ?_⟩
  intro z hz
  have hz0 := hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz0
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz0.1 k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  set c : K → ℂ := fun k => (((Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ) with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    rw [hcdef]
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hpos k)).ne'
  have hck : ∀ k, ‖c k‖ ^ 2 = (∑ i, ‖z ⟨k, i⟩‖ ^ 2)⁻¹ := by
    intro k
    rw [hcdef]
    simp only
    rw [Complex.norm_real, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (hpos k).le]
  have hmem := torusSmul_mem_mcPts' P hP c hc z hz
  have hw : torusSmul c z ∈ S := by
    have hm := hmem
    simp only [mcPts, Set.mem_ofPred_eq] at hm
    simp only [hS, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hm.2⟩
    have e1 : ∀ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ‖z ⟨k, i⟩‖ ^ 2 := fun i => by
      show ‖c k * z ⟨k, i⟩‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum, hck k,
      inv_mul_cancel₀ (hpos k).ne']
  have hcov' := ht hw
  simp only [Set.mem_iUnion] at hcov'
  obtain ⟨i, hi, hiO⟩ := hcov'
  refine ⟨t.equivFin ⟨i, hi⟩, c, hc, ?_, hmem⟩
  show torusSmul c z ∈ O ((t.equivFin.symm (t.equivFin ⟨i, hi⟩) : C))
  rw [Equiv.symm_apply_apply]
  exact hiO

end GlobalTheory.CompanionTheory.Ar.ChartCover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem basis_iff_unique_combinations : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  intro K W _ _ _ S n b
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at he
    obtain ⟨x, hx⟩ := he
    refine ⟨x, hx.symm, fun y hy => ?_⟩
    have h0 : ∑ i, (y - x) i • b i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  · rintro ⟨hb, huniq⟩
    refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩
    · obtain ⟨x, _, hx⟩ := huniq 0 S.zero_mem
      have hg0 : g = x := hx g hg.symm
      have h00 : (0 : Fin n → K) = x := hx 0 (by simp)
      rw [hg0, ← h00]
      rfl
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
    · obtain ⟨x, hx, _⟩ := huniq e he
      rw [hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_appellHumbert_frame_of_cubical :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  intro A _ _ Lr cs g u₀
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hT := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hT A _ Lr.L g u₀ Lr.isLB cs.t cs.isGen _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u₀.Λ u₀.discrete u₀.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u₀.ex, ex_add := u₀.ex_add, ex_onto := u₀.ex_onto, Λ := u₀.Λ, ker := u₀.ker,
            discrete := u₀.discrete, full := u₀.full, hol := u₀.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem conjugate_coe_eq_bar (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (τ : E →+* ℂ) (a : 𝓞 E) :
    ComplexEmbedding.conjugate τ (a : E) = τ (H.bar a : 𝓞 E) ∧ H.bar (H.bar a) = a := by
  constructor
  · rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  · apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
