module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M SectionPairing
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace BergmanIntegrable

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

def SectionInnerProductSpace (V : Submodule ℂ (Fin A.n → X → ℂ)) : Type := V

variable (V : Submodule ℂ (Fin A.n → X → ℂ))

instance : AddCommGroup (SectionInnerProductSpace V) := inferInstanceAs (AddCommGroup V)

instance : Module ℂ (SectionInnerProductSpace V) := inferInstanceAs (Module ℂ V)

instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (SectionInnerProductSpace V) :=
  inferInstanceAs (FiniteDimensional ℂ V)

def val : SectionInnerProductSpace V →ₗ[ℂ] (Fin A.n → X → ℂ) := V.subtype

theorem val_mem (v : SectionInnerProductSpace V) : val V v ∈ V := (show V from v).2

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  (W : Weight L) (dV : SmoothVolume A) (n : ℕ)


omit [CompactSpace X] [T2Space X] [BorelSpace X] in
theorem integral_pairing_self (s : Fin A.n → X → ℂ) :
    ∫ x, pairing W n s s x ∂dV.μ = ((sectionL2NormSq W dV n s : ℝ) : ℂ) := by
  simp_rw [pairing_self]
  exact integral_ofReal

theorem pairing_integrable {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) : Integrable (pairing W n s t) dV.μ := by
  have := dV.isProb
  exact integrableOn_univ.1
    ((pairing_continuous W n hs ht).continuousOn.integrableOn_compact isCompact_univ)

@[instance_reducible]
def core (hV : V ≤ L.sections n) : InnerProductSpace.Core ℂ (SectionInnerProductSpace V) where
  inner v w := ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
  conj_inner_symm v w := by
    show conj (∫ x, pairing W n (val V w) (val V v) x ∂dV.μ) =
      ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
    rw [← integral_conj]
    congr 1
    funext x
    simp only [pairing, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  re_inner_nonneg v := by
    show 0 ≤ RCLike.re (∫ x, pairing W n (val V v) (val V v) x ∂dV.μ)
    rw [integral_pairing_self, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun x ↦ ptNormSq_nonneg W n _ x
  add_left u v w := by
    show ∫ x, pairing W n (val V (u + v)) (val V w) x ∂dV.μ =
      ∫ x, pairing W n (val V u) (val V w) x ∂dV.μ + ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
    rw [← integral_add (pairing_integrable W dV n (hV (val_mem V u)) (hV (val_mem V w)))
      (pairing_integrable W dV n (hV (val_mem V v)) (hV (val_mem V w))), map_add]
    congr 1
    funext x
    simp only [pairing, Pi.add_apply, map_add, add_mul]
  smul_left u w r := by
    show ∫ x, pairing W n (val V (r • u)) (val V w) x ∂dV.μ =
      conj r * ∫ x, pairing W n (val V u) (val V w) x ∂dV.μ
    rw [← integral_const_mul, map_smul]
    congr 1
    funext x
    simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  definite v h := by
    have hs : val V v ∈ L.sections n := hV (val_mem V v)
    have hl : sectionL2NormSq W dV n (val V v) = 0 := by
      have h' : ((sectionL2NormSq W dV n (val V v) : ℝ) : ℂ) = 0 := by
        rw [← integral_pairing_self]
        exact h
      exact_mod_cast h'
    have hpt : ∀ x, ptNormSq W n (val V v) x = 0 := by
      intro x
      by_contra hx
      have := dV.isProb
      have := isOpenPosMeasure dV
      have hpos := (ptNormSq_continuous W n hs).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := dV.μ) (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
        (fun y ↦ ptNormSq_nonneg W n _ y) hx
      rw [sectionL2NormSq] at hl
      linarith
    have hzero : val V v = 0 := by
      funext j x
      by_cases hx : x ∈ (A.chart j).source
      · have h1 := pairing_eq W n hs hs j hx
        rw [pairing_self, hpt x, Complex.conj_mul'] at h1
        have h2 : ‖val V v j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) = 0 := by
          exact_mod_cast h1.symm
        have h3 := (mul_eq_zero.1 h2).resolve_right (Real.exp_pos _).ne'
        simpa using h3
      · exact hs.2.2 j x hx
    exact (Subtype.ext hzero : (show V from v) = 0)

theorem bergman_eq_sum (hV : V ≤ L.sections n) [FiniteDimensional ℂ V] :
    ∃ (m : ℕ) (u : Fin m → Fin A.n → X → ℂ), (∀ i, u i ∈ V) ∧
      ∀ x, bergman W dV V n x = ∑ i, ptNormSq W n (u i) x := by
  let cd : InnerProductSpace.Core ℂ (SectionInnerProductSpace V) := core V W dV n hV
  let : NormedAddCommGroup (SectionInnerProductSpace V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ (SectionInnerProductSpace V) := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ v w : SectionInnerProductSpace V,
      ⟪v, w⟫_ℂ = ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ := fun _ _ ↦ rfl
  have hnorm : ∀ v : SectionInnerProductSpace V, sectionL2NormSq W dV n (val V v) = ‖v‖ ^ 2 := fun v ↦ by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v]
    show _ = RCLike.re (∫ x, pairing W n (val V v) (val V v) x ∂dV.μ)
    rw [integral_pairing_self, RCLike.re_to_complex, Complex.ofReal_re]
  let b := stdOrthonormalBasis ℂ (SectionInnerProductSpace V)
  refine ⟨_, fun i ↦ val V (b i), fun i ↦ val_mem V (b i), fun x ↦ ?_⟩
  let ev : SectionInnerProductSpace V →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) x).comp ((LinearMap.proj (R := ℂ) (chartIdx A x)).comp (val V))
  set w := Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) with hw
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hpt : ∀ v : SectionInnerProductSpace V, ptNormSq W n (val V v) x = ‖ev v‖ ^ 2 * w := fun _ ↦ rfl
  let r : SectionInnerProductSpace V := ∑ i, conj (ev (b i)) • b i
  have hr : ∀ v, ev v = ⟪r, v⟫_ℂ := fun v ↦ by
    calc ev v = ev (∑ i, ⟪b i, v⟫_ℂ • b i) := by rw [b.sum_repr']
      _ = ∑ i, ev (b i) * ⟪b i, v⟫_ℂ := by

          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
      _ = ⟪r, v⟫_ℂ := by
          rw [sum_inner]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_smul_left, Complex.conj_conj]
  have hrn : ‖r‖ ^ 2 = ∑ i, ‖ev (b i)‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right r]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← inner_conj_symm, ← hr, Complex.norm_conj]
  have hsum : ∑ i, ptNormSq W n (val V (b i)) x = ‖r‖ ^ 2 * w := by
    rw [hrn, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hpt _
  have hle : ∀ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s ≤ ‖r‖ ^ 2 * w := by
    intro s
    let v : SectionInnerProductSpace V := s
    change ptNormSq W n (val V v) x / sectionL2NormSq W dV n (val V v) ≤ ‖r‖ ^ 2 * w
    rw [hpt, hnorm]
    have hcs : ‖ev v‖ ≤ ‖r‖ * ‖v‖ := by rw [hr]; exact norm_inner_le_norm r v
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · rw [div_le_iff₀ (by positivity)]
      have h2 : ‖ev v‖ ^ 2 ≤ (‖r‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
      nlinarith [mul_le_mul_of_nonneg_right h2 hw0]
  have hattain : ptNormSq W n (val V r) x / sectionL2NormSq W dV n (val V r) = ‖r‖ ^ 2 * w := by
    have hn : ‖⟪r, r⟫_ℂ‖ = ‖r‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hpt, hnorm, hr, hn]
    rcases eq_or_ne ‖r‖ 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [hsum]
  refine le_antisymm (ciSup_le hle) ?_
  exact le_ciSup_of_le ⟨_, forall_mem_range.2 hle⟩ (show V from r) hattain.ge

theorem proof : BergmanIntegrable.Statement := by
  intro D X _ _ _ _ _ A L W dV n V _ hV
  obtain ⟨m, u, hu, h⟩ := bergman_eq_sum V W dV n hV
  have := dV.isProb
  have hc : Continuous (bergman W dV V n) := by
    rw [show bergman W dV V n = fun x ↦ ∑ i, ptNormSq W n (u i) x from funext h]
    exact continuous_finsetSum _ fun i _ ↦ ptNormSq_continuous W n (hV (hu i))
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

end BergmanIntegrable

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGraph

variable {κ : Type} {D : ℕ}

theorem linForm_projMat [Fintype κ] (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem graphIdeal_isPrime {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι) : (graphIdeal P g).IsPrime :=
  RingHom.ker_isPrime _

variable {Ω : Type} [Field Ω]

theorem frame_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    x (e k) ≠ 0 := by
  intro h
  have hX : (X k : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h]
  rw [hF.free, Ideal.mem_bot] at hX
  exact X_ne_zero k hX

theorem genFibre_x'_ne_zero {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    G.x' ⟨Sum.inl (), j⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl (), j⟩ : MRing (Sum.elim (GlobalTheory κ) ι₂)) ∈ graphIdeal (coordIdeal ℤ x) g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  have h2 : (X ⟨(), j⟩ : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact MvPolynomial.C_eq_zero.1 h1
  rw [coordIdeal, RingHom.mem_ker] at h2
  simp [coneMap] at h2
  exact hj h2

def fibreChart {K₂ : Type} {ι₂ : K₂ → Type} (j : κ) :
    (k : FibreBlock (Sum.inr : K₂ → Unit ⊕ K₂)) → fibreIdx (Sum.elim (GlobalTheory κ) ι₂) Sum.inr k
  | ⟨Sum.inl _, _⟩ => j
  | ⟨Sum.inr k, h⟩ => absurd ⟨k, rfl⟩ h

theorem isChart_fibreChart {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) (fibreChart (ι₂ := ι₂) j) := by
  rintro ⟨(u | k), h⟩
  · cases u
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact genFibre_x'_ne_zero G j hj
  · exact absurd ⟨k, rfl⟩ h

end ProjFrameGraph

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GradedSubmodules.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    KH.IsMGraded S ι 𝓜 →
    IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M) ∧
      ∀ P : Ideal (MRingOver S ι), IsMultiHomogIdeal P →
        KH.IsMGraded S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) ∧
          KH.IsMGraded S ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ArithKleiman.trivial_hyps (P P0 : Ideal (MRing ι)) :
    ((constLine (ι := ι) 0).a = fun k => ((0 : K → ℕ) k : ℤ)) ∧ IsSemipositiveRel P0 P (constLine (ι := ι) 0) ∧
      MonomialsBounded P (constLine (ι := ι) 0) 0 ∧ IsConjInvariantH (constLine (ι := ι) 0) := by
  have hh : (constLine (ι := ι) 0).h = fun _ => 1 := by
    funext z
    show Real.exp (-0) = 1
    simp
  refine ⟨by funext k; rfl, ⟨?_, fun z _ w _ => ?_⟩, fun z _ μ hμ => ?_, fun z => by rw [hh]⟩
  · show ContDiffOn ℝ _ (fun _ => Real.exp (-(0 : ℝ))) _
    exact contDiffOn_const
  · have hf : (fun z => Real.log ((constLine (ι := ι) 0).h z)) = fun _ => (0 : ℝ) := by
      rw [hh]
      funext z
      simp
    rw [hf]
    simp [leviForm]
  · have h0 : ∀ p, μ p = 0 := by
      rintro ⟨k, i⟩
      have := hμ k
      simp only [Pi.zero_apply, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at this
      exact this i
    rw [hh]
    simp [h0]

theorem ArithKleiman.proof (hMix : MixedKleiman.Statement) : ArithKleiman.Statement := by
  intro K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW
  obtain ⟨ha, hs, hm, hc⟩ := ArithKleiman.trivial_hyps (ι := ι) P P0
  have h := hMix K ι P P0 (D + 1) A (constLine 0) 0 II hII (Nat.succ_pos D) hP hP0 hsemi hnef hconj hW ha hs hm hc
    (D + 1) le_rfl
  have hl : (fun i : Fin (D + 1) => if (i : ℕ) < D + 1 then A else constLine 0) = fun _ => A :=
    funext fun i => if_pos i.isLt
  rwa [hl] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenSESStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M'']
    (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
    (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
    KH.IsMGraded S ι 𝓜' → KH.IsMGraded S ι 𝓜 → KH.IsMGraded S ι 𝓜'' →
    KH.IsMGradedMap S ι 𝓜' 𝓜 g → KH.IsMGradedMap S ι 𝓜 𝓜'' h →
    Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
    ∀ d : K → ℤ, Subsingleton (KH.cechHc ι 𝓜' d 1) → GeneratedMod S ι 𝓜' d → GeneratedMod S ι 𝓜'' d →
      GeneratedMod S ι 𝓜 d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1Vanishing.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1GenerationDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S → (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → H1GenAmple S P N) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
