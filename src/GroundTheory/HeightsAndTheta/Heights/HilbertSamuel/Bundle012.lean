module

public import GroundTheory.HeightsAndTheta.Heights.Bundle002
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder

noncomputable section

section Had

variable {K : Type*} [Field K] [NumberField K]

def fibreNorm (E : HermitianBundle K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ‖FibreSpace.equiv E.metric σ x‖

abbrev bundleRank (E : HermitianBundle K) : ℕ := Module.finrank (𝓞 K) E.carrier


structure BoundedInjection (E' E : HermitianBundle K) (A : (K →+* ℂ) → ℝ) where

  toLinearMap : E'.carrier →ₗ[𝓞 K] E.carrier
  injective : Function.Injective toLinearMap
  norm_le : ∀ (σ : K →+* ℂ) (x : Fibre σ E'.carrier),
    fibreNorm E σ (toLinearMap.lTensor (ComplexAt σ) x) ≤ A σ * fibreNorm E' σ x

structure ShortFamily (E : HermitianBundle K) (lam : (K →+* ℂ) → ℝ) where

  vec : Fin (bundleRank E) → E.carrier
  linearIndependent : LinearIndependent (𝓞 K) vec
  norm_le : ∀ (σ : K →+* ℂ) (i : Fin (bundleRank E)),
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] vec i) ≤ lam σ

end Had

section HadExamples

variable (K : Type*) [Field K] [NumberField K]

theorem fibreNorm_standard_single (n : ℕ) (σ : K →+* ℂ) (i : Fin n) :
    fibreNorm (HermitianBundle.standard K n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] Pi.single i 1) = 1 := by
  have h := norm_fibreVec_sq (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)
  rw [HermitianMetric.standard_inner_single, Complex.one_re] at h
  have h0 := norm_nonneg (fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1))
  have h1 : ‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ = 1 := by
    nlinarith [sq_nonneg (‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ - 1)]
  exact h1

theorem bundleRank_standard (n : ℕ) : bundleRank (HermitianBundle.standard K n) = n :=
  Module.finrank_fin_fun (𝓞 K)

def ShortFamily.standard (n : ℕ) : ShortFamily (HermitianBundle.standard K n) (fun _ ↦ 1) where
  vec i := (Pi.basisFun (𝓞 K) (Fin n) (Fin.cast (bundleRank_standard K n) i) : Fin n → 𝓞 K)
  linearIndependent :=
    (Pi.basisFun (𝓞 K) (Fin n)).linearIndependent.comp _ (Fin.cast_injective _)
  norm_le σ i := by
    rw [Pi.basisFun_apply]
    exact (fibreNorm_standard_single K n σ _).le


variable {K} in
def BoundedInjection.id (E : HermitianBundle K) : BoundedInjection E E (fun _ ↦ 1) where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  norm_le σ x := by rw [LinearMap.lTensor_id, LinearMap.id_apply, one_mul]

end HadExamples

def LogDetDerivative.Statement : Prop :=
  ∀ (m : ℕ) (G G' : ℝ → Matrix (Fin m) (Fin m) ℂ), (∀ t, (G t).PosDef) →
    (∀ t i j, HasDerivAt (fun s ↦ G s i j) (G' t i j) t) →
    ∀ t, HasDerivAt (fun s ↦ -(1 / 2) * Real.log (G s).det.re)
      (-(1 / 2) * ((G t)⁻¹ * G' t).trace.re) t

def GridSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    (fun n : ℕ ↦ (∑ a ∈ Finset.range n,
        (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D

def unitBallVolume (R : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin R)) 1)).toReal

structure ShortLatticeBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (La : Submodule ℤ V) (c : ℝ) where

  vec : Fin (Module.finrank ℝ V) → V
  mem : ∀ i, vec i ∈ La
  linearIndependent : LinearIndependent ℝ vec
  norm_le : ∀ i, ‖vec i‖ ≤ c

def LatticeCount.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (c b : ℝ), ShortLatticeBasis La c → 0 ≤ b →
      {x : V | x ∈ La ∧ ‖x‖ ≤ b}.Finite ∧
      ({x : V | x ∈ La ∧ ‖x‖ ≤ b}.ncard : ℝ) * ZLattice.covolume La ≤
        unitBallVolume (Module.finrank ℝ V) *
          (b + (Module.finrank ℝ V : ℝ) * c) ^ Module.finrank ℝ V

def SmallBallVolume.Statement : Prop := ∀ R : ℕ, unitBallVolume R ≤ 6

def MinkowskiCount.Statement : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (ρ : ℝ), 0 < ρ →
      Real.log (unitBallVolume (Module.finrank ℝ V)) +
          (Module.finrank ℝ V : ℝ) * Real.log (ρ / 2) - Real.log (ZLattice.covolume La) ≤
        Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ)) ∧
  ∀ R : ℕ, (2 / Real.sqrt R) ^ R ≤ unitBallVolume R

def Packing.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (La : Submodule ℤ V) [Module.Finite ℤ La]
    (S : Finset V) (b : ℝ), 0 ≤ b → (∀ s ∈ S, s ∈ La) → (∀ s ∈ S, ‖s‖ ≤ 1) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-b) ≤ ‖s - t‖) →
      Real.log S.card ≤ Module.finrank ℤ La * (b + Real.log 3)

section LatticeExamples

end LatticeExamples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenericFibre.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (D : ℕ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Ix κ) ℚ ⧸
          (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) = ((D + 1 : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsRank.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (n : ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
      (Module.finrank ℤ (sec ℤ x n) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenFibreHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω),
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section ValueSpan

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) : Submodule ℚ Ω :=
  Submodule.span ℚ {s | ∃ g : MRing ι, IsMultiHomog g a ∧ aeval y g = s}

end ValueSpan

def HilbFnValueSpan.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun k => (a k : ℤ)) =
      (Module.finrank ℚ (valueSpan y a) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace P1

theorem isSmoothHerm_fs {κ : Type} [Fintype κ] :
    IsSmoothHerm (HermLine.ofCone (fsMetric (ι := Ix κ))) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FSLevi.nsq (J := Ix κ)) := by
    unfold FSLevi.nsq
    exact ContDiff.sum fun p _ ↦ ((FSLevi.reP p).contDiff.pow 2).add ((FSLevi.imaginary p).contDiff.pow 2)
  have he : (HermLine.ofCone (fsMetric (ι := Ix κ))).h = fun z ↦ Real.sqrt (FSLevi.nsq z) := by
    funext z
    simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply,
      FSLevi.imaginaryPart_apply, FSLevi.norm_sq_eq]
  unfold IsSmoothHerm
  rw [he]
  refine hN.contDiffOn.sqrt fun z hz ↦ (FSLevi.nsq_pos ?_).ne'
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 ↦ hi (congrFun h0 _)

end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]

theorem weight_blockWeight_apply (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) e k = ∑ i, e ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem blockWeight_unit (v : Σ _ : Unit, ∀ k, ι k) :
    blockWeight (fun _ : Unit => ∀ k, ι k) v = fun _ => 1 := by
  funext u
  simp [blockWeight]


omit [∀ k, Fintype (ι k)] in
theorem segreMap_isMultiHomog {m : ℕ} {p : MRing (fun _ : Unit => ∀ k, ι k) F}
    (hp : IsWeightedHomogeneous (blockWeight (fun _ : Unit => ∀ k, ι k)) p (fun _ => m)) :
    IsWeightedHomogeneous (blockWeight ι) (segreMap F p) (fun _ => m) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial d r hr =>
    have hX : ∀ v : Σ _ : Unit, ∀ k, ι k,
        IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
      intro v
      have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
        (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩)
        (fun k _ => isWeightedHomogeneous_X _ _ _)
      convert h using 1
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have hsum : ∑ v ∈ d.support, d v = m := by
      have h := congrFun hr ()
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [blockWeight_unit, Finset.sum_apply] using h
    have hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m := by
      funext k
      simp [Finset.sum_apply, hsum]
    unfold segreMap
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ r
    rw [← hdeg]
    exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _


omit [DecidableEq K] in
theorem monomial_mem_map_segreMap (m : ℕ) :
    ∀ e : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = m) →
      monomial e (1 : F) ∈ (weightedHomogeneousSubmodule F
        (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map (segreMap F).toLinearMap := by
  classical
  induction m with
  | zero =>
    intro e he
    have he0 : e = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)
    subst he0
    refine ⟨1, ?_, ?_⟩
    · exact isWeightedHomogeneous_one _ _
    · simp
  | succ m ih =>
    intro e he
    have hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)
      exact ⟨i, hi⟩
    choose f hf using hne
    set s : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def
    have hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0 := fun k i => by simp [hs_def]
    have hse : s ≤ e := by
      rw [Finsupp.le_def]
      rintro ⟨k, i⟩
      rw [hs]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hf k)
      · exact Nat.zero_le _
    have hadd : e - s + s = e := tsub_add_cancel_of_le hse
    have he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m := fun k => by
      have h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1 := by
        rw [← Finset.sum_add_distrib, ← he k]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      have h2 : ∑ i, s ⟨k, i⟩ = 1 := by simp [hs]
      omega
    obtain ⟨g, hg, hge⟩ := ih (e - s) he'
    have hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [hs]
    refine ⟨g * X ⟨(), f⟩, ?_, ?_⟩
    · have h := (show IsWeightedHomogeneous _ g _ from hg).mul
        (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)
      rw [blockWeight_unit] at h
      exact h
    · simp only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢
      rw [hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]

theorem map_segreMap_weightedHomogeneousSubmodule (m : ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map
        (segreMap F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (fun _ => m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact segreMap_isMultiHomog F hp
  · intro p hp
    have hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m) := hp
    clear hp
    induction hp' using IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      have hd : ∀ k, ∑ i, d ⟨k, i⟩ = m := fun k => by
        rw [← weight_blockWeight_apply, hr]
      have h := Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)
      rwa [smul_monomial, smul_eq_mul, mul_one] at h

def segreQuotMap (q : Ideal (MRing ι F)) :
    MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q →ₐ[F] MRing ι F ⧸ q :=
  Ideal.quotientMapₐ (I := segrePrime F q) q (segreMap F) fun _ h => h


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreQuotMap_injective (q : Ideal (MRing ι F)) : Function.Injective (segreQuotMap F q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk q (segreMap F x) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))

def segreGradedPieceEquiv (q : Ideal (MRing ι F)) (m : ℕ) :
    gradedPiece (segrePrime F q) (fun _ : Unit => m) ≃ₗ[F] gradedPiece q (fun _ : K => m) :=
  have hinj : Function.Injective (segreQuotMap F q).toLinearMap := segreQuotMap_injective F q
  have hmap : (gradedPiece (segrePrime F q) (fun _ : Unit => m)).map (segreQuotMap F q).toLinearMap =
      gradedPiece q (fun _ : K => m) := by
    have hc : (segreQuotMap F q).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (segrePrime F q)).toLinearMap =
        (Ideal.Quotient.mkₐ F q).toLinearMap ∘ₗ (segreMap F).toLinearMap :=
      LinearMap.ext fun _ => rfl
    unfold gradedPiece
    rw [← Submodule.map_comp, hc, Submodule.map_comp, map_segreMap_weightedHomogeneousSubmodule]
  (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap)

theorem SegreHilb.proof : SegreHilb.Statement := by
  intro F _ K _ _ _ ι _ q n
  unfold hilbFn
  by_cases hn : 0 ≤ n
  · rw [if_pos (fun _ => hn), if_pos (fun _ => hn)]
    exact congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq
  · rw [if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
