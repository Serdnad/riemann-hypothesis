module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle001
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem sum_sq_comp_blockMap {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]
    {Kk : Type} {ιk : Kk → Type} [∀ k, Fintype (ιk k)]
    {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v)
    (z : (Σ k, ι k) → ℂ) (k' : Kk) :
    ∑ m, ‖(z ∘ v) ⟨k', m⟩‖ ^ 2 = ∑ i, ‖z ⟨κ k', i⟩‖ ^ 2 := by
  obtain ⟨hκ, hvi, hblk, hsurj⟩ := hv
  have key : ∀ m : ιk k', ∃ i : ι (κ k'), v ⟨k', m⟩ = ⟨κ k', i⟩ := by
    intro m
    have h := hblk ⟨k', m⟩
    rcases hh : v ⟨k', m⟩ with ⟨c, i⟩
    rw [hh] at h
    simp only at h
    subst h
    exact ⟨i, rfl⟩
  choose g hg using key
  have hinj : Function.Injective g := by
    intro m m' hmm
    have h : v ⟨k', m⟩ = v ⟨k', m'⟩ := by rw [hg, hg, hmm]
    have h' := hvi h
    simpa using h'
  have hsur : Function.Surjective g := by
    intro i
    obtain ⟨⟨k'', m⟩, hp⟩ := hsurj ⟨κ k', i⟩ ⟨k', rfl⟩
    have h := hblk ⟨k'', m⟩
    rw [hp] at h
    have hk : k'' = k' := (hκ h).symm
    subst hk
    refine ⟨m, ?_⟩
    rw [hg] at hp
    simpa using hp
  have hbij : Function.Bijective g := ⟨hinj, hsur⟩
  rw [← hbij.sum_comp (fun i => ‖z ⟨κ k', i⟩‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.comp_apply, hg]

theorem fsHerm_h_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (a : K → ℤ) (z : (Σ k, ι k) → ℂ), IsBlockMap κ v → (∀ k, a k ≠ 0 → k ∈ Set.range κ) → (fsHerm ι a).h z = (fsHerm ιk fun k => a (κ k)).h (z ∘ v) := by
  intro K _ ι _ Kk _ ιk _ κ v a z hv ha
  rw [fsHerm_h, fsHerm_h]
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_
  · intro k hk
    have h0 : a k = 0 := by
      by_contra h
      exact hk (ha k h)
    simp [h0]
  · intro k'
    rw [sum_sq_comp_blockMap hv z k']

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.IntegralKernel

theorem exists_clear_denominators {g : ℕ} (w : Fin g → ℚ) :
    ∃ (D : ℤ) (v : Fin g → ℤ), D ≠ 0 ∧ ∀ i, (v i : ℚ) = (D : ℚ) * w i := by
  classical
  have hdvd : ∀ i, ∃ k : ℤ, (∏ j, ((w j).den : ℤ)) = ((w i).den : ℤ) * k := fun i =>
    Finset.dvd_prod_of_mem (fun j => ((w j).den : ℤ)) (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨∏ j, ((w j).den : ℤ), fun i => (w i).num * k i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_nz
  · intro i
    rw [hk i]
    push_cast
    have h := Rat.mul_den_eq_num (w i)
    rw [← h]
    ring

theorem cast_mulVec {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) (i : Fin g) :
    (((S *ᵥ v) i : ℤ) : ℚ) = ((S.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ))) i := by
  simp [Matrix.mulVec, dotProduct]

theorem exists_smul_eq_mulVec (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) (hS : Sᵀ = S)
    (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  classical
  let Sq : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ)
  let uq : Fin g → ℚ := fun i => (u i : ℚ)
  have hSq : Sqᵀ = Sq := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at this
    simp [Sq, this]

  have hker : ∀ w : Fin g → ℚ, Sq *ᵥ w = 0 → uq ⬝ᵥ w = 0 := by
    intro w hw
    obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators w
    have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • w := by
      funext j; simp [hv j]
    have hSv : S *ᵥ v = 0 := by
      funext i
      have h1 := cast_mulVec S v i
      rw [hvq, Matrix.mulVec_smul] at h1
      have h2 : (((S *ᵥ v) i : ℤ) : ℚ) = 0 := by
        rw [h1]
        change ((D : ℚ) • (Sq *ᵥ w)) i = 0
        rw [hw]; simp
      exact_mod_cast h2
    have h0 := hu v hSv
    have h1 : ((u ⬝ᵥ v : ℤ) : ℚ) = (D : ℚ) * (uq ⬝ᵥ w) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hv, uq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simpa [hDq] using h1.symm
  let f : (Fin g → ℚ) →ₗ[ℚ] (Fin g → ℚ) := Sq.mulVecLin
  let φ : Module.Dual ℚ (Fin g → ℚ) :=
    { toFun := fun w => uq ⬝ᵥ w
      map_add' := fun a b => dotProduct_add uq a b
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hφ : φ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hker w (by simpa [f] using hw)
  obtain ⟨ψ, hψ⟩ := hφ
  let c : Fin g → ℚ := fun i => ψ (Pi.single i 1)
  have hψc : ∀ w, ψ w = c ⬝ᵥ w := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]

    simp [map_sum, c, dotProduct, mul_comm]
  have hu_eq : uq = Sq *ᵥ c := by
    funext i
    have h1 : φ (Pi.single i 1) = uq i := by
      change uq ⬝ᵥ Pi.single i 1 = uq i
      simp
    have h2 : φ (Pi.single i 1) = ψ (Sq *ᵥ Pi.single i 1) := by
      rw [← hψ]; rfl
    rw [← h1, h2, hψc, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSq]
    simp
  obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators c
  refine ⟨D, v, hD, ?_⟩
  funext i
  have h1 := cast_mulVec S v i
  have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • c := by
    funext j; simp [hv j]
  rw [hvq, Matrix.mulVec_smul] at h1
  have h2 : (((D • u) i : ℤ) : ℚ) = (((S *ᵥ v) i : ℤ) : ℚ) := by
    rw [h1]
    change _ = ((D : ℚ) • (Sq *ᵥ c)) i
    rw [← hu_eq]
    simp [uq]
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.IntegralKernel
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.SolveCoeff

private def colMat {g m : ℕ} (v : Fin m → Fin g → ℂ) : Matrix (Fin g) (Fin m) ℂ :=
  Matrix.of fun a i => v i a

private lemma colMat_eq_mul {g m : ℕ} (M f : Fin m → Fin g → ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i, f i = ∑ j, C j i • M j) : colMat f = colMat M * C := by
  ext a i
  simp only [colMat, Matrix.of_apply, Matrix.mul_apply]
  rw [h i]
  simp [Finset.sum_apply, mul_comm]

private lemma solve_eq {g m : ℕ} (A : Matrix (Fin g) (Fin m) ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (hd : (Aᴴ * A).det ≠ 0) : (Aᴴ * A)⁻¹ * Aᴴ * (A * C) = C := by
  have hu : IsUnit (Aᴴ * A).det := isUnit_iff_ne_zero.mpr hd
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

open scoped ComplexOrder in
private lemma gram_det_ne {g m : ℕ} (M : Fin m → Fin g → ℂ) (h : LinearIndependent ℂ M) :
    ((colMat M)ᴴ * colMat M).det ≠ 0 := by
  have hinj : Function.Injective (colMat M).mulVec := by
    intro x y hxy
    have hz : ∑ i, (x - y) i • M i = 0 := by
      funext a
      have h1 : (colMat M *ᵥ (x - y)) a = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      simpa [Matrix.mulVec, dotProduct, colMat, mul_comm, Finset.sum_apply] using h1
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ hz i)
  have hinj2 : Function.Injective ((colMat M)ᴴ * colMat M).mulVec := by
    intro x y hxy
    apply hinj
    have h0 : ((colMat M)ᴴ * colMat M) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).1 h0
    rw [Matrix.mulVec_sub] at h1
    exact sub_eq_zero.1 h1
  have := (Matrix.mulVec_injective_iff_isUnit).1 hinj2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

private lemma cat_mul {X : Type} [TopologicalSpace X] {x : X} {l k r : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} {B : X → Matrix (Fin k) (Fin r) ℂ}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) : ContinuousAt (fun z => A z * B z) x := by
  have c : Continuous (fun p : Matrix (Fin l) (Fin k) ℂ × Matrix (Fin k) (Fin r) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact c.continuousAt.comp (hA.prodMk hB)

private lemma cat_conj {X : Type} [TopologicalSpace X] {x : X} {l k : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z)ᴴ) x := by
  have c : Continuous (fun N : Matrix (Fin l) (Fin k) ℂ => Nᴴ) :=
    continuous_id.matrix_conjTranspose
  exact c.continuousAt.comp hA

private lemma cat_det {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).det) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
  exact c.continuousAt.comp hA

private lemma cat_adj {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).adjugate) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.adjugate) :=
    continuous_id.matrix_adjugate
  exact c.continuousAt.comp hA

private lemma colMat_continuousAt {n g m : ℕ} (M : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (h : ∀ i, ContinuousAt (fun z => M z i) 0) : ContinuousAt (fun z => colMat (M z)) 0 := by
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_
  exact (continuous_apply a).continuousAt.comp (h i)

theorem coeff_continuous (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (T₀ : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i, ContinuousAt (fun z => M z i) 0)
    (hf : ∀ i, ContinuousAt (fun z => f z i) 0) (hli : LinearIndependent ℂ (M 0))
    (h0 : ∀ i, f 0 i = ∑ j, T₀ j i • M 0 j)
    (hspan : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) :
    ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  have hA : ContinuousAt (fun z => colMat (M z)) 0 := colMat_continuousAt M hM
  have hF : ContinuousAt (fun z => colMat (f z)) 0 := colMat_continuousAt f hf
  have hG : ContinuousAt (fun z => (colMat (M z))ᴴ * colMat (M z)) 0 :=
    cat_mul (cat_conj hA) hA
  have hdet : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z)).det) 0 := cat_det hG
  have hd0 := gram_det_ne (M 0) hli
  have hinv : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹) 0 := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hdet.inv₀ hd0).smul (cat_adj hG)
  refine ⟨fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z),
    cat_mul (cat_mul hinv (cat_conj hA)) hF, ?_, ?_⟩
  · show ((colMat (M 0))ᴴ * colMat (M 0))⁻¹ * (colMat (M 0))ᴴ * colMat (f 0) = T₀
    rw [colMat_eq_mul (M 0) (f 0) T₀ h0]
    exact solve_eq _ _ hd0
  · filter_upwards [hspan, hdet.eventually_ne hd0] with z hz hdz i
    have hc : ∀ i, ∃ c : Fin m → ℂ, ∑ j, c j • M z j = f z i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hz i)
    choose c hc using hc
    have hcol : colMat (f z) = colMat (M z) * Matrix.of (fun j i => c i j) :=
      colMat_eq_mul (M z) (f z) _ (fun i => by simpa using (hc i).symm)
    have hT : ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z)
        = Matrix.of (fun j i => c i j) := by
      rw [hcol]; exact solve_eq _ _ hdz
    simp only [hT, Matrix.of_apply]
    exact (hc i).symm

end GlobalTheory.CompanionTheory.Ar.SolveCoeff
end
