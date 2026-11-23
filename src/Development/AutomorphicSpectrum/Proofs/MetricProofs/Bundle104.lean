module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace FlLines

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_integralCombination_of_mem_completedLattice {A B D : Type} [Fintype A] [Fintype B] [Fintype D] (ca : A → ℤ) (bb : A → D → ℤ) (P : B → ℤ)
    (G : D → B → ℤ) :
    ∑ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (P w * ca a) * ∑ k, bb a k * G k w := by
  have h1 : ∀ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (ca a * bb a k) * (P w * G k w) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => by ring

theorem geoNum_polar {σ : Type} [Fintype σ] (n : ℕ) (V : Ideal (MRing ι)) (c : Fin n → σ → ℤ) (b : σ → K → ℤ) :
    geoNum n V (fun r k => ∑ a, c r a * b a k) =
      ∑ w : Fin n → σ, (∏ r, c r (w r)) * geoNum n V (fun r => b (w r)) := by
  classical
  induction n generalizing V with
  | zero =>
    have h : ∀ a a' : Fin 0 → K → ℤ, geoNum 0 V a = geoNum 0 V a' := fun a a' => by
      rw [Subsingleton.elim a a']
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact h _ _
  | succ n ih =>
    by_cases hV : IsRelevant V
    · rw [← (Fin.snocEquiv (fun _ => σ)).sum_comp, Fintype.sum_prod_type]
      simp only [geoNum, dif_pos hV]
      have hin : ∀ (a : σ) (w' : Fin n → σ),
          Fin.init (fun r => b ((Fin.snocEquiv (fun _ => σ)) (a, w') r)) = fun r => b (w' r) := by
        intro a w'
        funext r
        simp [Fin.init, Fin.snocEquiv]
      have hla : ∀ (a : σ) (w' : Fin n → σ), (Fin.snocEquiv (fun _ => σ)) (a, w') (Fin.last n) = a := by
        intro a w'
        simp [Fin.snocEquiv]
      have hca : ∀ (a : σ) (w' : Fin n → σ) (r : Fin n),
          (Fin.snocEquiv (fun _ => σ)) (a, w') r.castSucc = w' r := by
        intro a w' r
        simp [Fin.snocEquiv]
      have hi2 : Fin.init (fun r k => ∑ a, c r a * b a k) =
          fun (r : Fin n) k => ∑ a, c r.castSucc a * b a k := by
        funext r k
        simp [Fin.init]
      simp only [hin, hla, Fin.prod_univ_castSucc, hca, hi2]
      have e : ∀ (k : K) (f : Ideal (MRing ι) → ℤ),
          ∑ᶠ W ∈ divSupp V (X ⟨k, (hV k).choose⟩ : MRing ι), f W =
            ∑ W ∈ (divSupp_finite V (X ⟨k, (hV k).choose⟩ : MRing ι)).toFinset, f W :=
        fun k f => finsum_mem_eq_finite_toFinset_sum f (divSupp_finite _ _)
      simp only [e]
      simp only [ih _ (fun r => c r.castSucc)]
      rw [← exists_integralCombination_of_mem_completedLattice (fun a => c (Fin.last n) a) b (fun w' : Fin n → σ => ∏ r, c r.castSucc (w' r))]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    · have e : ∀ a, geoNum (n + 1) V a = 0 := fun a => by simp only [geoNum, dif_neg hV]
      simp [e]

theorem degSum_polar {σ : Type} [Fintype σ] (e : ℕ) (S : Set (Ideal (MRing ι))) (hS : S.Finite)
    (m : Ideal (MRing ι) → ℝ) (lam : σ → ℤ) (b : σ → K → ℤ) :
    ∑ w : Fin e → σ, (∏ r, (lam (w r) : ℝ)) * ∑ᶠ V ∈ S, m V * (geoNum e V (fun r => b (w r)) : ℝ) =
      ∑ᶠ V ∈ S, m V * (geoNum e V (fun _ k => ∑ a, lam a * b a k) : ℝ) := by
  have e' : ∀ f : Ideal (MRing ι) → ℝ, ∑ᶠ V ∈ S, f V = ∑ V ∈ hS.toFinset, f V :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hS
  have hp : ∀ V : Ideal (MRing ι), geoNum e V (fun _ k => ∑ a, lam a * b a k) =
      ∑ w : Fin e → σ, (∏ r, lam (w r)) * geoNum e V (fun r => b (w r)) :=
    fun V => geoNum_polar e V (fun _ => lam) b
  simp only [e', hp]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun w _ => ?_
  ring

end Geo

section Wt

variable {Ψ : Type} {N : ℕ}

def gapZ (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) : ℤ :=
  lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

theorem gap_cast (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) :
    gap (fun q => (lam q : ℝ)) p = (gapZ lam p : ℝ) := by
  unfold gap gapX gapZ
  split_ifs <;> simp

theorem formPoly_eq_toWt [Fintype Ψ] (n : ℕ) (ax ay : (Fin n → Ψ × Fin N) → ℝ)
    (h : ∀ lam : Ψ × Fin N → ℤ, ∑ w, (∏ r, (lam (w r) : ℝ)) * ax w = ∑ w, (∏ r, (gapZ lam (w r) : ℝ)) * ay w) :
    formPoly n ax = toWt (formPoly n ay) := by
  refine MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro x hx
  choose lam hlam using fun i => hx i (Set.mem_univ i)
  have hxl : x = fun p => (lam p : ℝ) := funext fun p => (hlam p).symm
  rw [hxl, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ n ax).2, (formPoly_isHomogeneous_and_eval _ n ay).2]
  simp only [gap_cast]
  simpa only [mul_comm] using h lam

end Wt

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def yDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ :=
  fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0

variable {Ψ N}

theorem deg_abel (lam : Ψ × Fin N → ℤ) (q : FlBlock Ψ N) :
    ∑ p, lam p * xDeg Ψ N p q = ∑ p, gapZ lam p * yDeg Ψ N p q := by
  classical
  obtain ⟨τ, i⟩ := q
  have hi : (i : ℕ) + 1 < N := by have := i.2; omega
  have hi0 : (i : ℕ) < N := by omega
  have hx : ∀ p : Ψ × Fin N, xDeg Ψ N p (τ, i) =
      (if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0) - (if p = (τ, ⟨(i : ℕ) + 1, hi⟩) then 1 else 0) := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [xDeg, Fin.ext_iff, eq_comm]
    · simp [xDeg, ht, Ne.symm ht]
  have hy : ∀ p : Ψ × Fin N, yDeg Ψ N p (τ, i) = if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0 := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [yDeg, Fin.ext_iff, eq_comm]
    · simp [yDeg, ht, Ne.symm ht]
  simp only [hx, hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [gapZ, hi]

theorem deg_abel_smul (lam : Ψ × Fin N → ℤ) :
    ∑ p, lam p • xDeg Ψ N p = ∑ p, gapZ lam p • yDeg Ψ N p := by
  funext q
  simpa [Finset.sum_apply] using deg_abel lam q

end Flag

end FlLines

open FlLines

theorem flLines_polys : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  intro hIn II hII Ψ _ _ _ N _ hP
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  refine ⟨formPoly_eq_toWt _ _ _ fun lam => ?_, formPoly_eq_toWt _ _ _ fun lam => ?_⟩
  · have h1 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => lam) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => gapZ lam) (yDeg Ψ N)
    rw [deg_abel_smul lam, h2] at h1
    exact h1.symm
  · set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
    have hS : S.Finite := divSupp_finite _ _
    set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
      fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
    have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
        ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
      fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
    have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
      FlagHeightMultilinear.isSmoothHerm_fsHerm
    have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
    have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
    have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
        fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
      funext _ k
      exact deg_abel lam k
    rw [hv, ← h2] at h1
    have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    simp only [ex, ey]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec

theorem isValueAt_aeval {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
    {y' : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} {σ : Type} {s : σ → Ω} {w : σ → ℂ}
    (hv : ∀ q, IsValueAt y' (s q) z (w q)) (f : MvPolynomial σ ℤ) :
    IsValueAt y' (aeval s f) z (eval w (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C n => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_intCast y' z n
  | add p q hp hq => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hp hq
  | mul_X p i hp => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_mul hp (hv i)

theorem mem_mcPts_of_specialise : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  intro K _ ι _ K' _ ι' _ Ω _ a y' z zt e s t hz hzt he ht has hv
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * s p := funext has
    have h1 : aeval s g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e s
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hval := isValueAt_aeval (w := fun q => t q.1 * zt q) hv g
    rw [h1] at hval
    have h2 := GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_zero hz hval
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h2
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_coord_ratio :
    ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω]
      (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k),
      z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 →
        y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  intro K' _ ι' _ Ω _ y' z k c hz hzc
  have hy : y' ⟨k, c⟩ ≠ 0 := by
    intro h0
    have hm : (X ⟨k, c⟩ : MRing ι') ∈ mCoordIdeal y' := by
      refine RingHom.mem_ker.2 ?_
      simp [mConeMap, h0]
    have h1 := hz.2 _ hm
    simp only [map_X, eval_X] at h1
    exact hzc h1
  refine ⟨hy, fun i => ⟨fun l => if l = k then 1 else 0, X ⟨k, i⟩, X ⟨k, c⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, c⟩, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hy
  · simp only [aeval_X]
    field_simp
  · simpa using hzc
  · simp only [map_X, eval_X]
    rw [div_eq_inv_mul]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section

noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem log_vertFactor_eq_re_holo : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p M U s hp hU hs hhol y₀ hy₀
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy₀)
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy₀)
  rw [VertFactorSmooth.vertFactor_eq D hp (hs y₀ hy₀) hG hH hdeg hrel hHz] at hpos
  have hGz : eval (s y₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, zero_div, norm_zero] at hpos
    exact lt_irrefl _ hpos
  set A := M.atlas with hA
  have HG := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol G
  have HH := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol H
  set Gf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) G) with hGf
  set Hf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) H) with hHf
  set W₁ : Set M.Xc := U ∩ {y | Hf y ≠ 0} with hW₁
  have hW₁o : IsOpen W₁ := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.isOpen_inter_ne A hU HH
  have hsub : W₁ ⊆ U := Set.inter_subset_left
  have mono : ∀ {f : M.Xc → ℂ} {S T : Set M.Xc}, T ⊆ S → A.HoloOn S f → A.HoloOn T f := by
    intro f S T hTS hf j
    exact (hf j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hTS))
  set g : M.Xc → ℂ := fun y => Gf y / Hf y with hg
  have Hg : A.HoloOn W₁ g :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_div_congr A hW₁o (mono hsub HG) (mono hsub HH)
      (fun y hy => hy.2) fun y _ => rfl
  set c : ℂ := g y₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero hGz hHz
  set V : Set M.Xc := W₁ ∩ {y | g y / c ∈ Complex.slitPlane} with hV
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy, hsl⟩
    have hcont : ContinuousAt (fun y => g y / c) y :=
      (GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.continuousAt_of_holoOn A Hg hy).div_const c
    filter_upwards [hW₁o.mem_nhds hy, hcont (Complex.isOpen_slitPlane.mem_nhds hsl)] with u h1 h2
    exact ⟨h1, h2⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, hHz⟩, ?_⟩
    show g y₀ / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]
    exact Complex.one_mem_slitPlane
  refine ⟨V, hVo, hy₀V, fun y hy => hsub hy.1, fun y => Complex.log (g y / c) + (Real.log ‖c‖ : ℂ), ?_, ?_⟩
  · intro j u hu
    have hgu : AnalyticAt ℂ (g ∘ (A.chart j).symm) u :=
      Hg j u ⟨hu.1, hu.2.1⟩
    have hsl : (g ∘ (A.chart j).symm) u / c ∈ Complex.slitPlane := hu.2.2
    have h1 : AnalyticAt ℂ (fun v => (g ∘ (A.chart j).symm) v / c) u := hgu.div analyticAt_const hc0
    have h2 := (h1.clog hsl).add (analyticAt_const (v := ((Real.log ‖c‖ : ℝ) : ℂ)))
    exact h2
  · rintro y ⟨hy, hsl⟩
    have hsl' : g y / c ∈ Complex.slitPlane := hsl
    have hgy : g y ≠ 0 := by
      intro h
      rw [h, zero_div] at hsl'
      exact Complex.slitPlane_ne_zero hsl' rfl
    rw [VertFactorSmooth.vertFactor_eq D hp (hs y (hsub hy)) hG hH hdeg hrel hy.2]
    show Real.log ‖g y‖ = (Complex.log (g y / c) + ((Real.log ‖c‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div (g y) c,
      Real.log_div (norm_ne_zero_iff.2 hgy) (norm_ne_zero_iff.2 hc0)]
    ring

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end
