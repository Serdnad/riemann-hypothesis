module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

@[expose] public section

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd

theorem periodic_mul {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (i : Fin r) (k : ℕ)
    (m : Fin r → ℕ) : v (m + (Pi.single i (k * l) : Fin r → ℕ)) = v m := by
  induction k with
  | zero => simp
  | succ k ih => rw [add_mul, one_mul, Pi.single_add, ← add_assoc, hv, ih]

theorem reduce_on {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (s : Finset (Fin r))
    (m : Fin r → ℕ) : v m = v (fun i => if i ∈ s then m i % l else m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [ih]
    have hfun : (fun i => if i ∈ s then m i % l else m i) =
        (fun i => if i ∈ insert a s then m i % l else m i) +
          (Pi.single a (m a / l * l) : Fin r → ℕ) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha, Nat.mod_add_div']
      · simp [hj, Pi.single_eq_of_ne hj]
    rw [hfun, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.periodic_mul hv]

theorem bddW_of_periodic : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l →
    (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  intro r l v hl hv
  refine ⟨∑ f : Fin r → Fin l, |((v fun i => (f i : ℕ) : ℚ) : ℝ)|, fun m => ?_⟩
  have hm : v m = v fun i => ((⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l) : ℕ) := by
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.reduce_on hv Finset.univ m
  rw [hm]
  exact Finset.single_le_sum (f := fun f : Fin r → Fin l => |((v fun i => (f i : ℕ) : ℚ) : ℝ)|)
    (fun f _ => abs_nonneg _) (Finset.mem_univ fun i => (⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l))

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity

variable {r : ℕ}

theorem update_add_single (i : Fin r) (m : Fin r → ℕ) (n k : ℕ) :
    Function.update (m + (Pi.single i n : Fin r → ℕ)) i k = Function.update m i k := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem update_self_add (i : Fin r) (m : Fin r → ℕ) (e : ℕ) :
    Function.update m i (m i + e) = m + (Pi.single i e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem partialSum_succ (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    partialSum i v (m + Pi.single i 1) = partialSum i v m + v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_succ, Function.update_eq_self]

theorem partialSum_of_zero (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (h : m i = 0) :
    partialSum i v m = 0 := by
  simp [partialSum, h]

theorem partialSumMean_add_single_one (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    meanP l i v (m + Pi.single i 1) = meanP l i v m := by
  simp only [meanP, update_add_single]

theorem partialSum_period {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : GoodAt l i v)
    (m : Fin r → ℕ) : partialSum i v (m + Pi.single i l) = partialSum i v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_add]
  have h2 : ∑ e ∈ Finset.range l, v (Function.update m i (m i + e)) = 0 := by
    simp only [update_self_add]
    exact h.2 m
  rw [h2, add_zero]

theorem partialSum_bound {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (h : GoodAt l i v) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m, |(v m : ℝ)| ≤ C) :
    ∀ m, |(partialSum i v m : ℝ)| ≤ l * C := by
  have key : ∀ n, ∀ m : Fin r → ℕ, m i = n → |(partialSum i v m : ℝ)| ≤ l * C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm
      by_cases hn : n < l
      · simp only [partialSum, hm]
        push_cast
        calc |∑ k ∈ Finset.range n, (v (Function.update m i k) : ℝ)|
            ≤ ∑ k ∈ Finset.range n, |(v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
          _ = n * C := by simp
          _ ≤ l * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) hC0
      · rw [not_lt] at hn
        have hmm : m = Function.update m i (n - l) + Pi.single i l := by
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
            omega
          · simp [Function.update_apply, hj, Pi.single_apply]
        rw [hmm, partialSum_period h]
        exact ih (n - l) (by omega) _ (by simp)
  exact fun m => key (m i) m rfl

theorem abs_partialSumMean_le {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    {K : ℝ} (hK : ∀ m, |(partialSum i v m : ℝ)| ≤ K) (m : Fin r → ℕ) :
    |(meanP l i v m : ℝ)| ≤ K := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  simp only [meanP]
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  calc |∑ k ∈ Finset.range l, (partialSum i v (Function.update m i k) : ℝ)|
      ≤ ∑ k ∈ Finset.range l, |(partialSum i v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range l, K := Finset.sum_le_sum fun k _ => hK _
    _ = K * l := by simp [mul_comm]

theorem summable_cast_mul {α : Type*} (w : α → ℚ) (K : ℝ) (hw : ∀ m, |(w m : ℝ)| ≤ K)
    {g : α → ℂ} (hg : Summable g) : Summable (fun m => (w m : ℂ) * g m) := by
  have hn : Summable (fun m => ‖g m‖) := by
    first
      | exact hg.norm
      | exact summable_norm_iff.mpr hg
  refine Summable.of_norm_bounded (hn.mul_left K) (fun m => ?_)
  rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hw m) (norm_nonneg _)

theorem stepIdentity (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (g : (Fin r → ℕ) → ℂ)
    (hl : 0 < l) (hgood : GoodAt l i v) (hv : BddW v) (hg : Summable g) :
    ∑' m, (v m : ℂ) * g m = ∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m := by
  obtain ⟨C, hC⟩ := hv
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlC : 0 ≤ (l : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  have hPS := partialSum_bound hl hgood hC0 hC
  have hMP : ∀ m, |(meanP l i v m : ℝ)| ≤ l * C := abs_partialSumMean_le hl hPS
  set δ : Fin r → ℕ := Pi.single i 1 with hδ
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have hBb : ∀ m, |(Bop l i v m : ℝ)| ≤ l * C := by
    intro m
    unfold Bop
    split_ifs
    · exact hMP m
    · rw [Rat.cast_zero, abs_zero]
      exact hlC
  have hAb : ∀ m, |(Aop l i v m : ℝ)| ≤ 2 * (l * C) := by
    intro m
    simp only [Aop, Rat.cast_sub]
    calc _ ≤ |(partialSum i v (m + Pi.single i 1) : ℝ)| + |(meanP l i v m : ℝ)| := hsub _ _
      _ ≤ l * C + l * C := add_le_add (hPS _) (hMP m)
      _ = _ := by ring
  let T : (Fin r → ℕ) → ℂ := fun m =>
    ((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℂ) * g m
  have hTb : ∀ m, |((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℝ)| ≤ 3 * (l * C) := by
    intro m
    push_cast
    calc _ ≤ |(partialSum i v m : ℝ) - meanP l i v m| + |(Bop l i v m : ℝ)| := abs_add_le _ _
      _ ≤ (|(partialSum i v m : ℝ)| + |(meanP l i v m : ℝ)|) + |(Bop l i v m : ℝ)| :=
          add_le_add (hsub _ _) le_rfl
      _ ≤ (l * C + l * C) + l * C := add_le_add (add_le_add (hPS m) (hMP m)) (hBb m)
      _ = _ := by ring
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + δ) := add_left_injective δ
  have hgs : Summable (fun m => g (m + δ)) := hg.comp_injective hinj
  have hfd : Summable (fd i g) := by
    have : fd i g = fun m => g (m + δ) - g m := rfl
    rw [this]
    exact hgs.sub hg
  have hsB : Summable (fun m => (Bop l i v m : ℂ) * g m) := summable_cast_mul _ _ hBb hg
  have hsA : Summable (fun m => (Aop l i v m : ℂ) * fd i g m) := summable_cast_mul _ _ hAb hfd
  have hsT : Summable T := summable_cast_mul _ _ hTb hg
  have hsT' : Summable (fun m => T (m + δ)) := hsT.comp_injective hinj
  have hT0 : ∀ m, m i = 0 → T m = 0 := by
    intro m hm
    simp [T, Bop, hm, partialSum_of_zero i v m hm]
  have hBs : ∀ m, Bop l i v (m + δ) = 0 := by
    intro m
    simp [Bop, δ]
  have hpt : ∀ m, (v m : ℂ) * g m =
      ((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m) := by
    intro m
    have h1 := partialSum_succ i v m
    have h2 := partialSumMean_add_single_one l i v m
    have h3 : Bop l i v (m + Pi.single i 1) = 0 := hBs m
    simp only [T, Aop, fd, hδ, h1, h2, h3]
    push_cast
    ring
  have hshift : ∑' m, T (m + δ) = ∑' m, T m := by
    refine hinj.tsum_eq (f := T) ?_
    intro m hm
    have hmi : m i ≠ 0 := fun h0 => hm (hT0 m h0)
    refine ⟨m - δ, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, δ, Pi.single_eq_same]
      omega
    · simp [δ, Pi.single_apply, hj]
  calc ∑' m, (v m : ℂ) * g m
      = ∑' m, (((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m)) :=
        tsum_congr hpt
    _ = (∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m) +
          (∑' m, T (m + δ) - ∑' m, T m) := by
        rw [(hsB.sub hsA).tsum_add (hsT'.sub hsT), hsB.tsum_sub hsA, hsT'.tsum_sub hsT]
    _ = _ := by rw [hshift, sub_self, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma linF_line (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) (i : Fin r) (t : ℝ) :
    linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) = linF a b j x + t * a j i := by
  have h : ∀ k, a j k * (x + t • (Pi.single i 1 : Fin r → ℝ)) k
      = a j k * x k + (if k = i then t * a j i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; ring
    · simp [Pi.single_apply, hk]
  simp only [linF, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma linF_pos (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (j : ι) (y : Fin r → ℝ) (hy : ∀ k, 0 ≤ y k) : 0 < linF a b j y := by
  have : 0 ≤ ∑ i, a j i * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (hy i)
  have := hb j
  unfold linF
  linarith

lemma hasDerivAt_factor (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : ℂ) (j : ι) (i : Fin r)
    (x : Fin r → ℝ) (τ : ℝ)
    (hpos : 0 < linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ))) :
    HasDerivAt (fun t : ℝ => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ w)
      ((a j i : ℂ) * (w * ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (w - 1))) τ := by
  have hlin : HasDerivAt (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) (a j i) τ := by
    have : (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)))
        = fun t : ℝ => linF a b j x + t * a j i := by
      funext t; exact linF_line a b j x i t
    rw [this]
    simpa using ((hasDerivAt_id τ).mul_const (a j i)).const_add (linF a b j x)
  have hC := hlin.ofReal_comp
  have hslit : ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hpos
  have hpow := ((hasDerivAt_id _).cpow_const (c := w) hslit)
  refine (HasDerivAt.scomp τ hpow hC).congr_deriv ?_
  simp only [id, mul_one, smul_eq_mul]
  rfl

lemma hasDerivAt_Fr (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k) :
    HasDerivAt (fun t : ℝ => Fr a b s β (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun j (t : ℝ) => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ)))
    (x := τ)
    (fun j _ => hasDerivAt_factor a b (-s - (β j : ℂ)) j i x τ (linF_pos a b ha hb j _ hy))
  refine hprod.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))
      = ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ) - 1) *
        ∏ k ∈ Finset.univ.erase j,
          ((linF a b k (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β k : ℂ)) := by
    unfold Fr
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same]
      push_cast
      ring
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      simp [Pi.single_apply, hkj]
  rw [hF, smul_eq_mul]
  ring

theorem hasDerivAt_DLR_Fr (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ)
    (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hx : ∀ k, 0 ≤ x k) (hτ : 0 ≤ τ) :
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  induction cs generalizing x with
  | nil =>
    have hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ τ * (Pi.single i 1 : Fin r → ℝ) k := by
        refine mul_nonneg hτ ?_
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    simpa [DLR] using hasDerivAt_Fr a b ha hb s β i x τ hy
  | cons c cs ih =>
    have hxc : ∀ k, 0 ≤ (x + (Pi.single c 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ (Pi.single c 1 : Fin r → ℝ) k := by
        by_cases hk : k = c
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    have hsw : ∀ (G : (Fin r → ℝ) → ℂ) (t : ℝ),
        DLR (c :: cs) G (x + t • (Pi.single i 1 : Fin r → ℝ))
          = DLR cs G ((x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ))
            - DLR cs G (x + t • (Pi.single i 1 : Fin r → ℝ)) := by
      intro G t
      have : x + t • (Pi.single i 1 : Fin r → ℝ) + (Pi.single c 1 : Fin r → ℝ)
          = (x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ) := by abel
      change fdR c (DLR cs G) _ = _
      simp only [fdR, this]
    have h := (ih (x + Pi.single c 1) hxc).sub (ih x hx)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hsw _ t)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsw, mul_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.exists_prime_degree_one_avoiding : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
  ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_prime_absNorm_avoiding | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_prime_absNorm_avoiding | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_prime_absNorm_avoiding <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density

theorem denseRange_real_places (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange fun (x : F) (w : InfinitePlace F) =>
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hq : ∀ w : InfinitePlace F, ∃ q : ℚ, |(q : ℝ) - z w| < ε / 2 := by
    intro w
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show z w < z w + ε / 2 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi F)
    (fun w => WithAbs.toAbs w.1 ((q w : ℚ) : F)) (ε / 2) (by linarith)
  refine ⟨x, (dist_pi_lt_iff hε).mpr fun w => ?_⟩
  have hxw := (dist_pi_lt_iff (by linarith : (0 : ℝ) < ε / 2)).mp hx w
  try dsimp only at hxw
  rw [Pi.algebraMap_apply, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply] at hxw
  have h2 : w.1 ((q w : F) - x) =
      |(q w : ℝ) - InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x| := by
    have h := InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) ((q w : F) - x)
    rw [Real.norm_eq_abs, map_sub, map_ratCast] at h
    exact h.symm
  rw [h2] at hxw
  show dist (z w) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) < ε
  rw [Real.dist_eq]
  have h3 : |z w - (q w : ℝ)| < ε / 2 := by
    rw [abs_sub_comm]
    exact hq w
  linarith [abs_sub_le (z w) (q w : ℝ) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)]

theorem exists_place_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : F →+* ℝ) :
    ∃ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) = σ := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp σ), ?_⟩
  ext x
  have h1 := InfinitePlace.embedding_of_isReal_apply
    (IsTotallyReal.isReal (InfinitePlace.mk (Complex.ofRealHom.comp σ))) x
  rw [InfinitePlace.embedding_mk_eq_of_isReal hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe] at h1
  exact_mod_cast h1

theorem exists_approx : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ),
    0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  intro F _ _ _ y ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_real_places F)
    (fun w => y (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) ε hε
  refine ⟨x, fun σ => ?_⟩
  obtain ⟨w, hw⟩ := exists_place_eq F σ
  have h := (dist_pi_lt_iff hε).mp hx w
  rw [Real.dist_eq, hw, abs_sub_comm] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density
end
