module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXHasSubst
public import Mathlib.CategoryTheory.Category.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenPow
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)

def PolG [Fintype ι] (P : MvPolynomial ι k) (A : S) : S :=
  ∑ n ∈ P.support, κ (P.coeff n) * (Finset.univ : Finset ι).toList.foldr (fun l g => (D l)^[n l] g) A

theorem TG_replicate (n : ℕ) (l : ι) (A : S) : TG D (List.replicate n l) A = (D l)^[n] A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
    rfl

theorem foldr_iterate_eq_TG (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    rw [List.foldr_cons, ih]
    have e : word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by simp [word]
    rw [e, TG_append, TG_replicate]

theorem e_PolG [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by

  simp only [PolG, map_sum, map_mul, he, foldr_iterate_eq_TG]
  rfl

theorem half_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P (A * q)) = algebraMap ℚ k (1 / 2) * e (PolG D κ (secondOrder k c P) A) := by
  classical
  set ψ : List ι → k := fun w => e (TG D w A) with hψ
  rw [e_PolG D κ e he, e_PolG D κ e he]
  have h2 : (AddMonoidAlgebra.coeff (secondOrder k c P)).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) = lamW ψ (secondOrder k c P) := rfl
  rw [h2, lamW_secondOrder, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [e_TG_mul_q D κ hadd hC hmul e c q hq0 hq1 hq2 he]
  have h3 := sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) n ψ
  have h4 : (algebraMap ℚ k (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]; norm_num
  calc (AddMonoidAlgebra.coeff P) n * ((splits (word (Finset.univ : Finset ι).toList n)).map
        (fun p => e (TG D p.1 A) * ev2 c p.2)).sum
      = (AddMonoidAlgebra.coeff P) n * ((algebraMap ℚ k (1 / 2) * 2) *
          ((splits (word (Finset.univ : Finset ι).toList n)).map (fun p => ψ p.1 * ev2 c p.2)).sum) := by
        rw [h4, one_mul]
    _ = algebraMap ℚ k (1 / 2) * ((AddMonoidAlgebra.coeff P) n * rW ψ c n) := by
        rw [mul_assoc (algebraMap ℚ k (1 / 2)), h3]
        simp only [rW]
        ring

theorem kill_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (hP : secondOrder k c P = 0) (G Y : S) :
    e (PolG D κ P (G * (1 + q * Y))) = e (PolG D κ P G) := by
  have hsplit : G * (1 + q * Y) = G + G * Y * q := by ring
  have hlin : ∀ A B, PolG D κ P (A + B) = PolG D κ P A + PolG D κ P B := by
    intro A B
    simp only [PolG, foldr_iterate_eq_TG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TG_add, mul_add]
    exact hadd
  rw [hsplit, hlin, map_add (f := _), half_gen D κ hadd hC hmul e he c q hc hq0 hq1 hq2 P (G * Y), hP]
  simp [PolG]

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]

theorem sum_side {M : Type} [AddCommMonoid M] (s : ι → Bool) (g : ι → ι → M)
    (hg : ∀ l l', g l l' ≠ 0 → s l = true ∧ s l' = false) :
    ∑ l, ∑ l', g l l' = ∑ i, ∑ j, g ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j)) := by
  have h1 : ∀ l, ∑ l', g l l' = ∑ j, g l ((sideE s).symm (Sum.inr j)) := by
    intro l
    rw [← Equiv.sum_comp (sideE s).symm (g l), Fintype.sum_sum_type]
    have h0 : ∑ i, g l ((sideE s).symm (Sum.inl i)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_contra hne
      have h2 := (hg _ _ hne).2
      rw [side_inl s i] at h2
      simp at h2
    rw [h0, zero_add]
  rw [Finset.sum_congr rfl (fun l _ => h1 l),
    ← Equiv.sum_comp (sideE s).symm (fun l => ∑ j, g l ((sideE s).symm (Sum.inr j))),
    Fintype.sum_sum_type]
  have h3 : ∑ j, ∑ j', g ((sideE s).symm (Sum.inr j)) ((sideE s).symm (Sum.inr j')) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun j' _ => ?_))
    by_contra hne
    have h2 := (hg _ _ hne).1
    rw [side_inr s j] at h2
    simp at h2
  rw [h3, add_zero]

abbrev kapE (s : ι → Bool) (κ : ι → ι → k) (i : Fin (Fintype.card {l // s l = true}))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : k :=
  κ ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j))

theorem delta_rename (s : ι → Bool) (κ : ι → ι → k) (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false)
    (P : MvPolynomial ι k) :
    PI.WickFormula.delta (kapE s κ) (rename (sideE s) P) = rename (sideE s) (secondOrder k κ P) := by
  have hd : ∀ (x : Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}))
      (Q : MvPolynomial ι k),
      pderiv x (rename (sideE s) Q) = rename (sideE s) (pderiv ((sideE s).symm x) Q) := by
    intro x Q
    conv_lhs => rw [← (sideE s).apply_symm_apply x]
    exact pderiv_rename (sideE s).injective _ _
  rw [PI.WickFormula.delta_eq_gdelta, PI.WickFormula.Gen.gdelta_apply,
    show secondOrder k κ P = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' P) from rfl]

  simp only [map_sum, map_mul, rename_C]
  rw [sum_side s _ ?_]
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [smul_eq_C_mul, hd, hd]
  · intro l l' hne
    apply hκ
    intro h0
    apply hne
    rw [h0, map_zero, zero_mul]

theorem delta_pow_rename (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false) (n : ℕ) (P : MvPolynomial ι k) :
    (PI.WickFormula.delta (kapE s κ) ^ n) (rename (sideE s) P) =
      rename (sideE s) ((secondOrder k κ)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, delta_rename s κ hκ, Function.iterate_succ_apply']

section Van

variable {π : Type} [Fintype π] [DecidableEq π]

theorem pairMin_step (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) (l l' : ι) (hc : c l = c l')
    (hs : s l = true) (hs' : s l' = false) :
    pairMin c s (n + Finsupp.single l 1 + Finsupp.single l' 1) = pairMin c s n + 1 := by
  have key : ∀ q : π,
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x) =
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true), n x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false), n x) +
        if c l = q then 1 else 0 := by
    intro q
    classical
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : c l = q
    · have hq' : c l' = q := hc ▸ hq
      simp [hq, hq', hs, hs']
      try omega
    · have hq' : ¬ c l' = q := hc ▸ hq
      simp only [hq, hq', false_and, if_false]
      omega
  simp only [pairMin]
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem secondOrder_support (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (Q : MvPolynomial ι k) (p j : ℕ)
    (hQ : ∀ n ∈ Q.support, pairMin c s n + j ≤ p) :
    ∀ n ∈ (secondOrder k κ Q).support, pairMin c s n + (j + 1) ≤ p := by
  intro n hn
  rw [MvPolynomial.mem_support_iff] at hn
  have h1 : AddMonoidAlgebra.coeff (secondOrder k κ Q) n = ∑ l, ∑ l', κ l l' * AddMonoidAlgebra.coeff (pderiv l (pderiv l' Q)) n := by
    rw [show secondOrder k κ Q = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' Q) from rfl]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [h1] at hn
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨l', -, hl'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  have hκ0 : κ l l' ≠ 0 := left_ne_zero_of_mul hl'
  have hc0 : AddMonoidAlgebra.coeff (pderiv l (pderiv l' Q)) n ≠ 0 := right_ne_zero_of_mul hl'
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv] at hc0
  have hQn : n + Finsupp.single l 1 + Finsupp.single l' 1 ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hc0
    rw [h0, zero_mul, zero_mul]
  obtain ⟨hcl, hsl, hsl'⟩ := hκ l l' hκ0
  have h2 := hQ _ hQn
  rw [pairMin_step c s n l l' hcl hsl hsl'] at h2
  omega

theorem secondOrder_iterate_eq_zero (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (P : MvPolynomial ι k) (e : ℕ)
    (hP : ∀ n ∈ P.support, pairMin c s n ≤ e) (j : ℕ) (hj : e < j) :
    (secondOrder k κ)^[j] P = 0 := by
  have h : ∀ t, ∀ n ∈ ((secondOrder k κ)^[t] P).support, pairMin c s n + t ≤ e := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact secondOrder_support c s κ hκ _ e t ih
  by_contra hne
  obtain ⟨n, hn⟩ : ((secondOrder k κ)^[j] P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  have h2 := h j n hn
  omega

end Van

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end
