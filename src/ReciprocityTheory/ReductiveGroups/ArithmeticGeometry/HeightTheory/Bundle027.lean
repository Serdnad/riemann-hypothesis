module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow
import Mathlib.Algebra.MvPolynomial.Division
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle009

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]

  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by
  classical
  revert hks
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hks
  have hik : i ≠ k := fun h => hks (h ▸ Finset.mem_insert_self _ _)
  have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
  rw [← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik
    (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]
  congr 2
  funext t
  by_cases h1 : t.1 = i
  · simp [h1, hi, hks']
  · simp [h1, Finset.mem_insert]

theorem pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by
  classical
  let S := FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
  let φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S :=
    IsScalarTower.toAlgHom K _ S
  have hφ : Function.Injective φ := IsFractionRing.injective _ S
  let x : Fin (d.D + 2) → S := fun i => φ (X (Sum.inr i))
  let U : Fin (d.D + 2) → Fin (d.N + 1) → S := fun a j => φ (X (Sum.inl (a, j)))
  have hx : ∀ i, x i ≠ 0 := fun i h0 => X_ne_zero (R := K)
    (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))
  have hx1 := hx 1
  let r : TVar d.D d.N → S := fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2
  have hG : φ (bilinearSubstitution F0) = aeval r F0 := by
    rw [bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t; simp [r, x, U]
  let s : Finset (Fin (d.D + 1)) := Finset.univ.erase 0
  have hs : s.card = d.D := by simp [s, Finset.card_erase_of_mem]
  let W : TVar d.D d.N → S := fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2
  have e1 := d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))
  have hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) =
      fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t)
        else (if t.1 ∈ s then W t else r t) := by
    funext t
    split_ifs
    · simp only [r, W, Fin.succ_zero_eq_one]
      linear_combination (x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1
    · rfl
  rw [hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs] at e1
  have e2 := aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)
  rw [hs] at e2
  let P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K := fun t =>
    if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2))
    else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))
  have hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t)
      else (if t.1 ∈ s then W t else r t)) F0 := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t
    simp only [P]
    split_ifs
    · simp only [map_sub, map_mul, W, x, U]
      simp only [x] at hx1
      linear_combination (φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1
    · simp [r, x, U]
  have key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)
    rw [hG, ← e1, hP, e2]; ring
  have key' := hφ key
  have hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :=
    MvPolynomial.X_prime
  have hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣
      X (Sum.inr 1) ^ (d.D * d0) := by
    intro h
    obtain ⟨q, hq⟩ := hp.dvd_of_dvd_pow h
    have := congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq
    simp at this
  exact hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem fsum_le_of {α : Type*} (s : Set α) (f g : α → ℤ) (hf : {x | x ∈ s ∧ f x ≠ 0}.Finite)
    (hg : {x | x ∈ s ∧ g x ≠ 0}.Finite) (r : ℝ) (hle : ∀ x ∈ s, (f x : ℝ) ≤ r * g x) :
    ((∑ᶠ x ∈ s, f x : ℤ) : ℝ) ≤ r * ((∑ᶠ x ∈ s, g x : ℤ) : ℝ) := by
  classical
  set u : Finset α := (hf.union hg).toFinset with hu
  have hus : ∀ x ∈ u, x ∈ s := by
    intro x hx
    simp only [hu, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with h | h
    · exact h.1
    · exact h.1
  have ef : ∑ᶠ x ∈ s, f x = ∑ x ∈ u, f x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  have eg : ∑ᶠ x ∈ s, g x = ∑ x ∈ u, g x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  rw [ef, eg, Int.cast_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hle x (hus x hx)

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem pow_mem_ne (hd : d.AxH 𝒜) {G : WT} {ta : ∀ c, A c} (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (n : ℕ) : ∀ c, (ta ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (ta ^ (n + 1)) c ≠ 0 := by
  intro c
  haveI := hd.graded c
  induction n with
  | zero => simpa using hta c
  | succ n ih =>
    rw [pow_succ, Pi.mul_apply, succ_nsmul G (n + 1)]
    exact ⟨SetLike.mul_mem_graded ih.1 (hta c).1, hd.mul_ne_zero c ih.1 (hta c).1 ih.2 (hta c).2⟩

private lemma finsum_mem_const_mul {α : Type*} (s : Set α) (f : α → ℤ) (k : ℤ) (hk : k ≠ 0) :
    ∑ᶠ x ∈ s, k * f x = k * ∑ᶠ x ∈ s, f x := by
  classical
  have hs : s ∩ Function.support (fun x => k * f x) = s ∩ Function.support f := by
    ext x
    simp [hk]
  by_cases hf : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq (fun x => k * f x) (t := hf.toFinset) (by
        ext x
        simp [hk]
        try tauto),
      finsum_mem_eq_sum_of_inter_support_eq f (t := hf.toFinset) (by
        ext x
        simp
        try tauto),
      Finset.mul_sum]
  · rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), mul_zero]

private lemma nP_pow_succ_eq_succ_mul (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (n : ℕ) : d.nP h c ((n + 1) • G) ((ta ^ (n + 1)) c) p = ((n : ℤ) + 1) * d.nP h c G (ta c) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (ta ^ (n + 1 + 1)) c = (ta ^ (n + 1)) c * ta c := by rw [pow_succ, Pi.mul_apply]
    rw [e, succ_nsmul G (n + 1), d.nP_mul hd h c (d.pow_mem_ne hd hta n c).1 (hta c).1
      (d.pow_mem_ne hd hta n c).2 (hta c).2 hp, ih]
    push_cast
    ring

theorem aG_pow (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (n : ℕ) :
    d.aG h ((n + 1) • G) (ta ^ (n + 1)) = (n + 1) * d.aG h G ta := by
  unfold aG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← finsum_mem_const_mul _ (fun p => d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)) ((n : ℤ) + 1) (by positivity)]
  refine finsum_mem_congr rfl fun p hp => ?_
  rw [nP_pow_succ_eq_succ_mul d hd h hta c hp n, mul_assoc]

theorem aG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hord : ∀ c v, d.admitted c v → 0 ≤ d.ord c v G (ta c)) : 0 ≤ d.aG h G ta := by
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  refine finsum_nonneg fun p => finsum_nonneg fun hp => ?_
  exact mul_nonneg (d.nP_nonneg hd h c hp G (ta c) (hord c)) (by positivity)

private lemma ratio_zero_left {F0 V0 : Type*} [Field F0] [AddCommGroup V0] [Module F0 V0] {g : V0}
    (hg : g ≠ 0) : ratio (Ω := F0) (0 : V0) g = 0 := by
  unfold ratio
  split_ifs with h0
  · rcases smul_eq_zero.1 h0.choose_spec.symm with h1 | h1
    · exact h1
    · exact absurd h1 hg
  · rfl

theorem thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he, -, hy⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := hy 1
  have key := hp c
  simp only [Pi.one_apply, mul_one] at key
  rw [Finset.sum_eq_zero] at key
  · exact hq c key
  · intro k _
    rw [hcon, ratio_zero_left (he c).2, map_zero, mul_zero]

theorem aG_sb (hd : d.AxH 𝒜) (h : d.S1) :
    d.aG h d.wL (fun c => d.w (d.jc c) c) =
      d.del + ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.Ep h c p * (d.dg (d.gen p) : ℤ) := by
  unfold aG del
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨F, -, -, -, h4, -⟩ := d.componentForm_properties hd h c
  have hf := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hE := d.Ep_ne hd h c _ (hd.w_mem _ c) (hd.w_base c)
  rw [← h4, ← finsum_mem_add_distrib']
  · exact finsum_mem_congr rfl fun p hp => by rw [d.nP_split hd h c hp]; ring
  · exact hf.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩
  · exact hE.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩

theorem aG_wx (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) :
    d.aG h d.wL (d.wx x) = d.aG h d.wL (fun c => d.w (d.jc c) c) :=
  (d.norm_factorization hd h).2.1 _ _ _ (fun c => ⟨d.wx_mem hd x c, hx c⟩) (fun c => ⟨hd.w_mem _ c, hd.w_base c⟩)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
