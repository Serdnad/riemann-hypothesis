module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

theorem UpperTheory.Reformulated.B.Qe31.proof :
    UpperTheory.Reformulated.B.Qe31.Statement := by
  intro T _ _ P _ h f _ hle
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hI : Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have key : ∀ x ∈ P, ∃ s ∉ P, s * x ∈ Ideal.span (Set.range f) := by
    intro x hx
    have h1 : algebraMap T (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
      rw [← hI]
      apply hm
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ :=
      (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).1 h1
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hab
    obtain ⟨⟨c, hc⟩, hcab⟩ := hab
    refine ⟨c * b, P.primeCompl.mul_mem hc hb, ?_⟩
    have : c * b * x = c * a := by
      simp only at hcab
      rw [← hcab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  choose! g hg1 hg2 using key
  refine ⟨∏ y ∈ S, g y, P.primeCompl.prod_mem (fun y hy ↦ hg1 y (hSP y hy)), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g hy
    rw [hc, mul_comm (g y) c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg2 y (hSP y hy))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ ha
end

section

theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [inst : CommRing A] [IsDomain A]
    {K : Type} [inst_2 : Field K] [inst_3 : Algebra A K] [IsFractionRing A K] {V : Type} [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module K V] [inst_7 : _root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hby⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hax
    · rw [mul_smul]
      exact M.smul_mem a hby
  | smul k x _ ih =>
    obtain ⟨a, ha, hax⟩ := ih
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap A K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem p hax
end

section

theorem UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image :
    ∀ {A F M N : Type} [inst : CommRing A]
    [IsDomain A] [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup M]
    [inst_6 : _root_.Module A M] [inst_7 : AddCommGroup N] [inst_8 : _root_.Module A N] [inst_9 : _root_.Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M),
    ∀ y ∈ Submodule.span F ((⇑φ : M → N) '' T),
      ∃ (d : A), d ≠ (0 : A) ∧ ∃ w ∈ Submodule.span A T, d • y = (φ : M → N) w := by
  intro A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul c x _ hx =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    have hab' : c * algebraMap A F b = algebraMap A F a := hab
    rw [map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a,
      ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]
    congr 1
    ring
end

section

theorem UpperTheory.aeval_map_eq_rename_map_iff :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by
  intro R S _ _ φ hφ σ M _ w ν f
  refine ⟨?_, ?_⟩
  · unfold MvPolynomial.IsWeightedHomogeneous
    refine forall_congr' fun d => ?_
    rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]
  · intro τ gR gS ρ hg
    have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
    subst hgS
    rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
      ← MvPolynomial.map_rename]
    exact (MvPolynomial.map_injective φ hφ).eq_iff
end

section

theorem UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) →
      ∃ (g : σ → MvPowerSeries σ O), f = ∑ i : σ, MvPowerSeries.X i * g i := by
  intro O σ _ _ f hf
  classical
  have hex : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ i, m i ≠ 0 := by
    intro m hm
    by_contra h
    apply hm
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  choose c hc using hex
  let p : (σ →₀ ℕ) → σ → Prop := fun m i => ∃ hm : m ≠ 0, c m hm = i
  let g : σ → MvPowerSeries σ O := fun i n =>
    if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0
  have hg : ∀ i n, MvPowerSeries.coeff n (g i) =
      if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f
      else 0 := fun _ _ => rfl
  have key : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * g i) =
      if p m i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : Finsupp.single i 1 ≤ m
    · rw [if_pos h, one_mul, hg, tsub_add_cancel_of_le h]
    · rw [if_neg h, if_neg]
      rintro ⟨hm, hi⟩
      apply h
      rw [Finsupp.single_le_iff, ← hi]
      exact Nat.one_le_iff_ne_zero.mpr (hc m hm)
  refine ⟨g, ?_⟩
  ext m

  rw [map_sum]
  simp only [key]
  by_cases hm : m = 0
  · subst hm
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    simp
  · rw [Finset.sum_eq_single (c m hm)]
    · rw [if_pos ⟨hm, rfl⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
end

section

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

theorem UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
end

section

private theorem exp_second_order {A : Type} [CommRing A] [Algebra ℚ A] {y : A}
    (hy : IsNilpotent y) : ∃ d : A, IsNilpotent.exp y = 1 + y + y ^ 2 * d := by
  obtain ⟨k, hk⟩ := hy
  have h2 : y ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  refine ⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹) • y ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have h : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ)⁻¹) • y ^ (i + 1 + 1)
      = y ^ 2 * ((((i + 2).factorial : ℚ)⁻¹) • y ^ i) := by
    intro i _
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl h]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    pow_one, pow_zero]
  ring

private theorem exp_approx {A : Type} [CommRing A] [Algebra ℚ A] {n : A}
    (hn : IsNilpotent n) (k : ℕ) :
    ∃ x c : A, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n + n ^ (k + 1) * c := by
  induction k with
  | zero => exact ⟨0, -1, IsNilpotent.zero, by rw [IsNilpotent.exp_zero]; ring⟩
  | succ k ih =>
    obtain ⟨x, c, hx, he⟩ := ih
    have hy : IsNilpotent (n * (-(n ^ k * c))) :=
      (Commute.all _ _).isNilpotent_mul_right hn
    obtain ⟨d, hd⟩ := exp_second_order hy
    refine ⟨x + n * (-(n ^ k * c)),
      -c - n ^ k * c ^ 2 + (1 + n + n ^ (k + 1) * c) * (n ^ k * c ^ 2 * d),
      (Commute.all _ _).isNilpotent_add hx hy, ?_⟩
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hx hy, he, hd]
    ring

theorem UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto :
    ∀ {A : Type} [inst : CommRing A] [inst_1 : Algebra ℚ A] {n : A},
    IsNilpotent n → ∃ (x : A), IsNilpotent x ∧ IsNilpotent.exp x = (1 : A) + n := by
  intro A _ _ n hn
  obtain ⟨k, hk⟩ := id hn
  obtain ⟨x, c, hx, he⟩ := exp_approx hn k
  exact ⟨x, hx, by rw [he, pow_succ, hk, zero_mul, zero_mul, add_zero]⟩
end

section

private theorem coeff_mul_mem_of_lt {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    ∀ k < n, PowerSeries.coeff k (f * g) ∈ S := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

private theorem coeff_mul_mem_step {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    PowerSeries.coeff n (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : p.1 = 0
  · rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact S.zero_mem
  by_cases h2 : p.2 = 0
  · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, mul_zero]
    exact S.zero_mem
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

theorem UpperTheory.formal_group_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (a₁ a₂ a₃ a₄ a₆ : R) (w : PowerSeries R), a₁ ∈ S → a₂ ∈ S → a₃ ∈ S → a₄ ∈ S → a₆ ∈ S → PowerSeries.constantCoeff w = 0 → w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * PowerSeries.X * w + PowerSeries.C a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C a₃ * w ^ 2 + PowerSeries.C a₄ * PowerSeries.X * w ^ 2 + PowerSeries.C a₆ * w ^ 3 → ∀ n, PowerSeries.coeff n w ∈ S := by
  intro R _ S a₁ a₂ a₃ a₄ a₆ w h₁ h₂ h₃ h₄ h₆ h0 hw n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hX : ∀ k < n, PowerSeries.coeff k (PowerSeries.X : PowerSeries R) ∈ S := by
      intro k _
      rw [PowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
      PowerSeries.constantCoeff_X
    have hX3 : PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ 3) ∈ S := by
      rw [PowerSeries.coeff_X_pow]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hXw0 : PowerSeries.constantCoeff (PowerSeries.X * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hww0 : PowerSeries.constantCoeff (w * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hXw := coeff_mul_mem_of_lt S n _ _ hX ih
    have hww := coeff_mul_mem_of_lt S n _ _ ih ih
    have e : w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * (PowerSeries.X * w)
        + PowerSeries.C a₂ * (PowerSeries.X * (PowerSeries.X * w))
        + PowerSeries.C a₃ * (w * w) + PowerSeries.C a₄ * (PowerSeries.X * (w * w))
        + PowerSeries.C a₆ * (w * (w * w)) := by
      refine hw.trans ?_
      ring
    have e' := congrArg (PowerSeries.coeff n) e
    rw [e']
    simp only [map_add (f := _), PowerSeries.coeff_C_mul]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem hX3
      (S.mul_mem h₁ (coeff_mul_mem_step S n _ _ hX0 h0 hX ih)))
      (S.mul_mem h₂ (coeff_mul_mem_step S n _ _ hX0 hXw0 hX hXw)))
      (S.mul_mem h₃ (coeff_mul_mem_step S n _ _ h0 h0 ih ih)))
      (S.mul_mem h₄ (coeff_mul_mem_step S n _ _ hX0 hww0 hX hww)))
      (S.mul_mem h₆ (coeff_mul_mem_step S n _ _ h0 hww0 ih hww))
end

section

theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
end

section

namespace UpperTheory.Reformulated.B.Qk3

theorem aux1 {A : Type} [CommRing A] : RingHomInvPair (RingHom.id A) (RingHom.id A) :=
  RingHomInvPair.ids

noncomputable def unopS (A E S : Type) [CommRing A] [Ring E] [Algebra A E]
    [CommRing S] [Algebra A S] : TensorProduct A S Eᵐᵒᵖ →ₗ[S] TensorProduct A S E :=
  LinearMap.baseChange S (MulOpposite.opLinearEquiv A).symm.toLinearMap

theorem unopS_mul {A E : Type} [CommRing A] [Ring E] [Algebra A E]
    (S : Type) [CommRing S] [Algebra A S] (x y : TensorProduct A S Eᵐᵒᵖ) :
    unopS A E S (x * y) = unopS A E S y * unopS A E S x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  | tmul s e =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add (f := _), map_add (f := _), h₁, h₂, add_mul]
    | tmul t f => simp [unopS, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s t]

end UpperTheory.Reformulated.B.Qk3
end

section

theorem UpperTheory.Reformulated.B.Qk54.tensor_hom_ext :
    ∀ {A A' C Ω : Type}
    [inst : CommRing A] [inst_1 : CommRing A'] [inst_2 : CommRing C] [inst_3 : Algebra A A'] [inst_4 : Algebra A C]
    [inst_5 : CommRing Ω] {u v : TensorProduct A C A' →+* Ω},
    (∀ (c : C), (u : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A')) = (v : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A'))) →
      (∀ (b : A'), (u : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b) = (v : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b)) →
        u = v := by
  intro A A' C Ω _ _ _ _ _ _ u v h₁ h₂
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have e : c ⊗ₜ[A] b = (c ⊗ₜ[A] (1 : A')) * ((1 : C) ⊗ₜ[A] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end
