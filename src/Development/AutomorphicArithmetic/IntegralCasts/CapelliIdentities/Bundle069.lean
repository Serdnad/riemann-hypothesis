module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qk2.map_surj :
    ∀ {A E : Type} [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] {E' : Type} [inst_3 : Ring E'] [inst_4 : Algebra A E'] (f : E' →ₐ[A] E),
    Function.Surjective (⇑f : E' → E) →
      ∀ (S : Type) [inst_5 : CommRing S] [inst_6 : Algebra A S],
        Function.Surjective
          (⇑(Algebra.TensorProduct.map (AlgHom.id S S) f) : TensorProduct A S E' → TensorProduct A S E) := by
  intro A E _ _ _ E' _ _ f hf S _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s e =>
    obtain ⟨e', rfl⟩ := hf e
    exact ⟨TensorProduct.tmul A s e', by simp⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
end

section

theorem UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω)
    {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω inst A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

section

theorem UpperTheory.Reformulated.B.Yla8.main :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω),
      (∃ (x : T), y x ≠ (0 : Ω)) → ∃ (x₀ : T), y x₀ ≠ (0 : Ω) ∧ ∀ (x : T), y x / y x₀ ∈ A := by
  intro Ω _ A T _ y ⟨x1, hx1⟩
  have : Nonempty {x : T // y x ≠ 0} := ⟨⟨x1, hx1⟩⟩
  obtain ⟨⟨x₀, h0⟩, hmax⟩ := Finite.exists_max (fun z : {x : T // y x ≠ 0} => A.valuation (y z.1))
  refine ⟨x₀, h0, fun x => ?_⟩
  by_cases hx : y x = 0
  · rw [hx, zero_div]; exact A.zero_mem
  · rw [← A.valuation_le_one_iff, map_div₀]
    have hpos : (0 : A.ValueGroup) < A.valuation (y x₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr h0
    exact (div_le_one₀ hpos).mpr (hmax ⟨x, hx⟩)
end

section

theorem UpperTheory.Reformulated.B.Qf13.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [e]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      calc A.valuation (a ^ n - b ^ n) * A.valuation a
          ≤ A.valuation (a ^ n - b ^ n) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · rw [map_mul, map_pow]
      have hb' : A.valuation b ^ n ≤ 1 := pow_le_one' hb n
      calc A.valuation (a - b) * A.valuation b ^ n
          ≤ A.valuation (a - b) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
end

section

theorem UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main.{u_1} :
    ∀ {Ω : Type} [inst : Field Ω] (W : ValuationSubring Ω) {κ : Type u_1} [Finite κ] (x : κ → Ω),
      (∃ (j : κ), x j ≠ (0 : Ω)) → ∃ (c : κ), x c ≠ (0 : Ω) ∧ ∀ (j : κ), x j / x c ∈ W := by
  intro Ω _ W κ _ x ⟨j0, hj0⟩
  have : Nonempty κ := ⟨j0⟩
  obtain ⟨c, hc⟩ := Finite.exists_max (fun j => W.valuation (x j))
  have hc0 : x c ≠ 0 := by
    intro h
    have h1 := hc j0
    simp only [h, map_zero] at h1
    exact hj0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  refine ⟨c, hc0, fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  have hpos : W.valuation (x c) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (hc j)
end

section

theorem UpperTheory.Reformulated.B.Qh11.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

section

theorem UpperTheory.Reformulated.B.Qi55.val_prime_of_lt :
    ∀ {Ω : Type} [inst : Field Ω]
    (A : ValuationSubring Ω) (n : ℕ),
    n ≠ (0 : ℕ) →
      (A.valuation : Ω → A.ValueGroup) (↑n : Ω) < (1 : A.ValueGroup) →
        ∃ (t : ℕ), Nat.Prime t ∧ t ∣ n ∧ (A.valuation : Ω → A.ValueGroup) (↑t : Ω) < (1 : A.ValueGroup) := by
  intro Ω _ A n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; simp at h
  | prime_mul p a hp ih =>
    intro hne h
    have ha : a ≠ 0 := right_ne_zero_of_mul hne
    by_cases hpv : A.valuation (p : Ω) < 1
    · exact ⟨p, hp, dvd_mul_right p a, hpv⟩
    · have hav : A.valuation (a : Ω) < 1 := by
        by_contra hc
        rw [Nat.cast_mul, map_mul] at h
        exact absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))
      obtain ⟨t, ht, hd, hv⟩ := ih ha hav
      exact ⟨t, ht, hd.mul_left p, hv⟩
end

section

open Filter Topology

theorem UpperTheory.Reformulated.B.Ydb1.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {K S : Set G},
      IsCompact K →
        S ⊆ K →
          (1 : G) ∈ S →
            ∀ {Ψ φ : G → G},
              Continuous Ψ →
                (∀ x ∈ S, Ψ x ∈ S) →
                  (∀ x ∈ S, φ x ∈ S) →
                    (∀ (x y : G), (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)) →
                      ∀ {l : ℕ},
                        (0 : ℕ) < l →
                          (∀ (U : Set G), IsOpen U → (1 : G) ∈ U → ∃ (m₀ : ℕ), ∀ m ≥ m₀, ∀ x ∈ S, φ^[l * m] x ∈ U) →
                            ∃ v ∈ K, Ψ v = v := by
  intro G _ _ _ _ K S hK hSK h1 Ψ φ hΨ hΨS hφS hrel l _ hconv
  have hφ1 : φ 1 = 1 := by
    have := hrel 1 1
    rw [inv_mul_cancel, inv_one, one_mul] at this
    exact this.symm
  have hΨx : ∀ y, Ψ y = Ψ 1 * φ y := fun y => by
    have := hrel 1 y
    rw [inv_one, one_mul] at this
    rw [← this, mul_inv_cancel_left]
  have hd : ∀ x y, φ (x⁻¹ * y) = (φ x)⁻¹ * φ y := fun x y => by
    rw [← hrel x y, hΨx x, hΨx y, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hmul : ∀ p q, φ (p * q) = φ p * φ q := by
    intro p q
    have hinv : φ p⁻¹ = (φ p)⁻¹ := by
      have := hd p 1
      rw [mul_one, hφ1, mul_one] at this
      exact this
    have := hd p⁻¹ q
    rw [inv_inv, hinv, inv_inv] at this
    exact this
  have hit : ∀ n x, Ψ^[n] x = Ψ^[n] 1 * φ^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih x, hΨx (Ψ^[n] 1 * φ^[n] x), hΨx (Ψ^[n] 1), hmul, mul_assoc]
  have ha : Ψ 1 ∈ S := hΨS 1 h1
  have hPS : ∀ n, Ψ^[n] 1 ∈ S := fun n => (Set.MapsTo.iterate (f := Ψ) hΨS n) h1
  have hφa : ∀ n, φ^[n] (Ψ 1) ∈ S := fun n => (Set.MapsTo.iterate (f := φ) hφS n) ha
  have hstep : ∀ n, Ψ (Ψ^[n] 1) = Ψ^[n] 1 * φ^[n] (Ψ 1) := fun n => by
    rw [← Function.iterate_succ_apply' Ψ n 1, Function.iterate_succ_apply, hit]
  have hlim : Tendsto (fun m : ℕ => φ^[l * m] (Ψ 1)) atTop (𝓝 1) := by
    rw [(nhds_basis_opens (1 : G)).tendsto_right_iff]
    rintro U ⟨h1U, hU⟩
    obtain ⟨m₀, hm₀⟩ := hconv U hU h1U
    exact eventually_atTop.2 ⟨m₀, fun m hm => hm₀ m hm _ ha⟩
  obtain ⟨v, hvK, hv⟩ := hK.exists_mapClusterPt (f := (atTop : Filter ℕ))
    (u := fun m : ℕ => Ψ^[l * m] 1)
    (by
      rw [le_principal_iff, mem_map]
      exact univ_mem' fun m => hSK (hPS (l * m)))
  obtain ⟨𝒰, h𝒰, hu⟩ := mapClusterPt_iff_ultrafilter.1 hv
  refine ⟨v, hvK, ?_⟩
  have h₁ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (Ψ v)) := (hΨ.tendsto v).comp hu
  have h₂ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (v * 1)) := by
    simp_rw [hstep]
    exact hu.mul (hlim.mono_left h𝒰)
  rw [mul_one] at h₂
  exact tendsto_nhds_unique h₁ h₂
end

section

private lemma sum_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable g) (s : Finset (ι → α)) :
    ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∏ _i : ι, ∑' x, g x := by
  haveI : DecidableEq α := Classical.decEq α
  let t : ι → Finset α := fun i => s.image fun η : ι → α => η i
  have hsub : s ⊆ Fintype.piFinset t := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨ξ, hξ, rfl⟩
  have h1 : ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun ξ _ _ => Finset.prod_nonneg fun i _ => hg (ξ i)
  have h2 : ∏ i, ∑ x ∈ t i, g x = ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.prod_univ_sum t fun _ x => g x
  have h3 : ∏ i, ∑ x ∈ t i, g x ≤ ∏ _i : ι, ∑' x, g x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => hg x
    · intro i _
      exact hs.sum_le_tsum (t i) fun x _ => hg x
  exact h1.trans (h2.symm.le.trans h3)

theorem UpperTheory.Reformulated.B.Qo1.summable_prod_coord.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by
  intro ι _ _ α g hg hs
  have h0 : ∀ ξ : ι → α, 0 ≤ ∏ i, g (ξ i) := fun ξ => Finset.prod_nonneg fun i _ => hg (ξ i)
  exact summable_of_sum_le h0 (sum_prod_le hg hs)
end

section

theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by
  intro P _ g
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ x ∈ s, ∏ p : P, g p (x p)
      ≤ ∑ x ∈ Fintype.piFinset (fun p => s.image (fun y : P → ℤ => y p)), ∏ p : P, g p (x p) := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact Fintype.mem_piFinset.2 fun p => Finset.mem_image_of_mem _ hx
    _ = ∏ p : P, ∑ n ∈ s.image (fun y : P → ℤ => y p), g p n :=
        (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ p : P, ∑' (n : ℤ), g p n :=
        Finset.prod_le_prod' fun p _ => ENNReal.sum_le_tsum _
end

section

noncomputable def UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk :
    {K : Type} →
      [inst : Field K] →
        [inst_1 : TopologicalSpace K] →
          [IsTopologicalRing K] →
            {n d : ℕ} → GL (Fin n) K → GL (Fin d) K → Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  fun {K} _ _ _ {n d} a c =>
    { toFun := fun y => (a : Matrix (Fin n) (Fin n) K) * y * (c : Matrix (Fin d) (Fin d) K)
      invFun := fun y =>
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y *
          ((c⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      left_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.mul_inv, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
end
