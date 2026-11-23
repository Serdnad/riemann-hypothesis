module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Associated
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke :
    {G : Type} → [inst : Group G] → [TopologicalSpace G] → Subgroup G → (G → ℂ) → Prop :=
    fun {G : Type} [Group G] [TopologicalSpace G] (K' : Subgroup G) (f : G → ℂ) ↦
      HasCompactSupport f ∧ ∀ k ∈ K', ∀ (x : G), f (k * x) = f x ∧ f (x * k) = f x

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a b : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → b ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * (a * b)) = u x := by
  intro H _ u a b ha hb x
  rw [← mul_assoc, hb, ha]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) (a : H), u (a * (1 : H)) = u a := by
  intro H _ u a
  rw [mul_one]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * a⁻¹) = u x := by
  intro H _ u a ha x
  have h := ha (x * a⁻¹)
  rw [inv_mul_cancel_right] at h
  exact h.symm

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.rStab :
    {H : Type} → [inst : Group H] → (H → ℂ) → Subgroup H :=
    fun {H : Type} [inst : Group H] (u : H → ℂ) ↦
      { carrier := {k : H | ∀ (x : H), u (x * k) = u x}, mul_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux2 H inst u,
        one_mem' := UpperTheory.Reformulated.B.HeckeGelfandPair.aux3 u, inv_mem' := @UpperTheory.Reformulated.B.HeckeGelfandPair.aux4 H inst u : Subgroup H }

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.hint :
    {H : Type} → [inst : Group H] → Subgroup H → (H → ℂ) → ℂ :=
    fun {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) ↦
      (↑((UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K).relIndex K) : ℂ)⁻¹ * ∑ᶠ (q : H ⧸ UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K), u (Quotient.out q)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.cv :
    {G : Type} → [inst : Group G] → Subgroup G → (G → ℂ) → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) (y : G) ↦ UpperTheory.Reformulated.B.HeckeGelfandPair.hint K fun (z : G) ↦ f z * g (z⁻¹ * y)

noncomputable def UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand :
    Prop :=
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (τ : G → G),
            (∀ (x y : G), τ (x * y) = τ y * τ x) →
              (∀ (x : G), τ (τ x) = x) →
                (∀ k ∈ K, τ k ∈ K) →
                  (∀ (x : G), ∃ k ∈ K, ∃ k' ∈ K, τ x = k * x * k') →
                    ∀ (f g : G → ℂ),
                      UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K f →
                        UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K g → UpperTheory.Reformulated.B.HeckeGelfandPair.cv K f g = UpperTheory.Reformulated.B.HeckeGelfandPair.cv K g f

private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    UpperTheory.Reformulated.B.HeckeGelfandPair.hint K u = ∑ᶠ q : H ⧸ K, u (Quotient.out q) := by
  have h : UpperTheory.Reformulated.B.HeckeGelfandPair.rStab u ⊓ K = K := inf_eq_right.mpr (fun k hk => hu k hk)
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.hint
  rw [h]
  simp

private theorem UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr {H : Type} [Group H] (K : Subgroup H) (u v : H → ℂ)
    (hv : ∀ k ∈ K, ∀ x, v (x * k) = v x) (e : H ≃ H)
    (he : ∀ a b, a⁻¹ * b ∈ K ↔ (e a)⁻¹ * e b ∈ K) (huv : ∀ z, v (e z) = u z) :
    ∑ᶠ q : H ⧸ K, u (Quotient.out q) = ∑ᶠ q : H ⧸ K, v (Quotient.out q) := by
  let E : H ⧸ K ≃ H ⧸ K := Quotient.congr e (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    exact he a b)
  rw [← finsum_comp_equiv E (f := fun q : H ⧸ K => v (Quotient.out q))]
  refine finsum_congr (fun q => ?_)
  have h1 : E q = (QuotientGroup.mk (e q.out) : H ⧸ K) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (e q.out)
  rw [h1, hk, hv _ k.2, huv]

theorem UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand :
    UpperTheory.Reformulated.B.HeckeGelfandPair.CvGelfand := by
  intro G _ _ _ K _ _ τ hmul hinv hK hdc f g hf hg
  have h1 : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hi : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_right
    rw [← hmul, inv_mul_cancel, h1]
  have hτ : ∀ φ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → ∀ x, φ (τ x) = φ x := by
    intro φ hφ x
    obtain ⟨k, hk, k', hk', h⟩ := hdc x
    rw [h, (hφ.2 k' hk' _).2, (hφ.2 k hk _).1]
  have hr : ∀ φ ψ : G → ℂ, UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K φ → UpperTheory.Reformulated.B.HeckeGelfandPair.IsHecke K ψ →
      ∀ y, ∀ k ∈ K, ∀ x, φ (x * k) * ψ ((x * k)⁻¹ * y) = φ x * ψ (x⁻¹ * y) := by
    intro φ ψ hφ hψ y k hk x
    rw [(hφ.2 k hk x).2, mul_inv_rev, mul_assoc, (hψ.2 k⁻¹ (K.inv_mem hk) _).1]
  funext y
  obtain ⟨k, hk, k', hk', hy⟩ := hdc y
  unfold UpperTheory.Reformulated.B.HeckeGelfandPair.cv
  rw [UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr f g hf hg y), UpperTheory.Reformulated.B.HeckeGelfandPair.hint_eq K _ (hr g f hg hf y)]
  let e : G ≃ G :=
    { toFun := fun z => y * k' * (τ z)⁻¹
      invFun := fun w => τ (w⁻¹ * (y * k'))
      left_inv := fun z => by
        have : (y * k' * (τ z)⁻¹)⁻¹ * (y * k') = τ z := by group
        simp only [this, hinv]
      right_inv := fun w => by
        simp only [hinv]
        group }
  refine UpperTheory.Reformulated.B.HeckeGelfandPair.sum_congr K (fun z => f z * g (z⁻¹ * y)) (fun z => g z * f (z⁻¹ * y))
    (hr g f hg hf y) e ?_ ?_
  · intro a b
    have h : (e a)⁻¹ * e b = τ (a⁻¹ * b)⁻¹ := by
      change (y * k' * (τ a)⁻¹)⁻¹ * (y * k' * (τ b)⁻¹) = _
      rw [hi, hmul, hi]
      group
    rw [h]
    constructor
    · exact fun hab => hK _ (K.inv_mem hab)
    · intro hab
      have h2 := hK _ hab
      rw [hinv] at h2
      exact K.inv_mem_iff.mp h2
  · intro z
    change g (y * k' * (τ z)⁻¹) * f ((y * k' * (τ z)⁻¹)⁻¹ * y) = f z * g (z⁻¹ * y)
    have h2 : (y * k' * (τ z)⁻¹)⁻¹ * y = τ z * k'⁻¹ := by group
    have h3 : τ (z⁻¹ * y) = k * (y * k' * (τ z)⁻¹) := by
      rw [hmul, hi, hy]
      group
    rw [h2, (hf.2 _ (K.inv_mem hk') _).2, hτ f hf, ← hτ g hg (z⁻¹ * y), h3, (hg.2 k hk _).1,
      mul_comm]
end

section

noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan.{u_1} :
    {Ω : Type u_1} → [inst : CommRing Ω] → {q r : ℕ} → (Fin q → Ω) → (Fin r → ℕ) → (Fin r → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type u_1} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) ↦
      AddSubgroup.closure
        {x : Ω | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j : Fin q, μ j = n ∧ x = t l * ∏ j : Fin q, w j ^ μ j}

@[reducible] noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.pc :
    {Ω : Type} → [inst : Field Ω] → {q : ℕ} → (Fin q → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω) (n : ℕ) ↦
      UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan w (fun (x : Fin (1 : ℕ)) ↦ (0 : ℕ)) (fun (x : Fin (1 : ℕ)) ↦ (1 : Ω)) n

theorem UpperTheory.Reformulated.B.GradedSpanProducts.pc_mul :
    ∀ {Ω : Type} [inst : Field Ω] {q : ℕ} (w : Fin q → Ω) {a b : ℕ} {x z : Ω},
      x ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w a → z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w b → x * z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w (a + b) := by
  intro Ω _ q w a b x z hx hz
  unfold UpperTheory.Reformulated.B.GradedSpanProducts.pc UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan at *
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, μ, hμ, rfl⟩ := hx
      obtain ⟨_, ν, hν, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨l, fun j => μ j + ν j, ?_, ?_⟩
      · simp only [zero_add] at hμ hν ⊢
        rw [Finset.sum_add_distrib, hμ, hν]
      · simp only [one_mul, pow_add, Finset.prod_mul_distrib]
    | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg z _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | neg x _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
end

section

noncomputable def UpperTheory.Reformulated.B.Qf37.aOp :
    {G : Type} → [Group G] → Finset G → G → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) (g : G) ↦ ∑ r ∈ R, φ (g * r * t)

theorem UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant :
    ∀ {G : Type} [inst : Group G] {I : Subgroup G} {t : G} {R : Finset G},
      (∀ r ∈ R, r ∈ I) →
        (∀ i ∈ I, ∃! r : G, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) →
          ∀ {φ : G → ℂ},
            (∀ (g i : G), i ∈ I → φ (g * i) = φ g) →
              ∀ (g i : G), i ∈ I → UpperTheory.Reformulated.B.Qf37.aOp R t φ (g * i) = UpperTheory.Reformulated.B.Qf37.aOp R t φ g := by
  intro G inst I t R hR hU φ hφ g i hi
  have hex : ∀ r ∈ R, ∃ s, s ∈ R ∧ t⁻¹ * (s⁻¹ * (i * r)) * t ∈ I := fun r hr =>
    (hU (i * r) (I.mul_mem hi (hR r hr))).exists
  choose σ hσR hσ using hex
  have hinj : ∀ a (ha : a ∈ R) b (hb : b ∈ R), σ a ha = σ b hb → a = b := by
    intro a ha b hb hab
    have h1 := hσ a ha
    have h2 := hσ b hb
    rw [← hab] at h2
    have h3 := I.mul_mem (I.inv_mem h1) h2
    have h4 : t⁻¹ * (a⁻¹ * b) * t ∈ I := by
      convert h3 using 1
      group
    have h5 : t⁻¹ * (b⁻¹ * b) * t ∈ I := by
      simp
    exact (hU b (hR b hb)).unique ⟨ha, h4⟩ ⟨hb, h5⟩
  unfold UpperTheory.Reformulated.B.Qf37.aOp
  refine Finset.sum_bij σ hσR hinj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσR
      (fun a b ha hb h => hinj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  · intro a ha
    rw [← hφ (g * σ a ha * t) _ (hσ a ha)]
    congr 1
    group
end

section

theorem UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq :
    ∀ {M ι : Type} [inst : CommRing M] (f : ι → M) (y : M)
    (s : Finset ι),
    (∀ a ∈ s, Prime (f a)) → (∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) → (∀ a ∈ s, f a ∣ y) → ∏ a ∈ s, f a ∣ y := by
  intro M ι inst f y s
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro hp hd hy
    have hpa : Prime (f a) := hp a (Finset.mem_insert_self a s)
    obtain ⟨c, hc⟩ := ih (fun b hb => hp b (Finset.mem_insert_of_mem hb))
      (fun b hb d hd' => hd b (Finset.mem_insert_of_mem hb) d (Finset.mem_insert_of_mem hd'))
      (fun b hb => hy b (Finset.mem_insert_of_mem hb))
    have h1 : f a ∣ (∏ b ∈ s, f b) * c := hc ▸ hy a (Finset.mem_insert_self a s)
    rcases hpa.dvd_or_dvd h1 with h2 | h2
    · obtain ⟨b, hb, hab⟩ := hpa.exists_mem_finset_dvd h2
      have h3 : a = b := hd a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) hab
      exact absurd (h3 ▸ hb) ha
    · rw [Finset.prod_insert ha, hc, mul_comm (f a)]
      exact mul_dvd_mul_left _ h2
end

section

theorem UpperTheory.Reformulated.B.AlternatingSumZero.alt_sum_zero.{u_1} :
    ∀ {A : Type u_1} [inst : AddCommGroup A] {n : ℕ}
      (G : ({ len := n : SimplexCategory } ⟶ { len := n + (2 : ℕ) : SimplexCategory }) → A),
      ∑ i : Fin (n + (3 : ℕ)),
          ∑ j : Fin (n + (2 : ℕ)),
            ((-1 : ℤ) ^ (↑i : ℕ) * (-1 : ℤ) ^ (↑j : ℕ)) •
              G (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ j) (SimplexCategory.δ i)) =
        (0 : A) := by
  intro A _ n G
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 3) × Fin (n + 2) => (p.1 : ℕ) ≤ (p.2 : ℕ)), add_eq_zero_iff_eq_neg,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun p hp => (p.2.succ, p.1.castLT
      (lt_of_le_of_lt (Finset.mem_filter.mp hp).2 p.2.isLt))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ h
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    have hi := i.isLt
    simp only [not_le] at h
    refine ⟨(j.castSucc, ⟨i.val - 1, by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
      omega
    · simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT, Fin.val_castSucc,
        and_true]
      omega
  · rintro ⟨i, j⟩ hp
    have h : (i : ℕ) ≤ (j : ℕ) := (Finset.mem_filter.mp hp).2
    have hi : (i : ℕ) < n + 2 := lt_of_le_of_lt h j.isLt
    have key := SimplexCategory.δ_comp_δ (i := i.castLT hi) (j := j) h
    rw [Fin.castSucc_castLT] at key
    dsimp only
    rw [key, ← neg_smul]
    congr 1
    simp only [Fin.val_succ, Fin.val_castLT]
    ring
end

section

theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
end

section

noncomputable def UpperTheory.Reformulated.B.CasimirElement.casC :
    {n : ℕ} → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (τ : Fin n → ℂ) ↦
      ∑ a : Fin n, τ a ^ (2 : ℕ) + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else (0 : ℂ)

namespace YgaHelp

private lemma inner_left {n : ℕ} (σ : Fin n → ℂ) (a : Fin n) :
    (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - ((a : ℕ) : ℂ)) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have h : (a : ℕ) ≤ n - 1 := by omega
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h, Nat.cast_sub h1]
  push_cast; ring

private lemma inner_right {n : ℕ} (σ : Fin n → ℂ) (b : Fin n) :
    (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * ((b : ℕ) : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  ring

end YgaHelp

theorem UpperTheory.Reformulated.B.CasimirElement.main :
    ∀ {n : ℕ} (σ : Fin n → ℂ),
      UpperTheory.Reformulated.B.CasimirElement.casC σ =
        ∑ a : Fin n, σ a ^ (2 : ℕ) + ∑ a : Fin n, σ a * ((↑n : ℂ) - (1 : ℂ) - (2 : ℂ) * (↑(↑a : ℕ) : ℂ)) := by
  intro n σ
  unfold UpperTheory.Reformulated.B.CasimirElement.casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := by
    intro a b; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [YgaHelp.inner_left, YgaHelp.inner_right]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
end

section

noncomputable def UpperTheory.Reformulated.B.Qj27.dc :
    {Y : Type} → {m : ℕ} → ((Fin (m + (1 : ℕ)) → Y) → ℝ) → (Fin (m + (2 : ℕ)) → Y) → ℝ :=
    fun {Y : Type} {m : ℕ} (F : (Fin (m + (1 : ℕ)) → Y) → ℝ) (y : Fin (m + (2 : ℕ)) → Y) ↦
      ∑ i : Fin (m + (2 : ℕ)), (-1 : ℝ) ^ (↑i : ℕ) * F fun (j : Fin (m + (1 : ℕ))) ↦ y (i.succAbove j)

theorem UpperTheory.Reformulated.B.Qj27.dc_cons :
    ∀ {Y : Type} {m : ℕ} (F : (Fin (m + (2 : ℕ)) → Y) → ℝ) (a : Y) (w : Fin (m + (2 : ℕ)) → Y),
      UpperTheory.Reformulated.B.Qj27.dc F (Fin.cons a w) =
        F w - UpperTheory.Reformulated.B.Qj27.dc (fun (w' : Fin (m + (1 : ℕ)) → Y) ↦ F (Fin.cons a w')) w := by
  intro Y m F a w
  have h : ∀ i : Fin (m + 2),
      (fun j : Fin (m + 2) ↦ (Fin.cons a w : Fin (m + 3) → Y) (i.succ.succAbove j)) =
        (Fin.cons a (fun j : Fin (m + 1) ↦ w (i.succAbove j)) : Fin (m + 2) → Y) := by
    intro i
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  unfold UpperTheory.Reformulated.B.Qj27.dc
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i, Fin.val_succ, pow_succ]
    ring
end
