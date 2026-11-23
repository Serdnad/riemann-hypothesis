module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Basic
import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Card

@[expose] public section

section

open Function Cardinal

namespace GlobalTheory

theorem mk_addMonoidHom_le_of_surjective_of_injective {A A' X Y : Type} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup X] [AddCommGroup Y] (f : A →+ A') (hf : Surjective f)
    (ι : X →+ Y) (hι : Injective ι) : #(A' →+ X) ≤ #(A →+ Y) := by
  refine mk_le_of_injective (f := fun g => (ι.comp g).comp f) ?_
  intro g h hgh
  ext x
  obtain ⟨a, rfl⟩ := hf x
  exact hι (DFunLike.congr_fun hgh a)

theorem exists_injective_zmod_addMonoidHom {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) :
    ∃ ι : ZMod a →+ ZMod n, Injective ι := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  haveI : NeZero a := ⟨ha⟩
  refine ⟨ZMod.lift a ⟨zmultiplesHom (ZMod (a * k)) (k : ZMod (a * k)), ?_⟩, ?_⟩
  · simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : ((x.val : ℤ) : ZMod a) = x := by simp
    rw [← h2, ZMod.lift_coe] at hx
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul] at hx
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
    have hd : a ∣ x.val := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hk) hx
    have hv : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]

theorem mk_lt_mk_addMonoidHom_zmod_prime (p : ℕ) [hp : Fact p.Prime] (V : Type) [AddCommGroup V]
    (hV : ∀ x : V, p • x = 0) [Infinite V] : #V < #(V →+ ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod p) V := AddCommGroup.zmodModule hV
  let b := Module.Basis.ofVectorSpace (ZMod p) V
  set ι := Module.Basis.ofVectorSpaceIndex (ZMod p) V
  have hι : Infinite ι := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    haveI := h
    haveI : Finite V := Finite.of_equiv _ b.equivFun.toEquiv.symm
    exact not_finite V
  have hV1 : #V = #ι := by
    rw [b.repr.toEquiv.cardinal_eq, mk_finsupp_of_infinite, max_eq_left]
    exact (lt_aleph0_of_finite _).le.trans (aleph0_le_mk ι)
  have hr : Module.rank (ZMod p) V = #ι := b.mk_eq_rank''.symm
  have h0 : ℵ₀ ≤ Module.rank (ZMod p) V := hr ▸ aleph0_le_mk ι
  have h1 := lift_rank_lt_rank_dual h0
  rw [lift_id, rank_dual_eq_card_dual_of_aleph0_le_rank h0] at h1
  calc #V = Module.rank (ZMod p) V := by rw [hV1, hr]
    _ < #(V →ₗ[ZMod p] ZMod p) := h1
    _ = #(V →+ ZMod p) := ((AddMonoidHom.toZModLinearMapEquiv p).toEquiv.cardinal_eq).symm

theorem mk_lt_mk_addMonoidHom_zmod (n : ℕ) : ∀ (A : Type) [AddCommGroup A],
    (∀ x : A, n • x = 0) → n ≠ 0 → Infinite A → #A < #(A →+ ZMod n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ hA hn hinf
  rcases eq_or_ne n 1 with rfl | h1
  · exfalso
    haveI : Subsingleton A := ⟨fun x y => by
      have hx : x = 0 := by simpa using hA x
      have hy : y = 0 := by simpa using hA y
      rw [hx, hy]⟩
    exact not_finite A
  obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
  haveI := Fact.mk hp
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  let f : A →+ A := AddMonoidHom.mk' (fun x => p • x) (fun x y => nsmul_add x y p)
  let P : AddSubgroup A := f.range
  have hmul : #A = #(A ⧸ P) * #P := by
    rw [(AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := P)).cardinal_eq, mk_prod,
      lift_id, lift_id]
  have hPle : #P ≤ #A := mk_le_of_injective Subtype.val_injective
  have hQle : #(A ⧸ P) ≤ #A := mk_le_of_surjective (QuotientAddGroup.mk_surjective)
  have hAinf : ℵ₀ ≤ #A := aleph0_le_mk A
  rcases hPle.lt_or_eq with hPlt | hPeq
  · rcases hQle.lt_or_eq with hQlt | hQeq
    · exact absurd hmul (ne_of_gt (mul_lt_of_lt hAinf hQlt hPlt))

    · letI : Infinite (A ⧸ P) := Cardinal.infinite_iff.mpr (hQeq ▸ hAinf)
      have hQp : ∀ y : A ⧸ P, p • y = 0 := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩
      obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_right p m)
      calc #A = #(A ⧸ P) := hQeq.symm
        _ < #(A ⧸ P →+ ZMod p) := mk_lt_mk_addMonoidHom_zmod_prime p (A ⧸ P) hQp
        _ ≤ #(A →+ ZMod (p * m)) :=
          mk_addMonoidHom_le_of_surjective_of_injective (QuotientAddGroup.mk' P)
            (QuotientAddGroup.mk_surjective) ι hι

  · letI : Infinite P := Cardinal.infinite_iff.mpr (hPeq ▸ hAinf)
    have hPm : ∀ y : P, m • y = 0 := by
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      show m • (p • x) = 0
      rw [smul_smul, mul_comm, hA x]
    have hlt : m < p * m := by
      have := hp.two_le
      have := Nat.pos_of_ne_zero hm
      nlinarith
    have hP := ih m hlt P hPm hm inferInstance
    obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_left m p)
    calc #A = #P := hPeq.symm
      _ < #(P →+ ZMod m) := hP
      _ ≤ #(A →+ ZMod (p * m)) :=
        mk_addMonoidHom_le_of_surjective_of_injective f.rangeRestrict
          f.rangeRestrict_surjective ι hι

theorem finite_of_perfect_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A]
    [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C]
    [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C),
    Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  intro n _ A B C _ _ _ _ _ _ _ b ⟨e⟩ hb hbf
  have key : ∀ (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [AddCommGroup Y]
      [Module (ZMod n) Y] (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] C), Bijective c.flip → Infinite X →
      #X < #Y := by
    intro X Y _ _ _ _ c hc hX
    have h1 : #Y = #(X →+ ZMod n) := by
      have e1 := (LinearEquiv.ofBijective c.flip hc).toEquiv
      have e2 : (X →ₗ[ZMod n] C) ≃ (X →ₗ[ZMod n] ZMod n) :=
        { toFun := fun g => e.toLinearMap ∘ₗ g
          invFun := fun g => e.symm.toLinearMap ∘ₗ g
          left_inv := fun g => by ext; simp
          right_inv := fun g => by ext; simp }
      have e3 := (AddMonoidHom.toZModLinearMapEquiv n (M := X) (M₁ := ZMod n)).toEquiv.symm
      exact (e1.trans (e2.trans e3)).cardinal_eq
    rw [h1]
    refine mk_lt_mk_addMonoidHom_zmod n X (fun x => ?_) (NeZero.ne n) hX
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hbff : Bijective b.flip.flip := by simpa using hb
  have hA : Finite A := by
    by_contra hA
    rw [not_finite_iff_infinite] at hA
    have h1 := key A B b hbf hA
    haveI : Infinite B := Cardinal.infinite_iff.mpr ((aleph0_le_mk A).trans h1.le)
    exact lt_asymm h1 (key B A b.flip hbff inferInstance)
  have hB : Finite B := by
    by_contra hB
    rw [not_finite_iff_infinite] at hB
    have h1 := key B A b.flip hbff hB
    haveI : Infinite A := Cardinal.infinite_iff.mpr ((aleph0_le_mk B).trans h1.le)
    exact not_finite A
  exact ⟨hA, hB⟩

end GlobalTheory
end

section

open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem quotient_equiv_restrictedFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  intro Γ _ K ι c hK hfin hidem horth
  classical
  have hmk : ∀ v (g h : Γ), ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)) = QuotientGroup.mk h) ↔
      c v (g⁻¹ * h) ∈ K := by
    intro v g h
    rw [QuotientGroup.eq, Subgroup.mem_comap]
  have hle : ∀ v, K ≤ K.comap (c v) := fun v g hg => (hK g).1 hg v
  let F : Γ ⧸ K → ∀ v, Γ ⧸ K.comap (c v) := fun q v =>
    Quotient.liftOn' q (fun g => (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      exact (QuotientGroup.eq).2 (hle v hab))
  have hF : ∀ g v, F (QuotientGroup.mk g) v = QuotientGroup.mk g := fun g v => rfl
  have hsupp : ∀ g, {w | F (QuotientGroup.mk g) w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))} =
      {v | c v g ∉ K} := by
    intro g
    ext w
    simp only [Set.mem_setOf_eq, hF, ne_eq, hmk, mul_one, map_inv, inv_mem_iff]
  let G : Γ ⧸ K → {f : ∀ v, Γ ⧸ K.comap (c v) //
      {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite} := fun q =>
    ⟨F q, by
      refine QuotientGroup.induction_on q ?_
      intro g
      rw [hsupp]
      exact hfin g⟩
  have hinj : Function.Injective G := by
    intro q₁ q₂ h12
    refine QuotientGroup.induction_on q₁ (fun g => ?_) h12
    refine QuotientGroup.induction_on q₂ (fun k => ?_)
    intro h12
    have h' : ∀ v, F (QuotientGroup.mk g) v = F (QuotientGroup.mk k) v :=
      fun v => congrFun (congrArg Subtype.val h12) v
    rw [QuotientGroup.eq, hK]
    intro v
    have := h' v
    rw [hF, hF, hmk] at this
    exact this
  have hcw : ∀ w (g : Γ), (QuotientGroup.mk (c w g) : Γ ⧸ K.comap (c w)) = QuotientGroup.mk g := by
    intro w g
    rw [hmk, map_mul, map_inv, hidem, inv_mul_cancel]
    exact K.one_mem
  have hlist : ∀ (x : ι → Γ) (l : List ι), l.Nodup → ∀ w,
      c w ((l.map (fun v => c v (x v))).prod) = if w ∈ l then c w (x w) else 1 := by
    intro x l
    induction l with
    | nil => intro _ w; simp
    | cons a t ih =>
      intro hl w
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
      by_cases hw : w = a
      · subst hw
        simp [hidem, hl.1]
      · rw [horth a w _ (Ne.symm hw), one_mul]
        simp [hw]
  have hsurj : Function.Surjective G := by
    rintro ⟨f, hf⟩
    let x : ι → Γ := fun v => (f v).out
    refine ⟨QuotientGroup.mk ((hf.toFinset.toList.map (fun v => c v (x v))).prod), ?_⟩
    apply Subtype.ext
    funext w
    show F (QuotientGroup.mk _) w = f w
    rw [hF, ← hcw w, hlist x hf.toFinset.toList (Finset.nodup_toList _) w]
    by_cases hw : w ∈ hf.toFinset.toList
    · rw [if_pos hw, hcw]
      exact Quotient.out_eq (f w)
    · rw [if_neg hw]
      rw [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      exact hw.symm
  exact ⟨Equiv.ofBijective G ⟨hinj, hsurj⟩, fun g v => rfl⟩

end GlobalTheory
end

section

open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem numerical_bounds_of_forty_mul_lt : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 →
    40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  intro l H N η r hN hη hηH hr hl
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hH : 2 ≤ H := by omega
  have hHN : 4 * H ≤ H * N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    nlinarith
  have hNr : 4 * (N * r) ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    rw [this]; nlinarith
  have hsub : (N - 1) * r ≤ N * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hηr : 4 * (η * r) ≤ H * N ^ 2 := by
    have : η * r ≤ H * r := Nat.mul_le_mul_right _ hηH.le
    nlinarith
  have hNη : (N + 2) * η ≤ H * N ^ 2 := by
    have h1 : (N + 2) * η ≤ (N + 2) * H := Nat.mul_le_mul_left _ hηH.le
    have h2 : N + 2 ≤ N ^ 2 := by nlinarith
    have h3 : (N + 2) * H ≤ N ^ 2 * H := Nat.mul_le_mul_right _ h2
    nlinarith
  have hrη : r * η ≤ H * N ^ 2 := by
    have : r * η ≤ r * H := Nat.mul_le_mul_left _ hηH.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 * (N - 1) * r = 2 * ((N - 1) * r) := by ring
    rw [this]; nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have : 4 * η * r = 4 * (η * r) := by ring
    rw [this]; nlinarith
  · have : (r + 2) * η = r * η + 2 * η := by ring
    rw [this]; nlinarith

end GlobalTheory
end

section

namespace GlobalTheory.RelationExtension

section
variable {A E F : Type} [CommRing A] [CommRing E] [CommRing F]

def Rel (ι : A →+* E) (f : A →+* F) (π P : A) (e : E) (x : F) : Prop :=
  ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y ∧ x * f π ^ m = f a

theorem rel_unique (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) {e : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e x') : x = x' := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  obtain ⟨b, hb⟩ := hk (a * π ^ m' - a' * π ^ m) (y' * ι π ^ m - y * ι π ^ m') (by
    simp only [map_sub, map_mul, map_pow]
    linear_combination (-(ι π ^ m')) * h1 + (ι π ^ m) * h1')
  have hf := congrArg f hb
  rw [map_mul, hP, zero_mul, map_sub, map_mul, map_mul, map_pow, map_pow] at hf
  have hu' : IsUnit (f π ^ (m + m')) := hu.pow _
  have h3 : x * f π ^ (m + m') = x' * f π ^ (m + m') := by
    rw [pow_add]
    linear_combination (f π ^ m') * h2 - (f π ^ m) * h2' + hf
  exact hu'.mul_right_cancel h3

theorem rel_map (ι : A →+* E) (f : A →+* F) (π P : A) (a : A) : Rel ι f π P (ι a) (f a) := ⟨a, 0, 0, by simp, by simp⟩

theorem rel_add (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e + e') (x + x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * π ^ m' + a' * π ^ m, m + m', y * ι π ^ m' + y' * ι π ^ m, ?_, ?_⟩
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (ι π ^ m') * h1 + (ι π ^ m) * h1'
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (f π ^ m') * h2 + (f π ^ m) * h2'

theorem rel_mul (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e * e') (x * x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * a', m + m', y * ι a' + ι a * y' + ι P * y * y', ?_, ?_⟩
  · rw [pow_add, map_mul]
    linear_combination (e' * ι π ^ m') * h1 + (ι a + ι P * y) * h1'
  · rw [pow_add, map_mul]
    linear_combination (x' * f π ^ m') * h2 + f a * h2'

end

theorem exists_extension {A E F : Type} [CommRing A] [CommRing E] [CommRing F]
    (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hs : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) :
    ∃ g : E →+* F, ∀ a : A, g (ι a) = f a := by
  have hex : ∀ e, ∃ x, Rel ι f π P e x := fun e => by
    obtain ⟨a, m, y, h⟩ := hs e
    exact ⟨f a * Ring.inverse (f π ^ m), a, m, y, h, by rw [mul_assoc, Ring.inverse_mul_cancel _ (hu.pow m), mul_one]⟩
  choose g hg using hex
  have hgu : ∀ e x, Rel ι f π P e x → g e = x := fun e x h => rel_unique ι f π P hu hP hk (hg e) h
  have h1 := rel_map ι f π P 1
  rw [map_one, map_one] at h1
  have h0 := rel_map ι f π P 0
  rw [map_zero, map_zero] at h0
  exact ⟨{ toFun := g
           map_one' := hgu _ _ h1
           map_mul' := fun e e' => hgu _ _ (rel_mul ι f π P (hg e) (hg e'))
           map_zero' := hgu _ _ h0
           map_add' := fun e e' => hgu _ _ (rel_add ι f π P (hg e) (hg e')) },
    fun a => hgu _ _ (rel_map ι f π P a)⟩

end GlobalTheory.RelationExtension
end

section

namespace GlobalTheory

theorem card_le_of_double_annihilator (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X]
    (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O)
    (h1 : ∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S)
    (h2 : ∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0)
    (h3 : ∀ e : E, a • e = 0 → e ∈ Es) :
    Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  classical
  let L : X →ₗ[O] (F → E) :=
    LinearMap.pi fun y => if (∀ s ∈ S, β (y : Y) s = 0) then β y else 0
  have hL : ∀ x (y : F), L x y = if (∀ s ∈ S, β (y : Y) s = 0) then β y x else 0 := by
    intro x y
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hS : S ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext y
    rw [hL]
    split_ifs with h
    · exact h x hx
    · rfl
  have hker : LinearMap.ker L ≤ S := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply h1
    intro y hy
    have := congrFun hx ⟨y, (h2 y hy).1⟩
    rw [hL, if_pos hy] at this
    exact this
  have hmem : ∀ x (y : F), L x y ∈ Es := by
    intro x y
    apply h3
    rw [hL]
    split_ifs with h
    · rw [← LinearMap.smul_apply, ← map_smul, (h2 y h).2, map_zero, LinearMap.zero_apply]
    · exact smul_zero a
  let g : X ⧸ S → (F → Es) := fun q y =>
    ⟨S.liftQ L hS q y, by
      induction q using Submodule.Quotient.induction_on with
      | H x => simpa using hmem x y⟩
  have hinj : Function.Injective g := by
    intro q r hqr
    have h' : S.liftQ L hS q = S.liftQ L hS r := by
      funext y
      have := congrFun hqr y
      simpa [g] using congrArg Subtype.val this
    exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot S L hS hker)) h'
  have hq : Nat.card (X ⧸ S) ≤ Es.card ^ F.card := by
    have := Nat.card_le_card_of_injective g hinj
    rwa [Nat.card_fun, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard] at this
  rw [Submodule.card_eq_card_quotient_mul_card S, mul_comm]
  exact Nat.mul_le_mul_right _ hq

end GlobalTheory
end
