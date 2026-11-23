module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open UpperTheory.V.FW

private theorem cancel_prod {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι] (a : ι → A)
    (S : Finset ι) (h : ∀ j ∈ S, ∀ m : ℕ, m • a j = 0 → m = 0) (x : AddMonoidAlgebra k A)
    (hx : x * ∏ j ∈ S, (1 - AddMonoidAlgebra.single (a j) (1 : k)) = 0) : x = 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert j S hj ih =>
    apply ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    apply nzd k A (a j) _ (h j (Finset.mem_insert_self _ _))
    rw [Finset.prod_insert hj] at hx
    rw [← hx]; ring

theorem UpperTheory.V.FW.sinLem :
    ∀ (k A ι : Type) [CommRing k] [AddCommGroup A] [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ι → A) (N : ℕ) (P : ℕ → k), N ≠ 0 → (∀ i (m : ℤ), m • η i = 0 → m = 0) → (∀ i j, i ≠ j → ∀ a b : ℤ, a • η i = b • η j → a = 0) → sinE η N P = 0 → ∀ s < N, P s = 0 := by
  intro k A ι _ _ _ _ _ η N P hN htor hpair hE s hs
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let H : AddSubgroup A := AddSubgroup.zmultiples (N • η i0)
  let φ : A →+ A ⧸ H := QuotientAddGroup.mk' H
  have hmap := sinMap k A (A ⧸ H) ι φ η N P
  rw [hE, map_zero] at hmap
  simp only [sinE] at hmap
  rw [Finset.sum_eq_single i0] at hmap
  · have hF : (∑ t ∈ Finset.range N, AddMonoidAlgebra.single (t • φ (η i0)) (P t) : AddMonoidAlgebra k (A ⧸ H)) = 0 := by
      apply cancel_prod (fun j => N • φ (η j)) (Finset.univ.erase i0) _ _ hmap.symm
      intro j hj m hm
      have hji : j ≠ i0 := Finset.ne_of_mem_erase hj
      rw [← map_nsmul φ, ← map_nsmul φ] at hm
      have hm' : m • N • η j ∈ H := (QuotientAddGroup.eq_zero_iff _).mp hm
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hm'
      have e1 : ((m * N : ℕ) : ℤ) • η j = m • N • η j := by
        rw [natCast_zsmul, mul_smul]
      have e2 : (b * (N : ℤ)) • η i0 = b • N • η i0 := by
        rw [mul_smul, natCast_zsmul]
      have hz := hpair j i0 hji ((m * N : ℕ) : ℤ) (b * N) (by rw [e1, e2, hb])
      have hmN : m * N = 0 := by exact_mod_cast hz
      rcases Nat.mul_eq_zero.mp hmN with h | h
      · exact h
      · exact absurd h hN
    have hcoef := congrArg (fun f : AddMonoidAlgebra k (A ⧸ H) => f.coeff (s • φ (η i0))) hF
    simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
      Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
    rw [Finset.sum_eq_single s] at hcoef
    · simpa using hcoef
    · intro t ht hts
      rw [Finsupp.single_apply, if_neg]
      intro he
      rw [← map_nsmul φ, ← map_nsmul φ] at he
      have hmem := (QuotientAddGroup.eq (s := H)).mp he
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      have h0 : (b * N - ((s : ℤ) - t)) • η i0 = 0 := by
        rw [sub_smul, mul_smul, natCast_zsmul, hb, sub_smul, natCast_zsmul, natCast_zsmul]
        abel
      have h1 := htor i0 _ h0
      have htN := Finset.mem_range.mp ht
      have hts' : (t : ℤ) = s := by
        rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
        · nlinarith
        · subst hb0
          omega
        · nlinarith
      exact hts (by exact_mod_cast hts')
    · intro h
      exact absurd (Finset.mem_range.mpr hs) h
  · intro i _ hi
    have hmem : i0 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hmem, mul_zero]
    have hz : N • φ (η i0) = 0 := by
      rw [← map_nsmul φ]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)
    rw [hz, sub_eq_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i0) h
end

section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.algK :
    ∀ (l : ℕ) [Fact l.Prime] (a m b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [IsAlgClosed k] [CommGroup G] [Finite G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ J : G) (θ : MonoidAlgebra k G), m.Coprime l → γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, (g * (p g)⁻¹) ^ (l ^ a * m) = 1) → p J = 1 → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → (∀ χ : G →* kˣ, χ J = -1 → tw χ π θ ≠ 0) → (MonoidAlgebra.of k G γ - 1) ^ (l ^ K * l ^ a) ∈ Ideal.span {θ, 1 + MonoidAlgebra.of k G J} := by
  intro l _ a m b K k G Q _ _ _ _ _ _ p π γ J θ hml hγ hp hord hpJ hπ hπγ htw
  have hl : l.Prime := Fact.out
  let I : Ideal (MonoidAlgebra k G) := Ideal.span {θ, 1 + MonoidAlgebra.of k G J}
  let r : MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⧸ I) := Ideal.Quotient.mkₐ k I
  have hr : ∀ x, r x = 0 ↔ x ∈ I := fun x => by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem
  let qh : G →* G :=
    { toFun := fun g => (g * (p g)⁻¹) ^ (l ^ a)
      map_one' := by simp
      map_mul' := by
        intro x y
        rw [map_mul, mul_inv, mul_mul_mul_comm, mul_pow] }
  let D : Subgroup G := qh.range
  let qD : G →* D := qh.rangeRestrict
  have hcard : (Nat.card D : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k l] at h
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' l h
    obtain ⟨g, hg⟩ := d.2
    have h1 : (d : G) ^ m = 1 := by
      rw [← hg]
      show ((g * (p g)⁻¹) ^ (l ^ a)) ^ m = 1
      rw [← pow_mul]
      exact hord g
    have h2 : orderOf d ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using h1)
    rw [hd] at h2
    have h3 : l ∣ Nat.gcd m l := Nat.dvd_gcd h2 dvd_rfl
    rw [hml] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  let ρ : D →* (MonoidAlgebra k G ⧸ I) :=
    ((r : MonoidAlgebra k G →+* (MonoidAlgebra k G ⧸ I)) : MonoidAlgebra k G →* (MonoidAlgebra k G ⧸ I)).comp
      ((MonoidAlgebra.of k G).comp D.subtype)
  have hρ : ∀ g, ρ (qD g) = r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ (l ^ a))) := fun g => rfl
  have hθ : r θ = 0 := (hr θ).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hJ : r (MonoidAlgebra.of k G J) = -1 := by
    have h0 : r (1 + MonoidAlgebra.of k G J) = 0 :=
      (hr _).mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [map_add (f := _), map_one] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have hla : l ^ a ≠ 0 := pow_ne_zero _ hl.ne_zero
  rw [← hr]
  apply sepChar k D _ ρ _ hcard
  intro ψ e he
  by_cases he0 : e = 0
  · rw [he0, mul_zero]
  let F : k ≃+* k := (iterateFrobeniusEquiv k l a).symm
  let χ : G →* kˣ := (Units.map (F : k →* k)).comp (ψ.comp qD)
  have hχ : ∀ g, (χ g : k) ^ (l ^ a) = ψ (qD g) := by
    intro g
    show (F (ψ (qD g) : k)) ^ (l ^ a) = _
    rw [← iterateFrobeniusEquiv_def]
    exact RingEquiv.apply_symm_apply _ _
  have hT : r (tw χ p θ) ^ (l ^ a) * e = 0 := by
    have := frobEig l a k G _ r p χ e θ (by
      intro g
      rw [hχ g, ← hρ g]
      exact he (qD g))
    rw [← this, hθ, zero_pow hla, zero_mul]
  have hχJ : χ J = -1 := by
    have h1 := he (qD J)
    rw [hρ J, hpJ, inv_one, mul_one, map_pow, map_pow, hJ] at h1
    have h2 : ((-1 : k) ^ (l ^ a)) • e = (ψ (qD J) : k) • e := by
      rw [← h1, Algebra.smul_def, map_pow, map_neg, map_one]
    have h3 := smul_left_injective k he0 h2
    rw [← hχ J] at h3
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    apply (iterateFrobeniusEquiv k l a).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def]
    exact h3.symm
  obtain ⟨c, hc⟩ := phiDvd l b K k G Q p π γ χ θ hγ hp hπ hπγ (htw χ hχJ)
  rw [pow_mul, hc, mul_pow, map_mul, map_pow, map_pow, mul_right_comm, hT, zero_mul]
end

section

open UpperTheory.V.FW

private theorem UpperTheory.V.FW.card_range_inf_torsion_le_index_pow (l : ℕ) [Fact l.Prime] (C : Type) [CommGroup C] [Finite C]
    (φ ψ : C →* C) (N : ℕ) (hc : ∀ x, φ (ψ x) = ψ (φ x))
    (hN : ∀ x, ∃ y, (φ y) ^ l = φ (ψ^[N] x)) :
    Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ ψ.range).index ^ N := by
  set U : Subgroup C := (powR (C := φ.range) l).comap φ.rangeRestrict with hUdef
  have hU : ∀ x, x ∈ U ↔ ∃ y, (φ y) ^ l = φ x := by
    intro x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨φ y, y, rfl⟩, Subtype.ext hy⟩
  have h1 : Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) = U.index := by
    rw [hUdef, Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective,
      (cardTors φ.range).1 l]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩,
      fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hle : U ≤ U.comap ψ := by
    intro x hx
    obtain ⟨y, hy⟩ := (hU x).1 hx
    exact (hU _).2 ⟨ψ y, by rw [hc, hc, ← hy, map_pow]⟩
  set S : C ⧸ U →* C ⧸ U := QuotientGroup.map U U ψ hle with hS
  let T : AddMonoid.End (Additive (C ⧸ U)) := MonoidHom.toAdditive S
  have hT : ∀ n (x : C), (T ^ n) (Additive.ofMul (x : C ⧸ U)) =
      Additive.ofMul ((ψ^[n] x : C) : C ⧸ U) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Function.iterate_succ_apply, ← ih]
      rfl
  have hT0 : T ^ N = 0 := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have : v = Additive.ofMul (x : C ⧸ U) := by rw [hx]; rfl
    subst this
    have h := hT N x
    rw [(QuotientGroup.eq_one_iff _).2 ((hU _).2 (hN x))] at h
    exact h
  have h2 := nilCard _ T N hT0
  have h3 : (AddMonoidHom.range T).index = S.range.index := rfl
  have h4 : S.range.index ∣ (powR (C := C) l ⊔ ψ.range).index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]
    refine Subgroup.index_dvd_of_le (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff _).2 ((hU _).2 ⟨x, by simp⟩)).symm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : C ⧸ U), rfl⟩
  rw [h1]
  refine le_trans (le_of_eq ?_) (h2.trans ?_)
  · rfl
  · rw [h3]
    exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h4) N

theorem UpperTheory.V.FW.core :
    ∀ (l : ℕ) [Fact l.Prime] (G C : Type) [CommGroup G] [CommGroup C] [Finite C] (ρ : Representation ℤ G (Additive C)) (J γ : G) (Jc γc : C →* C) (θ : MonoidAlgebra ℤ G) (N : ℕ), J * J = 1 → (∀ x, ρ J (Additive.ofMul x) = Additive.ofMul (Jc x)) → (∀ x, ρ γ (Additive.ofMul x) = Additive.ofMul (γc x)) → ρ.asAlgebraHom (θ * (1 - MonoidAlgebra.of ℤ G J)) = 0 → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} → Nat.card (difR Jc ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ difR γc).index ^ N := by
  intro l _ G C _ _ _ ρ J γ Jc γc θ N hJJ hJ hγ hθ hmem
  have key : ∀ (g : G) (gc : C →* C), (∀ x, ρ g (Additive.ofMul x) = Additive.ofMul (gc x)) →
      ∀ x, ρ.asAlgebraHom (1 - MonoidAlgebra.of ℤ G g) (Additive.ofMul x) =
        Additive.ofMul ((MonoidHom.id C / gc) x) := by
    intro g gc h x
    rw [map_sub, map_one, Representation.asAlgebraHom_of, LinearMap.sub_apply, h]
    simp
  have hφ := key J Jc hJ
  have hψ := key γ γc hγ
  set φ := MonoidHom.id C / Jc
  set ψ := MonoidHom.id C / γc
  set a := 1 - MonoidAlgebra.of ℤ G J with ha
  set b := 1 - MonoidAlgebra.of ℤ G γ with hb
  have hit : ∀ n x, ρ.asAlgebraHom (b ^ n) (Additive.ofMul x) = Additive.ofMul (ψ^[n] x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, map_mul, mul_apply_eq_comp, hψ, ih, Function.iterate_succ_apply]
  refine card_range_inf_torsion_le_index_pow l C φ ψ N (fun x => ?_) (fun x => ?_)
  · apply Additive.ofMul.injective
    rw [← hφ, ← hψ, ← hψ, ← hφ, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul,
      ← map_mul, mul_comm]
  · have hmem' : b ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} := by
      have : b = -(MonoidAlgebra.of ℤ G γ - 1) := by rw [hb, neg_sub]
      rw [this, neg_pow]
      exact Ideal.mul_mem_left _ _ hmem
    obtain ⟨u, w, hw, h1⟩ := Ideal.mem_span_insert.1 hmem'
    obtain ⟨v, z, h2⟩ := Ideal.mem_span_pair.1 hw
    have hJ2 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by
      rw [← map_mul, hJJ, map_one]
    have h3 : a * b ^ N = u * (θ * a) + l • (a * z) := by
      rw [h1, ← h2, ha, nsmul_eq_mul]
      linear_combination (-v) * hJ2
    refine ⟨Additive.toMul (ρ.asAlgebraHom z (Additive.ofMul x)), ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow, ← hφ, ← hφ, ← hit, ofMul_toMul, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
      ← map_mul, ← map_mul, h3, map_add, map_mul _ u, hθ, mul_zero, zero_add, map_nsmul,
      LinearMap.smul_apply]
end

section

open UpperTheory.V.FW

private theorem card_hom_surj (l : ℕ) {G A : Type} [Group G] [Group A] (π : G →* A) (hπ : Function.Surjective π)
    (P : G → Prop) (hP : ∀ u, P u ↔ π u = 1) :
    Nat.card {φ : G → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u, P u → φ u = 0} =
      Nat.card (A →* Multiplicative (ZMod l)) := by
  have key : ∀ (φ : G → ZMod l), (∀ a b, φ (a * b) = φ a + φ b) → (∀ u, P u → φ u = 0) →
      ∀ x y, π x = π y → φ x = φ y := by
    intro φ hadd hker x y hxy
    have h0 : φ (y⁻¹ * x) = 0 := hker _ ((hP _).mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    calc φ x = φ (y * (y⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = φ y := by rw [hadd, h0, add_zero]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun f => ⟨fun g => Multiplicative.toAdd (f (π g)), ?_, ?_⟩) ⟨?_, ?_⟩
  · intro a b
    simp [map_mul]
  · intro u hu
    show Multiplicative.toAdd (f (π u)) = 0
    rw [(hP u).mp hu, map_one, toAdd_one]
  · intro f f' h
    ext a
    obtain ⟨g, rfl⟩ := hπ a
    have := congrArg (fun φ => φ.1 g) h
    simpa using this
  · rintro ⟨φ, hadd, hker⟩
    refine ⟨{ toFun := fun a => Multiplicative.ofAdd (φ (Function.surjInv hπ a)), map_one' := ?_, map_mul' := ?_ }, ?_⟩
    · show Multiplicative.ofAdd (φ (Function.surjInv hπ 1)) = 1
      rw [key φ hadd hker _ 1 (by rw [Function.surjInv_eq hπ, map_one]), hker 1 ((hP 1).mpr (map_one π)), ofAdd_zero]
    · intro a b
      show Multiplicative.ofAdd (φ (Function.surjInv hπ (a * b))) =
        Multiplicative.ofAdd (φ (Function.surjInv hπ a)) * Multiplicative.ofAdd (φ (Function.surjInv hπ b))
      have e : φ (Function.surjInv hπ (a * b)) = φ (Function.surjInv hπ a * Function.surjInv hπ b) :=
        key φ hadd hker _ _ (by simp only [map_mul, Function.surjInv_eq hπ])
      rw [e, hadd, ofAdd_add]
    · apply Subtype.ext
      funext g
      show Multiplicative.toAdd (Multiplicative.ofAdd (φ (Function.surjInv hπ (π g)))) = φ g
      rw [toAdd_ofAdd]
      exact key φ hadd hker _ _ (Function.surjInv_eq hπ _)

private theorem card_hom_sub_le (l : ℕ) [Fact l.Prime] (A : Type) [CommGroup A] [Finite A] (B : Subgroup A) :
    Nat.card (B →* Multiplicative (ZMod l)) ≤ Nat.card (A →* Multiplicative (ZMod l)) := by
  rw [(cardTors B).2 l, (cardTors A).2 l, (cardTors B).1 l, (cardTors A).1 l]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : B) : A), ?_⟩) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx ⊢
    simp only [powMonoidHom_apply] at hx ⊢
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

theorem UpperTheory.V.FW.homCyc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U N : Subgroup Γ) [U.Normal] [N.Normal] [N.FiniteIndex], N ≤ U → IsCyclic (Γ ⧸ U) → (∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N) → Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} ≤ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ N, φ u = 0} := by
  intro l _ Γ _ U N _ _ _ hNU hcyc hcomm
  have hU : ∀ (h : Γ ⧸ N) (u : Γ), u ∈ U → Commute h (u : Γ ⧸ N) := by
    intro h u hu
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
    have := hcomm g u hu
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨gU, hgen⟩ := IsCyclic.exists_generator (α := Γ ⧸ U)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective gU
  have hdecomp : ∀ x : Γ, ∃ i : ℤ, ∃ u ∈ U, x = g0 ^ i * u := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (x : Γ ⧸ U))
    refine ⟨i, (g0 ^ i)⁻¹ * x, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [← QuotientGroup.mk_zpow] at hi
    exact QuotientGroup.eq.mp hi
  have hcomm' : ∀ a b : Γ ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, u1, hu1, rfl⟩ := hdecomp x
    obtain ⟨j, u2, hu2, rfl⟩ := hdecomp y
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
    have c12 : Commute ((g0 : Γ ⧸ N) ^ i) ((g0 : Γ ⧸ N) ^ j) := Commute.zpow_zpow_self _ _ _
    apply Commute.eq
    exact Commute.mul_left (c12.mul_right (hU _ u2 hu2))
      (((hU _ u1 hu1).symm).mul_right (hU _ u2 hu2))
  letI : CommGroup (Γ ⧸ N) := { (inferInstance : Group (Γ ⧸ N)) with mul_comm := hcomm' }
  let f : U →* Γ ⧸ N := (QuotientGroup.mk' N).comp U.subtype
  have h1 := card_hom_surj l f.rangeRestrict f.rangeRestrict_surjective (fun u : U => u.1 ∈ N) (by
    intro u
    rw [← Subtype.coe_inj]
    simp [f, QuotientGroup.eq_one_iff])
  have h2 := card_hom_surj l (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (fun u => u ∈ N)
    (by intro u; simp [QuotientGroup.eq_one_iff])
  beta_reduce at h1 h2
  rw [h1, h2]
  exact card_hom_sub_le l (Γ ⧸ N) f.range
end
