module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

section

open Polynomial IntermediateField

namespace GlobalTheory

theorem isSeparable_and_natDegree_le_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G) [N.FiniteIndex]
    (hG : ∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E))
    (x : E) (hx : ∀ n ∈ N, act n x = x) :
    IsIntegral F x ∧ IsSeparable F x ∧ (minpoly F x).natDegree ≤ N.index := by
  classical
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let f : G ⧸ N → E := fun q => Quotient.liftOn' q (fun g => act g x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := hx _ hab
    show act a x = act b x
    calc act a x = act a (act (a⁻¹ * b) x) := by rw [this]
      _ = act b x := by rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hf : ∀ g : G, f (QuotientGroup.mk g) = act g x := fun g => rfl
  let S : Finset E := Finset.univ.image f
  have hS : ∀ y, y ∈ S ↔ ∃ g : G, act g x = y := by
    intro y
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, (hf g).symm⟩
    · rintro ⟨g, rfl⟩; exact ⟨_, hf g⟩
  have hcard : S.card ≤ N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact Finset.card_image_le.trans (by simp)
  let p : E[X] := ∏ y ∈ S, (X - C y)
  have hpmon : p.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hpsep : p.Separable := separable_prod_X_sub_C_iff'.2 (fun a _ b _ h => h)
  have hpdeg : p.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card S id
  have hpinv : ∀ g : G, p.map ((act g : E ≃ₐ[F] E) : E →+* E) = p := by
    intro g
    simp only [p, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
    have himg : S.image (act g) = S := by
      ext y
      simp only [Finset.mem_image, hS]
      constructor
      · rintro ⟨z, ⟨h, rfl⟩, rfl⟩
        exact ⟨g * h, by rw [map_mul, AlgEquiv.mul_apply]⟩
      · rintro ⟨h, rfl⟩
        exact ⟨act (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, by
          rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]⟩
    conv_rhs => rw [← himg]
    rw [Finset.prod_image (fun a _ b _ h => (act g).injective h)]
    rfl
  have hlift : p ∈ lifts (algebraMap F E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have : p.coeff n ∈ (⊥ : IntermediateField F E) := by
      apply hG
      intro g
      conv_rhs => rw [← hpinv g]
      rw [coeff_map]
      rfl
    exact mem_bot.1 this
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hpmon
  have hxS : x ∈ S := (hS x).2 ⟨1, by simp⟩
  have hqx : aeval x q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hqmap, eval_prod]
    exact Finset.prod_eq_zero hxS (by simp)
  have hint : IsIntegral F x := ⟨q, hqmon, hqx⟩
  have hdvd : minpoly F x ∣ q := minpoly.dvd F x hqx
  have hqsep : q.Separable := (separable_map (algebraMap F E)).1 (hqmap ▸ hpsep)
  refine ⟨hint, hqsep.of_dvd hdvd, ?_⟩
  calc (minpoly F x).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hqmon.ne_zero
    _ = S.card := by rw [hqdeg, hpdeg]
    _ ≤ N.index := hcard

theorem finiteDimensional_fixedField_map_of_finiteIndex : ∀ {F E : Type} [Field F] [Field E]
    [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex →
    (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) →
    FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  intro F E _ _ _ G _ act N hN hG
  set L := IntermediateField.fixedField (N.map act) with hLdef
  have key : ∀ y ∈ L, IsIntegral F y ∧ IsSeparable F y ∧ (minpoly F y).natDegree ≤ N.index := by
    intro y hy
    refine isSeparable_and_natDegree_le_of_fixed G act N hG y fun n hn => ?_
    exact (mem_fixedField_iff _ _).1 hy _ (Subgroup.mem_map_of_mem act hn)
  have hbound : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ N.index := by
    intro y hy
    rw [adjoin.finrank (key y hy).1]
    exact (key y hy).2.2
  let D : Set ℕ := {d | ∃ y ∈ L, Module.finrank F F⟮y⟯ = d}
  have hDne : D.Nonempty := ⟨_, 0, L.zero_mem, rfl⟩
  have hDbdd : BddAbove D := ⟨N.index, by rintro d ⟨y, hy, rfl⟩; exact hbound y hy⟩
  obtain ⟨x, hxL, hxmax⟩ := Nat.sSup_mem hDne hDbdd
  have hle : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ Module.finrank F F⟮x⟯ := by
    intro y hy
    rw [hxmax]
    exact le_csSup hDbdd ⟨y, hy, rfl⟩
  have hLx : L ≤ F⟮x⟯ := by
    intro y hy
    have hx := key x hxL
    have hy' := key y hy
    haveI := isSeparable_adjoin_pair_of_isSeparable F E hx.2.1 hy'.2.1
    haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin (by
      rintro z (rfl | rfl)
      · exact hx.1
      · exact hy'.1)
    obtain ⟨α, hα⟩ := Field.exists_primitive_element F F⟮x, y⟯
    have hz : F⟮(α : E)⟯ = F⟮x, y⟯ := by
      simpa only [lift_adjoin_simple, lift_top] using congr_arg lift hα
    have hKL : F⟮x, y⟯ ≤ L := by
      rw [adjoin_le_iff]
      rintro z (rfl | rfl)
      · exact hxL
      · exact hy
    have hxK : F⟮x⟯ ≤ F⟮x, y⟯ := adjoin_simple_le_iff.2 (subset_adjoin F _ (by simp))
    have heq : F⟮x⟯ = F⟮x, y⟯ := by
      apply eq_of_le_of_finrank_le hxK
      rw [← hz]
      exact hle _ (hKL α.2)
    rw [heq]
    exact subset_adjoin F _ (by simp)
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (key x hxL).1
  exact Module.Finite.of_injective (IntermediateField.inclusion hLx).toLinearMap
    (IntermediateField.inclusion_injective hLx)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem algebraMap_quot_bijective (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  haveI : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k (A ⧸ P)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem maximal_part (P : Ideal A) (hP : P.IsMaximal) :
    Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0 := by
  have hb := algebraMap_quot_bijective (k := k) P
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hb
  refine ⟨?_, ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩⟩
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · change u ∈ P ↔ e.symm (Ideal.Quotient.mkₐ k P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (P : Ideal A) [P.IsMaximal] (a : A) :
    ∃ c : k, a - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quot_bijective (k := k) P).2 (Ideal.Quotient.mk P a)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hc
  rw [← P.neg_mem_iff, neg_sub]
  exact hc

theorem span_sup_mul_eq (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (x : A) (hx : x ∈ I)
    (hxP : x ∉ I * P) : Ideal.span {x} ⊔ I * P = I := by
  have hKI : Ideal.span {x} ⊔ I * P ≤ I :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) Ideal.mul_le_left
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hKI
  have hPL : I * P ≤ I * L := hL ▸ le_sup_right
  have hLP : P ≤ L := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1
    (Ideal.dvd_iff_le.2 hPL))
  by_cases hLt : L = ⊤
  · rw [hL, hLt, Ideal.mul_top]
  · have := hP.eq_of_le hLt hLP
    subst this
    exact absurd (hL ▸ (le_sup_left : Ideal.span {x} ≤ _) (Ideal.mem_span_singleton_self x)) hxP

theorem rank_quot_mul_maximal (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) :
    Module.rank k (A ⧸ (I * P)) = Module.rank k (A ⧸ I) + 1 := by
  haveI := hP
  have hne : I * P ≠ I := by
    intro h
    have h2 : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact hP.ne_top (mul_left_cancel₀ (show I ≠ 0 from hI) h2)
  obtain ⟨x, hx, hxP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm Ideal.mul_le_left h)
  let f : (A ⧸ (I * P)) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_left : I * P ≤ I)).toLinearMap
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  set v : A ⧸ (I * P) := Ideal.Quotient.mk _ x with hvdef
  have hv0 : v ≠ 0 := fun h => hxP (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hker : LinearMap.ker f = k ∙ v := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hy : y ∈ I := by
        have h0 : f (Ideal.Quotient.mk _ y) = 0 := hz
        exact Ideal.Quotient.eq_zero_iff_mem.1 h0
      have hyK : y ∈ Ideal.span {x} ⊔ I * P := by
        rw [span_sup_mul_eq I P hI hP x hx hxP]; exact hy
      obtain ⟨a', ha', z', hz', hsum⟩ := Submodule.mem_sup.1 hyK
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
      obtain ⟨c, hc⟩ := exists_sub_mem (k := k) P a
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← hsum, hvdef, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        Ideal.Quotient.eq]
      have h3 : algebraMap k A c * x - (a * x + z') = -((a - algebraMap k A c) * x) - z' := by
        ring
      rw [h3]
      refine Ideal.sub_mem _ ((I * P).neg_mem ?_) hz'
      rw [mul_comm I P]
      exact Ideal.mul_mem_mul hc hx
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show f v = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  have h1 := LinearMap.rank_range_add_rank_ker f
  rw [LinearMap.range_eq_top.2 hf, rank_top, hker] at h1
  have hv1 : Module.rank k (k ∙ v) = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hv0]; simp
  rw [← h1, hv1]

end DedekindCodim
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem rank_quot_top : Module.rank k (A ⧸ (⊤ : Ideal A)) = 0 := by
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact rank_subsingleton' k _

theorem maximal_of_prime {p : Ideal A} (hp : Prime p) : p ≠ ⊥ ∧ p.IsMaximal := by
  have hne : p ≠ ⊥ := hp.ne_zero
  exact ⟨hne, ((Ideal.prime_iff_isPrime hne).1 hp).isMaximal hne⟩

theorem rank_quot_lt (J : Ideal A) (hJ : J ≠ ⊥) : Module.rank k (A ⧸ J) < Cardinal.aleph0 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top]; exact Cardinal.aleph0_pos
  | h₃ a p ha hp ih =>
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    rw [mul_comm, rank_quot_mul_maximal a p ha hpm]
    exact Cardinal.add_lt_aleph0 (ih ha) Cardinal.one_lt_aleph0

theorem rank_quot_mul (J : Ideal A) (hJ : J ≠ ⊥) : ∀ I : Ideal A, I ≠ ⊥ →
    Module.rank k (A ⧸ (I * J)) = Module.rank k (A ⧸ I) + Module.rank k (A ⧸ J) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    intro I _
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top, Ideal.mul_top, add_zero]
  | h₃ a p ha hp ih =>
    intro I hI
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    have hIa : I * a ≠ ⊥ := mul_ne_zero (show I ≠ 0 from hI) ha
    rw [show I * (p * a) = (I * a) * p by ring, rank_quot_mul_maximal _ p hIa hpm, ih ha I hI,
      mul_comm p a, rank_quot_mul_maximal a p ha hpm, add_assoc]

theorem finite_quot (I : Ideal A) (hI : I ≠ ⊥) : Module.Finite k (A ⧸ I) :=
  Module.rank_lt_aleph0_iff.1 (rank_quot_lt I hI)

theorem finrank_quot_mul (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J) := by
  haveI := finite_quot (k := k) I hI
  haveI := finite_quot (k := k) J hJ
  haveI := finite_quot (k := k) (I * J) (mul_ne_zero (show I ≠ 0 from hI) (show J ≠ 0 from hJ))
  have h := rank_quot_mul (k := k) J hJ I hI
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem eq_of_le_of_finrank_le (I J : Ideal A) (hI : I ≠ ⊥) (hIJ : I ≤ J)
    (hr : Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J)) : I = J := by
  obtain ⟨L, rfl⟩ := Ideal.dvd_iff_le.2 hIJ
  have hJ : J ≠ ⊥ := fun h => hI (by rw [h]; exact (zero_mul L : (0 : Ideal A) * L = 0))
  have hL : L ≠ ⊥ := fun h => hI (by rw [h]; exact (mul_zero J : J * (0 : Ideal A) = 0))
  rw [finrank_quot_mul J L hJ hL] at hr
  have h0 : Module.finrank k (A ⧸ L) = 0 := by omega
  haveI := finite_quot (k := k) L hL
  have hs : Subsingleton (A ⧸ L) := Module.finrank_zero_iff.1 h0
  rw [Ideal.Quotient.subsingleton_iff.1 hs, Ideal.mul_top]

theorem dedekind_finiteType_codim : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A],
    (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧
      ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J) := by
  intro k A _ _ _ _ _ _ _
  exact ⟨fun I hI => finite_quot I hI, fun P hP => maximal_part P hP,
    fun I J hI hJ => finrank_quot_mul I J hI hJ,
    fun I J hI hIJ hr => eq_of_le_of_finrank_le I J hI hIJ hr⟩

end DedekindCodim
end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem mem_pow_of_jets_vanish (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) =
      ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w))
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w; rw [hL 0 hN0]; simp
  have halg : ∀ c : k, Δ 0 (algebraMap k A c) = c := by
    intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, h01, smul_eq_mul, mul_one]
  let φ : A →+* k :=
    { toFun := Δ 0, map_one' := h01, map_mul' := hmul0, map_zero' := map_zero _,
      map_add' := map_add _ }
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, halg c⟩
  have hQmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hmemQ : ∀ u, u ∈ RingHom.ker φ ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  set Q := RingHom.ker φ with hQ
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    simp [Finset.sum_range_succ, h01] at this
    linear_combination this
  have ha : ∀ m, ∀ u ∈ Q ^ m, ∀ l < m, l < N → Δ l u = 0 := by
    intro m
    induction m with
    | zero => intro u _ l hl; omega
    | succ m ih =>
      intro u hu l hlm hlN
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun u => Δ l u = 0) hu ?_ ?_
      · intro x hx y hy
        show Δ l (x * y) = 0
        rw [hL l hlN]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        by_cases hpm : p < m
        · rw [ih x hx p hpm (by omega)]; simp
        · have : l - p = 0 := by omega
          rw [this, (hmemQ y).mp hy]; simp
      · intro x y hx hy
        show Δ l (x + y) = 0
        rw [map_add (f := _), hx, hy, add_zero]
  set π' : A := π - algebraMap k A (Δ 0 π) with hπ'
  have hπ'Q : π' ∈ Q := by
    rw [hmemQ, hπ', map_sub, halg, sub_self]
  have hπ'1 : Δ 1 π' = 1 := by
    rw [hπ', map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h11, smul_zero, sub_zero, hπ]
  have hb : ∀ m < N, Δ m (π' ^ m) = (m.factorial : k) := by
    intro m
    induction m with
    | zero => intro _; simp [h01]
    | succ m ih =>
      intro hm
      rw [pow_succ', hL (m+1) hm]
      rw [Finset.sum_eq_single 1]
      · simp [hπ'1, ih (by omega), Nat.factorial_succ]
      · intro p hp hp1
        have hp' := Finset.mem_range.mp hp
        rcases Nat.lt_or_gt_of_ne hp1 with h | h
        · have : p = 0 := by omega
          subst this; rw [(hmemQ π').mp hπ'Q]; simp
        · rw [ha m (π' ^ m) (Ideal.pow_mem_pow hπ'Q m) (m + 1 - p) (by omega) (by omega)]; simp
      · intro h; simp at h
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have : π' = 0 := by rw [← Ideal.mem_bot, ← h]; exact hπ'Q
    rw [this, map_zero] at hπ'1; exact zero_ne_one hπ'1
  have hnot : ∀ m < N, π' ^ m ∉ Q ^ (m + 1) := by
    intro m hm hmem
    have := ha (m + 1) _ hmem m (by omega) hm
    rw [hb m hm] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) this
  have hc : ∀ f : A, (∀ l < N, Δ l f = 0) → ∀ m ≤ N, f ∈ Q ^ m := by
    intro f hf m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hfm := ih (by omega)
      have hI : Ideal.span {π' ^ m} ⊔ Q ^ (m + 1) = Q ^ m := by
        apply Ideal.eq_prime_pow_of_succ_lt_of_le hQ0
        · refine lt_of_le_of_ne le_sup_right ?_
          intro h; apply hnot m (by omega); rw [h]
          exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
        · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hπ'Q m))
            (Ideal.pow_le_pow_right (Nat.le_succ m))
      rw [← hI] at hfm
      obtain ⟨y, hy, g, hg, hyg⟩ := Submodule.mem_sup.mp hfm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hdc : d - algebraMap k A (Δ 0 d) ∈ Q := by
        rw [hmemQ, map_sub, halg, sub_self]
      have hrest : (d - algebraMap k A (Δ 0 d)) * π' ^ m ∈ Q ^ (m + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hdc (Ideal.pow_mem_pow hπ'Q m)
      have hrg : (d - algebraMap k A (Δ 0 d)) * π' ^ m + g ∈ Q ^ (m + 1) :=
        Ideal.add_mem _ hrest hg
      have e : f = (Δ 0 d) • π' ^ m + ((d - algebraMap k A (Δ 0 d)) * π' ^ m + g) := by
        rw [← hyg, Algebra.smul_def]; ring
      have hΔ : Δ m f = Δ 0 d * m.factorial := by
        rw [e, map_add (f := _), map_smul, hb m (by omega), ha (m + 1) _ hrg m (by omega) (by omega),
          smul_eq_mul, add_zero]
      have hc0 : Δ 0 d = 0 := by
        have := hf m (by omega); rw [hΔ] at this
        exact (mul_eq_zero.mp this).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      rw [e]; exact Ideal.add_mem _ (by rw [hc0, zero_smul]; exact Ideal.zero_mem _) hrg
  exact ⟨Q, hQmax, hmemQ, fun f hf => hc f hf N le_rfl⟩

end GlobalTheory
end
