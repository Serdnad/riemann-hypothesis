module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.MulAction
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

section

open PowerSeries

namespace GlobalTheory

namespace CompletedInvariants

theorem smodEq_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (a b : R) :
    a ≡ b [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule R R)] ↔ q ^ n ∣ a - b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

theorem eq_zero_of_dvd {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (z : R) (hz : ∀ k : ℕ, q ^ k ∣ z) : z = 0 := by
  refine IsHausdorff.haus h.toIsHausdorff z fun n => ?_
  rw [smodEq_iff, sub_zero]; exact hz n

theorem exists_lim {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (f : ℕ → R) (hf : ∀ m n, m ≤ n → q ^ m ∣ f m - f n) : ∃ L, ∀ n, q ^ n ∣ f n - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f)
    (fun {m n} hmn => (smodEq_iff q m _ _).2 (hf m n hmn))
  exact ⟨L, fun n => (smodEq_iff q n _ _).1 (hL n)⟩

theorem map_dvd' {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (p k : ℕ) {z : R} (h : (p : R) ^ k ∣ z) : (p : S) ^ k ∣ f z := by
  have := map_dvd f h
  simpa using this

end CompletedInvariants


open CompletedInvariants in
theorem completed_localisation_invariants : ∀ {O A A' E E' J : Type} [CommRing O] [CommRing A] [CommRing A'] [CommRing E] [CommRing E'] [Algebra O A] [Algebra O A'] [Algebra O E] [Algebra O E'] (p : ℕ) (x : A) (x' : A') (ι : A →ₐ[O] E) (ι' : A' →ₐ[O] E') (j : A →ₐ[O] A') (g : E →ₐ[O] E') (D : Finset J) (δA : J → (A' →ₐ[O] A')) (δE : J → (E' →ₐ[O] E')), (∀ a, g (ι a) = ι' (j a)) → (∀ d a, δE d (ι' a) = ι' (δA d a)) → IsUnit (ι x) → IsAdicComplete (Ideal.span {(p : E)}) E → IsAdicComplete (Ideal.span {(p : E')}) E' → (∀ (y : E) (k : ℕ), ∃ (a : A) (m : ℕ), (p : E) ^ k ∣ y * ι (x ^ m) - ι a) → (∀ (y : E') (k : ℕ), ∃ (a : A') (m : ℕ), (p : E') ^ k ∣ y * ι' (x' ^ m) - ι' a) → (∀ (a : A') (k : ℕ), (p : E') ^ k ∣ ι' a → (p : A') ^ k ∣ a) → (∀ (a : A) (k : ℕ), (p : A') ^ k ∣ j a → (p : A) ^ k ∣ a) → x' ∣ j x → IsUnit (D.card : O) → (∀ a', (∃ a, j a = a') ↔ ∀ d ∈ D, δA d a' = a') → (∀ a', ∀ d ∈ D, δA d (∑ d' ∈ D, δA d' a') = ∑ d' ∈ D, δA d' a') → Function.Injective g ∧ ∀ y, (∃ z, g z = y) ↔ ∀ d ∈ D, δE d y = y := by
  intro O A A' E E' J _ _ _ _ _ _ _ _ _ p x x' ι ι' j g D δA δE hg hδ hx hE hE' dE dE' sE' sj
    hxx hD hinv havg
  have hxm : ∀ m : ℕ, IsUnit (ι (x ^ m)) := fun m => by rw [map_pow]; exact hx.pow m
  have hfix : ∀ a, ∀ d ∈ D, δE d (g (ι a)) = g (ι a) := fun a d hd => by
    rw [hg, hδ, (hinv (j a)).1 ⟨a, rfl⟩ d hd]
  have sat : ∀ (z : E) (k : ℕ), (p : E') ^ k ∣ g z → (p : E) ^ k ∣ z := by
    intro z k hz
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 : (p : E') ^ k ∣ g (ι a) := (dvd_sub_right (hz.mul_right _)).1 h1
    rw [hg] at h2
    have h3 := map_dvd' ι p k (sj a k (sE' _ k h2))
    have h4 : (p : E) ^ k ∣ z * ι (x ^ m) := by
      have := dvd_add h h3
      simpa using this
    exact (hxm m).dvd_mul_right.1 h4
  refine ⟨?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_dvd _ hE z fun k => sat z k (hz ▸ dvd_zero _)
  · rintro ⟨z, rfl⟩ d hd
    rw [← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 := map_dvd' (δE d) p k h1
    rw [map_sub, map_mul, hfix _ d hd, hfix _ d hd] at h2
    have h3 := dvd_sub h2 h1
    have hu : IsUnit (g (ι (x ^ m))) := (hxm m).map g
    refine hu.dvd_mul_right.1 ?_
    convert h3 using 1
    ring
  · have key : ∀ k : ℕ, ∃ z, (p : E') ^ k ∣ y - g z := by
      intro k
      obtain ⟨a', m, h⟩ := dE' y k
      obtain ⟨c, hc⟩ := hxx
      have h1 : (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (a' * c ^ m) := by
        have := h.mul_right (ι' (c ^ m))
        convert this using 1
        rw [hg, map_pow j, hc, mul_pow, map_mul, map_mul]
        ring
      set b := a' * c ^ m
      have h2 : ∀ d ∈ D, (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (δA d b) := fun d hd => by
        have := map_dvd' (δE d) p k h1
        rwa [map_sub, map_mul, hfix _ d hd, hy d hd, hδ] at this
      have h3 := Finset.dvd_sum h2
      obtain ⟨a, ha⟩ := (hinv _).2 (havg b)

      rw [Finset.sum_sub_distrib, ← map_sum, ← ha, ← hg, Finset.sum_const, nsmul_eq_mul] at h3
      obtain ⟨n, hn⟩ := hD.exists_left_inv
      obtain ⟨v, hv⟩ := (hxm m).exists_right_inv
      have hn' : algebraMap O E' n * (D.card : E') = 1 := by
        have := congrArg (algebraMap O E') hn
        simpa using this
      have hv' : g (ι (x ^ m)) * g v = 1 := by rw [← map_mul, hv, map_one]
      refine ⟨algebraMap O E n * ι a * v, ?_⟩
      have := h3.mul_right (algebraMap O E' n * g v)
      convert this using 1
      rw [map_mul, map_mul, AlgHom.commutes]
      linear_combination (-y) * hv' - y * (g (ι (x ^ m)) * g v) * hn'
    choose z hz using key
    obtain ⟨L, hL⟩ := exists_lim _ hE z fun m n hmn => sat _ _ (by
      have := dvd_sub ((pow_dvd_pow _ hmn).trans (hz n)) (hz m)
      convert this using 1
      rw [map_sub]; ring)
    refine ⟨L, ?_⟩
    rw [eq_comm, ← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    have := dvd_add (hz k) (map_dvd' g p k (hL k))
    convert this using 1
    rw [map_sub]; ring

end GlobalTheory
end

section

open IsLocalRing Matrix TensorProduct

namespace GlobalTheory.LocalSurj

theorem exists_sub_mem_map_pow_succ {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (n : ℕ) (a : A)
    (ha : a ∈ (m ^ n).map f) : ∃ x ∈ m ^ n, a - f x ∈ (m ^ (n + 1)).map f := by
  change a ∈ Ideal.span (f '' ((m ^ n : Ideal R) : Set R)) at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨x', hx2, hx2'⟩ := hz
    refine ⟨x + x', add_mem hx hx2, ?_⟩
    have : y + z - f (x + x') = (y - f x) + (z - f x') := by rw [map_add (f := _)]; ring
    rw [this]; exact add_mem hx' hx2'
  | smul c y _ hy =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨s, hs⟩ := hm c
    refine ⟨s * x, Ideal.mul_mem_left _ _ hx, ?_⟩
    have : c • y - f (s * x) = c * (y - f x) + (c - f s) * f x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_left _ _ hx') ?_
    rw [pow_succ', Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem f hx)

noncomputable def approx {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) :
    (n : ℕ) → {x : R // a - f x ∈ (m ^ n).map f}
  | 0 => ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | n + 1 =>
    let p := approx f m hm a n
    let h := exists_sub_mem_map_pow_succ f m hm n _ p.2
    ⟨p.1 + h.choose, by
      have := h.choose_spec.2
      rwa [map_add, ← sub_sub]⟩

theorem approx_succ_sub {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by
  simp only [approx, add_sub_cancel_left]
  exact (exists_sub_mem_map_pow_succ f m hm n _ (approx f m hm a n).2).choose_spec.1

theorem approx_sub_mem {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have e : (approx f m hm a (n + 1)).1 - (approx f m hm a k).1 =
        ((approx f m hm a (n + 1)).1 - (approx f m hm a n).1) +
        ((approx f m hm a n).1 - (approx f m hm a k).1) := by ring
    rw [e]
    exact add_mem (Ideal.pow_le_pow_right hkn (approx_succ_sub f m hm a n)) ih

theorem surjective_of_residue_of_cotangent (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : R →+* A)
    (hc : IsAdicComplete (maximalIdeal R) R) (hf : IsLocalHom f)
    (hres : ∀ z : A, ∃ r, z - f r ∈ maximalIdeal A)
    (hcot : maximalIdeal A ≤ (maximalIdeal R).map f ⊔ maximalIdeal A ^ 2) :
    Function.Surjective f := by
  set m := maximalIdeal R

  have hle : maximalIdeal A ≤ m.map f := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · simpa [pow_two, Ideal.smul_eq_mul] using hcot
  have hm : ∀ z : A, ∃ r, z - f r ∈ m.map f := fun z =>
    (hres z).imp fun r hr => hle hr
  have hmap : m.map f ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit f x hx
  intro a

  obtain ⟨L, hL⟩ := hc.prec' (fun n => (approx f m hm a n).1) (fun {k n} h => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact approx_sub_mem f m hm a h)
  refine ⟨L, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_iInf]
  intro n
  have h1 := (approx f m hm a n).2
  have h2 := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h2
  have e : a - f L = (a - f (approx f m hm a n).1) + f ((approx f m hm a n).1 - L) := by
    rw [map_sub]; ring
  rw [e]
  refine (Ideal.map_pow f m n ▸ Ideal.pow_right_mono hmap n) (add_mem h1 (Ideal.mem_map_of_mem f h2))

end GlobalTheory.LocalSurj
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.AdicCompleteFinite

theorem isPrecomplete_of_finite {R M : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) a (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem isPrecomplete_of_pow_le {S : Type} [CommRing S] {I J : Ideal S} (hIJ : I ≤ J) {k : ℕ}
    (hk : J ^ k ≤ I) [h : IsPrecomplete I S] : IsPrecomplete J S := by
  have hk' : J ^ (k + 1) ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  refine ⟨fun f hf => ?_⟩
  have hg : ∀ {m n : ℕ}, m ≤ n →
      f ((k + 1) * m) ≡ f ((k + 1) * n) [SMOD (I ^ m • ⊤ : Submodule S S)] := by
    intro m n hmn
    refine (hf (Nat.mul_le_mul_left (k + 1) hmn)).mono ?_
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk' m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h (f := fun n => f ((k + 1) * n)) hg
  refine ⟨L, fun n => ?_⟩
  refine (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos k))).trans ?_
  exact (hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))

theorem isAdicComplete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hrad : maximalIdeal S ≤ ((maximalIdeal R).map (algebraMap R S)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hP, hprime⟩
    have h1 : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hP
    have h2 : P.comap (algebraMap R S) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) h1).symm
    have h3 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S)
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h2 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) S := isPrecomplete_of_finite _
  haveI : IsPrecomplete ((maximalIdeal R).map (algebraMap R S)) S :=
    IsPrecomplete.map_algebraMap_iff.mpr this
  haveI : IsPrecomplete (maximalIdeal S) S := isPrecomplete_of_pow_le hle hk
  exact {}

end GlobalTheory.AdicCompleteFinite
end

section

open Polynomial

namespace GlobalTheory

theorem adjoinRoot_map_mk_map {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (h f : R[X]) :
    AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h f) = AdjoinRoot.mk (h.map g) (f.map g) := by
  have : (AdjoinRoot.map g h (h.map g) dvd_rfl).comp (AdjoinRoot.mk h) =
      (AdjoinRoot.mk (h.map g)).comp (Polynomial.mapRingHom g) := by
    ext <;> simp
  exact DFunLike.congr_fun this f

theorem trace_adjoinRoot_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]),
    h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) =
      Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  intro R S _ _ g h hm x
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  have hm' : (h.map g).Monic := hm.map g
  have hn : (h.map g).natDegree = h.natDegree := hm.natDegree_map g
  have key : ∀ (y : AdjoinRoot h) (k : ℕ),
      (AdjoinRoot.modByMonicHom hm' (AdjoinRoot.map g h (h.map g) dvd_rfl y)).coeff k =
        g ((AdjoinRoot.modByMonicHom hm y).coeff k) := by
    intro y k
    induction y using AdjoinRoot.induction_on with
    | ih f =>
      rw [adjoinRoot_map_mk_map, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
        ← Polynomial.map_modByMonic g hm, Polynomial.coeff_map]
  let b : Module.Basis (Fin h.natDegree) R (AdjoinRoot h) := (AdjoinRoot.powerBasis' hm).basis
  let b' : Module.Basis (Fin h.natDegree) S (AdjoinRoot (h.map g)) := (AdjoinRoot.powerBasis' hm').basis.reindex (finCongr hn)
  have hb : ∀ i, b i = AdjoinRoot.root h ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hm).basis_eq_pow i
  have hb' : ∀ i, b' i = AdjoinRoot.root (h.map g) ^ (i : ℕ) := fun i => by
    simp only [b', Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
    rfl
  have hr : ∀ (z : AdjoinRoot h) (i : Fin h.natDegree), b.repr z i = (AdjoinRoot.modByMonicHom hm z).coeff i :=
    fun _ _ => rfl
  have hr' : ∀ (z : AdjoinRoot (h.map g)) (i : Fin h.natDegree),
      b'.repr z i = (AdjoinRoot.modByMonicHom hm' z).coeff i := fun z i => by
    simp only [b', Module.Basis.repr_reindex_apply]
    rfl

  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b', Matrix.trace, Matrix.trace,
  map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  have hbi : b' i = AdjoinRoot.map g h (h.map g) dvd_rfl (b i) := by
    rw [hb, hb', map_pow, AdjoinRoot.map_root]
  rw [hbi, ← map_mul, hr', hr, key]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem units_adicCompletion_hom_ext (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B)
    (hf : IsOpen (f.ker : Set (v.adicCompletion F)ˣ))
    (hg : IsOpen (g.ker : Set (v.adicCompletion F)ˣ))
    (hc : ∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) =
      g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) :
    ∀ x, f x = g x := by
  intro x
  set S : Set (v.adicCompletion F)ˣ :=
    (fun y => x⁻¹ * y) ⁻¹' ((f.ker : Set (v.adicCompletion F)ˣ) ∩ g.ker) with hS
  have hSo : IsOpen S := (hf.inter hg).preimage (continuous_const.mul continuous_id)
  have hxS : x ∈ S := by simp [hS, MonoidHom.mem_ker]
  obtain ⟨U, hU, hUS⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hSo
  have hxU : (x : v.adicCompletion F) ∈ U := by
    rw [← hUS] at hxS; exact hxS
  have hU0 : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open
    hU0 ⟨x, hxU, by simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hk.2 (by simp)
  set c : Fˣ := Units.mk0 k hk0
  have hcS : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c ∈ S := by
    rw [← hUS]; simpa [c] using hk.1
  simp only [hS, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    map_mul, map_inv] at hcS
  have h1 : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = f x := by
    have := hcS.1; rw [inv_mul_eq_one] at this; exact this.symm
  have h2 : g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g x := by
    have := hcS.2; rw [inv_mul_eq_one] at this; exact this.symm
  rw [← h1, ← h2, hc]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

variable {E : Type} [Field E] [NumberField E]

def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1

theorem bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl

  rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)

end GlobalTheory.StdAtPrime
end

section

namespace GlobalTheory

theorem linearMap_continuous_of_compactSpace_of_finite
    {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type}
    [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') : Continuous f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O M
  have hgc : Continuous g := g.continuous_on_pi
  have hq : Topology.IsQuotientMap g := hgc.isClosedMap.isQuotientMap hgc hg
  have hfg : Continuous (f ∘ g) := (f.comp g).continuous_on_pi
  exact hq.continuous_iff.mpr hfg

end GlobalTheory
end
