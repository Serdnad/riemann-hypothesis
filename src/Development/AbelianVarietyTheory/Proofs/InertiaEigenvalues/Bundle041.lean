module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Order.Fin.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZMod.UnitsCyclic
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
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

section

open PowerSeries

namespace GlobalTheory.PadicUnitGen

theorem dvd_iff_toZMod {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem one_add_pow_eq {R : Type*} [CommRing R] (t : R) (j : ℕ) :
    ∃ z, (1 + t) ^ j = 1 + j * t + t ^ 2 * z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨j + z + t * z, by rw [pow_succ, hz]; push_cast; ring⟩

theorem exists_pow_approx {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]) (h2 : l ≠ 2)
    (hu : Associated (u - 1) (l : ℤ_[l])) (x : ℤ_[l]) (hx : (l : ℤ_[l]) ∣ x - 1) (k : ℕ) :
    ∃ m : ℕ, (l : ℤ_[l]) ^ (k + 1) ∣ x - u ^ m := by
  obtain ⟨w, hw⟩ := hu.symm
  have hu' : u = 1 + l * (w : ℤ_[l]) := by rw [hw]; ring
  have h3 : 3 ≤ l := by
    have := hl.out.two_le
    omega
  have hl0 : PadicInt.toZMod (l : ℤ_[l]) = 0 := by simp
  have hw0 : PadicInt.toZMod (w : ℤ_[l]) ≠ 0 :=
    (w.isUnit.map (PadicInt.toZMod (p := l))).ne_zero
  have hu1 : PadicInt.toZMod u = 1 := by rw [hu']; simp
  induction k with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨m, c, hc⟩ := ih
    obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := l) (v := l)
      hl.out dvd_rfl (by rw [← pow_two, ← pow_succ]; exact pow_dvd_pow _ h3) (w : ℤ_[l]) k
    rw [← hu'] at hy
    set j : ℕ := (PadicInt.toZMod c / PadicInt.toZMod (w : ℤ_[l])).val with hj
    obtain ⟨z, hz⟩ := one_add_pow_eq ((l : ℤ_[l]) ^ k * l * (w + l * y)) j
    refine ⟨m + l ^ k * j, ?_⟩
    have hd : (l : ℤ_[l]) ∣ c - u ^ m * (j * (w + l * y)
        + (l : ℤ_[l]) ^ k * l * (w + l * y) ^ 2 * z) := by
      rw [dvd_iff_toZMod]
      simp only [map_sub, map_mul, map_add (f := _), map_pow, hl0, hu1, map_natCast, hj,
        ZMod.natCast_zmod_val, ZMod.natCast_self]
      field_simp
      ring
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [pow_add, pow_mul, hy, hz]
    linear_combination hc + (l : ℤ_[l]) ^ (k + 1) * hd

theorem exists_lift {l : ℕ} [hl : Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (hΔ : Nat.card Δ = l - 1) (x : (ZMod l)ˣ) :
    ∃ δ ∈ Δ, PadicInt.toZMod (δ : ℤ_[l]) = x := by
  let f : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →* ZMod l)).comp Δ.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have h1 : PadicInt.toZMod ((δ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := congrArg Units.val hδ
    have h2 : ((δ : ℤ_[l]ˣ) : ℤ_[l]) ^ (l - 1) = 1 := by
      have : δ ^ (l - 1) = 1 := by rw [← hΔ]; exact pow_card_eq_one'
      have := congrArg (fun t : Δ => ((t : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa using this
    have h3 := geom_sum_mul ((δ : ℤ_[l]ˣ) : ℤ_[l]) (l - 1)
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · exfalso
      have := congrArg (PadicInt.toZMod (p := l)) h

      simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at this
      rw [Nat.cast_pred hl.out.pos] at this
      simp at this
    · apply Subtype.ext
      apply Units.ext
      exact sub_eq_zero.1 h
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hΔ, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨δ, hδ⟩ := hbij.2 x
  exact ⟨δ, δ.2, congrArg Units.val hδ⟩

theorem exists_root_mul_pow_approx :
    ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (u : ℤ_[l]), l ≠ 2 →
      Nat.card Δ = l - 1 → Associated (u - 1) (l : ℤ_[l]) → ∀ k a : ℕ, ¬ l ∣ a →
      ∃ δ ∈ Δ, ∃ m : ℕ, (l : ℤ_[l]) ^ k ∣ (a : ℤ_[l]) - (δ : ℤ_[l]) * u ^ m := by
  intro l hl Δ _ u h2 hΔ hu k a ha
  have ha0 : (a : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨δ, hδ, hδa⟩ := exists_lift Δ hΔ (Units.mk0 _ ha0)
  have hx : (l : ℤ_[l]) ∣ (a : ℤ_[l]) * (δ⁻¹ : ℤ_[l]ˣ) - 1 := by
    have : (l : ℤ_[l]) ∣ (a : ℤ_[l]) - δ := by
      rw [dvd_iff_toZMod, map_sub, hδa]; simp
    have h := this.mul_right ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    rwa [sub_mul, Units.mul_inv] at h
  obtain ⟨m, hm⟩ := exists_pow_approx u h2 hu _ hx k
  refine ⟨δ, hδ, m, (pow_dvd_pow _ (Nat.le_succ k)).trans ?_⟩
  have h := hm.mul_left (δ : ℤ_[l])
  rwa [mul_sub, mul_comm (a : ℤ_[l]), Units.mul_inv_cancel_left] at h

end GlobalTheory.PadicUnitGen
end

section

namespace GlobalTheory.StrictAntiAddLe

theorem add_le_of_strictAnti : ∀ {m : ℕ} {s : Fin m → ℕ}, StrictAnti s →
    ∀ (k : ℕ) (i j : Fin m), (↑j : ℕ) = (↑i : ℕ) + k → s j + k ≤ s i := by
  intro m s hs k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hlt : (i : ℕ) + k < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hlt⟩ rfl
    have h2 : s j < s ⟨(i : ℕ) + k, hlt⟩ := by
      apply hs
      rw [Fin.lt_def]
      show (i : ℕ) + k < (j : ℕ)
      omega
    omega

end GlobalTheory.StrictAntiAddLe
end

section

open IsLocalRing Matrix

namespace GlobalTheory.BurnsideMonoid

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isIrreducible {G K V : Type} [Monoid G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_matrix_eq_top_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Monoid Γ] (σ : Γ →* Matrix ι ι K)
    (h : ∀ W : Submodule K (ι → K), (∀ g, ∀ w ∈ W, σ g *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Submodule.span K (Set.range σ) = ⊤ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
  let τ : Representation K Γ (ι → K) :=
    { toFun := fun g => Matrix.toLin' (σ g)
      map_one' := by simp; rfl
      map_mul' := fun g g' => by simp [Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => ?_⟩
      have h1 : (⊥ : Submodule K (ι → K)) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
      exact bot_ne_top h1
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isIrreducible τ hirr
  have hm : Set.range σ =
      (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

end GlobalTheory.BurnsideMonoid
end

section

open scoped NNReal

namespace GlobalTheory.ValCompletion

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ (Nat.le_succ n)]
  exact key.map _

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end General

section Val
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}

theorem not_pow_succ_dvd_pow (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : ¬ x ^ (m + 1) ∣ x ^ m := by
  rintro ⟨c, hc⟩
  apply hxu
  have h : x ^ m * 1 = x ^ m * (x * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
  exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm

theorem algebraMap_pow_ne_zero (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h
  rw [← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact not_pow_succ_dvd_pow hx0 hxu m h2

theorem exists_eq_mul_unit (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (y : AdicCompletion (Ideal.span {x}) V) (hy : y ≠ 0) :
    ∃ (a : V) (n : ℕ), a ∣ x ^ n ∧ ∃ u : (AdicCompletion (Ideal.span {x}) V)ˣ, y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * u := by
  obtain ⟨n, hn⟩ : ∃ n, AdicCompletion.evalₐ (Ideal.span {x}) n y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (AdicCompletion.ext_evalₐ fun n => by rw [hc n, map_zero])
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {x}) (n + 1) y)
  have hna : ¬ x ^ n ∣ a := by
    intro hd
    apply hn
    rw [← factorPow_evalₐ (Nat.le_succ n), ← ha, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd
  obtain ⟨b, hb⟩ : a ∣ x ^ n := by
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a (x ^ n)
    · exact ⟨c, hc.symm⟩
    · exact absurd ⟨c, hc.symm⟩ hna
  obtain ⟨z, hz⟩ : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) ∣ y - algebraMap V (AdicCompletion (Ideal.span {x}) V) a := by
    rw [← evalₐ_eq_zero_iff rfl, map_sub, evalₐ_algebraMap, ← ha, sub_self]
  have hunit : IsUnit (1 + algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) x * z) := by
    apply isUnit_of_evalₐ
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_add (f := _), map_one, map_mul, map_mul, evalₐ_algebraMap, evalₐ_algebraMap, hx1,
      mul_zero, zero_mul, add_zero]
    exact isUnit_one
  refine ⟨a, n, ⟨b, hb⟩, hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, mul_add, mul_one]
  have : y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a + algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) * z := by rw [← hz]; ring
  rw [this, pow_succ, ← map_pow, hb, map_mul]
  ring

end Val

end GlobalTheory.ValCompletion


open GlobalTheory.ValCompletion in
theorem GlobalTheory.adicCompletion_valuationRing_props : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  intro V _ _ _ x hx0 hxu
  have hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 := by
    simpa using algebraMap_pow_ne_zero hx0 hxu 1
  have hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V) := ⟨⟨_, _, hne⟩⟩
  have hdom : IsDomain (AdicCompletion (Ideal.span {x}) V) := by
    refine @NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨a, n, ⟨c, hc1⟩, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hc.1
    obtain ⟨b, m, ⟨d, hd1⟩, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hc.2
    apply algebraMap_pow_ne_zero hx0 hxu (n + m)
    have h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0 := by
      have h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0 := by
        rw [← hyz]; ring
      exact (Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)
    rw [pow_add, ← map_pow, ← map_pow, hc1, hd1]
    simp only [map_mul]
    calc _ = (algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b) * (algebraMap V (AdicCompletion (Ideal.span {x}) V) c * algebraMap V (AdicCompletion (Ideal.span {x}) V) d) := by ring
      _ = 0 := by rw [h1, zero_mul]
  refine ⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩
  · by_cases hy : y = 0
    · exact ⟨0, Or.inr (by rw [hy, mul_zero])⟩
    by_cases hz : z = 0
    · exact ⟨0, Or.inl (by rw [hz, mul_zero])⟩
    obtain ⟨a, n, -, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hy
    obtain ⟨b, m, -, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hz
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * w * ((u : AdicCompletion (Ideal.span {x}) V) * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * u * ((w : AdicCompletion (Ideal.span {x}) V) * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
  · rintro ⟨v, hv⟩
    apply hxu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at h2
    exact isUnit_of_dvd_one h2
  · have e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← e, IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)
end

section

namespace GlobalTheory.LimitOfDivisibility

theorem exists_limit_of_pow_dvd_sub {R : Type} [inst : CommRing R] (p : ℕ)
    [IsAdicComplete (Ideal.span {(↑p : R)}) R] (f : ℕ → R)
    (h : ∀ (n : ℕ), (↑p : R) ^ n ∣ f (n + (1 : ℕ)) - f n) :
    ∃ (L : R), ∀ (n : ℕ), (↑p : R) ^ n ∣ L - f n := by
  have key : ∀ (n : ℕ) (x y : R),
      x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R R)] ↔ (p : R) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hc : ∀ m k : ℕ, (p : R) ^ m ∣ f (m + k) - f m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (p : R) ^ m ∣ f (m + k + 1) - f (m + k) :=
        (pow_dvd_pow _ (Nat.le_add_right m k)).trans (h (m + k))
      have h2 := dvd_add h1 ih
      have e : f (m + k + 1) - f (m + k) + (f (m + k) - f m) = f (m + (k + 1)) - f m := by
        rw [← Nat.add_assoc]; ring
      rwa [e] at h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) (M := R) inferInstance (f := f) (by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, dvd_sub_comm]
    exact hc m k)
  refine ⟨L, fun n => ?_⟩
  rw [dvd_sub_comm]
  exact (key n _ _).1 (hL n)

end GlobalTheory.LimitOfDivisibility
end
