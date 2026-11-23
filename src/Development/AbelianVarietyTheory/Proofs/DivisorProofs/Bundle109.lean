module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CommonValuation

theorem exists_eq_pow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

theorem le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top

theorem exists_centre {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add (f := _)]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h

end GlobalTheory.CommonValuation
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.ValBoundDenom

theorem exists_nat_le_exp (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)

theorem exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by
  classical
  have hfin : {w | ¬ β w ≤ 1}.Finite := Filter.eventually_cofinite.mp hβ
  set T := hfin.toFinset with hT
  choose k hk using fun w => exists_nat_le_exp (β w)
  set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨D, hDI, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨D, hD0, fun x hx => ?_⟩
  have hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · have hmem : D ∈ w.asIdeal ^ k w :=
        (Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)
      have h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem
      have h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ) := (hx w).trans (hk w)
      calc w.valuation E (D : E) * w.valuation E x
          ≤ WithZero.exp (-(k w : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' h1 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have hw1 : β w ≤ 1 := by
        by_contra h
        exact hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)
      exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle
  rw [← hr]
  exact r.isIntegral_coe

end GlobalTheory.ValBoundDenom
end

section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.RootIdeal

theorem exists_pow_eq_spanSingleton (K : Type) [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    ∃ (h : ℕ) (x : K), 0 < h ∧ x ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x = J ^ h := by
  classical
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 J hJ
  have hpos : 0 < orderOf (ClassGroup.mk K u) := orderOf_pos _
  have h1 : ClassGroup.mk K (u ^ orderOf (ClassGroup.mk K u)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := h1.principal
  have hJh : ((u ^ orderOf (ClassGroup.mk K u) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = J ^ orderOf (ClassGroup.mk K u) := by
    simp [u]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x =
      J ^ orderOf (ClassGroup.mk K u) := by
    rw [← hJh]
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, hx]
  refine ⟨_, x, hpos, ?_, key⟩
  rintro rfl
  rw [FractionalIdeal.spanSingleton_zero] at key
  exact pow_ne_zero _ hJ key.symm

theorem exists_count_spanSingleton_eq_mul (K : Type) [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 K) →₀ ℚ) :
    ∃ (n : ℕ) (x : K), 0 < n ∧ x ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) : ℤ) : ℚ) = n * r v := by
  classical
  set d : ℕ := ∏ v ∈ r.support, (r v).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun v _ => (r v).pos)
  have hdvd : ∀ v, (r v).den ∣ d := by
    intro v
    by_cases hv : v ∈ r.support
    · exact Finset.dvd_prod_of_mem _ hv
    · rw [Finsupp.notMem_support_iff.mp hv]
      simp
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    Finsupp.mapRange (fun q : ℚ => q.num * ((d / q.den : ℕ) : ℤ)) (by simp) r
  have he : ∀ v, ((e v : ℤ) : ℚ) = d * r v := by
    intro v
    simp only [e, Finsupp.mapRange_apply]
    have hden : ((r v).den : ℚ) ≠ 0 := by exact_mod_cast (r v).pos.ne'
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hdvd v) hden]
    conv_rhs => rw [← Rat.num_div_den (r v)]
    field_simp
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    e.prod (fun v n => ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)
    with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count K v J = e v := fun v =>
    FractionalIdeal.count_finsuppProd K v e
  obtain ⟨h, x, hh, hx0, hxJ⟩ := exists_pow_eq_spanSingleton K J hJ0
  refine ⟨h * d, x, Nat.mul_pos hh hdpos, hx0, fun v => ?_⟩
  rw [hxJ, FractionalIdeal.count_pow, hcount, Int.cast_mul, Int.cast_natCast, he]
  push_cast
  ring

end GlobalTheory.RootIdeal
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1

end GlobalTheory.CMModel
end

section

open NumberField

namespace GlobalTheory


open TensorProduct in
theorem natCard_quot_maximal_smul_top_eq {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

theorem natCard_quot_smul_top_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La →
    ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g →
    Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧
      Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  intro E _ _ La _ _ hfin hproj I g hg hI
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact hg.prime.irreducible)
  have hne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  have hR : Nat.card (𝓞 E ⧸ I) = g := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard := natCard_quot_maximal_smul_top_eq (R := 𝓞 E) (M := La) I
  rw [hR] at hcard
  refine ⟨?_, hcard.le⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hg.ne_zero

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatDescent

theorem mem_of_mem_span_of_isBaseChange {A B M M' : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module B M'] [IsScalarTower A B M'] {f : M →ₗ[A] M'} (hf : IsBaseChange B f)
    (N : Submodule A M) (w : M) (hw : f w ∈ Submodule.span B (f '' (N : Set M))) : w ∈ N := by
  let g : B ⊗[A] N →ₗ[B] M' := hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B
  have hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩
  obtain ⟨x, hx⟩ := hspan hw
  have h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x := by
    apply hf.equiv.injective
    have : hf.equiv (N.subtype.baseChange B x) = f w := hx
    rw [this, IsBaseChange.equiv_tmul, one_smul]
  have hq : N.mkQ ∘ₗ N.subtype = 0 := by
    ext c
    simp
  have h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0 := by
    have := congrArg (N.mkQ.baseChange B) h1
    rw [LinearMap.baseChange_tmul] at this
    rw [this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  have h3 : N.mkQ w = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)
    simpa using h2
  simpa using h3

theorem mem_of_mem_span_map :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  intro K K' _ _ _ _ j n N w hw
  letI := j.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'
  have hb : IsBaseChange (𝓞 K')
      ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n)) :=
    hP.out.finitePow (Fin n)
  exact mem_of_mem_span_of_isBaseChange hb N w hw

end GlobalTheory.FlatDescent
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCoprime

theorem coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add (f := _), ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

end GlobalTheory.NormCoprime
end
