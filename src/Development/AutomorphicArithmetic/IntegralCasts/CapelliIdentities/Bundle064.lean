module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
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
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

@[expose] public section

section

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra A K) {t y : K} (hty : t * y = 1) (hy : y ∈ B) (ht : IsIntegral A t) :
    t ∈ B := by
  obtain ⟨p, hm, hp⟩ := ht
  have key : ∀ (q : A[X]) (n : ℕ), q.natDegree ≤ n → y ^ n * aeval t q ∈ B := by
    intro q n hq
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ n * (q.coeff i • t ^ i) = q.coeff i • y ^ (n - i) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
      rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add]
      congr 1
      rw [mul_comm (y ^ i), mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hy _) _
  have h0 : aeval t p = 0 := hp
  have hd : p.natDegree ≠ 0 := by
    intro h
    have h1 := eq_one_of_monic_natDegree_zero hm h
    simp [h1] at h0
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h2 : aeval t p.eraseLead + t ^ (d + 1) = 0 := by
    have h3 := p.eraseLead_add_C_mul_X_pow
    rw [← h3, map_add (f := _), map_mul, aeval_C, map_pow, aeval_X, hm.leadingCoeff, map_one, one_mul,
      hd'] at h0
    exact h0
  have h4 : t = -(y ^ d * aeval t p.eraseLead) := by
    have h5 : y ^ d * t ^ (d + 1) = t := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, one_mul]
    have h6 : aeval t p.eraseLead = -t ^ (d + 1) := eq_neg_of_add_eq_zero_left h2
    rw [h6, mul_neg, neg_neg, h5]
  rw [h4]
  refine neg_mem (key _ _ ?_)
  have := p.eraseLead_natDegree_le
  omega

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le {l : ℕ} [Fact (Nat.Prime l)] {K : Type}
    [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K]
    [IsScalarTower ℤ_[l] ℚ_[l] K] (z : K) (hz : spectralNorm ℚ_[l] K z ≤ 1) :
    IsIntegral ℤ_[l] z := by
  have hzi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hzi
  have hc := (spectralValue_le_one_iff hmon).mp hz
  have hl : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, ← eval₂_map, hq]
  exact minpoly.aeval ℚ_[l] z

theorem UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] {K : Type} [inst_4 : Field K]
    [inst_5 : Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [inst_7 : Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R,
      IsIntegral ℤ_[l] ((x : R → K) a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ (x : R → K) a ^ n = (↑l : K) * b := by
  intro l _ R _ _ _ K _ _ _ _ _ x a ha
  have hA : ∀ t : K, t * x a = 1 → ¬ IsIntegral ℤ_[l] t := by
    intro t hty ht
    obtain ⟨r, hr⟩ : t ∈ x.range :=
      UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one x.range hty ⟨a, rfl⟩ ht
    have hr' : x r = t := hr
    have hmem : a * r ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
    have hu : IsUnit (1 - a * r) := by
      by_contra hn
      have h1 : 1 - a * r ∈ IsLocalRing.maximalIdeal R := hn
      have h2 := Ideal.add_mem _ h1 hmem
      rw [sub_add_cancel] at h2
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
    have h3 := hu.map x
    have h4 : x (1 - a * r) = 0 := by
      rw [map_sub, map_mul, map_one, hr', mul_comm, hty, sub_self]
    rw [h4] at h3
    exact not_isUnit_zero h3
  change IsIntegral ℤ_[l] (x a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ x a ^ n = (↑l : K) * b
  generalize x a = y at hA
  by_cases hy : y = 0
  · subst hy
    exact ⟨isIntegral_zero, 1, 0, isIntegral_zero, by simp⟩
  let f := spectralMulAlgNorm ℚ_[l] K
  have hf : ∀ z, f z = spectralNorm ℚ_[l] K z := fun _ => rfl
  have hfmul : ∀ u v, f (u * v) = f u * f v := fun u v => map_mul f u v
  have hf1 : f 1 = 1 := map_one f
  have hfy : f y < 1 := by
    have h1 : ¬ f y⁻¹ ≤ 1 := fun h =>
      hA y⁻¹ (inv_mul_cancel₀ hy) (UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ h)
    have h2 : f y * f y⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ hy, hf1]
    have h3 : 0 ≤ f y := (hf y).symm ▸ spectralNorm_nonneg y
    push_neg at h1
    nlinarith
  have hfpow : ∀ (n : ℕ) (z : K), f (z ^ n) = f z ^ n := by
    intro n z
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hfmul, ih, pow_succ]
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime l).pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hlpos) hfy
  have hlK : (l : K) ≠ 0 := by
    have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h1]
    have h2 : (l : ℚ_[l]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    exact (map_ne_zero (algebraMap ℚ_[l] K)).mpr h2
  refine ⟨UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ hfy.le, n, y ^ n * (l : K)⁻¹,
    UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ ?_, ?_⟩
  · have h1 : f ((l : K)⁻¹) = l := by
      have h2 : (l : K)⁻¹ = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by simp
      rw [h2, hf, spectralNorm_extends, norm_inv, Padic.norm_p]
      simp
    change f (y ^ n * (l : K)⁻¹) ≤ 1
    rw [hfmul, hfpow, h1]
    calc f y ^ n * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ hlpos.ne'
  · field_simp
end

section

theorem UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by
  intro R _ π ξ hc J h x hx
  choose! a z hz he using h
  have hsm : ∀ (n : ℕ) (u v : R),
      u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have hzs : ∀ n : ℕ, z^[n] x ∈ J := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hz _ ih
  let f : ℕ → R := fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i
  have hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n := fun n => Finset.sum_range_succ _ _
  have key : ∀ n, x = f n * ξ + z^[n] x * π ^ n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf]
      have h1 := he _ (hzs n)
      linear_combination ih + π ^ n * h1
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hf, ← sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcau
  have h0 : x - L * ξ = 0 := by
    apply IsHausdorff.haus hc.toIsHausdorff
    intro n
    rw [hsm]
    obtain ⟨c, hc'⟩ := (hsm _ _ _).1 (hL n)
    exact ⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩
  exact Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩
end

section

theorem UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (P : ℕ → R → Prop),
    (∀ (n : ℕ) (x : R), P n x → ∃ (y : R), y - x ∈ I ^ n ∧ P (n + (1 : ℕ)) y) →
      ∀ {x₀ : R}, P (0 : ℕ) x₀ → ∃ (x : R), ∀ (n : ℕ), ∃ (y : R), P n y ∧ x - y ∈ I ^ n := by
  intro R _ I hI P h x₀ h₀
  choose g hg hP using h
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3
end

section

theorem UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le :
    ∀ {A : Type} [inst : CommRing A]
    {I J : Ideal A}, J ≤ I → ∀ {e : ℕ}, I ^ e ≤ J → ∀ [IsPrecomplete J A], IsPrecomplete I A := by
  intro A _ I J hJI e he hJ
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    SModEq.mono (Submodule.smul_mono_left (h1 m)) (hf (Nat.mul_le_mul_left _ hmn)))
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos e))).trans
    (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)) (hL n))
end

section

private theorem UpperTheory.Reformulated.B.Qk17.pi_precomplete {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, IsPrecomplete I (N i)] : IsPrecomplete I (∀ i, N i) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose r hr using fun j : ι =>
    AdicCompletion.of_surjective I (N j) (AdicCompletion.pi I N y j)
  refine ⟨r, (AdicCompletion.piEquivOfFintype I N).injective ?_⟩
  rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.piEquivOfFintype_apply]
  funext j
  rw [← hr j]
  exact AdicCompletion.map_of I (LinearMap.proj (R := R) (φ := N) j) r

theorem UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type u_2)
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] [Module.Finite R M], IsPrecomplete I M := by
  intro R _ I _ M _ _ _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have := UpperTheory.Reformulated.B.Qk17.pi_precomplete I (fun _ : Fin n => R)
  rw [← AdicCompletion.of_surjective_iff]
  intro x
  obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective I hf x
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I (Fin n → R) y
  exact ⟨f r, (AdicCompletion.map_of I f r).symm⟩
end

section

theorem UpperTheory.Reformulated.B.Qg4.sxLimPt :
    ∀ {Λ A R S : Type} [inst : CommRing Λ] [inst_1 : CommRing A] [inst_2 : Algebra Λ A]
    [inst_3 : CommRing R] [inst_4 : Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R),
    (∀ (N : ℕ),
        ∃ (f : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          ∀ (s : S),
            (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) =
              (Ideal.Quotient.mk (I ^ (N + (1 : ℕ))) : R → R ⧸ I ^ (N + (1 : ℕ))) (y s)) →
      (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          (∀ (s : S), (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) = (f' : A → R ⧸ I ^ (N + (1 : ℕ))) (e s)) → f = f') →
        ∃ (f : A →ₐ[Λ] R), ∀ (s : S), (f : A → R) (e s) = y s := by
  intro Λ A R S _ _ _ _ _ I _ e y hex huniq
  choose f hf using hex
  have hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    refine huniq m _ _ fun s => ?_
    rw [AlgHom.comp_apply, hf, hf]
    rfl
  let g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    refine AlgHom.ext fun a => ?_
    simp only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f n a)
    rw [← hr]
    rfl
  refine ⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩
  have key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y := by
    apply IsHausdorff.funext' I
    intro n t
    have h1 := IsAdicComplete.mk_liftAlgHom I g hg n (e t)
    refine h1.trans ?_
    simp only [g, AlgHom.comp_apply, hf]
    rfl
  exact congrFun key s
end

section

theorem UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite :
    ∀ {O M : Type} [inst : CommRing O] [IsNoetherianRing O]
    (I : Ideal O) [IsAdicComplete I O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M] [Module.Finite O M],
    IsPrecomplete I M := by
  intro O M _ _ I _ _ _ _
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
end

section

open Polynomial

private theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (p : O[X])
    (hp : ∃ i, p.coeff i ∉ IsLocalRing.maximalIdeal O) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    obtain ⟨i, hi⟩ := hp
    intro h
    apply hi
    have := congrArg (PowerSeries.coeff i) h
    rwa [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero,
      IsLocalRing.residue_eq_zero_iff] at this
  obtain ⟨g, h, hg, hh, e⟩ := PowerSeries.exists_isWeierstrassFactorization h0
  have hI : IsLocalRing.maximalIdeal O ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hd := hg.isWeierstrassDivisorAt hI
  have hn : (((g : PowerSeries O).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree := by
    rw [← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1
      (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]
    simp
  have hdeg : g.degree = g.natDegree := Polynomial.degree_eq_natDegree hg.monic.ne_zero
  have e2 := Polynomial.modByMonic_add_div p g
  have key := hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O))
    (r := 0) (r' := p %ₘ g)
    (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic)
    (by
      rw [← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add,
        add_comm, e2])
  refine ⟨g, p /ₘ g, hg.monic, ?_, ?_⟩
  · have := PowerSeries.isUnit_iff_constantCoeff.1 hh
    rw [key.1] at this
    simpa using this
  · rw [← key.2, zero_add] at e2
    exact e2.symm

theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type} [inst_4 : CommRing R]
    [inst_5 : Algebra O R] [inst_6 : IsLocalRing R] {K : Type} [inst_7 : Field K] [inst_8 : Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R, IsIntegral O ((f : R → K) a) := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f a ha
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid O) := inferInstance
  have h1 : aeval (f a) p.primPart = 0 := aeval_primPart_eq_zero hp0 hp
  have h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O := by
    by_contra hc
    push Not at hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    apply hϖ.not_isUnit
    apply isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := hc i
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨g, q, hg, hq, e⟩ := UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2
  have h3 : IsUnit (aeval a q) := by
    by_contra hu
    have hm : aeval a q ∈ IsLocalRing.maximalIdeal R := hu
    have e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add q]
      simp
    rw [e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)] at hm
    exact hm (hq.map _)
  have h4 : aeval (f a) q ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (h3.map f).ne_zero
  rw [e, map_mul] at h1
  exact ⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩
end

section

theorem UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator :
    ∀ {B : Type} [inst : CommRing B] [IsDedekindDomain B] (I p : Ideal B) [hp : p.IsPrime],
      ∃ π ∈ I, ∃ s ∉ p, ∀ x ∈ I, s * x ∈ Ideal.span {π} := by
  intro B _ _ I p hp
  by_cases hI : I = ⊥
  · refine ⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩
    rw [hI, Ideal.mem_bot] at hx
    simp [hx]
  have hne : ¬ I ≤ I * p := by
    intro h
    have h1 : I * p = I * 1 := by
      rw [mul_one]
      exact le_antisymm Ideal.mul_le_left h
    have h2 : p = 1 := mul_left_cancel₀ (show I ≠ 0 from hI) h1
    exact hp.ne_top (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.mp hne
  have hle : Ideal.span {π} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJp : ¬ J ≤ p := by
    intro h
    apply hπ'
    have : π ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self π
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, s, hs', fun x hx => ?_⟩
  rw [hJ, mul_comm s x]
  exact Ideal.mul_mem_mul hx hs
end
