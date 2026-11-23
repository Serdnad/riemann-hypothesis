module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.Approximation
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified :
    ∀ (E : Type) [Field E] [NumberField E],
      (∀ P : HeightOneSpectrum (𝓞 E),
        (Ideal.absNorm P.asIdeal).Prime ↔ P.asIdeal.inertiaDeg ℤ = 1) ∧
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by
  intro E _ _
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ := by
    intro P
    haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
    exact ⟨Nat.absNorm_under_prime P.asIdeal,
      (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm⟩
  refine ⟨fun P => ?_, ?_⟩
  · obtain ⟨hq, hN⟩ := key P
    rw [hN]
    constructor
    · intro hpow
      have hf0 : P.asIdeal.inertiaDeg ℤ ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hpow
        exact Nat.not_prime_one hpow
      rcases hpow.eq_one_or_self_of_dvd _ (dvd_pow_self _ hf0) with h1 | h1
      · exact absurd h1 hq.one_lt.ne'
      · exact Nat.pow_right_injective hq.two_le (by simpa using h1.symm)
    · intro h1
      rw [h1, pow_one]
      exact hq
  · set d := (discr E).natAbs with hd_def
    have hd : 0 < d := Int.natAbs_pos.mpr (discr_ne_zero E)
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 E) (d ^ Module.finrank ℤ (𝓞 E))).preimage
      (fun P _ Q _ h => HeightOneSpectrum.ext h)).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hP ⊢
    obtain ⟨hq, -⟩ := key P
    set q := Ideal.absNorm (P.asIdeal.under ℤ) with hq_def
    have hmem := Int.absNorm_under_mem P.asIdeal
    rw [← hq_def] at hmem
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hqd : (q : ℤ) ∣ discr E := by
      by_contra hnd
      have hun := (not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) hqZ).mp hnd
      have hlies : P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
        (Ideal.liesOver_span_iff P.isPrime.ne_top hqZ).mpr (by simpa using hmem)
      exact hP (hun.ramificationIdx_eq_one hlies)
    have hqle : q ≤ d := Nat.le_of_dvd hd (by simpa using Int.natAbs_dvd_natAbs.mpr hqd)
    have hdvd : Ideal.absNorm P.asIdeal ∣ q ^ Module.finrank ℤ (𝓞 E) := by
      have hle : Ideal.span {((q : ℤ) : 𝓞 E)} ≤ P.asIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        simpa using hmem
      have hnorm : Algebra.norm ℤ ((q : ℤ) : 𝓞 E) = (q : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
        rw [← eq_intCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h
    calc Ideal.absNorm P.asIdeal ≤ q ^ Module.finrank ℤ (𝓞 E) :=
          Nat.le_of_dvd (pow_pos hq.pos _) hdvd
      _ ≤ d ^ Module.finrank ℤ (𝓞 E) := Nat.pow_le_pow_left hqle _

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory.UniformCoboundary

theorem exists_finset_fixed {K : Type} [Field K] {Γ : Type} (S : Set Γ)
    (M : Γ → Matrix (Fin 2) (Fin 2) K) :
    ∃ T : Finset Γ, (↑T ⊆ S) ∧
      ∀ v : Fin 2 → K, (∀ t ∈ T, M t *ᵥ v = v) → ∀ s ∈ S, M s *ᵥ v = v := by
  classical
  let W : Finset Γ → Submodule K (Fin 2 → K) :=
    fun T => ⨅ t ∈ T, LinearMap.ker (Matrix.toLin' (M t) - LinearMap.id)
  have hW : ∀ (T : Finset Γ) (v : Fin 2 → K), v ∈ W T ↔ ∀ t ∈ T, M t *ᵥ v = v := by
    intro T v
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]
  obtain ⟨_, ⟨T, hTS, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K (Fin 2 → K))).has_min
      {P | ∃ T : Finset Γ, ↑T ⊆ S ∧ W T = P} ⟨_, ∅, by simp, rfl⟩
  refine ⟨T, hTS, fun v hv s hs => ?_⟩
  have hle : W (insert s T) ≤ W T := by
    intro w hw
    rw [hW] at hw ⊢
    exact fun t ht => hw t (Finset.mem_insert_of_mem ht)
  have hnlt : ¬ W (insert s T) < W T :=
    hmin _ ⟨insert s T, by rw [Finset.coe_insert]; exact Set.insert_subset hs hTS, rfl⟩
  have heq : W (insert s T) = W T := (hle.lt_or_eq).resolve_left hnlt
  have hv' : v ∈ W (insert s T) := by rw [heq, hW]; exact hv
  exact (hW _ _).1 hv' s (Finset.mem_insert_self s T)

theorem exists_bound {K : Type} [NormedField K] {ι : Type} [Fintype ι]
    (L : (ι → K) →ₗ[K] (Fin 2 → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ι → K) (ε : ℝ), 0 ≤ ε → (∀ p, ‖w p‖ ≤ ε) → ∀ k, ‖L w k‖ ≤ C * ε := by
  classical
  refine ⟨∑ k, ∑ p, ‖L (Pi.single p 1) k‖, by positivity, fun w ε hε hw k => ?_⟩
  have h1 : w = ∑ p, w p • (Pi.single p 1 : ι → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : L w k = ∑ p, w p * L (Pi.single p 1) k := by
    conv_lhs => rw [h1]

    simp [map_sum, Finset.sum_apply]
  have h3 : ‖L w k‖ ≤ (∑ p, ‖L (Pi.single p 1) k‖) * ε := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hw p) (norm_nonneg _)
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ hε)
  exact Finset.single_le_sum (f := fun k => ∑ p, ‖L (Pi.single p 1) k‖)
    (fun k _ => by positivity) (Finset.mem_univ k)

theorem coboundary_of_approx {K : Type} [NormedField K] (q : K) (hq : ‖q‖ < 1) (Γ : Type)
    (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) K) (f : ℕ → Γ → Fin 2 → K) (y : Γ → Fin 2 → K)
    (hM : ∀ s i j, ‖M s i j‖ ≤ 1)
    (hf : ∀ r, ∃ v : Fin 2 → K, ∀ s ∈ S, f r s = M s *ᵥ v - v)
    (hy : ∀ r s i, ‖y s i - f r s i‖ ≤ ‖q ^ r‖) :
    ∃ v : Fin 2 → K, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_finset_fixed S M
  let e : (Fin 2 → K) →ₗ[K] (T × Fin 2 → K) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Matrix.toLin' (M p.1) - LinearMap.id)
  have he : ∀ v (p : T × Fin 2), e v p = (M p.1 *ᵥ v - v) p.2 := by
    intro v p
    simp [e, Matrix.toLin'_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective e.rangeRestrict
    (LinearMap.range_rangeRestrict e)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend g
  have heL : ∀ v, e (L (e v)) = e v := by
    intro v
    have h1 : L (e v) = g (e.rangeRestrict v) := LinearMap.congr_fun hL (e.rangeRestrict v)
    have h2 : e.rangeRestrict (g (e.rangeRestrict v)) = e.rangeRestrict v :=
      LinearMap.congr_fun hg (e.rangeRestrict v)
    rw [h1]
    exact congrArg Subtype.val h2
  have hSL : ∀ v, ∀ s ∈ S, M s *ᵥ (L (e v)) - L (e v) = M s *ᵥ v - v := by
    intro v s hs
    have h0 : e (L (e v) - v) = 0 := by rw [map_sub, heL, sub_self]
    have h1 : ∀ t ∈ T, M t *ᵥ (L (e v) - v) = L (e v) - v := by
      intro t ht
      rw [← sub_eq_zero]
      funext i
      have := congrFun h0 (⟨t, ht⟩, i)
      rw [he] at this
      exact this
    have h2 := hT _ h1 s hs
    rw [Matrix.mulVec_sub] at h2
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2
  obtain ⟨C, hC, hCb⟩ := exists_bound L
  let Y : T × Fin 2 → K := fun p => y p.1 p.2
  refine ⟨L Y, fun s hs => ?_⟩
  funext i
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have key : ∀ r : ℕ, ‖y s i - (M s *ᵥ L Y - L Y) i‖ ≤ (1 + 3 * C) * ‖q‖ ^ r := by
    intro r
    obtain ⟨vr, hvr⟩ := hf r
    have hε : 0 ≤ ‖q‖ ^ r := by positivity
    have hu : ∀ k, ‖L (Y - e vr) k‖ ≤ C * ‖q‖ ^ r := by
      refine hCb _ _ hε fun p => ?_
      rw [Pi.sub_apply, he, ← hvr p.1 (hTS p.1.2), ← norm_pow]
      exact hy r p.1 p.2
    have hv : L Y = L (e vr) + L (Y - e vr) := by simp [map_sub]
    generalize L (Y - e vr) = u at hu hv
    have hid : M s *ᵥ L Y - L Y = f r s + (M s *ᵥ u - u) := by
      rw [hvr s hs, ← hSL vr s hs, hv, Matrix.mulVec_add]
      abel
    have hMu : ‖(M s *ᵥ u) i‖ ≤ 2 * (C * ‖q‖ ^ r) := by
      have : (M s *ᵥ u) i = M s i 0 * u 0 + M s i 1 * u 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [this]
      have hb : ∀ k, ‖M s i k * u k‖ ≤ C * ‖q‖ ^ r := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hM s i k)).trans (hu k)
      have := norm_add_le (M s i 0 * u 0) (M s i 1 * u 1)
      linarith [hb 0, hb 1]
    have h1 : y s i - (M s *ᵥ L Y - L Y) i = (y s i - f r s i) - ((M s *ᵥ u) i - u i) := by
      rw [hid]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h2 := hy r s i
    rw [norm_pow] at h2
    rw [h1]
    have h3 := norm_sub_le (y s i - f r s i) ((M s *ᵥ u) i - u i)
    have h4 := norm_sub_le ((M s *ᵥ u) i) (u i)
    have h5 := hu i
    linarith
  have hlim : Filter.Tendsto (fun r : ℕ => (1 + 3 * C) * ‖q‖ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (1 + 3 * C)
  exact ge_of_tendsto' hlim key

theorem coboundary_of_padic_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  intro l _ Γ S M f y hM hf hy
  refine coboundary_of_approx ((l : ℕ) : PadicAlgCl l) ?_ Γ S M f y hM hf hy
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  have h0 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [h, h0]
  exact Padic.norm_p_lt_one

end GlobalTheory.UniformCoboundary
end

section

open scoped TensorProduct

namespace GlobalTheory.EmbUnitBallConj

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {ι : Type}
    [Fintype ι] (y : ι → E) (c : ι → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) :
    ∑ k, c k • b (y k) = 0 := by
  haveI : CharZero E := a.charZero
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : ι → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : ι → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : ι → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_equiv_of_ker_le {F T K : Type} [Field F] [CommRing T] [Algebra F T] [Field K]
    [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F K] (f g : T →ₐ[F] K)
    (h : RingHom.ker f ≤ RingHom.ker g) : ∃ σ : K ≃ₐ[F] K, ∀ x, σ (f x) = g x := by
  let S : IntermediateField F K :=
    Subalgebra.IsAlgebraic.toIntermediateField (S := f.range)
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
  let φ : f.range →ₐ[F] K :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)).comp
      (Ideal.quotientKerEquivRange f).symm.toAlgHom
  have hφ : ∀ x, φ ⟨f x, x, rfl⟩ = g x := by
    intro x
    have : (Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩ = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)
      ((Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩) = g x
    rw [this]
    rfl
  let φ' : S →ₐ[F] K := φ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := F) (L := S) (M := K)
    (E := K) φ'
  refine ⟨AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ), fun x => ?_⟩
  rw [← hφ x]
  exact DFunLike.congr_fun hψ (⟨f x, x, rfl⟩ : S)

noncomputable def ext (a : E →+* PadicAlgCl l) : ℚ_[l] ⊗[ℤ] E →ₐ[ℚ_[l]] PadicAlgCl l :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) a.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem ext_tmul (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by
  simp [ext, Algebra.smul_def, Algebra.ofId_apply]

theorem exists_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] (j₁ j₂ : Ω →+* PadicAlgCl l), (∀ x, ‖j₁ x‖ ≤ 1 ↔ ‖j₂ x‖ ≤ 1) → ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j₁ x) = j₂ x := by
  intro l _ Ω _ a b h
  have h' : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have ha : 0 < ‖a x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have hb : 0 < ‖b x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have := h x⁻¹
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ ha, inv_le_one₀ hb] at this
      rw [← not_le, ← not_le, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_of_ker_le (ext a) (ext b) (by
    intro t ht
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t

    rw [RingHom.mem_ker, map_sum] at ht ⊢
    simp only [ext_tmul] at ht ⊢
    rw [← Finset.sum_coe_sort] at ht ⊢
    exact sum_eq_zero a b h' _ _ ht)
  refine ⟨σ, fun x => ?_⟩
  simpa [ext_tmul] using hσ (1 ⊗ₜ x)

end GlobalTheory.EmbUnitBallConj
end

section

namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicAlgCl (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  rw [Metric.denseRange_iff]
  intro a δ δpos
  haveI : CharZero Ω := j.charZero
  have hint : IsIntegral ℚ_[l] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[l][X] := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have he : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l))
      = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, he, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, hc⟩ := hb
  exact ⟨c, by rw [hc, dist_eq_norm]; exact hab⟩

theorem padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x

end GlobalTheory
end

section

namespace GlobalTheory.IntegralNormAlgebraMap

theorem norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact a.2

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := fun y => by
    change ‖y‖₊ ≤ 1 ↔ _
    exact_mod_cast Iff.rfl
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
      (fun a => (hv _).2 (norm_algebraMap_le_one a))
  have h : IsIntegral v.integer x :=
    IsIntegral.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl) hx
  exact (hv x).1 (Valuation.Integers.mem_of_integral (Valuation.integer.integers v) h)

end GlobalTheory.IntegralNormAlgebraMap
end

section

namespace GlobalTheory.ContinuousZModPow

theorem continuous_toZModPow (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ) :
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hl.out.pos) _
  have hev : ∀ᶠ y in nhds x, PadicInt.toZModPow n y = PadicInt.toZModPow n x := by
    filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
    exact hy
  exact tendsto_nhds_of_eventually_eq hev

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ),
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  intro l _ n
  exact continuous_toZModPow l n

end GlobalTheory.ContinuousZModPow
end
