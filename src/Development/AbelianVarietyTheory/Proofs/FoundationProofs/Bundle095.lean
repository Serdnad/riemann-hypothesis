module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.NumberTheory.FunctionField
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

@[expose] public section

section

open GlobalTheory.K5 GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.Glue.DPsi

variable {p : ℕ} [Fact p.Prime]

theorem thL_add (a b : Lau p) : thL (a + b) = thL a + thL b := by
  ext r
  simp [thL, mul_add]

theorem thL_zero : thL (0 : Lau p) = 0 := by
  ext r
  simp [thL]

def sh (N : ℕ) (i : ℤ) (w : ℤ → ℤ_[p]) (b : Lau p) : Lau p where
  coeff r := if (N : ℤ) ∣ r then w r * b.coeff (r + i) else 0
  isPWO_support' := by
    refine (b.isPWO_support.image_of_monotone (f := fun r : ℤ => r - i) (fun x y h => by simpa using h)).mono ?_
    intro r hr
    refine ⟨r + i, ?_, by simp⟩
    intro h
    apply hr
    simp [h]

def dn (N : ℕ) (hN : 0 < N) (B : Lau p) : Lau p where
  coeff j := B.coeff ((N : ℤ) * j)
  isPWO_support' := by
    have hm : StrictMono (fun j : ℤ => (N : ℤ) * j) := fun x y h =>
      mul_lt_mul_of_pos_left h (by exact_mod_cast hN)
    have hwf := B.isPWO_support
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at hwf ⊢
    intro g hg
    obtain ⟨m, n, hmn, h⟩ := hwf (fun k => (N : ℤ) * g k) hg
    exact ⟨m, n, hmn, hm.le_iff_le.1 h⟩

theorem coeff_natCast_mul (n : ℕ) (X : Lau p) (s : ℤ) : ((n : Lau p) * X).coeff s = (n : ℤ_[p]) * X.coeff s := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], HahnSeries.coeff_smul, smul_eq_mul]

theorem decomp (N : ℕ) (hN : 0 < N) (b : Lau p) :
    b = ∑ i ∈ Finset.range N, HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b := by
  ext s
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (s % N).toNat]
  · have h0 : (((s % N).toNat : ℕ) : ℤ) = s % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')
    have h1 : (N : ℤ) ∣ s - s % N := Int.dvd_self_sub_emod
    rw [HahnSeries.coeff_single_mul, h0]
    simp [sh, h1]
  · intro i hi hne
    have h1 : ¬ (N : ℤ) ∣ s - i := by
      intro h
      have h2 : (i : ℤ) % N = s % N := (Int.modEq_iff_dvd).2 h
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.1 hi)] at h2
      apply hne
      rw [← h2]
      simp
    rw [HahnSeries.coeff_single_mul]
    simp [sh, h1]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have := Int.emod_lt_of_pos s hN'
    have := Int.emod_nonneg s hN'.ne'
    omega

theorem thL_part (N i : ℕ) (b : Lau p) :
    thL (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) =
      (i : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) +
      (N : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun r => ((r / N : ℤ) : ℤ_[p])) b) := by
  ext s : 2
  rw [HahnSeries.coeff_add, coeff_natCast_mul, coeff_natCast_mul]
  change (s : ℤ_[p]) * _ = _
  simp only [HahnSeries.coeff_single_mul, sh, one_mul]
  split_ifs with h
  · have h1 : (s : ℤ_[p]) = i + N * (((s - i) / N : ℤ) : ℤ_[p]) := by
      have h2 : s = i + N * ((s - i) / N) := by rw [Int.mul_ediv_cancel' h]; ring
      exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) h2
    rw [← mul_assoc, ← add_mul, ← h1]
  · simp

theorem part_eq_zero {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] [Module A M]
    (D : Derivation A R M) (q β γ : R) (i N : ℕ) (hβ : D β = 0) (hN : (N : R) • D q = 0) :
    q • D (q ^ i * β) - ((i : R) * (q ^ i * β) + (N : R) * γ) • D q = 0 := by
  rw [Derivation.leibniz, hβ, smul_zero, zero_add, add_smul, mul_comm (N : R), mul_smul γ, hN, smul_zero, add_zero,
    Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul, ← sub_smul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h : q * β * i * q ^ (i - 1) - i * (q ^ i * β) = 0 := by
      conv_lhs => rw [← mul_pow_sub_one hi.ne' q]
      ring
    rw [h, zero_smul]

theorem smul_D_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  intro p hp Ω _ _ T L ψ hψ b x y qL hx hy hq
  have hqi : IsIntegral (O0 p) (T.qq L) :=
    IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hmem : ∀ z, ψ z ∈ integralClosure (O0 p) Ω := fun z => by
    have h1 : ψ z ∈ ψ.range := ⟨z, rfl⟩
    rw [hψ.rng] at h1
    exact adjoin_le_integralClosure hqi h1
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Lau p →+* integralClosure (O0 p) Ω, ∀ c, (Ψ c : Ω) = ψ (algebraMap (Lau p) (O0 p) c) :=
    ⟨(ψ.codRestrict (integralClosure (O0 p) Ω) hmem).comp (algebraMap (Lau p) (O0 p)), fun _ => rfl⟩
  have hx' : x = Ψ b := Subtype.ext (hx.trans (hΨ _).symm)
  have hy' : y = Ψ (thL b) := Subtype.ext (hy.trans (hΨ _).symm)
  rw [hx', hy']
  generalize KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) = D
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hqN : qL ^ p ^ L = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, hq, Basic.qq_pow]; rfl)
  have hND : ((p ^ L : ℕ) : integralClosure (O0 p) Ω) • D qL = 0 := by
    have h1 : D (qL ^ p ^ L) = 0 := by rw [hqN]; exact D.map_algebraMap _
    rw [Derivation.leibniz_pow] at h1
    have h2 : qL • ((p ^ L) • qL ^ (p ^ L - 1) • D qL) = 0 := by rw [h1, smul_zero]
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), smul_smul, smul_smul, mul_right_comm,
      mul_pow_sub_one hN.ne', hqN, mul_smul] at h2
    have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p)) := (Basic.isUnit_qO p).map _
    exact hu.smul_left_cancel.1 (h2.trans (smul_zero _).symm)
  have hmono : ∀ i : ℕ, Ψ (HahnSeries.single (i : ℤ) (1 : ℤ_[p])) = qL ^ i := by
    intro i
    have h1 : (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) : Lau p) = (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) ^ i := by
      rw [HahnSeries.single_pow]; simp
    have h2 : Ψ (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) = qL :=
      Subtype.ext (by rw [hΨ, hq]; exact hψ.par)
    rw [h1, map_pow, h2]
  have hsub : ∀ (i : ℤ), D (Ψ (sh (p ^ L) i (fun _ => 1) b)) = 0 := by
    intro i
    have h1 : Ψ (sh (p ^ L) i (fun _ => 1) b) = algebraMap (O0 p) (integralClosure (O0 p) Ω)
        (algebraMap (Lau p) (O0 p) (dn (p ^ L) hN (sh (p ^ L) i (fun _ => 1) b))) := by
      apply Subtype.ext
      rw [hΨ]
      refine hψ.sub _ _ (fun j => ?_) (fun r hr => ?_)
      · simp [dn]
      · have h2 : ¬ ((p ^ L : ℕ) : ℤ) ∣ r := by simpa using hr
        exact if_neg h2
    rw [h1]
    exact D.map_algebraMap _
  let E : Lau p →+ KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω) :=
    { toFun := fun c => qL • D (Ψ c) - Ψ (thL c) • D qL
      map_zero' := by simp [thL_zero]
      map_add' := by
        intro a c
        simp only [thL_add, map_add (f := _), add_smul, smul_add]
        abel }
  have hpart : ∀ i ∈ Finset.range (p ^ L),
      E (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh (p ^ L) i (fun _ => 1) b) = 0 := by
    intro i _
    change qL • D (Ψ _) - Ψ (thL _) • D qL = 0
    rw [thL_part, map_add Ψ, map_mul Ψ (i : Lau p), map_mul Ψ ((p ^ L : ℕ) : Lau p), map_mul Ψ, map_natCast Ψ, map_natCast Ψ, hmono]
    exact part_eq_zero D qL _ _ i (p ^ L) (hsub i) hND
  have hE : E b = 0 := by

    rw [decomp (p ^ L) hN b, map_sum]
    exact Finset.sum_eq_zero hpart
  exact sub_eq_zero.1 hE

end GlobalTheory.Glue.DPsi
end
end

section

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.TInv

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

theorem const_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) : ∃ c : Ω, algebraMap Ω X.K c = x := by
  have hint : IsIntegral Ω x := IsIntegral.of_pow hL (by rw [hx]; exact isIntegral_one)
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (hx := hdeg))
  exact ⟨c, hc⟩

theorem cast_eq_of_dvd {d : ℕ} {y c : ℤ} (h : (d : ℤ) ∣ y - c) : (y : ZMod d) = (c : ZMod d) := ((ZMod.intCast_eq_intCast_iff_dvd_sub c y d).mpr h).symm

theorem exists_sl2_scalar_mod_coprime (A₁ A₂ : ℕ) (hcop : Nat.Coprime A₁ A₂) :
    ∃ δ : SL(2, ℤ), (A₁ : ℤ) ∣ δ 0 0 - 1 ∧ (A₁ : ℤ) ∣ δ 1 1 - 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 1 0 ∧
      ((A₁ : ℤ) * A₂) ∣ δ 0 1 ∧ (A₂ : ℤ) ∣ δ 0 0 + 1 ∧ (A₂ : ℤ) ∣ δ 1 1 + 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 0 0 - δ 1 1 := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((A₁ : ℤ) ^ 2) ((A₂ : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  refine ⟨⟨!![v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2, (A₁ : ℤ) * A₂;
      -4 * u * v * ((A₁ : ℤ) * A₂), v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination (u * (A₁ : ℤ) ^ 2 + v * (A₂ : ℤ) ^ 2 + 1) * huv
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-4 * u * v, by
      show -4 * u * v * ((A₁ : ℤ) * A₂) = _
      ring⟩
  · exact ⟨1, by
      show (A₁ : ℤ) * A₂ = _
      ring⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨0, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - (v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2) = _
      ring⟩

private lemma t_inv_mul_mul_t_mul_inv_mem_gamma {M : ℕ} (δ : SL(2, ℤ)) (hc : (M : ℤ) ∣ δ 1 0) (had : (M : ℤ) ∣ δ 0 0 - δ 1 1) :
    ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  have hc' : ((δ 1 0 : ℤ) : ZMod M) = 0 := by
    simpa using cast_eq_of_dvd (d := M) (c := 0) (by simpa using hc)
  have had' : ((δ 0 0 : ℤ) : ZMod M) = ((δ 1 1 : ℤ) : ZMod M) := cast_eq_of_dvd had
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, hc', had'] <;> ring

theorem exists_delta (N M l n : ℕ) (hl : l.Prime) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (hM : 0 < M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 N ∧ -δ ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  obtain ⟨e, m, hlm, hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.one_lt.ne'
  have hcl : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlm
  have hcN : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
  have hcop : Nat.Coprime (N * m) (l ^ (n + e)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hcN.symm hcl.symm)
  obtain ⟨δ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_sl2_scalar_mod_coprime (N * m) (l ^ (n + e)) hcop
  have hN1 : (N : ℤ) ∣ ((N * m : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (Dvd.intro m rfl)
  have hln : ((l ^ n : ℕ) : ℤ) ∣ ((l ^ (n + e) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow l (Nat.le_add_right n e))
  have hln' : ((l ^ n : ℕ) : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := Dvd.dvd.mul_left hln _
  have hMd : (M : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := by
    have : M ∣ (N * m) * l ^ (n + e) := by
      rw [hM']
      exact ⟨N * l ^ n, by ring⟩
    exact_mod_cast this
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h1)
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h2)
    · simpa using cast_eq_of_dvd (d := N) (c := 0) (by rw [sub_zero]; exact dvd_trans (hN1.mul_right _) h3)
  · rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 0) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h5).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 1) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h4).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 0) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h3).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 1) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h6).neg_right)
  · exact t_inv_mul_mul_t_mul_inv_mem_gamma δ (dvd_trans hMd h3) (dvd_trans hMd h7)

private lemma sl_eq_self_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) (g : GQ) : X.sl g x = x := by
  obtain ⟨c, rfl⟩ := const_of_pow_eq_one X hL hx
  exact (X.sl g).commutes c

theorem sl_T_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (u : X.K) (hu : u ≠ 0)
    (hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)))
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) :
    X.sl (ofSL ModularGroup.T) u = u := by
  have hL : 0 < l ^ n := pow_pos hl.pos n
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  have huL : u ^ (l ^ n) ≠ 0 := pow_ne_zero _ hu
  obtain ⟨ζ, hTu⟩ : ∃ ζ : X.K, X.sl (ofSL ModularGroup.T) u = ζ * u :=
    ⟨X.sl (ofSL ModularGroup.T) u / u, (div_mul_cancel₀ _ hu).symm⟩
  have hζL : ζ ^ (l ^ n) = 1 := by
    have h1 : X.sl (ofSL ModularGroup.T) (u ^ (l ^ n)) = u ^ (l ^ n) := hinv _ hT
    rw [map_pow, hTu, mul_pow] at h1
    exact mul_right_cancel₀ huL (h1.trans (one_mul _).symm)
  have hζfix : ∀ h : GQ, X.sl h ζ = ζ := fun h => sl_eq_self_of_pow_eq_one X hL hζL h
  obtain ⟨M, hM, hMu⟩ := X.level u
  obtain ⟨δ, hδ1, hδl, hδM⟩ := exists_delta N M l n hl hlN hN hM
  obtain ⟨g, hg, hgL⟩ := hδ δ hδ1 hδl
  have hsu : X.sl (ofSL δ) u ≠ 0 := fun h =>
    hu ((X.sl (ofSL δ)).injective (h.trans (map_zero _).symm))
  have hP0 : u * X.sl (ofSL δ) u ≠ 0 := mul_ne_zero hu hsu
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hL.ne'] at hgL
    exact hP0 ((pow_eq_zero_iff hL.ne').mp hgL)
  have hw : (u * X.sl (ofSL δ) u / g) ^ (l ^ n) = 1 := by
    rw [div_pow, hgL, div_self (pow_ne_zero _ hg0)]
  have hTP : X.sl (ofSL ModularGroup.T) (u * X.sl (ofSL δ) u) = u * X.sl (ofSL δ) u := by
    rw [← div_mul_cancel₀ (u * X.sl (ofSL δ) u) hg0, map_mul, sl_eq_self_of_pow_eq_one X hL hw, hg _ hT]
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ CongruenceSubgroup.Gamma M,
      δ * ModularGroup.T = ModularGroup.T * γ * δ := ⟨_, hδM, by group⟩
  have hTδ : X.sl (ofSL ModularGroup.T) (X.sl (ofSL δ) u) = ζ * X.sl (ofSL δ) u := by
    rw [← X.sl_mul, ← map_mul ofSL δ ModularGroup.T, hγeq, map_mul, map_mul, X.sl_mul, X.sl_mul, hTu,
      map_mul (X.sl (ofSL γ)), hζfix, hMu γ hγ, map_mul (X.sl (ofSL δ)), hζfix]
  have hsq : ζ ^ 2 = 1 := by
    have h := hTP
    rw [map_mul, hTu, hTδ] at h
    have h2 : ζ ^ 2 * (u * X.sl (ofSL δ) u) = 1 * (u * X.sl (ofSL δ) u) := by
      linear_combination h
    exact mul_right_cancel₀ hP0 h2
  have hodd : Odd (l ^ n) := (hl.odd_of_ne_two hl2).pow
  obtain ⟨k, hk⟩ := hodd
  have hζ1 : ζ = 1 := by
    have h3 : ζ ^ (l ^ n) = ζ := by rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← h3, hζL]
  rw [hTu, hζ1, one_mul]

end GlobalTheory.TInv
end
end

section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

theorem exists_map_const_eq_of_isAlgClosed {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [Field L] (i : Ω →+* L) (σ : L →+* L) (c : Ω) : ∃ c' : Ω, σ (i c) = i c' := by
  letI : Algebra Ω L := i.toAlgebra
  obtain ⟨p, hp, h0⟩ : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have e : (σ.comp i).comp (algebraMap ℚ Ω) = i.comp (algebraMap ℚ Ω) := RingHom.ext_rat _ _
  have hint : IsIntegral Ω (σ (i c)) := by
    refine ⟨p.map (algebraMap ℚ Ω), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    show p.eval₂ (i.comp (algebraMap ℚ Ω)) ((σ.comp i) c) = 0
    rw [← e, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one Ω (σ (i c))
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  exact ⟨c', hc'.symm⟩

theorem isIntegral_map_of_map_range {R L : Type} [CommRing R] [Field L] [Algebra R L] (σ : L →+* L)
    (h : ∀ r : R, ∃ r' : R, σ (algebraMap R L r) = algebraMap R L r') {x : L} (hx : IsIntegral R x) :
    IsIntegral R (σ x) := by
  obtain ⟨p, hp, h0⟩ := hx
  have hl : p.map (σ.comp (algebraMap R L)) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨r', hr'⟩ := h (p.coeff n)
    exact ⟨r', by rw [Polynomial.coeff_map, RingHom.comp_apply, hr']⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, h0, map_zero]

theorem map_mem_ringOfIntegers_of_fix_mdl :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ)
      (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)),
      letI := GlobalTheory.K4.algPoly X Γ'
      letI := GlobalTheory.K4.algMdl X Γ' S
      ∀ (σ : GlobalTheory.K4.lev X Γ' ≃ₐ[GlobalTheory.K4.mdl X Γ' S] GlobalTheory.K4.lev X Γ') (x : GlobalTheory.K4.lev X Γ'),
        x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') →
          σ x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ _ ε X Γ' S
  letI := GlobalTheory.K4.algPoly X Γ'
  letI := GlobalTheory.K4.algMdl X Γ' S
  intro σ x hx
  have hj : σ ⟨X.jK, jK_mem_lev X Γ'⟩ = ⟨X.jK, jK_mem_lev X Γ'⟩ :=
    σ.commutes (⟨X.jK, jK_mem_mdl X Γ' S⟩ : mdl X Γ' S)
  have key : ∀ P : Polynomial Ω, ∃ Q : Polynomial Ω, σ (jPoly X Γ' P) = jPoly X Γ' Q := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P P' hP hP' =>
      obtain ⟨Q, hQ⟩ := hP
      obtain ⟨Q', hQ'⟩ := hP'
      exact ⟨Q + Q', by rw [map_add (f := _), map_add (f := _), hQ, hQ', map_add (f := _)]⟩
    | monomial n c =>
      obtain ⟨c', hc'⟩ := exists_map_const_eq_of_isAlgClosed (levConst X Γ') (σ : lev X Γ' →+* lev X Γ') c
      refine ⟨Polynomial.monomial n c', ?_⟩
      simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_pow]
      rw [hj, ← hc']
      rfl
  exact isIntegral_map_of_map_range (R := Polynomial Ω) (σ : lev X Γ' →+* lev X Γ') key hx

end GlobalTheory.K4
end

section

open GlobalTheory.KZ Matrix

namespace GlobalTheory

theorem galois_relation_of_frob_approx : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Type} [NormedField E] (r : ℕ) (A : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin r) (Fin r) E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (v : Fin r → E), (∀ (s : Ω ≃ₐ[ℚ] Ω) (δ : ℝ), 0 < δ → ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → (∀ i j, ‖A (s * s') i j - A s i j‖ < δ) ∧ ‖t (s * s') - t s‖ < δ ∧ ‖d (s * s') - d s‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s, FrobAt q s → ∀ i, ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < δ) → (∀ (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ), ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s')) → ∀ s, A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v = 0 := by
  intro Ω _ _ E _ r A t d v hcont happrox hdens s
  funext i

  let G : (Fin r → Fin r → E) × E × E → E := fun x =>
    (Matrix.of x.1 *ᵥ (Matrix.of x.1 *ᵥ v) - x.2.1 • (Matrix.of x.1 *ᵥ v) + x.2.2 • v) i
  have hG : Continuous G := by
    simp only [G, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    fun_prop
  have key : ∀ ε : ℝ, 0 < ε → ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hGη⟩ := Metric.continuous_iff.mp hG (fun a b => A s a b, t s, d s) (ε / 2) (by linarith)
    obtain ⟨E0, hE0⟩ := hcont s η hη
    obtain ⟨S, hS⟩ := happrox (ε / 2) (by linarith)
    obtain ⟨s', q, hfix, hq, hqS, hfr⟩ := hdens s E0 S
    obtain ⟨hA, ht, hd⟩ := hE0 s' hfix
    have h1 := hS q hq hqS (s * s') hfr i
    have hdist : dist (fun a b => A (s * s') a b, t (s * s'), d (s * s')) (fun a b => A s a b, t s, d s) < η := by
      rw [Prod.dist_eq, Prod.dist_eq]
      refine max_lt ?_ (max_lt ?_ ?_)
      · rw [dist_pi_lt_iff hη]; intro a
        rw [dist_pi_lt_iff hη]; intro b
        rw [dist_eq_norm]; exact hA a b
      · rw [dist_eq_norm]; exact ht
      · rw [dist_eq_norm]; exact hd
    have h2 := hGη _ hdist
    have e1 : G (fun a b => A (s * s') a b, t (s * s'), d (s * s')) = (A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i := rfl
    have e2 : G (fun a b => A s a b, t s, d s) = (A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i := rfl
    rw [e1, e2, dist_eq_norm] at h2
    have := norm_sub_le_norm_sub_add_norm_sub ((A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i) ((A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i) 0
    rw [norm_sub_rev] at h2
    simp only [sub_zero] at this
    linarith
  have : ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ = 0 := by
    by_contra h
    have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    exact lt_irrefl _ (key _ hpos)
  simpa using this

end GlobalTheory
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) → IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  first | exact @GlobalTheory.K5.PDiv.pdiv | exact GlobalTheory.K5.PDiv.pdiv | (intros; apply GlobalTheory.K5.PDiv.pdiv <;> assumption)
end
