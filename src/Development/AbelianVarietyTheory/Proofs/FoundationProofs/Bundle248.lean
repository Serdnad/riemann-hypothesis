module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.UnitaryTransvection

def tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  1 + μ • Matrix.vecMulVec w (fun i => D.host.conj (w i))

theorem tv_mulVec (D : D7) {n : ℕ} (μ : D.host.E) (w v : Fin n → D.host.E) :
    (tv D μ w).mulVec v = v + (μ * hE D v w) • w := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, hE,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cT_tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) :
    cT D (tv D μ w) = tv D (D.host.conj μ) w := by
  ext i j
  simp only [cT, tv, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, conj_conj, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp only [if_true, map_one]; ring
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]; ring

theorem tv_unitary (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E)
    (h : μ + D.host.conj μ + μ * D.host.conj μ * hE D w w = 0) : tv D μ w * cT D (tv D μ w) = 1 := by
  rw [cT_tv]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, Matrix.one_mulVec,
    hE_add_left, hE_smul_left, add_assoc, ← add_smul]
  have : D.host.conj μ * hE D v w + μ * (hE D v w + D.host.conj μ * hE D v w * hE D w w) = 0 := by
    linear_combination hE D v w * h
  rw [this, zero_smul, add_zero]

theorem smul_mem_int {D : D7} {n : ℕ} (N : Lat D n) {c : D.host.E} (hc : IntE D c) {v : Fin n → D.host.E}
    (hv : v ∈ N) : c • v ∈ N := by
  obtain ⟨a, rfl⟩ := hc
  rw [algebraMap_smul]
  exact N.smul_mem a hv

theorem intE_nat (D : D7) (m : ℕ) : IntE D (m : D.host.E) := ⟨m, map_natCast _ m⟩

theorem gen {D : D7} {n : ℕ} (s : Matrix (Fin n) (Fin n) D.host.E) (c : D.host.E) (M N : Lat D n)
    (z : Fin n → D.host.E) (hM : ∀ y ∈ M, c • s.mulVec y ∈ N) (hz : c • s.mulVec z ∈ N) :
    ∀ v ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z}, c • s.mulVec v ∈ N := by
  intro v hv
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [Matrix.mulVec_add, smul_add]
  refine N.add_mem (hM y hy) ?_
  rw [← algebraMap_smul D.host.E a z, Matrix.mulVec_smul, smul_comm]
  exact smul_mem_int N ⟨a, rfl⟩ hz

theorem step {D : D7} {n : ℕ} (M N : Lat D n) (hMN : M ≤ N) (w y : Fin n → D.host.E) (μ : D.host.E) (m : ℕ)
    (hw : ((m : D.host.E) * μ) • w ∈ M) (hy : y ∈ N) (hi : IntE D (hE D y w)) :
    ((m * m : ℕ) : D.host.E) • (tv D μ w).mulVec y ∈ N := by
  rw [tv_mulVec, smul_add, smul_smul]
  refine N.add_mem (smul_mem_int N (intE_nat D _) hy) ?_
  have : ((m * m : ℕ) : D.host.E) * (μ * hE D y w) = ((m : D.host.E) * hE D y w) * ((m : D.host.E) * μ) := by
    push_cast; ring
  rw [this, mul_smul]
  exact smul_mem_int N (mul_mem (intE_nat D m) hi) (hMN hw)

theorem transvection : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  intro D n q P hP M b x lam m hbx hM hww hl hmq ⟨p, hp, hpl⟩ ⟨p', hp', hpl'⟩
  have hPw : ∀ a ∈ P, (a : D.host.E) • (b + x) ∈ M := by
    intro a ha
    have : a • (b + x) ∈ M := by
      rw [smul_add]; exact M.add_mem (hbx a ha).1 (hbx a ha).2
    rw [← algebraMap_smul D.host.E a (b + x)] at this
    exact this
  have hcl : (m : D.host.E) * D.host.conj lam = ((sgO D p : 𝓞 D.host.E) : D.host.E) := by
    rw [sgO_coe, ← hpl, map_mul, map_natCast]
  have h1 : ((m : D.host.E) * lam) • (b + x) ∈ M := by rw [hpl]; exact hPw p hp
  have h2 : ((m : D.host.E) * D.host.conj lam) • (b + x) ∈ M := by rw [hcl]; exact hPw _ (hP p hp)
  have h3 : ((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x) ∈ M := by rw [hpl']; exact hPw p' hp'
  have hmem : ∀ z : Fin n → D.host.E, z ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z} := fun z =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hco : Nat.Coprime (m * m) q := Nat.Coprime.mul_left hmq hmq
  refine ⟨tv D lam (b + x), tv_unitary D lam _ hl, ⟨m * m, hco, ?_, ?_⟩, ⟨m * m, hco, ?_, ?_⟩⟩
  · exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h1 (hmem _) hww)
  · rw [cT_tv]
    exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h2 (hmem _) hww)
  · refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have : ((m * m : ℕ) : D.host.E) • (b + (lam * hE D b (b + x)) • (b + x)) =
        (m : D.host.E) • (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • x := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      push_cast; ring
    rw [this]
    exact Submodule.sub_mem _ (smul_mem_int _ (intE_nat D m) (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem x))
  · rw [cT_tv]
    refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have hx : hE D x (b + x) = hE D (b + x) (b + x) - hE D b (b + x) := by
      rw [hE_add_left]; ring
    have : ((m * m : ℕ) : D.host.E) • (x + (D.host.conj lam * hE D x (b + x)) • (b + x)) =
        ((m : D.host.E) + ((m : D.host.E) * D.host.conj lam) * hE D (b + x) (b + x)) •
          (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • b := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [hx]
      push_cast
      linear_combination (-((m : D.host.E) * m * hE D b (b + x) * (b i + x i))) * hl
    rw [this]
    refine Submodule.sub_mem _ (smul_mem_int _ ?_ (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem b))
    rw [hcl]
    exact add_mem (intE_nat D m) (mul_mem ⟨sgO D p, rfl⟩ hww)

end GlobalTheory.UnitaryTransvection
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.IdealGenerator

theorem coe_ideal_mul {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (I : FractionalIdeal R⁰ K) :
    (((P : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K) = P • (I : Submodule R K) := by
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨p, hp, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hm
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hp hn
  · rw [Submodule.smul_le]
    intro p hp n hn
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ((IsLocalization.mem_coeSubmodule _ _).2 ⟨p, hp, rfl⟩) hn

theorem exists_gen {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), ∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K) := by
  have hle : (P : FractionalIdeal R⁰ K) * I ≤ I := by
    calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := by
          gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := one_mul I
  have hne : (P : FractionalIdeal R⁰ K) * I ≠ I := by
    intro h
    have h1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI (by rw [h, one_mul])
    exact hP.ne_top (by simpa using (FractionalIdeal.coeIdeal_eq_one.1 h1))
  obtain ⟨t₀, ht₀, ht₀'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨t₀, ht₀, ?_⟩
  set S : FractionalIdeal R⁰ K := FractionalIdeal.spanSingleton R⁰ t₀ + (P : FractionalIdeal R⁰ K) * I with hS
  have hSle : S ≤ I := by
    rw [hS, ← FractionalIdeal.sup_eq_add]
    exact sup_le (FractionalIdeal.spanSingleton_le_iff_mem.2 ht₀) hle
  have hPS : (P : FractionalIdeal R⁰ K) * I ≤ S := by
    rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
  have hJ : S * I⁻¹ ≤ 1 := by
    calc S * I⁻¹ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  obtain ⟨J, hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ
  have hSJ : S = (J : FractionalIdeal R⁰ K) * I := by
    rw [hJ', mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hPJ : P ≤ J := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, hJ']
    calc (P : FractionalIdeal R⁰ K) = (P * I) * I⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ S * I⁻¹ := by gcongr
  have hJt : J = ⊤ := by
    by_contra h
    have hPJ' := hP.eq_of_le h hPJ
    apply ht₀'
    rw [hPJ', ← hSJ]
    have : FractionalIdeal.spanSingleton R⁰ t₀ ≤ S := by
      rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact this (FractionalIdeal.mem_spanSingleton_self _ _)
  have hSI : S = I := by rw [hSJ, hJt, FractionalIdeal.coeIdeal_top, one_mul]
  intro t ht
  have ht' : t ∈ (S : Submodule R K) := by rw [hSI]; exact ht
  rw [hS, FractionalIdeal.coe_add, coe_ideal_mul, FractionalIdeal.coe_spanSingleton, Submodule.add_eq_sup,
    Submodule.mem_sup] at ht'
  obtain ⟨y, hy, z, hz, rfl⟩ := ht'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨a, by simpa using hz⟩

theorem mem_range_of_mul_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : K)
    (h : ∀ t ∈ (I : Submodule R K), x * t ∈ (I : Submodule R K)) : x ∈ (algebraMap R K).range := by
  have h1 : FractionalIdeal.spanSingleton R⁰ x * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 h
  have h2 : FractionalIdeal.spanSingleton R⁰ x ≤ 1 := by
    calc FractionalIdeal.spanSingleton R⁰ x = (FractionalIdeal.spanSingleton R⁰ x * I) * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)

theorem exists_gen_and {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), (∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K)) ∧
      ∀ θ : K, θ ∉ (algebraMap R K).range → (∀ p ∈ P, p • θ ∈ (algebraMap R K).range) →
        ∀ a : R, a • (t₀ * θ) ∈ (I : Submodule R K) → a ∈ P := by
  obtain ⟨t₀, ht₀, hgen⟩ := exists_gen P hP I hI
  refine ⟨t₀, ht₀, hgen, fun θ hθ hPθ a ha => ?_⟩
  by_contra haP
  have hθP : ∀ z ∈ P • (I : Submodule R K), θ * z ∈ (I : Submodule R K) := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp n hn => ?_) (fun x y hx hy => ?_)
    · obtain ⟨q, hq⟩ := hPθ p hp
      have : θ * p • n = q • n := by
        rw [Algebra.smul_def q, hq, smul_mul_assoc, mul_smul_comm]
      rw [this]; exact Submodule.smul_mem _ _ hn
    · rw [mul_add]; exact add_mem hx hy
  have haθ : a • θ ∈ (algebraMap R K).range := by
    refine mem_range_of_mul_mem I hI _ fun t ht => ?_
    obtain ⟨b, hb⟩ := hgen t ht
    have : a • θ * t = a • (θ * (t - b • t₀)) + b • (a • (t₀ * θ)) := by
      simp only [Algebra.smul_def]; ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (hθP _ hb)) (Submodule.smul_mem _ _ ha)
  obtain ⟨u, p, hp, hup⟩ := hP.exists_inv haP
  apply hθ
  have : θ = algebraMap R K u * (a • θ) + p • θ := by
    rw [← Algebra.smul_def, smul_smul, ← add_smul, hup, one_smul]
  rw [this]
  exact add_mem (mul_mem ⟨u, rfl⟩ haθ) (hPθ p hp)

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  unfold Formalism.BasicNotions.Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)

theorem isFractional_Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : IsFractional (𝓞 D.host.E)⁰ (Iid D cc) := by
  obtain ⟨d, hd, hd'⟩ := D.host.AA0.isFractional
  refine (FractionalIdeal.isFractional_span_iff).2 ⟨d, hd, ?_⟩
  rintro _ ⟨c, -, a, ha, rfl⟩
  rw [← mul_smul_comm]
  refine IsLocalization.isInteger_mul ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩ (hd' a ha)

theorem Iid_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) : Iid D cc ≠ ⊥ := by
  obtain ⟨c, hcc, hc0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    inverseHalfDifferent_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hA
  refine (Submodule.ne_bot_iff _).2 ⟨_, Submodule.subset_span ⟨c, hcc, a, ha, rfl⟩, mul_ne_zero ?_ ha0⟩
  intro h
  apply hc0
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem exists_generator_Iid : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  intro D cc hc P hP
  exact exists_gen_and P hP ⟨Iid D cc, isFractional_Iid D cc⟩
    (fun h => Iid_ne_bot D cc hc (FractionalIdeal.coeToSubmodule_eq_bot.2 h))

end GlobalTheory.IdealGenerator
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TraceOne

theorem exists_of_sq (D : D7) (q n : ℕ) (hn : n % 4 = 3) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  have hm' : (n : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
  have hint : IsIntegral ℤ ((1 + b) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_natCast]
      linear_combination (1 / 4 : D.host.E) * hb - (1 / 4 : D.host.E) * hm'
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  have hcw : D.host.conj ((1 + b) / 2) = (1 - b) / 2 := by
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, hconj, sub_eq_add_neg]
  let w : 𝓞 D.host.E := ⟨(1 + b) / 2, hint⟩
  have hw : (w : D.host.E) = (1 + b) / 2 := rfl
  have hs : ((sgO D w : 𝓞 D.host.E) : D.host.E) = (1 - b) / 2 := by rw [sgO_coe, hw, hcw]
  refine ⟨w, ?_, fun P hP hq hmem => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_add (f := _), map_one]
    change (w : D.host.E) + ((sgO D w : 𝓞 D.host.E) : D.host.E) = 1
    rw [hw, hs]; ring
  · have hsq : (w - sgO D w) * -(w - sgO D w) = (n : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_neg, map_sub, map_natCast]
      change ((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) *
        -((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) = _
      rw [hw, hs]
      linear_combination (-1 : D.host.E) * hb
    have hnP : (n : 𝓞 D.host.E) ∈ P := hsq ▸ P.mul_mem_right _ hmem
    obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2
      (huv ▸ P.add_mem (P.mul_mem_left u hq) (P.mul_mem_left v hnP)))

theorem exists_trace_one : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  intro D q hq
  obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
  by_cases h : q = D.host.d
  · refine exists_of_sq D q D.host.q (by omega) ((Nat.coprime_primes hq hq₁).2 (by omega))
      (D.host.sqq) D.host.sqq_sq
  · exact exists_of_sq D q D.host.d (by omega) ((Nat.coprime_primes hq hd).2 h)
      (D.host.sqd) (D.host.sqd_sq)

end GlobalTheory.TraceOne
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaTranslateCoef

theorem sum_trivial_char_eq_zero {G ι : Type} [Monoid G] [Fintype ι] (κ : ι → (G →* ℂ)) (c : ι → ℂ)
    (h : ∀ y, ∑ i, c i * κ i y = 0) : ∑ i, (if κ i = 1 then c i else 0) = 0 := by
  have li := linearIndependent_monoidHom G ℂ
  rw [linearIndependent_iff] at li
  have h0 := li (∑ i, Finsupp.single (κ i) (c i)) (by

    rw [map_sum]
    funext y
    simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h y)
  have h1 := congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by congr

def kap (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (z : VC D N N') :
    Multiplicative A →* ℂ where
  toFun y := bc D T ((Multiplicative.toAdd y : A) : VC D N N') z / bc D T z ((Multiplicative.toAdd y : A) : VC D N N')
  map_one' := by
    simp only [toAdd_one, ZeroMemClass.coe_zero, bc_zero_left, bc_zero_right, div_one]
  map_mul' x y := by
    simp only [toAdd_mul, AddMemClass.coe_add, bc_add_left, bc_add_right, mul_div_mul_comm]

theorem kap_eq_one_iff {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (z : VC D N N') : kap D T A z = 1 ↔ z ∈ A := by
  constructor
  · intro hk
    refine h.2.2 z fun y hy => ?_
    have := DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))
    change bc D T y z / bc D T z y = 1 at this
    exact ((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm
  · intro hz
    refine MonoidHom.ext fun y => ?_
    change bc D T _ z / bc D T z _ = 1
    rw [h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]

theorem Wd_Wd_fixed (D : D7) (T : Tor D) {N N' : ℕ} (y z : VC D N N') (e : VC D N N' → ℂ)
    (he : Wd D T y e = e) : Wd D T y (Wd D T z e) = (bc D T y z / bc D T z y) • Wd D T z e := by
  have h1 := Wd_Wd D T z y e
  rw [he, add_comm] at h1
  rw [Wd_Wd]
  conv_rhs => rw [h1]
  rw [smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]

def WdL (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T y
  map_add' := Wd_add D T y
  map_smul' := Wd_smul D T y

theorem coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A →
    ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'),
      (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  intro D T N N' A hA e he hne ι _ a z hrel
  have hfix := ((hA.mem_ThSp e).1 he).2
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hsum : ∑ i, a i • Wd D T (z i) e = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel w
  have key := sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by
    intro y
    have h1 := congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum

    rw [map_sum, map_zero] at h1
    have h2 := congrFun h1 v
    rw [Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change _ = a i * Wd D T _ (Wd D T (z i) e) v
    rw [Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]
    change a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)
    ring)
  have h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0 := by
    refine Eq.trans ?_ key
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : z i ∈ A
    · rw [if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]
    · rw [if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]
  exact (mul_eq_zero.1 h3).resolve_right hv

end GlobalTheory.ThetaTranslateCoef
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.standard_weyl_lattices_fock_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (x : Pol K ι n), x ∈ VV K lam → ((∀ y ∈ delStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ nabStd K lam) ∧ ((∀ y ∈ nabStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ delStd K lam) := by
  first | exact @GlobalTheory.StdDual.std_dual | exact GlobalTheory.StdDual.std_dual | (intros; apply GlobalTheory.StdDual.std_dual <;> assumption)
end
