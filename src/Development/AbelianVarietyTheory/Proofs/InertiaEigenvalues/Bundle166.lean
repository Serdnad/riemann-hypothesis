module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
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
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LiftExp

variable {l : ℕ} [hl : Fact l.Prime]

theorem one_add_pow_expand (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring

theorem norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt

theorem zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h

theorem norm_pow_sub_one_of (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)

theorem norm_pow_coprime (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this

theorem norm_pow_prime (j : ℕ) (hj : Lev l j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ l - 1‖ = (l : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
  have hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ)) := by simp
  have hj1 := hj.1
  push_cast
  by_cases h2 : l = 2
  · have := hj.2 h2
    exact norm_pow_sub_one_of j hj.1 u hu l 1 0 hn
      (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      (by omega) (by omega)
  · have h3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
    obtain ⟨m, hm⟩ := hl.out.dvd_choose_self (k := 2) two_ne_zero h3
    refine norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)
    rw [hm, Nat.cast_mul, norm_mul, hn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih

theorem norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hl.out.ne_zero) hm0,
    Nat.multiplicity_prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp

theorem norm_zpow_sub_one : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← Nat.padicValNat_def, ← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp

end GlobalTheory.Cyc.LiftExp
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unimodular_hermitian_matrix_congruent_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 → ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  first | exact @GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | exact GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | (intros; apply GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitary_action_hermitian_invariants_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by
  first | exact @GlobalTheory.JR.HermInv.herm_invariants | exact GlobalTheory.JR.HermInv.herm_invariants | (intros; apply GlobalTheory.JR.HermInv.herm_invariants <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedStandardAddChar_conductor_properties : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ → IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  first | exact @GlobalTheory.StdChar.psi_conductor | exact GlobalTheory.StdChar.psi_conductor | (intros; apply GlobalTheory.StdChar.psi_conductor <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unimod

open GlobalTheory.UnitLemma Polynomial

theorem eta_gramDet_eq_one : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty →
    K.eta (B.gramDet x) = 1 := by
  intro K B x hx ⟨L, hlat, _, hsd⟩
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.self_dual_hermitian_lattice_basis_exists K B.A (B.herm x)
    (fun y y' z => by unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)])
    (fun e y z => Basic.herm_smul_left B x y z e)
    (fun y z => Basic.herm_symm B x hx y z) L hlat.1 hlat.2 hsd
  rw [← Orbit.eta_gram B x b]
  have h1 : (Matrix.of fun i j => B.herm x (b i) (b j)) = 1 := by
    ext i j; simp [hb, Matrix.one_apply]
  rw [h1, Matrix.det_one]
  simp [UQ.eta, val]

end GlobalTheory.UnitLemma.Unimod
end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_finset_cosets_integral_norm_units : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) → ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  first | exact @GlobalTheory.NormUnits.exists_finset_normUnits | exact GlobalTheory.NormUnits.exists_finset_normUnits | (intros; apply GlobalTheory.NormUnits.exists_finset_normUnits <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  first | exact @GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | exact GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | (intros; apply GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SesqAsym

theorem trace_σ {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a
  rw [h, RingEquiv.apply_symm_apply]

theorem sesq_asym : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → (∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g)) ∧ ∀ (s : B.A → B.A → K.E), (∀ x y z, s (x + y) z = s x z + s y z) → (∀ (c : K.E) x z, s (c • x) z = c * s x z) → (∀ y, (∀ z, s y z = 0) → y = 0) → (∀ y z, K.c (s z y) = s (ε * B.g * y) z) → ∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g) ∧ ∀ y z, s y z = B.herm β y z := by
  intro K B hg hP ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  set u := ε * B.g with hu_def
  have hu : u * B.σ u = 1 := by
    rw [hu_def, map_mul, hσε]
    calc ε * B.g * (ε * B.σ B.g) = (ε * ε) * (B.g * B.σ B.g) := by ring
      _ = 1 := by rw [hεε, hg, one_mul]
  refine ⟨GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg K B u hu, ?_⟩
  intro s hadd hlin hnd hsym
  have hvu : B.σ u * u = 1 := by rw [mul_comm]; exact hu

  have hsym' : ∀ y z, s y z = K.c (s z (B.σ u * y)) := by
    intro y z
    rw [hsym, ← mul_assoc, hu, one_mul]
  have hadd2 : ∀ y z z', s y (z + z') = s y z + s y z' := by
    intro y z z'
    rw [hsym', hadd, map_add (f := _), ← hsym', ← hsym']
  have hlin2 : ∀ (e : K.E) y z, s y (e • z) = K.c e * s y z := by
    intro e y z
    rw [hsym', hlin, map_mul, ← hsym']
  have hsu : ∀ y z, s (u * y) (u * z) = s y z := by
    intro y z
    rw [← hsym, ← hsym, K.c_c]
  have hneg1 : ∀ y z, s (-y) z = - s y z := by
    intro y z
    have := hlin (-1) y z
    simpa using this
  have hneg2 : ∀ y z, s y (-z) = - s y z := by
    intro y z
    have := hlin2 (-1) y z
    simpa using this
  have hsg : ∀ y z, s (B.g * y) (B.g * z) = s y z := by
    intro y z
    rcases hε with rfl | rfl
    · simpa [hu_def] using hsu y z
    · have := hsu y z
      simp only [hu_def, neg_mul, one_mul] at this
      rw [hneg1, hneg2, neg_neg] at this
      exact this
  have hadj_g : ∀ y z, s (B.g * y) z = s y (B.σ B.g * z) := by
    intro y z
    conv_lhs => rw [show z = B.g * (B.σ B.g * z) by rw [← mul_assoc, hg, one_mul]]
    exact hsg _ _
  have hadj : ∀ a y z, s (a * y) z = s y (B.σ a * z) := by
    intro a
    obtain ⟨f, rfl⟩ := GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP a
    induction f using Polynomial.induction_on with
    | C e =>
      intro y z
      rw [aeval_C, ← Algebra.smul_def, B.σ_alg, ← Algebra.smul_def, hlin, hlin2, K.c_c]
    | add p q hp hq =>
      intro y z
      rw [map_add (f := _), add_mul, hadd, hp, hq, map_add (f := _), add_mul, hadd2]
    | monomial n e ih =>
      intro y z
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, ih, hadj_g]
      congr 1
      rw [map_mul B.σ _ B.g]
      ring

  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun y => s y 1
      map_add' := fun x y => hadd x y 1
      map_smul' := fun c x => hlin c x 1 }
  let φ : B.A →ₗ[K.E] Module.Dual K.E B.A := Algebra.traceForm K.E B.A
  have hφi : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) w fun y => ?_
    have := LinearMap.congr_fun hw y
    simpa [φ, Algebra.traceForm_apply] using this
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hφi
  obtain ⟨β, hβ⟩ := hφs ℓ
  have hβs : ∀ y, s y 1 = Algebra.trace K.E B.A (β * y) := by
    intro y
    have := LinearMap.congr_fun hβ y
    simpa [φ, ℓ, Algebra.traceForm_apply] using this.symm
  have hform : ∀ y z, s y z = B.herm β y z := by
    intro y z
    have h1 := hadj (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hβs]
    unfold InvAlg.herm
    congr 1; ring

  have hβinj : Function.Injective (LinearMap.mulLeft K.E β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : β * y = 0 := hy
    refine hnd y fun z => ?_
    rw [hform]
    unfold InvAlg.herm
    rw [hy', zero_mul, map_zero]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hβinj) 1
  have hxβ : β * x = 1 := hx
  refine ⟨⟨β, x, hxβ, by rw [mul_comm]; exact hxβ⟩, ?_, hform⟩
  show B.σ β = β * u
  rw [← sub_eq_zero]
  refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_
  have h3 : Algebra.trace K.E B.A (B.σ β * y) = Algebra.trace K.E B.A (β * u * y) := by
    have h2 := hsym y 1
    rw [hform, hform] at h2
    unfold InvAlg.herm at h2
    rw [← trace_σ] at h2
    simp only [map_mul B.σ, map_one, B.σ_σ, mul_one] at h2
    rw [h2]; congr 1; ring
  rw [sub_mul, map_sub, h3, sub_self]

end GlobalTheory.SesqAsym
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

theorem _root_.GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | exact GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | (intros; apply GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | exact GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | (intros; apply GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g → ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u → algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  first | exact @GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | exact GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | (intros; apply GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin <;> assumption)
end

section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.weightedOrbitSum_congr_coefficientRing : ∀ {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A] (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A)), (∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) → (∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L') → intUnits O A ⊓ G = intUnits O' A ⊓ G → orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  first | exact @GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | exact GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | (intros; apply GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe <;> assumption)
end
