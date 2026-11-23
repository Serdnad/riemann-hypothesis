module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle163
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle158
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle157
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_levelFunctions_intermediateField : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧ ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  first | exact @GlobalTheory.KZ.LevelField.exists_level_field | exact GlobalTheory.KZ.LevelField.exists_level_field | (intros; apply GlobalTheory.KZ.LevelField.exists_level_field <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem atkinLehner_conj_int (N l : ℕ) (a b c d : ℤ) (h : (N : ℤ) * a * d - l * b * c = 1) (γ : M2)
    (hγ : ((N * l : ℕ) : ℤ) ∣ γ 1 0) (hdet : γ.det = 1) :
    ∃ γ' : M2, !![(N : ℤ) * a, b; N * l * c, N * d] * γ = γ' * !![(N : ℤ) * a, b; N * l * c, N * d] ∧
    γ'.det = 1 ∧ ((N * l : ℕ) : ℤ) ∣ γ' 1 0 ∧ (N : ℤ) ∣ γ' 1 1 - γ 0 0 := by
  obtain ⟨r, hr⟩ := hγ
  push_cast at hr
  set p := γ 0 0
  set q := γ 0 1
  set s := γ 1 1
  have hdet' : p * s - (N * l * r) * q = 1 := by
    rw [Matrix.det_fin_two] at hdet; rw [hr] at hdet; linarith
  refine ⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s,
     -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s;
     N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s),
     -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ?_, ?_, ?_, ?_⟩
  · have hγe : γ = !![p, q; N * l * r, s] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]
    rw [hγe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -(N * a * p + b * N * l * r) * h
    · linear_combination -(N * a * q + b * s) * h
    · linear_combination -(N * l * c * p + N * d * N * l * r) * h
    · linear_combination -(N * l * c * q + N * d * s) * h
  · rw [Matrix.det_fin_two_of]
    linear_combination ((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    exact Dvd.intro _ rfl
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact ⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩

theorem inv_slz_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ),
    N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f →
    Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  intro k N l χ f a b c d h hk hN hf
  set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ
  have hQdet : 0 < Q.det := by
    have : Q.det = N * (N * a * d - l * b * c) := by rw [hQ, Matrix.det_fin_two_of]; ring
    rw [this, h, mul_one]; exact_mod_cast hN
  have hiff := (slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)
  have hiff0 := (slz_props k f hk).2.2.1 (N * l) (ch χ)
  refine hiff.2 fun γ hγ => ?_
  have hγdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0 := by exact_mod_cast hγ
  obtain ⟨g, hg, hgdet, hgdvd, hgcong⟩ := atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet
  let γ₁ : SL(2, ℤ) := ⟨g, hgdet⟩
  have hf1 := hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)
  have hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f) := by
    rw [← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg,
      slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]
  rw [hcalc, hf1]
  have hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1) := by
    simp only [ch]
    have e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have : (N : ℤ) ∣ g 1 1 - γ 0 0 := hgcong
        rw [← dvd_neg, neg_sub]; exact this)
    have e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have hd := hγdet
      rw [Matrix.det_fin_two] at hd
      obtain ⟨r, hr⟩ := hγ'
      have : ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1 := by
        rw [hd]; simp
      rw [hr] at this
      push_cast at this
      simpa using this
    rw [e1, MulChar.inv_apply_eq_inv']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, e2, map_one]
  funext τ
  simp only [slz]
  rw [hchar]
  ring

end GlobalTheory.EisM
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.slashIntMatrixPosDet_properties : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  first | exact @GlobalTheory.EisM.slz_props | exact GlobalTheory.EisM.slz_props | (intros; apply GlobalTheory.EisM.slz_props <;> assumption)
end

section

open Filter Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem strip_exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 →
    (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) →
    ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ r t ψ ϖ hψ _ hϖ _ y hy
  have hy' := (GlobalTheory.CuspEntries.mem_unipRad_two_stdSum rfl y).1 hy

  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  have hball : {z : k | valuation k z < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨1, one_ne_zero, fun _ hz => hz⟩
  have P := (triv_ev_props k)
  have hev : ∀ i j : Fin (r + t), ∀ᶠ m : ℕ in atTop,
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    intro i j
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [hij, and_self, if_true]
      have hsm : IsSmoothChar (ψ i / ψ j) := by
        have h1 := hψ i
        have h2 := hψ j
        unfold IsSmoothChar at *
        have : (ψ i).ker ⊓ (ψ j).ker ≤ (ψ i / ψ j).ker := by
          intro u hu
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hu
          rw [MonoidHom.mem_ker, MonoidHom.div_apply, hu.1, hu.2, div_one]
        exact Subgroup.isOpen_mono this (by rw [Subgroup.coe_inf]; exact h1.inter h2)
      have hopen := (P.2.2.2.2.2.1 _ hsm).1
      have hT : {z : k | Triv (ψ i / ψ j) z} ∈ 𝓝 (0 : k) := hopen.mem_nhds (P.2.2.1 _)
      have ht : Tendsto (fun m : ℕ => ϖ ^ m * y.val i j) atTop (𝓝 0) := by
        simpa using hpow.mul_const (y.val i j)
      filter_upwards [ht (inter_mem hball hT)] with m hm
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hij, if_false]
      exact Eventually.of_forall fun _ => hy' i j hij
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin (r + t),
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact hev i
  obtain ⟨m, hm⟩ := hall.exists
  exact ⟨m, hm⟩

end GlobalTheory.PsType
end

section

open UpperHalfPlane Complex
open scoped Real

namespace GlobalTheory.EisM

private theorem norm_cexp_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-(2 * π * n * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : (2 * π * Complex.I * n * τ : ℂ) = ((2 * π * n : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem qs_bdd_above_one : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  intro b hb
  obtain ⟨hs, -⟩ := qs_summable_continuous b hb
  refine ⟨∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖, fun τ hτ => ?_⟩
  have hpt : ∀ n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_cexp_qterm, norm_cexp_qterm]
    gcongr
    simp only [UpperHalfPlane.I_im, mul_one]
    have h0 : (0 : ℝ) ≤ 2 * π * n := by positivity
    nlinarith
  calc ‖qs b τ‖ ≤ ∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ := by
        unfold qs; exact norm_tsum_le_tsum_norm (hs τ)
    _ ≤ _ := Summable.tsum_le_tsum hpt (hs τ) (hs _)

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.modularFormCoeffSeq_linear_structure : ∀ (k L : ℕ) (χ : ℤ → ℂ), (MF k L χ 0) ∧ (∀ a b, MF k L χ a → MF k L χ b → MF k L χ (a + b) ∧ qs (a + b) = qs a + qs b) ∧ (∀ (c : ℂ) a, MF k L χ a → MF k L χ (c • a) ∧ qs (c • a) = c • qs a) ∧ (∀ χ' a, (∀ d : ℤ, IsCoprime d L → χ d = χ' d) → MF k L χ a → MF k L χ' a) ∧ (∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a) ∧ (∀ L' a, L ∣ L' → CF k L χ a → CF k L' χ a) := by
  first | exact @GlobalTheory.EisM.mf_linear | exact GlobalTheory.EisM.mf_linear | (intros; apply GlobalTheory.EisM.mf_linear <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.qExpansion_polyGrowth_summable_continuous : ∀ a : ℕ → ℂ, PolyB a → (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  first | exact @GlobalTheory.EisM.qs_summable_continuous | exact GlobalTheory.EisM.qs_summable_continuous | (intros; apply GlobalTheory.EisM.qs_summable_continuous <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.tendsto_sum_Icc_periodic_mul_inv_floor_div : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) atTop (𝓝 0) := by
  first | exact @GlobalTheory.FloorTelescope.tendsto_sum_Icc_div | exact GlobalTheory.FloorTelescope.tendsto_sum_Icc_div | (intros; apply GlobalTheory.FloorTelescope.tendsto_sum_Icc_div <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.lipschitz_formula_periodic_weight : ∀ (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 2 ≤ j → 0 < L → 0 < z.im → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  first | exact @GlobalTheory.EisM.lipschitz_periodic | exact GlobalTheory.EisM.lipschitz_periodic | (intros; apply GlobalTheory.EisM.lipschitz_periodic <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul : ∀ (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ), (∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) → lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j * lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  first | exact @GlobalTheory.EisM.lat_smul | exact GlobalTheory.EisM.lat_smul | (intros; apply GlobalTheory.EisM.lat_smul <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  first | exact @GlobalTheory.EisM.eis_qseries | exact GlobalTheory.EisM.eis_qseries | (intros; apply GlobalTheory.EisM.eis_qseries <;> assumption)
end
