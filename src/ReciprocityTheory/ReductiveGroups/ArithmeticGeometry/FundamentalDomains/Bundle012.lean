module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem pointNorm_eq_norm_mul (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    X.pnorm la G z = ‖G z‖ * X.pnorm la (fun _ => (1 : ℂ)) z := by
  simp only [Data.pnorm, norm_one, one_mul]

theorem pointNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.pnorm la G z := by
  unfold Data.pnorm
  refine mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem hatNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.hatN la G z := by
  unfold Data.hatN
  refine Real.sSup_nonneg fun t ht => ?_
  obtain ⟨x', -, -, rfl⟩ := ht
  exact X.pointNorm_nonneg la G x'

end Data

theorem epsilonZero_spec {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 ∧
    ∀ ε, 0 < ε → ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w →
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * ((4 * fdeg E : ℕ) : ℝ)) +
        ((4 * fdeg E : ℕ) : ℝ) + 2 <
        (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) := by
  have hf1 : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  have hd0 : 0 < dE E := field_discr_constant_pos
  have hg0 : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC0 : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  generalize hK : (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) = K2
  have hK1 : 1 ≤ K2 := by
    rw [← hK]
    have : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by positivity
    linarith
  have hN : ((4 * fdeg E : ℕ) : ℝ) = 4 * (fdeg E : ℝ) := by push_cast; ring
  generalize hR : w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * K2 * ((4 * fdeg E : ℕ) : ℝ)) +
      ((4 * fdeg E : ℕ) : ℝ) + 2 = R2
  have hR0 : 0 < R2 := by
    rw [← hR, hN]
    have : 0 ≤ 4 * (fdeg E : ℝ) * Real.log (2 * K2 * (4 * (fdeg E : ℝ))) :=
      mul_nonneg (by linarith) (Real.log_nonneg (by nlinarith))
    linarith
  generalize hB : (X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 = B
  have hB0 : 0 < B := by rw [← hB]; positivity
  have heq : flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w = min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) := by
    rw [← hB, ← hR, ← hK, hN]
    simp only [flowEpsilonBound]
    rw [← rootDiscriminant_eq_rpow]
  rw [heq]
  refine ⟨lt_min one_pos (div_pos (by positivity) (mul_pos hB0 hR0)), min_le_left _ _, fun ε hε hεlt => ?_⟩
  have hle : min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) ≤ (fdeg E : ℝ) ^ 2 / (B * R2) := min_le_right _ _
  have h1 := (le_div_iff₀ (mul_pos hB0 hR0)).1 (le_of_lt (lt_of_lt_of_le hεlt hle))
  rw [lt_div_iff₀ (mul_pos hB0 hε)]
  have hε' : ε * (B * R2) < (fdeg E : ℝ) ^ 2 := by
    have h2 := (lt_div_iff₀ (mul_pos hB0 hR0)).1 (lt_of_lt_of_le hεlt hle)
    exact h2
  calc R2 * (B * ε) = ε * (B * R2) := by ring
    _ < (fdeg E : ℝ) ^ 2 := hε'


theorem unipotent_vector_eq_smul_component {r : ℕ} (X : DataX E r) (z0 : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) (K : ℂ)
    (a : X.Ψ → Fin 2 → ℂ) (ha : a τ = ![-(K * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K / (X.NC : ℂ)]) :
    X.uvec ![ξ, (X.NC : E) • x] a τ = K • X.ucomp z0 ξ (X.embV x) τ := by
  have hNCc : (X.NC : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  rw [X.toData.orthogonal_component_apply]
  funext j
  simp only [Data.uvec, ha, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Data.emb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_natCast]
  generalize X.Hf z0 τ (fun a => τ.1 (x a)) (fun a => τ.1 (ξ a)) /
    X.Hf z0 τ (fun a => τ.1 (ξ a)) (fun a => τ.1 (ξ a)) = q
  field_simp
  ring


theorem short_vector_setting_exists {r : ℕ} (X : DataX E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {ξ : Fin r → E}
    {ν : X.Ψ → ℝ} {c1 w : ℝ} {z0 : Frame X.Ψ r} (hH : ShortVectorHypotheses X la P ξ ν c1 w z0) {x : Fin r → E}
    (hxL : x ∈ X.L') (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    ∃ a, IsotropicFlowSetting X la P ξ ν c1 w z0 x a := by
  have hξ0 : ξ ≠ 0 := hH.2.2.1.2.2
  have hune : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0 := X.toData.orthogonal_component_ne_zero z0 hξ0 hxE
  obtain ⟨K, hK⟩ : ∃ K : X.Ψ → ℂ, ∀ τ,
      K τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨fun τ => ![-(K τ * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K τ / (X.NC : ℂ)],
    hH, hxL, hxξ, hxx, hxE, hune, fun τ => ?_⟩
  rw [← hK τ]
  exact unipotent_vector_eq_smul_component X z0 ξ x τ (K τ) _ rfl

theorem isotropic_pair_in_lattice {r : ℕ} (X : DataX E r) {ξ x : Fin r → E} (hiso : X.IsIso ξ) (hxL : x ∈ X.L')
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] ∧ ∀ i, ![ξ, (X.NC : E) • x] i ∈ X.Λ := by
  have hξ0 : ξ ≠ 0 := hiso.2.2
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ, HermitianTraceFormVanishing.cc_zero]
  refine ⟨⟨fun i k => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases k <;>
      simp [hiso.2.1, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hxξ, hξx, hxx]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNCE : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
      have htN : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNCE
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]; exact eq_neg_of_add_eq_zero_right hst
      apply hxE (-(s / (t * (X.NC : E))))
      calc x = (t * (X.NC : E))⁻¹ • ((t * (X.NC : E)) • x) := by
            rw [smul_smul, inv_mul_cancel₀ htN, one_smul]
        _ = -(s / (t * (X.NC : E))) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · fin_cases i
    · exact hiso.1
    · exact X.NC_sub x hxL

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem cc_kappa0 : cc X.κ0 = -X.κ0 := by
  have hx : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  rcases X.κ0_xi with h | h <;> rw [h] <;> simp only [cc, map_mul, map_neg, map_ofNat, hx] <;> ring

theorem tau_kappa0 (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by
  have hcc := congrArg τ.1 X.cc_kappa0
  have hconj : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
    rw [← map_neg, ← hcc]
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ.1 X.κ0).symm
  have hre : (τ.1 X.κ0).re = 0 := by
    have h := congrArg Complex.re hconj
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have him := X.κ0_sign τ
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    simp only [Data.c]
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [map_mul, map_neg, norm_mul, map_ofNat]
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have habs : ‖τ.1 X.κ0‖ = -(τ.1 X.κ0).im := by
    conv_lhs => rw [hz]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg him]
  apply Complex.ext
  · simp [hre]
  · simp
    linarith

noncomputable def Mmat (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)

theorem Mmat_map (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (τ : X.Ψ) :
    (X.Mmat u β).map τ.1 = X.zmat u (X.embH β) τ := by
  ext a j
  by_cases h : a = j <;>

    simp [h, Matrix.map_apply, Data.Mmat, Data.zmat, Data.embH, Data.emb, map_add (f := _), map_mul, map_sum,
    X.tau_kappa0 τ, cc, NumberField.IsCMField.complexEmbedding_complexConj] <;> ring

theorem Mmat_zero (u : Fin 2 → Fin r → E) : X.Mmat u 0 = 1 := by
  ext a j
  simp [Data.Mmat, Matrix.one_apply]

private lemma Mmat_mulVec_eq_add_sum (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_add_right_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, Pi.add_apply, cc, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem Mmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin 2) (Fin 2) E) : X.Mmat u β * X.Mmat u β' = X.Mmat u (β + β') := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains,
    herm_smul_left_fundamental_domains, Fin.sum_univ_two, hu, mul_zero, add_zero, Matrix.add_apply]
  first
    | module
    | (simp only [add_mul, mul_add, add_smul]; abel)

noncomputable def gam (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) : GL (Fin r) E :=
  ⟨X.Mmat u β, X.Mmat u (-β), by rw [X.Mmat_mul u hu, add_neg_cancel, Mmat_zero],
    by rw [X.Mmat_mul u hu, neg_add_cancel, Mmat_zero]⟩

private lemma cc_herm_Gm_eq_herm_swap (x y : Fin r → E) : cc (herm X.Gm x y) = herm X.Gm y x := by

  simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  first
    | (have hg := X.Gm_herm b a
       simp only [cc] at hg
       rw [hg]
       ring)
    | (have hg := X.Gm_herm a b
       simp only [cc] at hg
       rw [hg]
       ring)

theorem herm_Mmat (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (X.Mmat u β *ᵥ v) (X.Mmat u β *ᵥ w) = herm X.Gm v w := by
  have hk : IsCMField.complexConj E X.κ0 = -X.κ0 := X.cc_kappa0
  have hb' : ∀ i k, IsCMField.complexConj E (β i k) = β k i := hβ
  have hh : ∀ x y, IsCMField.complexConj E (herm X.Gm x y) = herm X.Gm y x := cc_herm_Gm_eq_herm_swap X
  simp only [Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains', herm_smul_left_fundamental_domains,
    herm_smul_right_eq_cc_mul', Fin.sum_univ_two, hu, mul_zero, add_zero, zero_add, cc, map_mul, map_add,
    hk, hb', hh]
  ring

theorem Mmat_mulVec (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_minor {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) :
    ∃ a b : Fin r, u 0 a * u 1 b - u 0 b * u 1 a ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu0 : u 0 ≠ 0 := hu.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a, u 0 a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (funext h)
  have key := Fintype.linearIndependent_iff.1 hu ![u 1 a, -(u 0 a)] (by
    funext b
    have hb := hcon a b
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply]
    linear_combination -hb)
  exact ha (by simpa using key 1)

lemma emb_li {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) (τ : E →+* ℂ) (c : Fin 2 → ℂ)
    (hc : ∑ i, c i • Data.emb τ (u i) = 0) : c = 0 := by
  obtain ⟨a, b, hab⟩ := exists_minor hu
  have hd : τ (u 0 a * u 1 b - u 0 b * u 1 a) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact hab
  simp only [map_sub, map_mul] at hd
  have ea := congrFun hc a
  have eb := congrFun hc b
  simp only [Finset.sum_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Data.emb,
    Pi.zero_apply] at ea eb
  have h0 : c 0 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 1 b) * ea - τ (u 1 a) * eb
  have h1 : c 1 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 0 a) * eb - τ (u 0 b) * ea
  have h0' := (mul_eq_zero.1 h0).resolve_right hd
  have h1' := (mul_eq_zero.1 h1).resolve_right hd
  funext i
  fin_cases i
  · simpa using h0'
  · simpa using h1'

variable (X : Data E r)

lemma uvec_ne {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) {a : X.Ψ → Fin 2 → ℂ} {τ : X.Ψ}
    (ha : a τ ≠ 0) : X.uvec u a τ ≠ 0 := fun h0 => ha (emb_li hu τ.1 (a τ) h0)

lemma hermC_uvec {u : Fin 2 → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (a b : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) = 0 := by
  have key : hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) =
      ∑ i, ∑ k, a τ i * conj (b τ k) * τ.1 (herm X.Gm (u i) (u k)) := by

    simp only [hermC, herm, Data.uvec, Data.emb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, emb_cc, Fin.sum_univ_two, map_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  simp [hu]

lemma isIsoV_uvec {u : Fin 2 → Fin r → E} (hu : IsIsoPair X.Gm u) {a : X.Ψ → Fin 2 → ℂ}
    (ha : ∀ τ, a τ ≠ 0) : X.IsIsoV (X.uvec u a) := fun τ => ⟨hermC_uvec X hu.1 a a τ, uvec_ne X hu.2 (ha τ)⟩

lemma herm_rank1 (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    IsHermFam (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) := by
  intro τ i k
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma pairR_rank1 (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) = ∑ τ, s τ * (X.chiAt χ a τ).re := by
  unfold Data.pairR Data.chiAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma posSemidef_of {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) (τ0 : X.Ψ)
    (h : ∀ x : Fin 2 → ℂ, x ≠ 0 → 0 ≤ (∑ i, ∑ k, χ τ0 i k * conj (x i) * x k).re) :
    (Matrix.of (χ τ0)).PosSemidef := by
  have hH : (Matrix.of (χ τ0)).IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hχ τ0 k i]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have hre : (star x ⬝ᵥ (Matrix.of (χ τ0)).mulVec x) =
      ∑ i, ∑ k, χ τ0 i k * conj (x i) * x k := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [hre, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · exact h x hx
  · rw [← hre]
    exact him.symm

lemma chiAt_embH (β : Matrix (Fin 2) (Fin 2) E) (c : Fin 2 → E) (τ : X.Ψ) :
    X.chiAt (X.embH β) (fun σ i => σ.1 (c i)) τ = τ.1 (∑ i, ∑ k, β i k * c i * cc (c k)) := by

  simp only [Data.chiAt, Data.embH, map_sum, map_mul, emb_cc]

lemma herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  intro τ i k
  simp only [Data.embH]
  rw [← hβ i k, emb_cc]

lemma herm_comb {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, IsHermFam (ω j))
    (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k

  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

end

end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
end
