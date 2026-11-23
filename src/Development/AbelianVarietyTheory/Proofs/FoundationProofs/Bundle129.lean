module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle110
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle085
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.RootOfUnityEqOne

open IsLocalRing

theorem eq_one_of_pow_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ}
    (hm : V.valuation (m : F) = 1) {ζ : F} (hζ : ζ ^ m = 1)
    (h1 : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  apply GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt <;> assumption

theorem main : ∀ {F : Type} [inst : Field F] (V : ValuationSubring F) {m : ℕ},
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (↑m : F) = (1 : ValuationSubring.ValueGroup V) →
    ∀ {ζ : F}, ζ ^ m = (1 : F) →
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (ζ - (1 : F)) < (1 : ValuationSubring.ValueGroup V) →
    ζ = (1 : F) := by
  intro F _ V m hm ζ hζ h1
  exact eq_one_of_pow_eq_one V hm hζ h1

end GlobalTheory.RootOfUnityEqOne
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hasQ_periodic {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) (τ : ℍ) :
    f ((N : ℝ) +ᵥ τ) = f τ := by
  have h1 := hasQ_vadd N f a (N : ℝ) h
  have hc : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N)) = a := by
    funext n
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hc] at h1
  exact congrFun (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique.2 N _ _ a h1 h) τ

theorem hasQ_of_integral_quot : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N →
    (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 →
    (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) →
    ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  intro N n A D s hN ⟨a, hA⟩ ⟨d, hD⟩ hs hD0 heq
  choose c hc using hs
  obtain ⟨hAm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N A a hN hA
  obtain ⟨hDm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N D d hN hD
  have hsm : ∀ j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s j) ∧ UpperHalfPlane.IsBoundedAtImInfty (s j) :=
    fun j => GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N (s j) (c j) hN (hc j)
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, D τ ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hD0 (funext hc')
  have hofc : ∀ z : ℂ, 0 < z.im → ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  obtain ⟨h₀, hh₀d, hh₀A, hh₀p⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral {z : ℂ | 0 < z.im} n
    (A ∘ UpperHalfPlane.ofComplex) (D ∘ UpperHalfPlane.ofComplex)
    (fun j => s j ∘ UpperHalfPlane.ofComplex) hUo hUc (UpperHalfPlane.mdifferentiable_iff.1 hAm)
    (UpperHalfPlane.mdifferentiable_iff.1 hDm) (fun j => UpperHalfPlane.mdifferentiable_iff.1 (hsm j).1)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ₀⟩
    (fun z _ => heq _)
  set h : ℍ → ℂ := fun τ => h₀ τ with hdef
  have hAh : ∀ τ, A τ = h τ * D τ := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀A (τ : ℂ) τ.im_pos
  have hhp : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0 := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀p (τ : ℂ) τ.im_pos
  have hhm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    refine UpperHalfPlane.mdifferentiable_iff.2 (hh₀d.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, hofc z hz]
  have hhNm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => h ((N : ℝ) +ᵥ τ)) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => h₀ (((N : ℝ) : ℂ) + z)) {z : ℂ | 0 < z.im} :=
      hh₀d.comp ((differentiableOn_const _).add differentiableOn_id) fun z hz => by
        show 0 < (((N : ℝ) : ℂ) + z).im
        simpa using hz
    refine UpperHalfPlane.mdifferentiable_iff.2 (hd.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, UpperHalfPlane.coe_vadd, hofc z hz]
  have hper : ∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ := by
    have hz : ∀ τ, (fun τ => h ((N : ℝ) +ᵥ τ) - h τ) τ * D τ = 0 := fun τ => by
      have e1 := hAh ((N : ℝ) +ᵥ τ)
      rw [hasQ_periodic hN hA, hasQ_periodic hN hD, hAh τ] at e1
      simp only
      linear_combination -e1
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ D (hhNm.sub hhm) hDm hz with h0 | h0
    · exact fun τ => sub_eq_zero.1 (congrFun h0 τ)
    · exact absurd h0 hD0
  have hbd : UpperHalfPlane.IsBoundedAtImInfty h := by
    have hS : (fun τ => ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (fun τ => ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := fun j _ => by
        have : (s j) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := (hsm j).2
        exact this.norm_left
      exact (Asymptotics.IsBigO.sum hb).congr_left fun τ => Finset.sum_apply _ _ _
    have h1 : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) :=
      ((Asymptotics.isBigO_refl (1 : ℍ → ℝ) _).add hS).congr_left fun τ => rfl
    have h2 : h =O[UpperHalfPlane.atImInfty] (fun τ => 1 + ∑ j, ‖s j τ‖) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
      have hb := GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hhp τ)
      have hnn : (0 : ℝ) ≤ 1 + ∑ j, ‖s j τ‖ := by positivity
      rw [Real.norm_of_nonneg hnn, one_mul]
      exact hb
    exact h2.trans h1
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hhm hper hbd
  exact ⟨h, b, hb, hAh⟩

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_qConj_level_one_invariant : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) → ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  first | exact @GlobalTheory.FN.exists_conj_level_one | exact GlobalTheory.FN.exists_conj_level_one | (intros; apply GlobalTheory.FN.exists_conj_level_one <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  first | exact @GlobalTheory.FN.laurent_iff | exact GlobalTheory.FN.laurent_iff | (intros; apply GlobalTheory.FN.laurent_iff <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  first | exact @GlobalTheory.KZ.H3.lev_fd | exact GlobalTheory.KZ.H3.lev_fd | (intros; apply GlobalTheory.KZ.H3.lev_fd <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HeckeEqv

theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  simp [toGL, hA, hB, hAB, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  ext i j
  simp [toGL, h, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.SpecialLinearGroup.mapGL]

theorem toGL_smul_mat (γ : SL(2, ℤ)) (τ : ℍ) : toGL (mat γ) • τ = γ • τ := by
  rw [toGL_mat]; rfl

theorem mem_of_natDegree_le {w : ℕ} {p : ℂ[X]} (h : p.natDegree ≤ w) : p ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => mem_of_natDegree_le ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  refine Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_pow_le (p := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) (n := i)).trans
    (Nat.mul_le_mul_left i (natDegree_linear_le))
  have h2 := (natDegree_pow_le (p := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) (n := w - i)).trans
    (Nat.mul_le_mul_left (w - i) (natDegree_linear_le))
  omega

theorem hecke_eqv (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk2 : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (hδ : ∀ i, 0 < (δ i).det)
    (hπ : ∀ γ : Γ, ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) :
    per Γ (k - 2) (hkF (k : ℤ) δ ⇑f) - hk Γ (k - 2) δ (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2) := by
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑f := f.holo'
  have hdet : ∀ i, (δ i).det ≠ 0 := fun i => (hδ i).ne'
  have hpc := (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 f).2
  set w := k - 2 with hw
  set F := eichler w ⇑f with hF
  set c : ι → ℂ[X] := fun i => slP w (δ i) (F (toGL (δ i) • UpperHalfPlane.I)) with hc
  set C := ∑ i, c i with hCdef
  have hC : -C ∈ degreeLT ℂ (w + 1) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => polySlash_mem _ _ _)
  refine ⟨⟨-C, hC⟩, ?_⟩
  funext γ
  have hγdet : (mat (γ : SL(2, ℤ))).det ≠ 0 := by simp [mat]
  obtain ⟨hex⟩ : Nonempty (∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) := ⟨hπ γ⟩
  have e2 : hk Γ w δ (per Γ w ⇑f) γ =
      ∑ i, slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) := by
    simp only [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  have e1 : per Γ w (hkF (k : ℤ) δ ⇑f) γ =
      ∑ i, (slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) - slP w (mat γ) (c i)) := by
    simp only [per, hkF]

    rw [GlobalTheory.T.eichlerIntegralFromI_finset_sum w _ (fun i => hfd.slash _ _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash k hk2 ⇑f hfd (δ i) (hδ i) ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
    rw [eq_sub_of_add_eq h.symm, map_sub, GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (δ i) (mat γ) _ (eichler_mem _ _ _),
      toGL_mul _ _ (hdet i) hγdet, mul_smul, toGL_smul_mat]
  have e3 : ∀ i, slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) =
      slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) + c (hex.choose i) := by
    intro i
    set γ' := (hex.choose_spec i).choose
    have hγ' : δ i * mat γ = mat γ' * δ (hex.choose i) := (hex.choose_spec i).choose_spec
    have hγ'det : (mat (γ' : SL(2, ℤ))).det ≠ 0 := by simp [mat]
    rw [hγ', toGL_mul _ _ hγ'det (hdet _), mul_smul, toGL_smul_mat,
      GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (mat γ') (δ (hex.choose i)) _ (eichler_mem _ _ _),
      hpc γ' (toGL (δ (hex.choose i)) • UpperHalfPlane.I), map_sub]
    simp only [hc]
    abel
  have hsum : ∑ i, c (hex.choose i) = C := Equiv.sum_comp hex.choose c
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply]
  rw [e1, e2]

  simp only [e3, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← map_sum, map_neg]
  abel

theorem tqFam_det (q : ℕ) (hq : q.Prime) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : 0 < (tqFam q σ i).det := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  unfold tqFam
  split_ifs
  · simpa [Matrix.det_fin_two_of] using hq0
  · simpa [Matrix.det_mul, mat, dg, Matrix.det_fin_two_of] using hq0

theorem ulFam_det (l : ℕ) (hl : l.Prime) (i : Fin l) : 0 < (ulFam l i).det := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl.pos
  simpa [ulFam, Matrix.det_fin_two_of] using hl0

theorem period_map_equivariant : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ f : ModularForm (Lev N l) (k : ℤ),
  (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
    per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) ∧
  per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2) ∧
  (∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    per (Lev N l) (k - 2) (DdF (k : ℤ) σ ⇑f) - DdZ (Lev N l) (k - 2) σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) := by
  intro N l k hN hl hlN hk f
  refine ⟨fun q σ hq hqN hσ => ?_, ?_, fun d σ hσ => ?_⟩
  · exact hecke_eqv _ k (by omega) f (tqFam q σ) (tqFam_det q hq σ)
      (GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets N l q hN hl hlN hq hqN σ hσ)
  · exact hecke_eqv _ k (by omega) f (ulFam l) (ulFam_det l hl) (GlobalTheory.T.heckeUlRepresentatives_right_mul_perm N l hN hl hlN)
  · exact hecke_eqv _ k (by omega) f (fun _ : Unit => mat σ) (fun _ => by simp [mat])
      (fun γ => ⟨Equiv.refl _, fun _ => GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel N l d σ hσ γ⟩)

end GlobalTheory.HeckeFamilyMatrices.HeckeEqv
end
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem approxRoot_fix_of_almostSep : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  intro L _ v p hp hp0 hp1 G _ _ hinv N hN hsep hroot
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨θ, hθ1, hθ⟩ := hroot
  set θ₀ : ℝ≥0 := max θ (v (p : L)) with hθ₀
  have hθ₀1 : θ₀ < 1 := max_lt hθ1 hp1
  obtain ⟨s, hs0, hs1⟩ := exists_between hθ₀1
  set r : ℝ≥0 := s ^ (((p + 1 : ℕ) : ℝ)⁻¹) with hr
  have hrpow : r ^ (p + 1) = s := NNReal.rpow_inv_natCast_pow s (by omega)
  have hr1 : r < 1 := NNReal.rpow_lt_one hs1 (by positivity)
  have hrs : θ₀ < r ^ (p + 1) := hrpow ▸ hs0
  have hrpos : 0 < r ^ (p + 1) := lt_of_le_of_lt bot_le hrs
  obtain ⟨n, a, b, c, hc, hrc⟩ := hsep r hr1
  refine ⟨θ₀ / r ^ (p + 1), (div_lt_one hrpos).2 hrs, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · refine ⟨0, zero_mem _, ?_⟩
    simp [hx0, hp.ne_zero]
  obtain ⟨d, hdF, hd0, hdr, hd1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp _ ⟨θ, hθ1, hθ⟩ hp0 hp1 r hr1 x hx0
  have hdN : d ∈ Fix L N := fun σ => hdF ⟨σ.1, Subgroup.mem_top _⟩
  have hx'N : x * d ^ p ∈ Fix L N := mul_mem hx (pow_mem hdN p)
  obtain ⟨w, hwN, hw⟩ :=
    GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily L v p hp G hinv N θ hθ1.le hθ n a b c hc (x * d ^ p) hx'N hd1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hrc
    exact (not_lt.2 (bot_le : (⊥ : ℝ≥0) ≤ r)) hrc
  refine ⟨w / (c * d), div_mem hwN (mul_mem hc.c_mem hdN), ?_⟩
  have key : x - (w / (c * d)) ^ p = (c ^ p * (x * d ^ p) - w ^ p) / (c ^ p * d ^ p) := by
    have hD0 : c ^ p * d ^ p ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
    rw [eq_div_iff hD0, div_pow, mul_pow, sub_mul, div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0))]
    ring
  have hD : 0 < v (c ^ p * d ^ p) := by
    rw [Valuation.pos_iff]
    exact mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
  rw [key, map_div₀, div_le_iff₀ hD]
  have hvx : v (x * d ^ p) = v x * v d ^ p := by rw [map_mul, map_pow]
  have hbig : r ^ (p + 1) ≤ v c ^ p * (v x * v d ^ p) := by
    rw [pow_succ, ← hvx]
    exact mul_le_mul' (pow_le_pow_left₀ bot_le hrc.le p) hdr.le
  calc v (c ^ p * (x * d ^ p) - w ^ p) ≤ θ₀ := hw
    _ = θ₀ / r ^ (p + 1) * r ^ (p + 1) := (div_mul_cancel₀ _ hrpos.ne').symm
    _ ≤ θ₀ / r ^ (p + 1) * (v c ^ p * (v x * v d ^ p)) := by gcongr
    _ = θ₀ / r ^ (p + 1) * v x * v (c ^ p * d ^ p) := by
      rw [map_mul, map_pow, map_pow]; ring

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  first | exact @GlobalTheory.PsType.theta_emb₂_std | exact GlobalTheory.PsType.theta_emb₂_std | (intros; apply GlobalTheory.PsType.theta_emb₂_std <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem not_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  intro k _ _ _ _ n ψ hord y hy hny
  classical

  have hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b) := by
    by_contra h
    push_neg at h
    exact hny ⟨hy, fun i j hij => h i j hij⟩
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, h⟩ := hbad
    exact ⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩
  set a := S.min' hS with ha_def
  have haS : a ∈ S := S.min'_mem hS
  have hamin : ∀ i ∈ S, a ≤ i := fun i hi => S.min'_le i hi
  let T : Finset (Fin n) := Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hT : T.Nonempty := by
    have := haS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by simp [T]; exact hb⟩
  set b := T.max' hT with hb_def
  have hbT : b ∈ T := T.max'_mem hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT
  obtain ⟨hab, hbad_ab⟩ := hbT
  have hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j) := by
    intro j hj
    by_contra hc
    have : j ∈ T := by simp [T]; exact ⟨lt_trans hab hj, hc⟩
    exact absurd (T.le_max' j this) (not_le.mpr hj)
  obtain ⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩ :=
    GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence k n ψ hord y hy a b hab hbad_ab hbmax
  have hprops := GlobalTheory.PsType.triv_ev_props k
  refine ⟨j, hj, ⟨hKO, ?_⟩, ?_⟩
  · intro i i' hii'
    rw [hval]
    by_cases hi' : i' = a
    · subst hi'
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one,
        if_neg (ne_of_lt hii'), zero_add]

      have hiS : i ∉ S := fun h => absurd (hamin i h) (not_le.mpr hii')
      have hib : Triv (ψ i / ψ b) (y.val i b) := by
        by_contra hc
        exact hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)
      have h2 : Triv (ψ i / ψ a) (y.val i b) := hord i i a b le_rfl hii'.le hab.le _ hib
      refine hprops.1 _ _ _ ?_ h2
      rw [map_mul]
      first
        | exact mul_le_of_le_one_left' hs
        | exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)
        | exact mul_le_of_le_one_left (zero_le _) hs
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero,
        if_neg (ne_of_lt hii'), add_zero]
      exact hprops.2.2.1 _
  · have hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ) := by
      refine GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_
      intro i
      by_cases hi : i = a
      · subst hi; simp [hsu]
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [hθj, hθ]
    intro h
    exact hne (Units.ext h).symm

end GlobalTheory.PsType
end
end
