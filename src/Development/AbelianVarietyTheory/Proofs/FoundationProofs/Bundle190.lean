module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle182
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle181
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle180
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_expansion_converges : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), Den (T.exp f) ∧ ∃ (φ : ℂ → ℂ) (C : ℝ), T.an f = (φ : Mero) ∧ HS ε C φ (T.exp f) := by
  first | exact @GlobalTheory.FN.frac_exp_converges | exact GlobalTheory.FN.frac_exp_converges | (intros; apply GlobalTheory.FN.frac_exp_converges <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_indep_reps : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  first | exact @GlobalTheory.EisM.RepInd.hsum_indep | exact GlobalTheory.EisM.RepInd.hsum_indep | (intros; apply GlobalTheory.EisM.RepInd.hsum_indep <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  first | exact @GlobalTheory.EisM.lat_eq_tsum_of_kills | exact GlobalTheory.EisM.lat_eq_tsum_of_kills | (intros; apply GlobalTheory.EisM.lat_eq_tsum_of_kills <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem toGL_entry (A : M2) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(GlobalTheory.HeckeFamilyMatrices.toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [GlobalTheory.HeckeFamilyMatrices.toGL_val A hA]; simp

theorem slz_eq_slash (k : ℕ) (hk : 1 ≤ k) (δ : M2) (hδ : 0 < δ.det) (f : ℍ → ℂ) :
    slz k δ f = f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by
  funext τ
  have hd : 0 < (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val := GlobalTheory.HeckeFamilyMatrices.toGL_det_pos δ hδ
  have hpt : ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))
      = GlobalTheory.HeckeFamilyMatrices.toGL δ • τ := by
    ext1
    rw [slzMob_coe δ hδ τ, UpperHalfPlane.coe_smul_of_det_pos hd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_entry δ hδ.ne']
  rw [ModularForm.slash_apply, GlobalTheory.HeckeFamilyMatrices.sigma_pos hd, slz, hpt]
  have hdet : (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val = (δ.det : ℝ) := GlobalTheory.HeckeFamilyMatrices.toGL_det δ hδ.ne'
  rw [hdet, abs_of_pos (by exact_mod_cast hδ)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, zpow_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.add_sub_cancel, UpperHalfPlane.denom, toGL_entry δ hδ.ne', Complex.ofReal_intCast]
  ring

end GlobalTheory.EisM.AtkinLehnerForm

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem qs_add_int (a : ℕ → ℂ) (τ : ℍ) (m : ℤ) : qs a (ofComplex ((τ : ℂ) + m)) = qs a τ := by
  have him : 0 < ((τ : ℂ) + m).im := by simpa using τ.im_pos
  have hcoe : ((ofComplex ((τ : ℂ) + m) : ℍ) : ℂ) = (τ : ℂ) + m := by
    rw [ofComplex_apply_of_im_pos him]
  simp only [qs, hcoe]
  congr 1
  funext n
  have e : cexp (2 * π * Complex.I * n * ((τ : ℂ) + m)) = cexp (2 * π * Complex.I * n * τ) := by
    rw [show 2 * π * Complex.I * n * ((τ : ℂ) + m) = 2 * π * Complex.I * n * τ + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

theorem slz_levelOne (k : ℕ) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ) (h : a₀ * d₀ = 1) :
    slz k !![((1 : ℕ) : ℤ) * a₀, b₀; ((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀, ((1 : ℕ) : ℤ) * d₀] (qs a)
      = fun τ => ((d₀ : ℂ) ^ k)⁻¹ * qs a τ := by
  funext τ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ))
        = (τ : ℂ) + ((b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp
  · have e : (((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ))
        = (τ : ℂ) + ((-b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp

end GlobalTheory.EisM.AtkinLehnerForm


open GlobalTheory.EisM.AtkinLehnerForm in
theorem GlobalTheory.EisM.atkinLehner_MF : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  intro k N l χ a a₀ b₀ c₀ d₀ h hk hN ha
  have hinv := GlobalTheory.T.atkinLehner_slash_inverse_character k N l χ (qs a) a₀ b₀ c₀ d₀ h hk hN ha.2
  suffices hex : ∃ a' : ℕ → ℂ, PolyB a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) by
    obtain ⟨a', h1, h2⟩ := hex
    exact ⟨a', ⟨h1, h2 ▸ hinv⟩, h2⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h' : (N : ℤ) * (a₀ * d₀) = 1 := by linear_combination h
    have hN1 : N = 1 := by exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h'
    subst hN1
    have had : a₀ * d₀ = 1 := by simpa using h'
    rw [slz_levelOne k a a₀ b₀ c₀ d₀ had]
    obtain ⟨C, A, hC⟩ := ha.1
    refine ⟨fun n => ((d₀ : ℂ) ^ k)⁻¹ * a n, ⟨‖((d₀ : ℂ) ^ k)⁻¹‖ * C, A, fun n => ?_⟩, ?_⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    · funext τ
      simp only [qs]
      rw [← tsum_mul_left]
      congr 1
      funext n
      ring
  · set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδdef
    have hdet : δ.det = N := by rw [hδdef, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * h
    have hδ : 0 < δ.det := by rw [hdet]; exact_mod_cast hN
    have hL : 0 < N * l := Nat.mul_pos hN hl
    haveI : NeZero (N * l) := ⟨hL.ne'⟩
    obtain ⟨f, hf⟩ := GlobalTheory.EisM.modularForm_gammaOne_of_MF k (N * l) N χ a hL (dvd_mul_right N l) ha
    have hF : slz k δ (qs a) = ⇑f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by rw [hf]; exact slz_eq_slash k hk δ hδ _
    let F : ModularForm (Gamma1 (N * l)) (k : ℤ) :=
      { toFun := slz k δ (qs a)
        slash_action_eq' := by
          rintro _ ⟨A, (hA : A ∈ Gamma1 (N * l)), rfl⟩
          exact GlobalTheory.EisM.OnGammaOne.slash_inv (dvd_mul_right N l) hinv A hA
        holo' := by
          show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slz k δ (qs a))
          rw [hF]; exact (ModularFormClass.holo f).slash _ _
        bdd_at_cusps' := by
          intro c hc
          show c.IsBoundedAt (slz k δ (qs a)) (k : ℤ)
          rw [hF, ← OnePoint.IsBoundedAt.smul_iff]
          apply ModularFormClass.bdd_at_cusps f
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact GlobalTheory.HeckeFamilyMatrices.isCusp_SL2Z_toGL_smul δ hδ.ne' hc }
    refine ⟨coef F, ?_, qs_coef_of_mfc F⟩
    have hb := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) F
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at hb
    exact polyB_of_isBigO hb
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.petersson_doubleCoset_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (α : κ → M2) (h f : ℍ → ℂ), 1 ≤ k → 0 < N → N ∣ L → 0 < q → q.Coprime N → Wt L ρ → (∀ δ ∈ Δ, δ.det = q ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → RRep L Δ α → Inv k L (ch ε) h → Inv k L (ch ε) f → Continuous h → Continuous f → (∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (h τ) * slz k (β i) f τ * (τ.im : ℂ) ^ k))) → pet k ρ h (hsum k (ch ε) β f) = pet k ρ (fun τ => ∑ j, ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h τ) f := by
  first | exact @GlobalTheory.EisM.pet_hsum_adjoint | exact GlobalTheory.EisM.pet_hsum_adjoint | (intros; apply GlobalTheory.EisM.pet_hsum_adjoint <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.qExpansion_heckeU_eq_sum_slash : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧ ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  first | exact @GlobalTheory.EisM.Uo_qs_sum_slz | exact GlobalTheory.EisM.Uo_qs_sum_slz | (intros; apply GlobalTheory.EisM.Uo_qs_sum_slz <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem unfold_strip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  intro L ρ Ψ W hρ hΨ hΨm hW
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  haveI : Countable (Gamma0 L) := Subtype.countable
  have memΓ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L ↔ (L : ℤ) ∣ γ 1 0 := by
    intro γ
    rw [Gamma0_mem]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hs : MeasurableSet strip := by
    have : strip = (fun τ : ℍ => τ.re) ⁻¹' Set.Ico 0 1 := by
      ext τ; simp [strip]
    rw [this]
    exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  set f : ℍ → ℂ := strip.indicator Ψ with hf_def
  have hfi : Integrable f := (integrable_indicator_iff hs).2 hΨ
  have hfm : AEStronglyMeasurable f := hfi.aestronglyMeasurable
  have mp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun τ : ℍ => γ • τ) volume volume := fun γ =>
    measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have me : ∀ γ : SL(2, ℤ), MeasurableEmbedding (fun τ : ℍ => γ • τ) := fun γ =>
    (MeasurableEquiv.smul ((γ : GL (Fin 2) ℝ))).measurableEmbedding
  have rowEq : ∀ (γ : SL(2, ℤ)) (a b : ℤ), γ 1 0 = a → γ 1 1 = b → UpperTheory.V.Af.Rs.row γ = ![a, b] := by
    intro γ a b ha hb
    funext i
    fin_cases i
    · simpa [UpperTheory.V.Af.Rs.row] using ha
    · simpa [UpperTheory.V.Af.Rs.row] using hb
  have step1 : ∀ τ : ℍ, ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ =
      ∑' γ : Gamma0 L, f ((γ : SL(2, ℤ)) • τ) := by
    intro τ
    have key : ∀ x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, ∃ γ : Gamma0 L,
        ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) = x.1 ∧ (γ : SL(2, ℤ)) • τ ∈ strip := by
      intro x
      obtain ⟨γ, ⟨hr, hst⟩, -⟩ := UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩
      have h0 : γ 1 0 = x.1.1 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 0
      have h1 : γ 1 1 = x.1.2 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 1
      refine ⟨⟨γ, (memΓ γ).2 (h0 ▸ x.2.2)⟩, ?_, hst⟩
      simp [h0, h1]
    choose g hg using key
    have ginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← (hg x).1, ← (hg y).1, hxy]
    have hsupp : Function.support (fun γ : Gamma0 L => f ((γ : SL(2, ℤ)) • τ)) ⊆ Set.range g := by
      intro γ hγ
      have hin : (γ : SL(2, ℤ)) • τ ∈ strip := by
        by_contra h
        exact hγ (Set.indicator_of_notMem h _)
      have hL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (memΓ γ).1 γ.2
      have hcop : IsCoprime ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := UpperTheory.V.Af.Rs.rowBij.1 γ
      refine ⟨⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩, ?_⟩
      set x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1} := ⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩
      have hx := hg x
      apply Subtype.ext
      exact (UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩).unique
        ⟨rowEq _ _ _ (congrArg Prod.fst hx.1) (congrArg Prod.snd hx.1), hx.2⟩ ⟨rowEq _ _ _ rfl rfl, hin⟩
    rw [← ginj.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    have hx := hg x
    have hL : (L : ℤ) ∣ (g x : SL(2, ℤ)) 1 0 := (memΓ _).1 (g x).2
    rw [hf_def, Set.indicator_of_mem hx.2, hW _ hL τ, hx.1]
  have hsum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ))⁻¹ • τ)) 1 := fun τ => by
    have := (Equiv.inv (Gamma0 L)).hasSum_iff.mpr (hρ.sum τ)
    simpa [Function.comp_def] using this
  set F : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ τ : ℂ) * f ((γ : SL(2, ℤ)) • τ) with hF
  set G : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℂ) * f τ with hG
  have hFG : ∀ γ, F γ = fun τ => G γ ((γ : SL(2, ℤ)) • τ) := by
    intro γ; funext τ; simp [hF, hG]
  have Gm : ∀ γ, AEStronglyMeasurable (G γ) := fun γ =>
    ((Complex.measurable_ofReal.comp (hρ.meas.comp (me ((γ : SL(2, ℤ))⁻¹)).measurable)).aestronglyMeasurable).mul hfm
  have Fm : ∀ γ, AEStronglyMeasurable (F γ) := fun γ => by
    rw [hFG γ]
    exact (Gm γ).comp_measurePreserving (mp γ)
  have tot : ∀ τ, ∑' γ : Gamma0 L, ‖G γ τ‖ₑ = ‖f τ‖ₑ := by
    intro τ
    simp only [hG, enorm_mul]
    rw [ENNReal.tsum_mul_right]
    have : ∑' γ : Gamma0 L, ‖((ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℝ) : ℂ)‖ₑ = 1 := by
      simp_rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hρ.nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => hρ.nonneg _) (hsum τ).summable, (hsum τ).tsum_eq,
        ENNReal.ofReal_one]
    rw [this, one_mul]
  have finG : ∑' γ, ∫⁻ τ, ‖G γ τ‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun γ => (Gm γ).enorm)]
    simp_rw [tot]
    exact hfi.hasFiniteIntegral.ne
  have finF : ∑' γ, ∫⁻ τ, ‖F γ τ‖ₑ ≠ ⊤ := by
    have : ∀ γ, ∫⁻ τ, ‖F γ τ‖ₑ = ∫⁻ τ, ‖G γ τ‖ₑ := fun γ => by
      rw [hFG γ]
      exact (mp γ).lintegral_comp_emb (me γ) (fun τ => ‖G γ τ‖ₑ)
    simp_rw [this]
    exact finG
  calc ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ
        = ∫ τ, ∑' γ, F γ τ := by
          congr 1; funext τ; rw [step1 τ, ← tsum_mul_left]
    _ = ∑' γ, ∫ τ, F γ τ := integral_tsum Fm finF
    _ = ∑' γ, ∫ τ, G γ τ := by
          refine tsum_congr fun γ => ?_
          rw [hFG γ]
          exact (mp γ).integral_comp (me γ) (G γ)
    _ = ∫ τ, ∑' γ, G γ τ := (integral_tsum Gm finG).symm
    _ = ∫ τ, f τ := by
          congr 1; funext τ
          simp only [hG]
          rw [tsum_mul_right, ← Complex.ofReal_tsum, (hsum τ).tsum_eq]
          simp
    _ = ∫ τ in strip, Ψ τ := integral_indicator hs

end GlobalTheory.EisM

end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y → HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ)) (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  first | exact @GlobalTheory.EisM.parseval_line | exact GlobalTheory.EisM.parseval_line | (intros; apply GlobalTheory.EisM.parseval_line <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  first | exact @GlobalTheory.EisM.mul_main | exact GlobalTheory.EisM.mul_main | (intros; apply GlobalTheory.EisM.mul_main <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffHeckeVOperator_raises_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l → (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  first | exact @GlobalTheory.Vo_level | exact GlobalTheory.Vo_level | (intros; apply GlobalTheory.Vo_level <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.lipschitz_weight_one_periodic_mean_zero : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  first | exact @GlobalTheory.EisM.LipOne.lipschitz_one | exact GlobalTheory.EisM.LipOne.lipschitz_one | (intros; apply GlobalTheory.EisM.LipOne.lipschitz_one <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.summable_regularizedEisensteinLatticeTerm : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L → Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  first | exact @GlobalTheory.LatSumZ.latsum_summable | exact GlobalTheory.LatSumZ.latsum_summable | (intros; apply GlobalTheory.LatSumZ.latsum_summable <;> assumption)
end
