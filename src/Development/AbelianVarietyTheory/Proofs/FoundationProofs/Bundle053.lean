module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.LevelGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def act (T : Tower Ω ε) : SL(2, ℤ) →* (T.K ≃ₐ[Ω] T.K) where
  toFun γ := T.sl (ofSL γ⁻¹)
  map_one' := by ext f; simp [T.sl_one]
  map_mul' γ δ := by
    ext f
    rw [AlgEquiv.mul_apply, mul_inv_rev, map_mul, T.sl_mul]

theorem act_apply (T : Tower Ω ε) (γ : SL(2, ℤ)) (f : T.K) : act T γ f = T.sl (ofSL γ⁻¹) f := rfl

theorem sl_fix (T : Tower Ω ε) (γ : SL(2, ℤ)) :
    ∀ x ∈ IntermediateField.adjoin Ω {T.jK}, T.sl (ofSL γ) x = x := by
  have hle : IntermediateField.adjoin Ω {T.jK} ≤ IntermediateField.fixedField (act T).range := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro σ ⟨δ, rfl⟩
    exact T.j_inv _
  intro x hx
  have := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) (act T γ⁻¹) ⟨γ⁻¹, rfl⟩
  rwa [act_apply, inv_inv] at this

def lvl (T : Tower Ω ε) (M : ℕ) : IntermediateField (IntermediateField.adjoin Ω {T.jK}) T.K where
  carrier := {f | ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f}
  mul_mem' {a b} ha hb γ hγ := by rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' γ _ := map_one _
  add_mem' {a b} ha hb γ hγ := by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  zero_mem' γ _ := map_zero _
  algebraMap_mem' c γ _ := by
    rw [IntermediateField.algebraMap_apply]
    exact sl_fix T γ _ c.2
  inv_mem' x hx γ hγ := by rw [map_inv₀, hx γ hγ]

theorem act_mem_lvl (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) {f : T.K} (hf : f ∈ lvl T M) :
    act T γ f ∈ lvl T M := by
  intro δ hδ
  have hc : γ⁻¹ * δ * γ⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ⁻¹
  have e : γ⁻¹ * δ = (γ⁻¹ * δ * γ⁻¹⁻¹) * γ⁻¹ := by group
  rw [act_apply, ← T.sl_mul, ← map_mul, e, map_mul, T.sl_mul, hf _ hc]

def rho (T : Tower Ω ε) (M : ℕ) :
    SL(2, ℤ) →* (lvl T M ≃ₐ[IntermediateField.adjoin Ω {T.jK}] lvl T M) where
  toFun γ :=
    { toFun := fun x => ⟨act T γ x, act_mem_lvl T M γ x.2⟩
      invFun := fun x => ⟨act T γ⁻¹ x, act_mem_lvl T M γ⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by
        show act T γ⁻¹ (act T γ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply])
      right_inv := fun x => Subtype.ext (by
        show act T γ (act T γ⁻¹ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (act T γ) (x : T.K) y)
      map_add' := fun x y => Subtype.ext (map_add (act T γ) (x : T.K) y)
      commutes' := fun c => Subtype.ext (by
        show act T γ (c : T.K) = (c : T.K)
        rw [act_apply]
        exact sl_fix T _ _ c.2) }
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by
    show act T 1 x = x
    rw [map_one, AlgEquiv.one_apply])
  map_mul' γ δ := AlgEquiv.ext fun x => Subtype.ext (by
    show act T (γ * δ) x = act T γ (act T δ x)
    rw [map_mul, AlgEquiv.mul_apply])

theorem rho_val (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (x : lvl T M) :
    ((rho T M γ x : lvl T M) : T.K) = T.sl (ofSL γ⁻¹) x := rfl

theorem gamma_le_ker (T : Tower Ω ε) (M : ℕ) : CongruenceSubgroup.Gamma M ≤ (rho T M).ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  show T.sl (ofSL γ⁻¹) x = x
  exact x.2 _ (inv_mem hγ)

theorem finite_range (T : Tower Ω ε) (M : ℕ) (hM : 0 < M) : Finite (rho T M).range := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  haveI : (rho T M).ker.FiniteIndex := Subgroup.finiteIndex_of_le (gamma_le_ker T M)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (rho T M)).toEquiv

end GlobalTheory.FN.LevelGal
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory.FN

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have h0 : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h0
  have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
  have h1 := h0 Complex.I hI
  rw [Set.empty_union] at h1
  have h2 : Hs ∈ 𝓝[≠] Complex.I := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 : (∅ : Set ℂ) ∈ 𝓝[≠] Complex.I := by
    have := Filter.inter_mem h2 h1
    simpa using this
  exact (Filter.empty_mem_iff_bot.mp h3 ▸ (inferInstance : (𝓝[≠] Complex.I).NeBot)).ne rfl

theorem eqOn_zero_of_germ_eq_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) = 0) :
    ∀ z ∈ Hs, a z = 0 := by
  haveI := codiscreteWithin_Hs_neBot
  have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
  · exact fun z hz => h hz
  · exfalso
    have he : a =ᶠ[Filter.codiscreteWithin Hs] (0 : ℂ → ℂ) := Filter.Germ.coe_eq.mp h0
    obtain ⟨z, hz1, hz2⟩ := (h.and he).exists
    exact hz1 hz2

theorem germ_main : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  haveI := codiscreteWithin_Hs_neBot
  refine ⟨inferInstance, ?_, ?_⟩
  · intro a b ha hb hab z hz
    have h0 : ((a - b : ℂ → ℂ) : Mero) = 0 := by
      rw [Filter.Germ.coe_sub, hab, sub_self]
    have := eqOn_zero_of_germ_eq_zero (ha.sub hb) h0 z hz
    simpa [sub_eq_zero] using this
  · intro a ha hne
    have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
    have hev : ∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0 := by
      rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
      · exfalso
        apply hne
        rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
        filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
        exact h hz
      · exact h
    refine ⟨hev, ?_⟩
    refine ⟨⟨(a : Mero), ((fun z => (a z)⁻¹ : ℂ → ℂ) : Mero), ?_, ?_⟩, rfl⟩
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]

end GlobalTheory.FN
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.diamond_diag_mul_eq_mul_upperTriangular_of_not_dvd_lowerLeft : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  first | exact @GlobalTheory.HkInvFin.sigma_dg_mul_eq | exact GlobalTheory.HkInvFin.sigma_dg_mul_eq | (intros; apply GlobalTheory.HkInvFin.sigma_dg_mul_eq <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) → ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.uOp q f ∣[k] γ = GlobalTheory.Hk.uOp q f := by
  first | exact @GlobalTheory.Hk.uOp_slash_lev | exact GlobalTheory.Hk.uOp_slash_lev | (intros; apply GlobalTheory.Hk.uOp_slash_lev <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), (q : ℂ) ^ (k - 1) • GlobalTheory.Hk.vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.smul_vOp_eq_slash | exact GlobalTheory.Hk.smul_vOp_eq_slash | (intros; apply GlobalTheory.Hk.smul_vOp_eq_slash <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.uOp_eq_sum_slash | exact GlobalTheory.Hk.uOp_eq_sum_slash | (intros; apply GlobalTheory.Hk.uOp_eq_sum_slash <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | exact GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | (intros; apply GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.dia_mul_inv_mem_lev | exact GlobalTheory.Hk.dia_mul_inv_mem_lev | (intros; apply GlobalTheory.Hk.dia_mul_inv_mem_lev <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_modularForm | exact GlobalTheory.Hk.dia_modularForm | (intros; apply GlobalTheory.Hk.dia_modularForm <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), GlobalTheory.Hk.IsDia N l d σ → γ ∈ GlobalTheory.Hk.lev N l → σ * γ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.isDia_conj_mem_lev | exact GlobalTheory.Hk.isDia_conj_mem_lev | (intros; apply GlobalTheory.Hk.isDia_conj_mem_lev <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.slash_rat_isBoundedAt | exact GlobalTheory.Hk.slash_rat_isBoundedAt | (intros; apply GlobalTheory.Hk.slash_rat_isBoundedAt <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.hecke_operator_commutes_diamond : ∀ (N l q : ℕ) (k d : ℤ) (σ ρ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  first | exact @GlobalTheory.Hk.heckeT_dia_comm | exact GlobalTheory.Hk.heckeT_dia_comm | (intros; apply GlobalTheory.Hk.heckeT_dia_comm <;> assumption)
end
