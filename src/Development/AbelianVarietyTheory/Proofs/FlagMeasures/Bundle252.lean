module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle244
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantModuleIsometriesEqNormOneResidues
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff ENNReal

namespace GlobalTheory.LocMass

theorem setLIntegral_le_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) (hinv : ∀ᵐ y ∂μ, ∀ γ : Γ, f ((γ : G) * y) = f y)
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN' : N ≠ ⊤)
    (hN : ∀ z : G, (({γ : Γ | (γ : G) * z ∈ S}.encard : ℕ∞) : ℝ≥0∞) ≤ N) :
    ∫⁻ y in S, f y ∂μ ≤ N * ∫⁻ y in D, f y ∂μ := by
  first
  | (rename_i h_1 h_2 h_3 h_4 h_5 h_7 h_9; revert G h_1 h_2 h_3 h_4 h_5 μ h_7 Γ h_9 D hD f hf hinv S hS N hN' hN; exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le)
  | exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | (apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le ..)

theorem encard_le {G : Type} [Group G] (Γ : Subgroup G) (U T : Set G) (x z : G)
    (hT : ∀ γ ∈ Γ, ∀ u ∈ U, ∀ u' ∈ U, x⁻¹ * γ * x = u * u'⁻¹ → γ ∈ T) :
    {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U}.encard ≤ T.encard := by
  rcases Set.eq_empty_or_nonempty {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U} with h | ⟨γ₀, h0⟩
  · rw [h]; simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : Γ => ((γ * γ₀⁻¹ : Γ) : G)) ?_ ?_
    · intro γ hγ
      refine hT _ (γ * γ₀⁻¹).2 _ hγ _ h0 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro a _ b _ hab
      exact mul_right_cancel (Subtype.ext hab)

theorem local_mass_le : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  intro B U hn hU hK
  obtain ⟨hT2, hL, hS, -, -, ⟨K, hKK⟩, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have hfund := B.fund_spec
  have hD := hfd B.μf B.fund hfund
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : B.I.rep B.fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hb : ∀ v : InfinitePlace B.I.F, ∃ r : ℝ, 0 ≤ r ∧ ∀ u ∈ U, ∀ u' ∈ U,
      dOp (uMat ((u * u'⁻¹).1 v)) ≤ r := by
    intro v
    have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((p.1 * p.2⁻¹).1 v)) :=
      (GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)).2.2.2.2.comp
        ((continuous_apply v).comp (continuous_fst.comp (continuous_fst.mul continuous_snd.inv)))
    obtain ⟨r, hr⟩ := (hU.prod hU).bddAbove_image hc.continuousOn
    exact ⟨max r 0, le_max_right _ _, fun u hu u' hu' =>
      (hr ⟨(u, u'), ⟨hu, hu'⟩, rfl⟩).trans (le_max_left _ _)⟩
  choose r hr0 hrb using hb
  refine ⟨(3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v),
    by positivity, fun y x => ?_⟩
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x x r hn hr0
  obtain ⟨hinv, hmeas⟩ := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y
  set N : ℝ := (3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) *
    Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) with hN
  have hNe : (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I x)) ^ (2 * B.I.n ^ 2 * B.I.f) *
      Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) = N := by
    rw [hN, div_eq_mul_inv, mul_inv, mul_pow, mul_pow (tau1 B.I x)⁻¹, ← pow_add,
      show 2 * B.I.n ^ 2 * B.I.f + 2 * B.I.n ^ 2 * B.I.f = 4 * B.I.n ^ 2 * B.I.f by ring]
    ring
  rw [hNe] at hcard
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hcard
  have hUm : MeasurableSet U := hU.measurableSet
  have hSm : MeasurableSet ((fun g => x⁻¹ * g) ⁻¹' U) := measurable_const_mul _ hUm
  have h1 := (measurePreserving_mul_left (B.I.muA B.μf) x⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft x⁻¹) (fun g => (‖B.I.ext y (x * g)‖₊ : ℝ≥0∞) ^ 2) U
  simp only [mul_inv_cancel_left] at h1
  rw [← h1]
  have h2 := setLIntegral_le_mul hD (f := fun g => (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2)
    (hmeas.enorm.pow_const 2)
    (hinv.mono fun z hz γ => by rw [hz γ (hΓ ▸ γ.2)]) hSm (ENNReal.ofReal N) ENNReal.ofReal_ne_top
    (fun z => by
      have := encard_le Γ U {γ ∈ B.I.GFset | (x⁻¹ * γ * x).2 ∈ B.I.Kset ∧
          ∀ v, dOp (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v} x z (fun γ hγ u hu u' hu' e => by
        refine ⟨hΓ ▸ hγ, ?_, fun v => ?_⟩
        · rw [e, ← hKK]
          have h1 : u.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u hu
          have h2 : u'.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u' hu'
          exact K.mul_mem h1 (K.inv_mem h2)
        · rw [e]; exact hrb v u hu u' hu')
      refine (ENat.toENNReal_le.2 this).trans ?_
      rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hN0]
  congr 1
  have h3 : ∫⁻ g in B.fund, (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2 ∂(B.I.muA B.μf) =
      ∫⁻ g in B.fund, ‖(y : B.I.GA → ℂ) g‖ₑ ^ (2 : ℝ) ∂(B.I.muA B.μf) := by
    refine lintegral_congr_ae ((GlobalTheory.RightRegFund.ae_rep_eq_self hD hfund.1 hr).mono fun z hz => ?_)
    simp only [AutInst.ext, hz]
    rw [ENNReal.rpow_two]; rfl
  rw [h3, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, Lp.enorm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num
  exact Lp.aestronglyMeasurable y

end GlobalTheory.LocMass
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInf.SobTranslate

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mulLeft {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => a * g) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)).contDiff

theorem inUH_mul {n : ℕ} {H a g : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hg : inUH H g) :
    inUH H (a * g) := by
  unfold inUH at *
  rw [conjTranspose_mul]
  calc gᴴ * aᴴ * H * (a * g) = gᴴ * (aᴴ * H * a) * g := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hg]

theorem smoothOnH_translate {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H a : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : SmoothOnH H (fun g => f (a * g)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (a * g₀) (inUH_mul ha hg₀)
  have hc := contDiff_mulLeft a
  refine ⟨(fun g => a * g) ⁻¹' U, fun g => F (a * g), hU.preimage hc.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hc.contDiffOn (fun _ h => h)
  · intro g hg hgH
    exact hfF _ hg (inUH_mul ha hgH)

end Smooth

theorem rdWord_translate {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Matrix (Fin m) (Fin m) ℂ) (ws : List (Matrix (Fin m) (Fin m) ℂ))
    (f : Matrix (Fin m) (Fin m) ℂ → V) :
    rdWord ws (fun g => f (a * g)) = fun g => rdWord ws f (a * g) := by
  induction ws with
  | nil => rfl
  | cons X w ih =>
    funext g
    show rdM X (rdWord w _) g = rdM X (rdWord w f) (a * g)
    rw [ih]
    simp only [rdM, Matrix.mul_assoc]

variable {k r : ℕ}

theorem inv_of_mem {a : Mat k r} (ha : a ∈ GG k r) : a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 := by
  by_cases hdet : IsUnit a.det
  · exact ⟨Matrix.mul_nonsing_inv a hdet, Matrix.nonsing_inv_mul a hdet⟩
  · exfalso
    have h0 : a⁻¹ ∈ GG k r := (gg_closedSub k r).2.2.2.2 a ha
    rw [Matrix.nonsing_inv_apply_not_isUnit a hdet] at h0
    have h1 : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := h0
    let i : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
    have h2 : Hpk k r i i = -1 := by simp [Hpk, i]
    rw [← h1] at h2
    simp at h2

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableEmbedding_lmul {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1) :
    MeasurableEmbedding (lmulM a : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := lmulM a
      invFun := lmulM b
      left_inv := fun x => by
        show b * (a * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rfl
      right_inv := fun x => by
        show a * (b * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
        rfl
      continuous_toFun := continuous_lmul a
      continuous_invFun := continuous_lmul b }
  exact e.measurableEmbedding

theorem lintegral_translate_le {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {a : Mat k r}
    (ha : a ∈ GG k r) {K₀ K₂ : Set (Mt k r)} (hK : ∀ y ∈ K₀, lmulM a y ∈ K₂)
    (φ : Mt k r → ENNReal) :
    ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in K₂, φ y ∂μ := by
  have hemb := measurableEmbedding_lmul (inv_of_mem ha).1 (inv_of_mem ha).2
  have hmap : μ.map (lmulM a) = μ := hμ.2.2.2 a ha
  calc ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in lmulM a ⁻¹' K₂, φ (lmulM a y) ∂μ :=
        lintegral_mono_set hK
    _ = ∫⁻ y, φ y ∂((μ.restrict (lmulM a ⁻¹' K₂)).map (lmulM a)) :=
        (hemb.lintegral_map _).symm
    _ = ∫⁻ y in K₂, φ y ∂μ := by
        rw [← hemb.restrict_map, hmap]

theorem ofReal_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ)
    (hg : ∀ y, 0 ≤ g y) : ENNReal.ofReal (∫ y, g y ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂ν := by
  by_cases h : AEStronglyMeasurable g ν
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg) h]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable h]
    simp

theorem list_sum_ofReal {α : Type*} (l : List α) (u : α → ℝ) (v : α → ENNReal) (hu : ∀ a, 0 ≤ u a)
    (h : ∀ a ∈ l, ENNReal.ofReal (u a) ≤ v a) :
    0 ≤ (l.map u).sum ∧ ENNReal.ofReal (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h0, h1⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨add_nonneg (hu a) h0, ?_⟩
    rw [ENNReal.ofReal_add (hu a) h0]
    exact add_le_add (h a List.mem_cons_self) h1

theorem sobolev_translate : ∀ (k r : ℕ) (μ : Measure (Mt k r)) (C₀ : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsHaarOn (GG k r) μ → IsCompact K₀ → (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C₀ * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μ).sum) → ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → (∀ ws ∈ Ws, ContinuousOn (rdWord ws f) (GG k r)) → ∀ x ∈ Q, Matrix.of x ∈ GG k r → ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (Ws.map fun ws => ∫⁻ y in K₂, (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ).sum := by
  intro k r μ C₀ Ws K₀ hμ hK₀ hS Q hQ
  let pr : Mt k r × Mt k r → Mt k r := fun p => lmulM (Matrix.of p.1) p.2
  have hpr : Continuous pr := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [pr, lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  refine ⟨pr '' (Q ×ˢ K₀), (hQ.prod hK₀).image hpr, ?_⟩
  intro B _ _ _ f hf _ x hxQ hxG
  have hsm : SmoothOnH (Hpk k r) (fun g => f (Matrix.of x * g)) :=
    smoothOnH_translate (a := Matrix.of x) hxG hf
  have hkey := hS B (fun g => f (Matrix.of x * g)) hsm
  simp only [Matrix.mul_one, rdWord_translate] at hkey
  obtain ⟨hS0, hSum⟩ := list_sum_ofReal Ws
    (fun ws => ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ)
    (fun ws => ∫⁻ y in pr '' (Q ×ˢ K₀), (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ)
    (fun _ => integral_nonneg fun _ => by positivity)
    (fun ws _ => by
      refine (ofReal_integral_le _ _ fun _ => by positivity).trans ?_
      have hφ := lintegral_translate_le hμ (a := Matrix.of x) hxG (K₀ := K₀)
        (K₂ := pr '' (Q ×ˢ K₀)) (fun y hy => ⟨(x, y), ⟨hxQ, hy⟩, rfl⟩)
        (fun y => (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2)
      refine le_trans (le_of_eq ?_) hφ
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      rfl)
  calc ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2)
      ≤ ENNReal.ofReal (|C₀| * (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum) :=
        ENNReal.ofReal_le_ofReal (hkey.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hS0))
    _ = ENNReal.ofReal |C₀| * ENNReal.ofReal (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum :=
        ENNReal.ofReal_mul (abs_nonneg _)
    _ ≤ _ := by gcongr

end GlobalTheory.SgInf.SobTranslate
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.RegLimit

theorem sq_le_four (a e b : ENNReal) (h : a ≤ e + b) : a ^ 2 ≤ 4 * (e ^ 2 + b ^ 2) := by
  have h1 : e + b ≤ 2 * max e b := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max e b ^ 2 ≤ e ^ 2 + b ^ 2 := by
    rcases le_total e b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc a ^ 2 ≤ (2 * max e b) ^ 2 := pow_le_pow_left₀ zero_le (h.trans h1) 2
    _ = 4 * max e b ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (e ^ 2 + b ^ 2) := by gcongr

theorem exists_continuous_limit : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  intro k r μ hμ Wp _ _ _ f g hf hg hC hL
  set T : Set (Mt k r) → Set (Mat k r) := fun Q => GG k r ∩ {y | Matrix.of.symm y ∈ Q} with hT
  have hUC : ∀ Q : Set (Mt k r), IsCompact Q → UniformCauchySeqOn f Filter.atTop (T Q) := by
    intro Q hQ
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC Q hQ (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have := hN m hm n hn (Matrix.of.symm y) hy.2 (by rw [Matrix.of.apply_symm_apply]; exact hy.1)
    simp only [Equiv.apply_symm_apply] at this
    rw [dist_eq_norm]; linarith
  set F : Mat k r → Wp := fun y => Filter.limUnder Filter.atTop (fun j => f j y) with hFdef
  have hF : ∀ y ∈ GG k r, Filter.Tendsto (fun j => f j y) Filter.atTop (nhds (F y)) := by
    intro y hy
    have hc := (hUC {Matrix.of.symm y} isCompact_singleton).cauchySeq
      (show y ∈ T {Matrix.of.symm y} from ⟨hy, rfl⟩)
    obtain ⟨L, hL'⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨L, hL'⟩
  have hU : ∀ Q : Set (Mt k r), IsCompact Q → TendstoUniformlyOn f F Filter.atTop (T Q) :=
    fun Q hQ => (hUC Q hQ).tendstoUniformlyOn_of_tendsto (fun y hy => hF y hy.1)
  have hsymm : Continuous (fun y : Mat k r => (Matrix.of.symm y : Mt k r)) := continuous_id
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hFc : ContinuousOn F (GG k r) := by
    intro x hx
    set Q : Set (Mt k r) := Metric.closedBall (Matrix.of.symm x) 1
    have hQ : IsCompact Q := isCompact_closedBall _ _
    have h1 : ContinuousOn F (T Q) :=
      (hU Q hQ).continuousOn (Filter.Eventually.of_forall (f := Filter.atTop) fun j => (hf j).mono Set.inter_subset_left).frequently
    have hxT : x ∈ T Q := ⟨hx, show (Matrix.of.symm x : Mt k r) ∈ Q from Metric.mem_closedBall_self (x := (Matrix.of.symm x : Mt k r)) zero_le_one⟩
    refine (h1 x hxT).mono_of_mem_nhdsWithin ?_
    exact inter_mem_nhdsWithin _ (hsymm.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ zero_lt_one))

  have hGcl : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := (gg_closedSub k r).2.1.preimage hof
  have hGae : ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r := ae_iff.2 hμ.2.2.1
  have hFm : AEStronglyMeasurable (fun x : Mt k r => F (Matrix.of x)) μ := by
    have h1 : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} :=
      hFc.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := μ) hGcl.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) hGae] at h2
  have hQae : ∀ Q : Set (Mt k r), IsCompact Q → MeasurableSet Q →
      ∀ᵐ x ∂(μ.restrict Q), F (Matrix.of x) = g x := by
    intro Q hQ hQm
    have hQfin : μ Q ≠ ⊤ := (haar_compact_lt_top hμ hQ).ne
    set a : Mt k r → ENNReal := fun x => (‖F (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 with ha
    have hbound : ∀ n : ℕ, ∫⁻ x in Q, a x ∂μ ≤
        4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q + ENNReal.ofReal (1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have e1 := Metric.tendstoUniformlyOn_iff.1 (hU Q hQ) _ hpos
      have e2 := ENNReal.tendsto_nhds_zero.1 (hL Q hQ) _ (ENNReal.ofReal_pos.2 hpos)
      obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
      calc ∫⁻ x in Q, a x ∂μ
          ≤ ∫⁻ x in Q, 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 +
              (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hGae] with x hxQ hxG
            apply sq_le_four
            have hd := hj1 (Matrix.of x) ⟨hxG, by simpa using hxQ⟩
            have htri : ‖F (Matrix.of x) - g x‖₊ ≤
                ‖F (Matrix.of x) - f j (Matrix.of x)‖₊ + ‖f j (Matrix.of x) - g x‖₊ := by
              have : F (Matrix.of x) - g x = (F (Matrix.of x) - f j (Matrix.of x)) + (f j (Matrix.of x) - g x) := by
                abel
              rw [this]; exact nnnorm_add_le _ _
            calc (‖F (Matrix.of x) - g x‖₊ : ENNReal)
                ≤ (‖F (Matrix.of x) - f j (Matrix.of x)‖₊ : ENNReal) + ‖f j (Matrix.of x) - g x‖₊ := by
                  rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 htri
              _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ‖f j (Matrix.of x) - g x‖₊ := by
                  gcongr
                  exact ENNReal.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le hpos.le).2
                    (by rw [coe_nnnorm, ← dist_eq_norm]; exact hd.le))
        _ = 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
              ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
              lintegral_const, Measure.restrict_apply_univ]
        _ ≤ _ := by gcongr
    have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 : Filter.Tendsto (fun n : ℕ => 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) ht)
        (Or.inr hQfin)).add ht) (a := (4 : ENNReal)) (Or.inr (by norm_num))
      simpa using this
    have hzero : ∫⁻ x in Q, a x ∂μ = 0 := le_antisymm (ge_of_tendsto' ht2 hbound) (zero_le)
    have hm : AEStronglyMeasurable (fun x => F (Matrix.of x) - g x) (μ.restrict Q) :=
      hFm.restrict.sub (hg Q hQ)
    have hae := (lintegral_eq_zero_iff' (hm.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)).1 hzero
    filter_upwards [hae] with x hx
    simpa [ha, sub_eq_zero] using hx
  refine ⟨F, hFc, ?_, hF⟩
  have hall : ∀ n : ℕ, ∀ᵐ x ∂(μ.restrict (Metric.closedBall (0 : Mt k r) n)), F (Matrix.of x) = g x :=
    fun n => hQae _ (isCompact_closedBall _ _) Metric.isClosed_closedBall.measurableSet
  have := (ae_restrict_iUnion_iff _ _).2 hall
  rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this

end GlobalTheory.SgInf.RegLimit
end
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries : PsiEigen := by
  first | exact @GlobalTheory.Dec.PsiEig.psiEigen | exact GlobalTheory.Dec.PsiEig.psiEigen | (intros; apply GlobalTheory.Dec.PsiEig.psiEigen <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  first | exact @GlobalTheory.ThA.haarW_twoSided_of_left | exact GlobalTheory.ThA.haarW_twoSided_of_left | (intros; apply GlobalTheory.ThA.haarW_twoSided_of_left <;> assumption)
end

section

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

theorem _root_.GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ L 𝔭 b a → ∀ i, vF 𝔭 (a i) = 1 → (∀ j, j ≠ i → vF 𝔭 (a j) = 0) → discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  first | exact @GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount | exact GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount | (intros; apply GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount <;> assumption)
end

section


theorem _root_.GlobalTheory.T.capelli_operator_unitaryGroup_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)
end
