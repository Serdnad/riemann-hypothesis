module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle017
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle012
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase

theorem vacS_of_isVac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ v hv
  have hA : TensVac.Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  let e := AddEquiv.ofBijective _ (TensVac.crdHom_bijective (n := n) hs)
  have he (y) : e.symm (TensVac.crdHom hs y) = y := e.symm_apply_apply y
  have ho (y y' : Matrix (Fin n) (Fin r) E) :
      Phase.om (TensVac.crdHom hs y) (TensVac.crdHom hs y') = -∑ k, EF X (y k) (y' k) :=
    TensVac.om_crdHom hs y y'
  refine ⟨(tens Λ L).map (TensVac.crdHom hs), fun p => epsW X w (e.symm p),
    Vac.fg_map hA.1 _, ?_, ?_, ?_, ⟨2, two_pos, ?_⟩, hv.1, ?_⟩
  · intro p
    obtain ⟨y, rfl⟩ := (TensVac.crdHom_bijective hs).2 p
    rw [AddSubgroup.mem_map_iff_mem (TensVac.crdHom_bijective hs).1, hA.2.1]
    constructor
    · rintro h _ ⟨y', hy', rfl⟩
      obtain ⟨k, hk⟩ := h y' hy'
      exact ⟨-k, by rw [ho, hk, Int.cast_neg]⟩
    · intro h y' hy'
      obtain ⟨k, hk⟩ := h _ ⟨y', hy', rfl⟩
      rw [ho] at hk
      exact ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := congrArg norm (TensVac.epsW_mul_conj (X := X) w (e.symm (TensVac.crdHom hs y)))
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    exact (mul_self_eq_one_iff.1 this).resolve_right fun h => by
      linarith [norm_nonneg (epsW X w (e.symm (TensVac.crdHom hs y)))]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [← map_add (f := _), he, he, he, ho, (hA.2.2 y hy).2 y' hy', Rat.cast_neg, mul_neg]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_nsmul, he, hA.eps_two hs hy]
  · rintro _ ⟨y, hy, rfl⟩
    rw [he]
    exact hv.2.2 y hy

end GlobalTheory.Phase
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.LatFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (γ γ' : GL (Fin r) E) (L : Lt E r) : mapL (γ * γ') L = mapL γ (mapL γ' L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL 1 L = L := by
  ext v
  simp [mapL]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] [IsCMField E] in
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact γ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop


omit [IsCMField E] in
theorem countable_fg : {L : Lt E r | L.FG}.Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine (Set.countable_range fun s : Finset (Fin r → E) =>
    Submodule.span (𝓞 E) (s : Set (Fin r → E))).mono ?_
  rintro L ⟨s, hs⟩
  exact ⟨s, hs⟩


omit [IsCMField E] in
theorem exists_den {L : Lt E r} (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ L, ∀ a, ∃ c : 𝓞 E, (c : E) = (d : E) * v a := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator ..)

theorem eq_zero_of_small (X : Data E r) (c : 𝓞 E) (h : ∀ τ : X.Ψ, ‖τ.1 (c : E)‖ < 1) : c = 0 := by
  by_contra hc
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hc
  by_cases hs : σ ∈ X.Ψ
  · exact absurd (h ⟨σ, hs⟩) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h2
      exact hs ((X.cmType σ).2 h2)
    have h3 := h ⟨_, h1⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h3
    exact absurd h3 (not_lt.2 hσ)

theorem exists_nhds (X : Data E r) {L : Lt E r} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ U ∈ 𝓝 x, ∀ γ : GL (Fin r) E, mapL γ L = L → lact γ x ∈ U → γ = 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_den hL
  obtain ⟨s, hs⟩ := hL
  let f : (Fin r → E) → X.Ψ → Fin r → Frame X.Ψ r → ℝ := fun v τ a y =>
    ‖τ.1 (d : E) * ((mat y τ *ᵥ ((mat x τ)⁻¹ *ᵥ fun b => τ.1 (v b))) a - τ.1 (v a))‖
  have hf : ∀ v τ a, Continuous (f v τ a) := fun v τ a => by
    simp only [f, mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => (hx τ).1.isUnit
  refine ⟨{y | ∀ v ∈ s, ∀ τ a, f v τ a y < 1}, ?_, fun γ hγ hy => ?_⟩
  · refine (Filter.eventually_all_finset s).2 fun v _ => Filter.eventually_all.2 fun τ =>
      Filter.eventually_all.2 fun a => ?_
    refine (hf v τ a).continuousAt.eventually_lt continuousAt_const ?_
    simp [f, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu τ)]
  · have h1 : ∀ v ∈ s, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      have hvL : v ∈ L := hs ▸ Submodule.subset_span hv
      have hγv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L := by
        rw [← hγ]
        exact ⟨v, hvL, by simp⟩
      funext a
      obtain ⟨c, hc⟩ := hd _ (L.sub_mem hγv hvL) a
      have hc0 : c = 0 := eq_zero_of_small X c fun τ => by
        have h2 := hy v hv τ a
        have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
        simp only [f, e1, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one] at h2
        rw [hc]
        convert h2 using 2
        simp [Matrix.mulVec, dotProduct]
      rw [hc0] at hc
      have hd1 : (d : E) ≠ 0 := by exact_mod_cast hd0
      have := (mul_eq_zero.1 (hc.symm.trans (by simp))).resolve_left hd1
      exact sub_eq_zero.1 this
    have h2 : ∀ v ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem v hv => exact h1 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    have h3 : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v => by
      have hv : v ∈ Submodule.span E (L : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact h2 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    ext i j
    have := congrFun (h3 (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply] using this

theorem exists_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)), (∀ γ ∈ Δ, IsUn X γ) → (∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) → 𝓛.Countable ∧ (∀ (γ γ' : GL (Fin r) E) L, mapL (γ * γ') L = mapL γ (mapL γ' L)) ∧ (∀ L : Lt E r, mapL 1 L = L) ∧ ∃ D : Lt E r → Set (Frame X.Ψ r), (∀ L, MeasurableSet (D L) ∧ D L ⊆ X.dom) ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ∃! γ : Δ, lact γ x ∈ D (mapL γ L) := by
  intro E _ _ _ r X Δ 𝓛 hun hlat hstab
  have hc : 𝓛.Countable := countable_fg.mono fun L hL => (hlat L hL).1
  refine ⟨hc, mapL_mul, mapL_one, ?_⟩
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have : Countable (GL (Fin r) E) := Units.val_injective.countable
  have : Countable 𝓛 := hc.to_subtype
  letI : TopologicalSpace 𝓛 := ⊥
  have : DiscreteTopology 𝓛 := ⟨rfl⟩
  letI : MeasurableSpace 𝓛 := ⊤
  have : OpensMeasurableSpace 𝓛 := ⟨le_top⟩
  letI act : MulAction Δ (𝓛 × X.dom) :=
    { smul := fun γ p => (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩)
      one_smul := fun p => Prod.ext (Subtype.ext (mapL_one _)) (Subtype.ext (lact_one _))
      mul_smul := fun γ γ' p =>
        Prod.ext (Subtype.ext (mapL_mul _ _ _)) (Subtype.ext (lact_mul _ _ _)) }
  have hsm : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p =
    (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩) := fun _ _ => rfl
  have : MeasurableConstSMul Δ (𝓛 × X.dom) := ⟨fun γ => by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_from_top (f := fun L : 𝓛 => (⟨mapL γ L, hstab _ γ.2 _ L.2⟩ : 𝓛))).comp
        measurable_fst
    · exact (((continuous_lact (γ : GL (Fin r) E)).measurable.comp
        measurable_subtype_coe).comp measurable_snd).subtype_mk⟩
  have hdisc : ∀ p : 𝓛 × X.dom, ∃ U ∈ 𝓝 p, ∀ γ : Δ, γ • p ∈ U → γ = 1 := fun p => by
    obtain ⟨U, hU, h⟩ := exists_nhds X (hlat _ p.1.2).1 (hlat _ p.1.2).2 p.2.2
    refine ⟨{p.1} ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hU), fun γ hγ => ?_⟩
    exact Subtype.ext (h γ (congrArg Subtype.val hγ.1) hγ.2)
  have hfree : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = p → γ = 1 := fun γ p h => by
    obtain ⟨U, hU, h'⟩ := hdisc p
    exact h' γ (h.symm ▸ mem_of_mem_nhds hU)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Δ)
    (X := 𝓛 × X.dom)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {p : 𝓛 × X.dom | g • p = p} = ∅ :=
          Set.eq_empty_of_forall_notMem fun p hp => hg (hfree g p hp)
        simp [this])
    (fun p => by
      obtain ⟨U, hU, h⟩ := hdisc p
      exact ⟨U, hU, fun g hg => by rw [h g hg, one_smul]⟩)
  refine ⟨fun L => {y | ∃ (hL : L ∈ 𝓛) (hy : y ∈ X.dom), ((⟨L, hL⟩, ⟨y, hy⟩) : 𝓛 × X.dom) ∈ D},
    fun L => ⟨?_, fun y hy => hy.2.1⟩, fun L hL x hx => ?_⟩
  · by_cases hL : L ∈ 𝓛
    · have h := (MeasurableEmbedding.subtype_coe
        (FourierCoefficientDomain.isOpen_dom X).measurableSet).measurableSet_image.2
        (measurable_prodMk_left (x := (⟨L, hL⟩ : 𝓛)) hD)
      convert h using 1
      ext y
      exact ⟨fun ⟨_, hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨z, h, e⟩ => e ▸ ⟨hL, z.2, h⟩⟩
    · simp [hL]
  · obtain ⟨g, hg⟩ := hcov (⟨L, hL⟩, ⟨x, hx⟩)
    refine ⟨g, ⟨_, _, hg⟩, fun k hk => ?_⟩
    obtain ⟨_, _, hk⟩ := hk
    have := hu _ hg (k * g⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)

end GlobalTheory.SW.LatFrame
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.UnAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exists_mem_dom (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show FD.gram τ.1 X.Gm (mat (fun τ => P τ) τ) = FD.gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0


omit [NumberField E] [IsCMField E] in
theorem lact_one' {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]


omit [NumberField E] [IsCMField E] in
theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

theorem isUn_mul {γ' γ : GL (Fin r) E} (h' : IsUn X γ') (h : IsUn X γ) : IsUn X (γ' * γ) := by
  intro u v
  rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, h', h]

theorem tauMat_mem (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    tauMat X bas idx x ∈ Siegel (Fin g) :=
  ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩

theorem eq_of_thA_eq (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) (h : thA X bas idx φ x = thA X bas idx ψ x) : φ = ψ := by
  refine eq_of_thS_eq _ _ φ ψ hφ hψ _ (tauMat_mem idx hs hx) fun ζ => ?_
  have h1 := congrFun h fun k => perMat X bas idx Sum.inl x *ᵥ ζ k
  simp only [thA, mulVec_mulVec, hMat_mul_perMat idx hs hx, one_mulVec] at h1
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (isUnit_det_hMat idx hs hx).ne_zero)
    (Complex.exp_ne_zero _)) h1

theorem thA_add (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) :
    thA X bas idx (φ + ψ) x = thA X bas idx φ x + thA X bas idx ψ x := by
  funext z
  have h1 := (SiegelSum.summable_norm_thetaTerm _ _ φ hφ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  have h2 := (SiegelSum.summable_norm_thetaTerm _ _ ψ hψ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  simp only [thA, thS, Pi.add_apply, add_mul]
  rw [h1.tsum_add h2, mul_add]

theorem thA_smul (x : Frame X.Ψ r) (a : ℂ) (φ : TF n g) :
    thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
  funext z
  simp only [thA, thS, Pi.smul_apply, smul_eq_mul, mul_assoc a, tsum_mul_left]
  ring

theorem exists_weil (hs : IsSympl X bas) (hn : Even n) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    ∃ ω : TF n g → TF n g, ∀ φ, IsSB φ → IsSB (ω φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (ω φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx n hs hn γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (Fin g) σ (by simpa using hn) hσ
  refine ⟨ω, fun φ hφ => ⟨(hω φ hφ).1, fun x hx => ?_, (hω φ hφ).2.2⟩⟩
  obtain ⟨-, hτ, h1, h2⟩ := h x hx
  funext z
  have h3 := (hω φ hφ).2.1 _ hτ fun k => hMat X bas idx x *ᵥ z k
  have h4 := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
    GlobalTheory.T.canonicalThetaExponent_symplectic_invariant _ σ hσ _ hτ (hMat X bas idx x *ᵥ z k)
  have hd := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ).1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h4
  have h5 (k) : hMat X bas idx (lact γ x) *ᵥ z k =
      (hMat X bas idx x *ᵥ z k) ᵥ* (spDen σ (tauMat X bas idx x))⁻¹ := by
    rw [h2, ← mulVec_mulVec, mulVec_transpose]
  have h6 : (hMat X bas idx (lact γ x)).det =
      (spDen σ (tauMat X bas idx x)).det⁻¹ * (hMat X bas idx x).det := by
    rw [h2, det_mul, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv']
  simp only [thA, h5, imInv_eq, h1, h6]
  rw [h3, ← h4, Fintype.card_fin, mul_add, Complex.exp_add, mul_pow, inv_pow]
  have h7 := pow_ne_zero (n / 2) hd
  rw [show ∀ t : ℂ, (π : ℂ) / 2 * (2 * I * t) = π * I * t from fun t => by ring]
  field_simp

theorem wG_eq (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {φ ψ : TF n g}
    (hψ : IsSB ψ) (h : ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x) :
    wG X bas idx γ φ = ψ := by
  have he : ∃ ψ : TF n g, IsSB ψ ∧ ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x :=
    ⟨ψ, hψ, h⟩
  obtain ⟨x, hx⟩ := exists_mem_dom X
  rw [wG, dite_eq_left he]
  exact eq_of_thA_eq idx hs (hγ.lact_mem hx) he.choose_spec.1 hψ
    ((he.choose_spec.2 x hx).trans (h x hx).symm)

theorem herm_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (u v : Fin g → ℂ) :
    (hMat X bas idx (lact γ x) *ᵥ u) ⬝ᵥ imInv X bas idx (lact γ x) *ᵥ
        star (hMat X bas idx (lact γ x) *ᵥ v) =
      (hMat X bas idx x *ᵥ u) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ v) := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx 0 hs Even.zero γ hγ
  obtain ⟨hx', hτ, h1, h2⟩ := h x hx
  obtain ⟨hd, -, -, h3, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ
  have h4 : imInv X bas idx x = (spDen σ (tauMat X bas idx x))⁻¹ * imInv X bas idx (lact γ x) *
      ((spDen σ (tauMat X bas idx x))⁻¹)ᴴ := by
    rw [← (imInv_isSymm idx hs hx).eq, ← (imInv_isSymm idx hs hx').eq, imInv_eq, imInv_eq, ← h3, h1,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, transpose_mul, transpose_mul,
      ← transpose_nonsing_inv (spDen _ _), transpose_transpose, conjTranspose_nonsing_inv,
      transpose_nonsing_inv (Matrix.map (spDen _ _) _)]
    rfl
  rw [h4, h2, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, mulVec_transpose, star_vecMul,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (spDen _ _)⁻¹]

end GlobalTheory.SW.UnAct

namespace GlobalTheory.SW

open UnAct

theorem wG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  intro E _ _ _ r X g bas idx n hs hn
  have key : ∀ γ, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ := by
    intro γ hγ φ hφ
    obtain ⟨ω, hω⟩ := exists_weil idx hs hn hγ
    have e : ∀ ψ, IsSB ψ → wG X bas idx γ ψ = ω ψ := fun ψ hψ =>
      wG_eq idx hs hγ (hω ψ hψ).1 (hω ψ hψ).2.1
    rw [e φ hφ]
    exact ⟨(hω φ hφ).1, (hω φ hφ).2.1, fun ψ hψ => by rw [e ψ hψ]; exact (hω φ hφ).2.2 ψ hψ⟩
  intro γ hγ φ hφ
  obtain ⟨k1, k2, k3⟩ := key γ hγ φ hφ
  refine ⟨k1, k2, fun ψ hψ => ⟨k3 ψ hψ, ?_, fun x hx => eq_of_thA_eq idx hs hx hφ hψ⟩,
    fun a => ?_, ?_, fun γ' hγ' => ?_, fun y => ?_⟩
  · obtain ⟨l1, l2, -⟩ := key γ hγ ψ hψ
    refine wG_eq idx hs hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 l1).1 fun x hx => ?_
    rw [thA_add idx hs (hγ.lact_mem hx) k1 l1, thA_add idx hs hx hφ hψ, k2 x hx, l2 x hx]
  · refine wG_eq idx hs hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 k1).2.1 a) fun x hx => ?_
    rw [thA_smul, thA_smul, k2 x hx]
  · exact wG_eq idx hs (fun u v => by simp) hφ fun x _ => by rw [lact_one']
  · obtain ⟨l1, l2, -⟩ := key γ' hγ' _ k1
    refine wG_eq idx hs (isUn_mul hγ' hγ) l1 fun x hx => ?_
    rw [lact_mul', l2 _ (hγ.lact_mem hx), k2 x hx]
  · obtain ⟨-, -, -, hH⟩ := heisG_laws E r X g bas idx n hs hn
    refine wG_eq idx hs hγ (hH _ _ k1).1 fun x hx => ?_
    funext z
    have hy (k) : per X (lact γ x) ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) = per X x (y k) := by
      rw [← per_lact x hγ]
      congr 1
      ext j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [(hH _ _ k1).2.2.2.2 _ (hγ.lact_mem hx), (hH _ _ hφ).2.2.2.2 _ hx, k2 x hx]
    simp only [hy, herm_lact idx hs hγ hx]

end GlobalTheory.SW
end
