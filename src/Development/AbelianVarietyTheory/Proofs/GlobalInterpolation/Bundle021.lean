module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle014
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaConstEqEtaWeberSqOfTripleProduct
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAddition
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QFormCount
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ hμ

end GlobalTheory
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space : ModulusClause := by
  first | exact @GlobalTheory.WeilCriterion.modulusClause | exact GlobalTheory.WeilCriterion.modulusClause | (intros; apply GlobalTheory.WeilCriterion.modulusClause <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompactDualQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def sg {P Q : ℕ} : Fin P ⊕ Fin Q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

def SignCompat (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Prop :=
  ∀ i, sg (e (some i)) = sg i

def l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖

def gauge (g : UpqT P Q) : ℝ := l1 (UpqT.mat g - 1)

def baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Sp P Q := Pi.single (e none) 1

def ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖

def tanGauge (t : ℝ × Sp P' Q') : ℝ := |t.1| + 2 * ∑ i, ‖t.2 i‖

def polarPt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim
    ((Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I)) t.2

def IsBlockEmb (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  ∀ g, UpqT.mat (j g) (e none) (e none) = 1 ∧ (∀ b, UpqT.mat (j g) (e none) (e (some b)) = 0) ∧
    (∀ a, UpqT.mat (j g) (e (some a)) (e none) = 0) ∧
    ∀ a b, UpqT.mat (j g) (e (some a)) (e (some b)) = UpqT.mat g a b

def expBall (P Q : ℕ) (r : ℝ) : Set (UpqT P Q) :=
  {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
    NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

theorem sg_eq (i : Fin P ⊕ Fin Q) : sg i = 1 ∨ sg i = -1 := by
  rcases i with i | i <;> simp [sg]

theorem sg_ne_zero (i : Fin P ⊕ Fin Q) : sg i ≠ 0 := by
  rcases sg_eq i with h | h <;> rw [h] <;> norm_num

theorem qf_eq_sum (x : Sp P Q) : qf x = ∑ i, sg i * Complex.normSq (x i) := by
  simp [qf, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem qf_baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    qf (baseVec e) = sg (e none) := by
  rw [qf_eq_sum, Finset.sum_eq_single (e none)]
  · simp [baseVec]
  · intro b _ hb; simp [baseVec, hb]
  · simp

theorem card_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : P + Q = P' + Q' + 1 := by
  simpa using (Fintype.card_congr e).symm

theorem polarPt_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') :
    polarPt e t (e none) =
      (Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I) := by
  simp [polarPt]

theorem polarPt_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : polarPt e t (e (some i)) = t.2 i := by
  simp [polarPt]

theorem weightAbsEntrySum_nonneg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : 0 ≤ l1 Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_matrixEntryAbsSum : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm

theorem continuous_gauge : Continuous (gauge : UpqT P Q → ℝ) :=
  continuous_matrixEntryAbsSum.comp
    ((Units.continuous_val.comp continuous_subtype_val : Continuous UpqT.mat).sub continuous_const)

theorem ptGauge_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) :
    0 ≤ ptGauge e y := by
  unfold ptGauge; positivity

theorem continuous_ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by
  unfold ptGauge; fun_prop

theorem tanGauge_nonneg (t : ℝ × Sp P' Q') : 0 ≤ tanGauge t := by
  unfold tanGauge; positivity

theorem continuous_tanGauge : Continuous (tanGauge : ℝ × Sp P' Q' → ℝ) := by
  unfold tanGauge; fun_prop

theorem tendsto_div_of_squeeze {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by
  have key : ∀ t : ℝ, 0 < t →
      Tendsto (fun r => F (t * r) / V r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ n) * c)) := by
    intro t ht
    have h1 : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos ht hr
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) (hF.comp h1)
      (Or.inr ENNReal.ofReal_ne_top)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h0 : ENNReal.ofReal (t ^ n) ≠ 0 := by simpa using pow_pos ht n
    simp only [Function.comp, hV t r ht hr]
    rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have lim : ∀ u : ℝ → ℝ, ContinuousAt u 1 → u 1 = 1 →
      Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n) * c) (𝓝[>] 1) (𝓝 c) := by
    intro u hu h1
    have h3 : Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n)) (𝓝 1) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.continuousAt.comp (hu.pow n)).tendsto
      simp only [Function.comp, Pi.pow_apply, h1, one_pow, ENNReal.ofReal_one] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := c) h3 (Or.inr hc)
    rw [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t⁻¹) (continuousAt_inv₀ one_ne_zero) inv_one).eventually
      (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t⁻¹ (inv_pos.2 (by linarith))).eventually (lt_mem_nhds h1), hA t ht]
      with r h3 h4 using h3.trans_le (ENNReal.div_le_div_right h4.1 _)
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t) continuousAt_id rfl).eventually
      (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t (by linarith)).eventually (gt_mem_nhds h1), hA t ht]
      with r h3 h4 using (ENNReal.div_le_div_right h4.2 _).trans_lt h3

end GlobalTheory.CompactDualQuot
end
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.UnitVectorStabEq

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (s : A →+* A) (J : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J y z = (s ∘ y) ⬝ᵥ (J *ᵥ z) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]

theorem hform_mulVec (s : A →+* A) (J g : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J (g *ᵥ y) (g *ᵥ z) = Formalism.UG.hform s (Formalism.UG.cT s g * J * g) y z := by
  have h : s ∘ (g *ᵥ y) = (g.map s) *ᵥ (s ∘ y) := by
    funext i
    exact RingHom.map_mulVec s g y i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (s ∘ y), Matrix.vecMul_transpose]

theorem hform_sub_smul (s : A →+* A) (J : Matrix n n A) (x y : n → A) (a : A) :
    Formalism.UG.hform s J x (y - a • x) = Formalism.UG.hform s J x y - a * Formalism.UG.hform s J x x := by
  simp only [hform_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

end General

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem mem_stabVec (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

theorem mem_stabLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (g : HA (Fv F v) σ J) :
    g ∈ stabLat σ J v L ↔ ∀ y, y ∈ L ↔ act σ J v g y ∈ L := Iff.rfl

theorem mem_perpLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x y : Fin M → Ev F E v) :
    y ∈ perpLat σ J v L x ↔ hR (Fv F v) σ J x y = 0 ∧ y ∈ L := Iff.rfl

theorem hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by
  unfold hR act
  rw [hform_mulVec]
  congr 1
  exact (show HR (Fv F v) σ J from g).2

theorem act_sub_smul (g : HA (Fv F v) σ J) (x y : Fin M → Ev F E v) (a : Ev F E v) :
    act σ J v g (y - a • x) = act σ J v g y - a • act σ J v g x := by
  unfold act
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem mem_iff (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (hL : IsSDLat σ J v L)
    (x : Fin M → Ev F E v) (hx : x ∈ L) (b : Ev F E v) (hb : b ∈ OEv F E v)
    (hb1 : hR (Fv F v) σ J x x * b = 1) (y : Fin M → Ev F E v) :
    y ∈ L ↔ (b * hR (Fv F v) σ J x y ∈ OEv F E v ∧
      y - (b * hR (Fv F v) σ J x y) • x ∈ perpLat σ J v L x) := by
  have hs : ∀ a ∈ OEv F E v, a • x ∈ L := fun a ha => L.smul_mem (⟨a, ha⟩ : OEv F E v) hx
  constructor
  · intro hy
    have ha : b * hR (Fv F v) σ J x y ∈ OEv F E v := mul_mem hb (((hL.2.2 y).1 hy).2 x hx)
    refine ⟨ha, (mem_perpLat σ J v L x _).2 ⟨?_, L.sub_mem hy (hs _ ha)⟩⟩
    have h : hR (Fv F v) σ J x (y - (b * hR (Fv F v) σ J x y) • x) =
        hR (Fv F v) σ J x y - (b * hR (Fv F v) σ J x y) * hR (Fv F v) σ J x x :=
      hform_sub_smul _ _ _ _ _
    rw [h]
    linear_combination (- hR (Fv F v) σ J x y) * hb1
  · rintro ⟨ha, hy⟩
    have := L.add_mem ((mem_perpLat σ J v L x _).1 hy).2 (hs _ ha)
    rwa [sub_add_cancel] at this

end Place

theorem stabLat_inf_stabVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), IsSDLat σ J v L → ∀ x ∈ L, (∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1) → stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x := by
  intro F E _ _ _ _ _ σ _ M J _ v L hL x hx ⟨b, hb, hb1⟩
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_left fun hg => ?_
  rw [mem_stabVec] at hg
  have hh : ∀ y, hR (Fv F v) σ J x (act σ J v g y) = hR (Fv F v) σ J x y := by
    intro y
    rw [← hR_act σ J v g x y, hg]
  rw [mem_stabLat, mem_stabLat]
  constructor
  · intro h y
    rw [mem_perpLat, mem_perpLat, hh, h y]
  · intro h y
    rw [mem_iff σ J v L hL x hx b hb hb1 y, mem_iff σ J v L hL x hx b hb hb1 (act σ J v g y), hh,
      h (y - _), act_sub_smul, hg]

end GlobalTheory.UnitVectorStabEq
end
end

section

open Complex

theorem _root_.GlobalTheory.T.weberFunction_product_eq_sqrt_two : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ) := by
  first | exact @GlobalTheory.WeberProduct.weber_prod | exact GlobalTheory.WeberProduct.weber_prod | (intros; apply GlobalTheory.WeberProduct.weber_prod <;> assumption)
end

section

open Complex

theorem _root_.GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  first | exact @GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | exact GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | (intros; apply GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff <;> assumption)
end

section

open Complex

theorem _root_.GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ := by
  first | exact @GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | exact GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | (intros; apply GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct <;> assumption)
end

section

open Complex

theorem _root_.GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition : Formalism.L2.Th1.F.SgStarAdd → (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) → (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) → (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  first | exact @GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | exact GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of | (intros; apply GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  first | exact @GlobalTheory.Hk.theta_qForm | exact GlobalTheory.Hk.theta_qForm | (intros; apply GlobalTheory.Hk.theta_qForm <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.tsum_exp_mul_aChi_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  first | exact @GlobalTheory.Hk.LFam.exp_sum_bounds | exact GlobalTheory.Hk.LFam.exp_sum_bounds | (intros; apply GlobalTheory.Hk.LFam.exp_sum_bounds <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x → {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧ |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x| ≤ 10 * Real.sqrt x := by
  first | exact @GlobalTheory.Hk.qForm_count | exact GlobalTheory.Hk.qForm_count | (intros; apply GlobalTheory.Hk.qForm_count <;> assumption)
end
