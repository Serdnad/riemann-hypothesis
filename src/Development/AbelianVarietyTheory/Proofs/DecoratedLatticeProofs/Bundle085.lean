module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HermTransversal

theorem isUnit_glue {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ} (e t : ι → R)
    (A : ι → Matrix (Fin n) (Fin n) R) (h1 : ∑ i, e i = 1) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (ht : ∀ i, t i * (A i).det = e i) : IsUnit (∑ i, e i • A i) := by
  classical
  have hee : ∀ i, e i * e i = e i := fun i => by
    have : e i * ∑ j, e j = e i * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_single i (fun j _ hj => ho i j (Ne.symm hj)) (by simp)
    rw [← this, h1, mul_one]
  have hs : ∀ i, e i • (∑ j, e j • A j) = e i • A i := fun i => by
    rw [Finset.smul_sum, Finset.sum_eq_single i]
    · rw [smul_smul, hee]
    · intro j _ hj
      rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
    · simp
  have hB : (∑ i, e i • A i) * (∑ j, (t j * e j) • (A j).adjugate) = 1 := by
    rw [Finset.mul_sum]
    have : ∀ j, (∑ i, e i • A i) * ((t j * e j) • (A j).adjugate) = e j • (1 : Matrix (Fin n) (Fin n) R) := fun j => by
      rw [Matrix.mul_smul, mul_smul, ← Matrix.smul_mul (e j), hs, Matrix.smul_mul, Matrix.mul_adjugate, smul_smul,
        smul_smul]
      congr 1
      rw [mul_right_comm, ht, hee]
    simp only [this]
    rw [← Finset.sum_smul, h1, one_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hB)

section Generic

variable {E R : Type} [Field E] [CharZero E] [CommRing R] {n : ℕ}

theorem exists_herm_notMem (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (ι : E →+* R) (τ : R →+* R)
    (hτι : ∀ z, τ (ι z) = ι (σ z)) (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) (M : Ideal R)
    (hM : M.IsMaximal) :
    ∃ x : Matrix (Fin n) (Fin n) E, (∀ i j, σ (x i j) = x j i) ∧
      (c * x.map ι + d).det * τ (c * x.map ι + d).det ∉ M := by
  letI := Ideal.Quotient.field M
  let π₀ : R →+* R ⧸ M := Ideal.Quotient.mk M
  let φ : E →+* R ⧸ M := π₀.comp ι
  let π := π₀.mapMatrix (m := Fin n)
  let ψ := (π₀.comp τ).mapMatrix (m := Fin n)
  have h1 : π c * π p + π d * π q = 1 := by rw [← map_mul, ← map_mul, ← map_add (f := _), h, map_one]
  have h2 : ψ c * ψ p + ψ d * ψ q = 1 := by rw [← map_mul, ← map_mul, ← map_add (f := _), h, map_one]
  obtain ⟨y, hy⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h1
  obtain ⟨y', hy'⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h2
  obtain ⟨x, hxs, hx1, hx2⟩ := GlobalTheory.T.exists_hermitian_two_det_ne_zero E (R ⧸ M) σ φ δ hδ hσδ n _ _ _ _ _ _ hy hy'
  have hx : ∀ i j, σ (x i j) = x j i := fun i j => congrFun (congrFun hxs i) j
  refine ⟨x, hx, fun hmem => ?_⟩
  rcases hM.isPrime.mem_or_mem hmem with h' | h'
  · apply hx1
    have e : π₀ (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (π (c * x.map ι + d)).det = 0 at e
    rw [map_add (f := _), map_mul] at e
    exact e
  · apply hx2
    have e : (π₀.comp τ) (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (ψ (c * x.map ι + d)).det = 0 at e
    rw [map_add (f := _), map_mul] at e
    have e2 : ψ (x.map ι) = x.transpose.map φ := by
      funext i j
      change π₀ (τ (ι (x i j))) = π₀ (ι (x j i))
      rw [hτι, hx]
    rw [e2] at e
    exact e

theorem exists_herm_isUnit_generic {A : Type} [CommRing A] (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (ι : E →+* R) (τ : R →+* R) (hτι : ∀ z, τ (ι z) = ι (σ z)) (hττ : ∀ z, τ (τ z) = z)
    (a : A →+* R) (ha : Function.Injective a) (hτa : ∀ z, τ (a z) = a z) (hfix : ∀ y, τ y = y → ∃ z, a z = y)
    (k : A) (hk : k * 2 = 1)
    (hid : ∀ (κ : Type) [Fintype κ] (f s : κ → A), ∑ i, s i * f i = 1 → ∃ e t : κ → A,
      ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i)
    (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) R, (x.map τ)ᵀ = x ∧ IsUnit (c * x + d) := by
  classical
  let H := {x : Matrix (Fin n) (Fin n) E // ∀ i j, σ (x i j) = x j i}
  let u : H → R := fun x => (c * x.1.map ι + d).det
  let f : H → R := fun x => u x * τ (u x)
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, hx, hn⟩ := exists_herm_notMem σ δ hδ hσδ ι τ hτι c d p q h M hM
    exact hn (hle (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range f) := (Ideal.eq_top_iff_one _).1 htop
  obtain ⟨C, hC⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  have hC' : ∑ i : C.support, C i * f i = 1 := by
    rw [Finset.sum_coe_sort C.support (fun i => C i * f i)]
    exact hC
  have hf : ∀ x, τ (f x) = f x := fun x => by
    simp only [f]
    rw [map_mul, hττ, mul_comm]
  choose g hg using fun x => hfix (f x) (hf x)
  have hs : ∀ x, τ (C x + τ (C x)) = C x + τ (C x) := fun x => by
    rw [map_add (f := _), hττ, add_comm]
  choose s hs' using fun x => hfix _ (hs x)
  have h2 : ∑ i : C.support, s i * g i = 2 := by
    apply ha
    have hc := congrArg τ hC'

    rw [map_sum, map_one] at hc
    simp only [map_mul τ, hf] at hc

    rw [map_sum, map_ofNat]
    simp only [map_mul, hg, hs', add_mul]
    rw [Finset.sum_add_distrib, hC', hc, one_add_one_eq_two]
  have h3 : ∑ i : C.support, (k * s i) * g i = 1 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, hk]
  obtain ⟨e, t, he1, heo, het⟩ := hid C.support (fun i => g i) _ h3
  have ha1 : ∑ i, a (e i) = 1 := by rw [← map_sum, he1, map_one]
  refine ⟨∑ i : C.support, a (e i) • i.1.1.map ι, ?_, ?_⟩
  · ext i j

    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    map_mul, hτa, hτι]
    exact Finset.sum_congr rfl fun x _ => by rw [x.1.2]
  · have : c * (∑ i : C.support, a (e i) • i.1.1.map ι) + d =
        ∑ i : C.support, a (e i) • (c * i.1.1.map ι + d) := by
      simp only [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ha1, one_smul, Finset.mul_sum]
      simp only [Matrix.mul_smul]
    rw [this]
    refine isUnit_glue _ (fun i => a (t i) * τ (u i)) _ ha1 (fun i j hij => ?_) (fun i => ?_)
    · rw [← map_mul, heo i j hij, map_zero]
    · rw [← het i, map_mul, hg, mul_assoc, mul_comm (τ (u i))]

end Generic

theorem cA_algebraMap {D : D7} (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.FinTranslate.cA_smul, map_one]

theorem algebraMap_inj {D : D7} : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem half_mul_two {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] :
    algebraMap F A (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F A) 2, ← map_mul]
  simp

theorem exists_herm_isUnit (D : D7) (n : ℕ) (c d p q : Mx D n n) (h : c * p + d * q = 1) :
    ∃ x : Mx D n n, GlobalTheory.MixModel.adj x = x ∧ IsUnit (c * x + d) :=
  exists_herm_isUnit_generic (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (incA D) (cA D) GlobalTheory.DualPairCheck.cA_incA GlobalTheory.DualPairCheck.cA_cA
    (algebraMap (AF D.host.F) (AE D)) algebraMap_inj cA_algebraMap
    (fun y hy => GlobalTheory.DetRootRows.exists_baseRing_of_conjugation_fixed_tensor D.sp.cm.sig
      (fun x => (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])) y hy)
    (algebraMap D.host.F (AF D.host.F) (1 / 2)) half_mul_two (GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' D.host.F) c d p q h

end GlobalTheory.HermTransversal

end
end

section

open MeasureTheory GlobalTheory.Grow GlobalTheory.Tw
open scoped ENNReal

namespace GlobalTheory.EvalAbs

theorem lintegral_eq_of_integral {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m₁ : Measure α} {m₂ : Measure β} {a : α → γ} {b : β → γ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ f : γ → ℂ, Measurable f → (Integrable (fun x => f (a x)) m₁ ↔ Integrable (fun y => f (b y)) m₂) ∧
      (Integrable (fun y => f (b y)) m₂ → ∫ x, f (a x) ∂m₁ = ∫ y, f (b y) ∂m₂))
    (F : γ → ℝ≥0∞) (hF : Measurable F) : ∫⁻ x, F (a x) ∂m₁ = ∫⁻ y, F (b y) ∂m₂ := by
  have e : m₁.map a = m₂.map b := by
    ext A hA
    rw [Measure.map_apply ha hA, Measure.map_apply hb hA]
    obtain ⟨h1, h2⟩ := h (A.indicator fun _ => 1) (measurable_const.indicator hA)
    have e1 : (fun x => A.indicator (fun _ => (1 : ℂ)) (a x)) = (a ⁻¹' A).indicator fun _ => 1 := rfl
    have e2 : (fun x => A.indicator (fun _ => (1 : ℂ)) (b x)) = (b ⁻¹' A).indicator fun _ => 1 := rfl
    rw [e1, e2, integrable_indicator_iff (ha hA), integrable_indicator_iff (hb hA), integrableOn_const_iff,
      integrableOn_const_iff] at h1
    rw [e1, e2, integrable_indicator_iff (hb hA), integrableOn_const_iff, integral_indicator (ha hA),
      integral_indicator (hb hA)] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter, Complex.real_smul, mul_one, Complex.ofReal_inj] at h1 h2
    by_cases hf : m₂ (b ⁻¹' A) < ∞
    · exact (ENNReal.toReal_eq_toReal_iff' (h1.2 hf).ne hf.ne).1 (h2 hf)
    · rw [not_lt_top_iff.1 hf, not_lt_top_iff.1 (fun h' => hf (h1.1 h'))]
  rw [← lintegral_map hF ha, e, lintegral_map hF hb]

theorem setLIntegral_mul_right {R : Type} [Group R] [MeasurableSpace R] [MeasurableMul R] {μ : Measure R}
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup R} [Countable Γ] {𝓡 : Set R}
    (h : IsFundamentalDomain Γ 𝓡 μ) (q : R → ℝ≥0∞) (hq : ∀ γ ∈ Γ, ∀ r, q (γ * r) = q r) (m : R) :
    ∫⁻ r in 𝓡, q (r * m) ∂μ = ∫⁻ r in 𝓡, q r ∂μ := by
  have hp : MeasurePreserving (· * m) μ μ := measurePreserving_mul_right μ m
  have h2 : IsFundamentalDomain Γ ((· * m) ⁻¹' 𝓡) μ :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h.setLIntegral_eq h2 (fun r => q (r * m)) fun γ r => by
    rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hq _ γ.2 _]
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight m).measurableEmbedding q 𝓡

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {R Γ : Subgroup G} {μR : Measure R} [μR.IsHaarMeasure] [μR.IsInvInvariant] {𝓡 : Set R} {𝓑 : Set G}

theorem exists_quotientIntegrable_of_le_mean (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ) {K : G → ℝ≥0∞}
    (hK : Measurable K) (hKΓ : ∀ γ ∈ Γ, ∀ g, K (γ * g) = K g) (hfin : ∫⁻ g in 𝓑, K g ∂μ < ∞) {f : G → ℂ}
    (hf : Measurable f) (hfR : ∀ r ∈ R, ∀ g, f (r * g) = f g) (hle : ∀ h, ‖f h‖ₑ ≤ ∫⁻ r in 𝓡, K (r * h) ∂μR) :
    ∃ z, IsQuotIntL1 μR μ f z := by
  refine ⟨_, (isQuotIntL1_iff hR hf).2 ⟨hfR, ⟨(measurable_comp_out hf hfR).aestronglyMeasurable, ?_⟩, rfl⟩⟩
  obtain ⟨S, hSm, hS⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable hSm
  have e : ∀ h : G, ∫⁻ r in 𝓡, K (r * h) ∂μR = ∫⁻ r : R, S.indicator K (r * h) ∂μR := fun h => by
    have hfd : IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR :=
      IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓR hS h)
    rw [h𝓡.setLIntegral_eq hfd (fun r : R => K (r * h)) fun γ r => by
      change K ((((γ : R) : G) * r) * h) = _
      rw [mul_assoc]; exact hKΓ _ γ.2 _, ← lintegral_indicator (hSh h)]
    rfl
  calc ∫⁻ c, ‖f (Quotient.out c)‖ₑ ∂quotMeas R μ μR
      ≤ ∫⁻ c, ∫⁻ r : R, S.indicator K (r * Quotient.out c) ∂μR ∂quotMeas R μ μR :=
        lintegral_mono fun c => (hle _).trans (e _).le
    _ = ∫⁻ g, S.indicator K g ∂μ := (isQuotMeasure_quotMeas hR _ (hK.indicator hSm)).symm
    _ = ∫⁻ g in 𝓑, K g ∂μ := by
        rw [lintegral_indicator hSm]
        exact hSfd.setLIntegral_eq h𝓑 K fun γ x => hKΓ _ γ.2 x
    _ < ∞ := hfin

theorem exists_quotientIntegrable_fold_unimodular (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ)
    {U : Type} [Group U] [MeasurableSpace U] [MeasurableMul U] [MeasurableInv U] {ν : Measure U} [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (j : U →* G) (hj : Measurable j) (hjR : ∀ u, j u ∈ R)
    {q : G → G → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (hqΓ : ∀ γ ∈ Γ, ∀ g, ∀ r ∈ R, q (γ * g) (γ * r) = q g r)
    (hqR : ∀ r ∈ R, ∃ v, ∀ g u, q g (r * j u) = q g (j (v * u)))
    (hfin : ∫⁻ g in 𝓑, ∫⁻ u, q g (j u) ∂ν ∂μ < ∞) {P : G → ℂ} (hP : Measurable P)
    (hPR : ∀ r ∈ R, ∃ v, ∀ g u, P (j u * (r * g)) = P (j (u * v) * g))
    (hle : ∀ h, ‖P h‖ₑ ≤ ∫⁻ r in 𝓡, q (r * h) r ∂μR) :
    ∃ z, IsQuotIntL1 μR μ (fun h => ((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)) z := by
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  have : ν.IsMulRightInvariant := by rw [← Measure.inv_eq_self ν]; infer_instance
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hU : ∀ r ∈ R, ∀ g, ∫⁻ u, q g (r * j u) ∂ν = ∫⁻ u, q g (j u) ∂ν := fun r hr g => by
    obtain ⟨v, hv⟩ := hqR r hr
    simp only [hv]
    exact lintegral_mul_left_eq_self (fun u => q g (j u)) v
  refine exists_quotientIntegrable_of_le_mean hΓR hR h𝓡 h𝓑 (K := fun g => ∫⁻ u, q g (j u) ∂ν) ?_ (fun γ hγ g => ?_) hfin ?_
    (fun r hr g => ?_) fun h => ?_
  · exact (hq.comp (measurable_fst.prodMk (hj.comp measurable_snd))).lintegral_prod_right'
  · rw [← hU γ⁻¹ (inv_mem (hΓR hγ)) g]
    refine lintegral_congr fun u => ?_
    rw [← hqΓ γ hγ g _ (mul_mem (inv_mem (hΓR hγ)) (hjR u)), mul_inv_cancel_left]
  · refine Complex.measurable_ofReal.comp (StronglyMeasurable.measurable ?_)
    exact (hP.comp ((hj.comp measurable_snd).mul measurable_fst)).norm.stronglyMeasurable.integral_prod_right'
  · obtain ⟨v, hv⟩ := hPR r hr
    simp only [hv]
    rw [integral_mul_right_eq_self (fun u => ‖P (j u * g)‖) v]
  · have hm : Measurable fun p : U × R => q (p.2 * h) (p.2 * j p.1⁻¹) :=
      hq.comp (((measurable_subtype_coe.comp measurable_snd).mul_const h).prodMk
        ((measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst.inv)))
    calc ‖((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)‖ₑ = ‖∫ u, ‖P (j u * h)‖ ∂ν‖ₑ := by
          simp [eNorm_eq_nnNorm]
      _ ≤ ∫⁻ u, ‖‖P (j u * h)‖‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ∫⁻ r in 𝓡, q (r * h) (r * j u⁻¹) ∂μR ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [enorm_norm]
          refine (hle _).trans (le_of_eq ?_)
          rw [← setLIntegral_mul_right h𝓡 (fun r : R => q (r * h) (r * j u⁻¹)) (fun γ hγ r => by
            simp only [Subgroup.coe_mul, mul_assoc]
            exact hqΓ _ hγ _ _ (mul_mem r.2 (hjR _))) ⟨j u, hjR u⟩]
          simp only [Subgroup.coe_mul, mul_assoc, map_inv, mul_inv_cancel, mul_one]
      _ = ∫⁻ r in 𝓡, ∫⁻ u, q (r * h) (r * j u⁻¹) ∂ν ∂μR := lintegral_lintegral_swap hm.aemeasurable
      _ = _ := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_inv_eq_self (μ := ν) fun u => q (r * h) (r * j u), hU r r.2]

end

end GlobalTheory.EvalAbs
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
end
