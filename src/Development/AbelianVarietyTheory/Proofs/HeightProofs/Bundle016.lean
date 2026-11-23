module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
import Formalism.RealPlaceAnalysis.Bundle004
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem _root_.GlobalTheory.T.field_size_adjoin_kth_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  first | exact @GlobalTheory.FieldSize.sz_sup_adjoin_root | exact GlobalTheory.FieldSize.sz_sup_adjoin_root | (intros; apply GlobalTheory.FieldSize.sz_sup_adjoin_root <;> assumption)
end

section

open Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompactDualUnique

theorem isOmegaLeb_unique {P Q : ℕ} {lam lam' : Measure (lieU P Q)}
    (h : IsOmegaLeb lam) (h' : IsOmegaLeb lam') : lam = lam' := by
  haveI : BorelSpace (lieU P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, lam = t • lam' := ⟨_, Measure.isAddLeftInvariant_eq_smul lam lam'⟩
  have hp : lam.prod lam = (t * t) • lam'.prod lam' := by
    rw [ht, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hf : AEMeasurable (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))
      (lam'.prod lam') := by
    apply Continuous.aemeasurable
    apply continuous_pi fun ij => ?_
    simp only [entries, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hc : Continuous (fun x : lieU P Q =>
        (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
      (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)
    exact (hc.comp continuous_fst).add (continuous_const.mul (hc.comp continuous_snd))
  rw [hp, Measure.map_smul _ hf, h2'] at h2
  have h3 := congrArg (fun m : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) =>
    m (Metric.ball 0 1)) h2
  simp only [Measure.smul_apply] at h3
  have hpos : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h4 : ((t * t : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    exact (ENNReal.mul_left_inj hpos hfin).1 (h3.trans (one_mul _).symm)
  have h5 : t * t = 1 := by exact_mod_cast h4
  have h6 : t = 1 := by
    have h7 : (t : ℝ) * t = 1 := by exact_mod_cast h5
    have h8 : (0 : ℝ) ≤ t := t.2
    have : (t : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [ht, h6, one_smul]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ℝ≥0∞}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, h1, h2⟩ := h
  obtain ⟨lam', h1', h2'⟩ := h'
  obtain rfl := isOmegaLeb_unique h1 h1'
  exact tendsto_nhds_unique h2 h2'

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (t : ℝ≥0)
    (h : OmegaDensity μ c) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, h1, h2⟩ := h
  refine ⟨lam, h1, ?_⟩
  have := ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞)) h2 (Or.inr ENNReal.coe_ne_top)
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem exists_eq_smul {P Q : ℕ} (μ ν : Measure (UpqT P Q)) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ∃ t : ℝ≥0, μ = t • ν := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul μ ν⟩

theorem eq_cd (cd : CDHaar) (P Q : ℕ) (ν : Measure (UpqT P Q)) (νc : Measure (UpqT (P + Q) 0))
    (c : ENNReal) (hν : ν.IsHaarMeasure) (hνc : νc.IsHaarMeasure) (hp : IsProbabilityMeasure νc)
    (_h0 : c ≠ 0) (_ht : c ≠ ⊤) (h1 : OmegaDensity ν c) (h2 : OmegaDensity νc c) :
    ν = cd.cd P Q := by
  haveI := cd.haar P Q
  haveI := cd.haar (P + Q) 0
  haveI := cd.prob (P + Q)
  obtain ⟨c', h0', ht', h1', h2'⟩ := cd.trick P Q
  obtain ⟨s, hs⟩ := exists_eq_smul νc (cd.cd (P + Q) 0)
  have hs1 : s = 1 := by
    have := congrArg (fun m : Measure (UpqT (P + Q) 0) => m Set.univ) hs
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [hs1, one_smul] at hs
  rw [hs] at h2
  obtain rfl := omegaDensity_unique h2 h2'
  obtain ⟨t, ht⟩ := exists_eq_smul ν (cd.cd P Q)
  have h3 := omegaDensity_smul t h1'
  rw [← ht] at h3
  have h4 := omegaDensity_unique h3 h1
  have h5 : (t : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0' ht').1 (h4.trans (one_mul _).symm)
  have h6 : t = 1 := by exact_mod_cast h5
  rw [ht, h6, one_smul]

end GlobalTheory.CompactDualUnique
end
end

section

open NumberField IsDedekindDomain IsLocalRing Polynomial

namespace GlobalTheory.QNorm

theorem exists_eq_sq_sub_mul_sq_finite {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0)
    {δ : k} (hδ : δ ≠ 0) (u : k) : ∃ a b : k, u = a ^ 2 - δ * b ^ 2 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hc
  have hf : (X ^ 2 : k[X]).degree = 2 := by simp
  have hg : (-(C δ) * X ^ 2 - C u : k[X]).degree = 2 := by
    have h1 : (-(C δ) * X ^ 2 : k[X]).degree = 2 := by simp [hδ]
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact degree_C_le.trans_lt (by norm_num)), h1]
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination -hab

theorem exists_integral_sq_sub_mul_sq_of_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ u : v.adicCompletion F), Valued.v (2 : v.adicCompletion F) = 1 → Valued.v δ = 1 → Valued.v u = 1 → ∃ x ∈ v.adicCompletionIntegers F, ∃ y ∈ v.adicCompletionIntegers F, u = x ^ 2 - δ * y ^ 2 := by
  intro F _ _ v δ u h2 hδ hu
  set O := v.adicCompletionIntegers F with hO
  have hmem : ∀ x : v.adicCompletion F, x ∈ O ↔ Valued.v x ≤ 1 := by
    intro x; rw [hO]; exact HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hval1 : ∀ z : O, IsUnit z → Valued.v (z : v.adicCompletion F) = 1 := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    have h1 : Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hw]
      simp
    have hz1 := (hmem _).1 z.2
    have hw1 := (hmem _).1 w.2
    refine le_antisymm hz1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) := h1.symm
      _ ≤ Valued.v (z : v.adicCompletion F) * 1 := mul_le_mul_right hw1 _
      _ = _ := mul_one _
  have : Finite (IsLocalRing.ResidueField O) := SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres_ne : ∀ z : O, Valued.v (z : v.adicCompletion F) = 1 → IsLocalRing.residue O z ≠ 0 := by
    intro z hz
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    have hz0 : (z : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    refine IsUnit.of_mul_eq_one (a := z) ⟨(z : v.adicCompletion F)⁻¹, (hmem _).2 (by rw [map_inv₀, hz, inv_one])⟩ ?_
    exact Subtype.ext (by simp [hz0])
  let uO : O := ⟨u, (hmem _).2 hu.le⟩
  let δO : O := ⟨δ, (hmem _).2 hδ.le⟩
  have hc2 : ((2 : O) : v.adicCompletion F) = 2 := map_ofNat O.subtype 2
  have h2O : IsLocalRing.residue O (2 : O) ≠ 0 := hres_ne 2 (by rw [hc2]; exact h2)
  have hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by rwa [map_ofNat] at h2O
  obtain ⟨a, b, hab⟩ := exists_eq_sq_sub_mul_sq_finite hk2 (hres_ne δO hδ) (IsLocalRing.residue O uO)
  obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective b
  let N : O := a' ^ 2 - δO * b' ^ 2
  have hresN : IsLocalRing.residue O N = IsLocalRing.residue O uO := by
    simp only [N, map_sub, map_mul, map_pow]; exact hab.symm
  have hvN : Valued.v (N : v.adicCompletion F) = 1 :=
    hval1 N ((IsLocalRing.residue_ne_zero_iff_isUnit N).1 (hresN ▸ hres_ne uO hu))
  have hN0 : (N : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hvN; exact zero_ne_one hvN
  have hz1 : Valued.v (u / (N : v.adicCompletion F)) = 1 := by rw [map_div₀, hu, hvN, div_one]
  let z : O := ⟨u / (N : v.adicCompletion F), (hmem _).2 hz1.le⟩
  have hzN : z * N = uO := Subtype.ext (by
    change u / (N : v.adicCompletion F) * (N : v.adicCompletion F) = u
    field_simp)
  have hresz : IsLocalRing.residue O z = 1 := by
    have h := congrArg (IsLocalRing.residue O) hzN
    rw [map_mul, hresN] at h
    have hne : IsLocalRing.residue O uO ≠ 0 := hres_ne uO hu
    calc IsLocalRing.residue O z = IsLocalRing.residue O z * IsLocalRing.residue O uO / IsLocalRing.residue O uO := by
          field_simp
      _ = 1 := by rw [h, div_self hne]
  obtain ⟨s, hs⟩ := isSquare_of_isSquare_residue_odd F v h2 z hz1 ⟨1, by rw [hresz, mul_one]⟩
  have hvs : Valued.v s ≤ 1 := by
    by_contra hc
    push Not at hc
    have : Valued.v s ≤ Valued.v s * Valued.v s := by
      calc Valued.v s = Valued.v s * 1 := (mul_one _).symm
        _ ≤ Valued.v s * Valued.v s := mul_le_mul_right hc.le _
    rw [← map_mul, ← hs, hz1] at this
    exact absurd (hc.trans_le this) (lt_irrefl _)
  have ha' := (hmem _).1 a'.2
  have hb' := (hmem _).1 b'.2
  refine ⟨s * a', (hmem _).2 ?_, s * b', (hmem _).2 ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' hvs ha'
  · rw [map_mul]; exact mul_le_one' hvs hb'
  · have hNK : (N : v.adicCompletion F) = (a' : v.adicCompletion F) ^ 2 - δ * (b' : v.adicCompletion F) ^ 2 := by
      simp [N, δO]
    have hzK : (z : v.adicCompletion F) = u / (N : v.adicCompletion F) := rfl
    calc u = (z : v.adicCompletion F) * (N : v.adicCompletion F) := by rw [hzK]; field_simp
      _ = _ := by rw [hs, hNK]; ring

end GlobalTheory.QNorm
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_normDiscrete_ne_zero_of_isDedekindDomain {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap S L b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective S L (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg
  have hI : Ideal.span {a * b} ≠ (⊥ : Ideal S) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 hb0
  refine ((Ideal.finite_factors hI).image (ValPl.addv L)).subset ?_
  rintro w ⟨hw, h0, hwg⟩
  let Q : Ideal S :=
    { carrier := {b | 0 < w (algebraMap S L b)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
        exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
  have hz : ∀ s : S, s ∉ Q → w (algebraMap S L s) = 0 := fun s hs =>
    le_antisymm (not_lt.1 (hs : ¬ 0 < w (algebraMap S L s))) (h0 s)
  have hprime : Q.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : S) ∈ Q := htop ▸ Submodule.mem_top
      simp [Q] at h1
    · change 0 < w (algebraMap _ L (a * b)) at hab
      rw [map_mul, AddValuation.map_mul] at hab
      by_contra hno
      rw [not_or] at hno
      rw [hz a hno.1, hz b hno.2, add_zero] at hab
      exact lt_irrefl _ hab
  have hab : a * b ∈ Q := by
    by_contra hno
    have ha := hz a fun h => hno (Q.mul_mem_right _ h)
    have hb := hz b fun h => hno (Q.mul_mem_left _ h)
    have h := w.map_mul (algebraMap S L a / algebraMap S L b) (algebraMap S L b)
    rw [div_mul_cancel₀ _ hb1, ha, hb, add_zero] at h
    exact hwg h.symm
  have hne : Q ≠ ⊥ := fun h => mul_ne_zero ha0 hb0 (by rwa [h, Ideal.mem_bot] at hab)
  refine ⟨⟨Q, hprime, hne⟩, ?_, (ValPl.eq_addv _ w hw h0 (fun s => Iff.rfl)).symm⟩
  exact Ideal.dvd_span_singleton.mpr hab


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem finite_zeros_poles_of_trdeg_one :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by
  open scoped IntermediateField.algebraAdjoinAdjoin in
  intro F Ω _ _ _ _ t hfg htr ht g hg
  have hind : AlgebraicIndependent F (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis F (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin F ({t} : Set Ω)) Ω := by
    have h := hbasis.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType F Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType (IntermediateField.adjoin F ({t} : Set Ω)) Ω := .of_comp F _ _
  have : FiniteDimensional (IntermediateField.adjoin F ({t} : Set Ω)) Ω :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsPrincipalIdealRing (Algebra.adjoin F ({t} : Set Ω)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental F t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental F t ht).surjective
  have : IsDedekindDomain (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) :=
    integralClosure.isDedekindDomain _ (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  have : IsFractionRing (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  refine (finite_normDiscrete_ne_zero_of_isDedekindDomain
    (S := integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) g hg).subset ?_
  rintro w ⟨hw, hF, hwt, hwg⟩
  refine ⟨hw, fun b => ?_, hwg⟩
  have hA : ∀ x ∈ Algebra.adjoin F ({t} : Set Ω), x ∈ vRing w := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact hwt
    | algebraMap r =>
      by_cases hr : r = 0
      · rw [hr, map_zero]; exact zero_mem _
      · exact (hF r hr).ge
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hb : IsIntegral (Algebra.adjoin F ({t} : Set Ω)) (b : Ω) := b.2
  let : Algebra (Algebra.adjoin F ({t} : Set Ω)) (vRing w) :=
    ((algebraMap (Algebra.adjoin F ({t} : Set Ω)) Ω).codRestrict (vRing w)
      (fun x => hA x x.2)).toAlgebra
  have : IsScalarTower (Algebra.adjoin F ({t} : Set Ω)) (vRing w) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) (b : Ω) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  change 0 ≤ w (b : Ω)
  rw [← hy]
  exact y.2

end GlobalTheory
end
