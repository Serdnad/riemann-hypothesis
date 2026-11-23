module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_local_sqrt_nontrivial (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  have hd : HasStrictDerivAt (fun x : K => x * x) 2 1 := by
    have := (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
    have h11 : (1 : K) * id 1 + id 1 * 1 = 2 := by simp; norm_num
    rw [h11] at this
    exact this
  have hF := hd.hasStrictFDerivAt_equiv h2
  let e := hF.toOpenPartialHomeomorph
  have he : ∀ x, e x = x * x := fun x => rfl
  have h1 : (1 : K) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  have h1' : e 1 = 1 := by rw [he, mul_one]
  refine ⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩
  · have := e.left_inv h1
    rwa [h1'] at this
  · intro u hu
    rw [← he]; exact e.right_inv hu

theorem exists_local_sqrt (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  by_cases h : ∃ x : K, 1 < ‖x‖
  · let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := h }
    exact exists_local_sqrt_nontrivial K h2
  · push Not at h
    refine ⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1,
      continuousOn_const, rfl, fun u hu => ?_⟩
    rw [mem_ball_iff_norm] at hu
    by_contra hne
    have h0 : u - 1 ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])
    have h3 := h (u - 1)⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact absurd hu (not_lt.2 h3)

theorem nice_field (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) : Nice K :=
  ⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩

theorem nice_pi {ι : Type} [Fintype ι] (K : ι → Type) [∀ i, NormedField (K i)]
    [∀ i, CompleteSpace (K i)] (h2 : ∀ i, (2 : K i) ≠ 0) : Nice (∀ i, K i) := by
  refine ⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩
  choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)
  refine ⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i,
    fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩
  exact continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn
    fun x hx => hx i trivial

theorem nice_ainf_fv : ∀ (F : Type) [Field F] [NumberField F],
    Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  intro F _ _
  refine ⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩
  · have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero
  · have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeProdFormula

theorem card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
  have ha1 : a ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
  have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
    (by simpa using ha)
  have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
      (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
    change _ ↔ _ ≤ Valued.v a
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  rw [pow_one, ← e] at h
  exact h

theorem modu_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) : (modu (Fv F v) x : ℝ) = ‖x‖ := by
  have hu : IsUnit x := hx.isUnit
  have hv : Valued.v x ≠ 0 := by simpa using hx
  let μ : Measure (Fv F v) := Measure.addHaar
  have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
    ext y
    rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
    rfl
  have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
  have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
    rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
      WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
    simp
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
    Fintype.card_unit, pow_one] at h
  have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
  rw [modu, dite_eq_left hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  congr 1

theorem distribHaarChar_pi_real (ι : Type) [Fintype ι] (u : (ι → ℝ)ˣ) :
    (distribHaarChar (ι → ℝ) u : ℝ) = ∏ i, |(u : ι → ℝ) i| := by
  have hu : ∀ i, (u : ι → ℝ) i ≠ 0 := fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero
  have hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]; simp
  have e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) =
      Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]
    have : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)
    rw [this]
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]
  · simp
  · rw [hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.addHaar_smul]
    rw [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
      ← Real.enorm_eq_ofReal_abs]
    rfl

theorem modu_infinite (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ainf F) (hx : IsUnit x) :
    (modu (Ainf F) x : ℝ) = ∏ w : InfinitePlace F, ‖x w‖ := by
  let r : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { r.toAddEquiv with
      continuous_toFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      continuous_invFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
          (continuous_apply w) }
  have h := GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit
    (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)
  rw [modu, dite_eq_left hx, ← h, distribHaarChar_pi_real]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)

theorem prod_modu_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  intro F _ _ _ e he
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) =
      FinitePlace.equivHeightOneSpectrum.symm v e := fun v => by
    rw [modu_finite F v _ ((map_ne_zero _).2 he)]
    rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      modu (Fv F v) (algebraMap F (Fv F v) e)).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport he).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_
    apply NNReal.coe_injective
    rw [hf]
    exact h
  refine ⟨hfin, NNReal.coe_injective ?_⟩
  have h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) =
      ∏ᶠ w : FinitePlace F, w e := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [← hf]
    exact (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin
  rw [NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)

end GlobalTheory.GaugeProdFormula
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeWittLoc

open Matrix Formalism.UG

theorem exists_quasiReflection {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin n → S) (c : S)
    (hc : c + s c = c * s c * hform s J w w) :
    ∃ g g' : Matrix (Fin n) (Fin n) S, g' * g = 1 ∧ cT s g * J = J * g' ∧
      ∀ z, g *ᵥ z = z - (c * hform s J w z) • w := by
  let r : Fin n → S := fun j => ∑ i, s (w i) * J i j
  have hr : ∀ z, r ⬝ᵥ z = hform s J w z := fun z => by
    simp only [r, dotProduct, hform, Finset.sum_mul]
    exact Finset.sum_comm
  let P : Matrix (Fin n) (Fin n) S := vecMulVec w r
  have hPP : P * P = hform s J w w • P := by
    ext i j
    rw [← hr]
    simp only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : cT s P * J = J * P := by
    ext i j
    have h1 : s (r i) = ∑ k, J i k * w k := by

      simp only [r, map_sum, map_mul, hs, hJ]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]
    calc ∑ k, s (w k) * s (r i) * J k j = s (r i) * r j := by
          simp only [r, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          rw [h1, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul,
      mul_comm (s c) c, ← hc, add_smul]
    abel
  · have : cT s (1 - c • P) = 1 - s c • cT s P := by
      ext i j
      simp [cT, Matrix.one_apply, eq_comm]
    rw [this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul,
      Matrix.mul_one]
  · rw [sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]
    congr 1
    ext i
    simp only [P, Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_unitary {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → S) (β v : S)
    (hx : hform s J x x = β) (hy : hform s J y y = β) (hv : v * s v = 1)
    (hD : IsUnit (β - v * hform s J y x)) :
    ∃ γ : GL (Fin n) S, cT s γ.1 * J * γ.1 = J ∧ γ.1 *ᵥ x = y := by
  have hsym : ∀ a b, s (hform s J a b) = hform s J b a := fun a b => by

    simp only [hform, map_sum, map_mul, hs, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hD.exists_left_inv
  have hβ : s β = β := by rw [← hx, hsym]
  have hc' : s c * (β - s v * hform s J x y) = 1 := by
    have := congrArg s hc
    rwa [map_mul, map_sub, map_mul, hsym, hβ, map_one] at this
  obtain ⟨g, g', h1, h2, h3⟩ := exists_quasiReflection s hs J hJ (x - s v • y) c (by
    rw [hl, hrr, hrr, hx, hy]
    linear_combination (-c) * hc' - s c * hc - c * s c * β * hv)
  have h4 : g * g' = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hv, h4, one_smul]
  · rw [smul_mul_smul_comm, mul_comm, hv, h1, one_smul]
  · have : cT s (v • g) = s v • cT s g := by
      ext i j
      simp [cT]
    show cT s (v • g) * J * (v • g) = J
    rw [this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul,
      Matrix.mul_one]
  · show (v • g) *ᵥ x = y
    rw [smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]

theorem exists_isUnit_sub {S : Type} [CommRing S] [Finite (MaximalSpectrum S)] (v : ℕ → S)
    (hv : ∀ k l, k ≠ l → IsUnit (v k - v l)) (β t : S) (hβ : IsUnit β) :
    ∃ k, IsUnit (β - v k * t) := by
  by_contra h
  push Not at h
  choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)
  obtain ⟨k, l, hkl, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))
  have he' : m k = m l := congrArg MaximalSpectrum.asIdeal he
  have h1 := hmem l
  rw [← he'] at h1
  have h2 : (v k - v l) * t ∈ m k := by
    have := (m k).sub_mem h1 (hmem k)
    convert this using 1
    ring
  have h3 : t ∈ m k := ((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2
  have h4 : β ∈ m k := by
    have := (m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)
    rwa [sub_add_cancel] at this
  exact (hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)

theorem exists_normOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k, a k * σ (a k) = 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | (apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)

theorem exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy
  have := hR'.1
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  obtain ⟨a, ha, hn⟩ := exists_normOne hcm
  obtain ⟨k, hk⟩ := exists_isUnit_sub (fun k => inclR R (a k))
    (fun k l hkl => by
      rw [← map_sub]
      exact (IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)
    (algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)
  obtain ⟨γ, h1, h2⟩ := exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J)
    (fun i j => by
      show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
      rw [hJ.1])
    (x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))
    (by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by
      show inclR R (a k) * inclR R (σ (a k)) = 1
      rw [← map_mul, hn, map_one])
    hk
  refine ⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h2

end GlobalTheory.GaugeWittLoc
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem modu_eq_modu_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ u k hu hk
  obtain ⟨-, -, h2, hc⟩ := h
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hc, hc, star_star]
  have hss : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = _
      rw [hσ]
  let b : Module.Basis (Fin 2) R (R ⊗[F] E) :=
    Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)
  have hku : IsUnit k := by
    have h1 : IsUnit (algebraMap R (R ⊗[F] E) k) := by
      rw [hk]; exact hu.mul (hu.map _)
    have h3 := h1.map (Algebra.norm R)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h3
    exact (isUnit_pow_iff two_ne_zero).1 h3
  refine ⟨hku, ?_⟩
  letI : StarRing (R ⊗[F] E) :=
    { star := sigR R σ
      star_involutive := hss
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add _ x y }
  haveI : ContinuousStar (R ⊗[F] E) := ⟨GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ⟩
  rw [modu, modu, dite_eq_left hu, dite_eq_left hku]
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm R (R ⊗[F] E) b.equivFun.symm
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap) hu.unit hku.unit hk

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_unit_pow_normV_sub_one' : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ),
    Valued.v ((y : v.adicCompletion E) - 1) < 1 →
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  first | exact @GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | exact GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | (intros; apply GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l, (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  first | exact @GlobalTheory.AdicCont.continuous_adic | exact GlobalTheory.AdicCont.continuous_adic | (intros; apply GlobalTheory.AdicCont.continuous_adic <;> assumption)
end
