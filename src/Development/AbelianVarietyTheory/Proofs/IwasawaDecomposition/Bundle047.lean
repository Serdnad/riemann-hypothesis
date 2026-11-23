module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

section

open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  first | exact @GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | exact GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | (intros; apply GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  first | exact @GlobalTheory.NormalDescent.exists_map_eq_charK | exact GlobalTheory.NormalDescent.exists_map_eq_charK | (intros; apply GlobalTheory.NormalDescent.exists_map_eq_charK <;> assumption)
end

section

open Matrix GlobalTheory.Mem.Lift

theorem _root_.GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  first | exact @GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | exact GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | (intros; apply GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.Ccr

theorem comm_comb {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module

theorem exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by
  let b : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by simp [mulVec_add, dotProduct_add])
    (fun r x y => by simp [mulVec_smul, dotProduct_smul])
    (fun x y y' => by simp [add_dotProduct])
    (fun r x y => by simp [smul_dotProduct])
  exact ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b), fun x y => rfl⟩

theorem im_self {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]

end GlobalTheory.Mem.Lift.Ccr


open GlobalTheory.Mem.Lift.Ccr in
theorem GlobalTheory.Mem.Lift.exists_isCCR_xOp_dOp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∃ x d : ι → Module.End ℂ (smS ρ), (∀ k f, (x k f).1 = xOp ρ k f.1) ∧ (∀ k f, (d k f).1 = dOp ρ H k f.1) ∧ IsCCR x d := by
  intro ι _ _ H hH hd B _ _ ρ hρ
  obtain ⟨om, hom⟩ := exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have key := GlobalTheory.T.heisenbergSmoothVector_derivative_calculus (ι → ℂ) B om ρ (fun x => by rw [hom, im_self hH]) hρ'
  let D : (ι → ℂ) → Module.End ℂ (smS ρ) := fun v =>
    { toFun := fun f => ⟨dH ρ v f.1, (key f.1 f.2).1 v⟩
      map_add' := fun f g => Subtype.ext (dH_add v f.2 g.2)
      map_smul' := fun a f => Subtype.ext (dH_smul v a f.2) }
  have hD : ∀ u v, D u * D v = D v * D u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u v
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := (key f.1 f.2).2.2.2.2 u v
    rw [hom, sub_eq_iff_eq_add'] at this
    exact this
  have hc : ∀ (u v : ι → ℂ) (s t : ℂ), (D u + s • D (I • u)) * (D v + t • D (I • v)) =
      (D v + t • D (I • v)) * (D u + s • D (I • u)) +
        (2 * π * I * ((1 + s * t) * (star v ⬝ᵥ H *ᵥ u).im + (s - t) * (star v ⬝ᵥ H *ᵥ u).re)) •
          (1 : Module.End ℂ (smS ρ)) := by
    intro u v s t
    rw [comm_comb _ _ _ _ s t _ _ _ _ (hD u v) (hD u (I • v)) (hD (I • u) v) (hD (I • u) (I • v))]
    congr 2
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  have hII : (1 : ℂ) + I * I = 0 := by simp
  refine ⟨fun k => D (Pi.single k 1) + (-I) • D (I • Pi.single k 1),
    fun l => (-(1 / (4 * π)) : ℂ) • (D (H⁻¹ *ᵥ Pi.single l 1) + I • D (I • H⁻¹ *ᵥ Pi.single l 1)),
    fun k f => ?_, fun k f => rfl, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [xOp, sub_eq_add_neg, ← neg_smul]
    rfl
  · beta_reduce
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc (Pi.single k 1), pair_inv hH hd, ← smul_sub, sub_add_cancel_left, ← neg_smul, smul_smul]
    by_cases h : k = l
    · simp only [h, if_true, one_im, one_re, ofReal_zero, ofReal_one]
      have hp : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (-(1 / (4 * π)) : ℂ) * -(2 * π * I * ((1 + -I * I) * 0 + (-I - I) * 1)) = 1 := by
        field_simp
        linear_combination (-4) * hII
      rw [this, one_smul]
    · simp [h]
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem exists_finset_close (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (N : ℕ) :
    ∃ F : Finset (v.adicCompletion L), ∀ x : v.adicCompletion L, Valued.v x ≤ 1 →
      ∃ f ∈ F, Valued.v (x - f) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L v
  set s : v.adicCompletion L := ((π ^ N : L) : v.adicCompletion L) with hsdef
  have hs : Valued.v s = WithZero.exp (-(N : ℤ)) := by
    rw [hsdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {y : v.adicCompletion L | Valued.v y < Valued.v s} := by
    have h := Valued.isOpen_ball (v.adicCompletion L) (Valued.v.restrict s)
    simpa [Valuation.restrict_lt_iff] using h
  obtain ⟨t, -, ht⟩ := (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers (F := L) v).elim_nhds_subcover
    (fun x => {y | Valued.v (y - x) < Valued.v s})
    (fun x _ => (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      show Valued.v (x - x) < Valued.v s
      rw [sub_self, map_zero, hs]
      exact zero_lt_iff.2 WithZero.exp_ne_zero))
  refine ⟨t, fun x hx => ?_⟩
  have hxO : x ∈ (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    by rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (ht hxO)
  exact ⟨f, hf, le_of_lt (hs ▸ hxf)⟩

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem relIndex_levSub_ne_zero (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) : (levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
  classical
  haveI : Finite S := hS.to_subtype
  choose F hF using fun v : S => exists_finset_close L v.1 N
  have hint : ∀ a : levSub L ∅ 0, ∀ v, Valued.v (compAt L v (a : (AdeleRing (𝓞 L) L)ˣ)) ≤ 1 :=
    fun a v => le_of_eq (a.2 v).1
  choose g hg hg' using fun (a : levSub L ∅ 0) (v : S) => hF v (compAt L v.1 a) (hint a v.1)
  let φ : levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0) → ((v : S) → (F v : Set (v.1.adicCompletion L))) :=
    fun q v => ⟨g q.out v, hg q.out v⟩
  have hφ : Function.Injective φ := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro w
    refine ⟨((q.out⁻¹ * q'.out).2 w).1, fun hw => ?_⟩
    have e1 : g q.out ⟨w, hw⟩ = g q'.out ⟨w, hw⟩ := congrArg Subtype.val (congrFun hqq ⟨w, hw⟩)
    have h1 := hg' q.out ⟨w, hw⟩
    have h2 := hg' q'.out ⟨w, hw⟩
    rw [e1] at h1
    set a : (AdeleRing (𝓞 L) L)ˣ := (q.out : (AdeleRing (𝓞 L) L)ˣ)
    set b : (AdeleRing (𝓞 L) L)ˣ := (q'.out : (AdeleRing (𝓞 L) L)ˣ)
    have hinv : Valued.v (compAt L w a⁻¹) = 1 := ((q.out⁻¹).2 w).1
    have hc : compAt L w a⁻¹ * compAt L w a = 1 := by rw [← compAt_mul, inv_mul_cancel, compAt_one]
    have e2 : compAt L w ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) - 1 =
        compAt L w a⁻¹ * ((compAt L w b - g q'.out ⟨w, hw⟩) - (compAt L w a - g q'.out ⟨w, hw⟩)) := by
      have : ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) = a⁻¹ * b := rfl
      rw [this, compAt_mul]
      linear_combination hc
    rw [e2, map_mul, hinv, one_mul]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  haveI : Finite (levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0)) := Finite.of_injective φ hφ
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem levSub_le_levSub_empty (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := fun a ha v => ⟨(ha v).1, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub_empty (L : Type) [Field L] [NumberField L] :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L ∅ 0).FiniteIndex := by
  classical
  haveI : Finite (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).range := inferInstance
  haveI := Subgroup.finiteIndex_ker (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L)
  refine Subgroup.finiteIndex_of_le (H := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).ker) ?_
  intro a ha
  obtain ⟨k, u, hu, rfl⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L a).1 ha
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, rfl⟩) (Subgroup.mem_sup_right ?_)
  exact fun v => ⟨(ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff L u).1 hu v, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex := by
  set R := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range
  have hle := levSub_le_levSub_empty L S N
  haveI := finiteIndex_range_sup_levSub_empty L
  have hT : R ⊔ levSub L S N ≤ R ⊔ levSub L ∅ 0 := sup_le_sup_left hle _
  have h1 : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
    intro h0
    have hd : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ∣ (levSub L S N).relIndex (levSub L ∅ 0) :=
      Subgroup.relIndex_dvd_of_le_left (levSub L ∅ 0) le_sup_right
    rw [h0] at hd
    exact relIndex_levSub_ne_zero L S N hS (Nat.eq_zero_of_zero_dvd hd)
  have h2 : R ⊔ levSub L S N ⊔ levSub L ∅ 0 = R ⊔ levSub L ∅ 0 := by
    rw [sup_assoc, sup_eq_right.2 hle]
  have h3 : (R ⊔ levSub L S N).relIndex (R ⊔ levSub L ∅ 0) ≠ 0 := by
    rw [← h2, Subgroup.relIndex_sup_left]; exact h1
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index hT]
  exact mul_ne_zero h3 (Subgroup.FiniteIndex.index_ne_zero)

theorem rayClass_finite : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex :=
  fun L _ _ S N hS => finiteIndex_range_sup_levSub L S N hS

end GlobalTheory.LevelChars
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.AUTREP Formalism.UG ReciprocityTheory.Aut

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K]

theorem antiJ_map (g : K →+* K) (n : ℕ) : (antiJ K n).map g = antiJ K n := by
  ext i j
  simp only [antiJ, Matrix.map_apply]
  split_ifs <;> simp

theorem cT_map (g σ σ' : K →+* K) (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : cT σ' (M.map g) = (cT σ M).map g := by
  ext i j
  simp [cT, hg]

def guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) (n : ℕ) :
    GU σ n →* GU σ' n :=
  ((bc (n := Fin n) (g : K →+* K)).comp (GU σ n).subtype).codRestrict (GU σ' n) (fun y => by
    have hy : cT σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antiJ K n := y.2
    show cT σ' (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K)) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K) = antiJ K n
    rw [cT_map (g : K →+* K) σ σ' hg, ← antiJ_map (g : K →+* K) n]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hy])

theorem guMap_val (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (y : GU σ n) :
    (((guMap g hg n y : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map g := rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def gEquiv (D D' : InertDatum L n v w) : w.adicCompletion L ≃+* w.adicCompletion L :=
  D.e.symm.trans D'.e

theorem gEquiv_e (D D' : InertDatum L n v w) (y) : gEquiv D D' (D.e y) = D'.e y := by
  simp [gEquiv]

theorem gEquiv_comm (D D' : InertDatum L n v w) :
    ∀ x, gEquiv D D' (D.σw x) = D'.σw (gEquiv D D' x) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [← D.comm, gEquiv_e, gEquiv_e, D'.comm]

theorem gEquiv_intL (D D' : InertDatum L n v w) :
    ∀ x, x ∈ intL (w.adicCompletion L) ↔ gEquiv D D' x ∈ intL (w.adicCompletion L) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [gEquiv_e, ← D.integ, ← D'.integ]

end GlobalTheory.SatInd
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitLocEq


open NumberField IsDedekindDomain TensorProduct in
theorem _root_.GlobalTheory.SplitLocEq.conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L]
    {n : ℕ} (x : _root_.ReciprocityTheory.Aut.GA L n) (i j : Fin n) :
    _root_.ReciprocityTheory.Aut.conjAL L ((x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) j i := by
  have h : (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
      _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := x.2
  have hinv : _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) := by
    have h' := congrArg
      (fun M => (((x.1)⁻¹ : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * M) h
    simpa [← mul_assoc] using h'
  rw [← hinv]
  rfl

theorem proj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x : GA L n)
    (i j : Fin n) : SplitPlace.proj s ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl

open NumberField IsDedekindDomain TensorProduct in
private theorem evalAt_apply' {L : Type} [Field L] [NumberField L] (w)
    (a : _root_.ReciprocityTheory.Aut.AFplus L) : _root_.ReciprocityTheory.Aut.evalAt L w a = a w := rfl

open NumberField IsDedekindDomain TensorProduct in
private theorem eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (d : _root_.ReciprocityTheory.Aut.AL L)
    (hw : ∀ w, w ≠ s.v → _root_.ReciprocityTheory.Aut.compAt L w d = 0) (h₁ : SplitPlace.proj s d = 0)
    (h₂ : SplitPlace.proj s (_root_.ReciprocityTheory.Aut.conjAL L d) = 0) : d = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L :=
    Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  obtain ⟨a, c, rfl⟩ := _root_.GlobalTheory.tensor_exists_decomp b d
  have hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0 := fun w hne =>
    _root_.GlobalTheory.tensor_decomp_eq_zero b _ _
      (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)
  simp only [map_add (f := _), _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂
  simp [evalAt_apply'] at h₁ h₂
  set σ := IsCMField.complexConj L
  have hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0 := by
    intro h0
    have h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0 :=
      (injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0
    have hb1 : b 1 ≠ 0 := b.ne_zero 1
    have hσb1 : σ (b 1) ≠ 0 := by simpa using hb1
    have hfix : σ (b 0 / b 1) = b 0 / b 1 := by
      rw [map_div₀, div_eq_div_iff hσb1 hb1]
      linear_combination -h0'
    obtain ⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1 :=
      ⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩
    have hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      have hsm : k • b 1 = (k : L) * b 1 := rfl
      rw [hsm, hk, div_mul_cancel₀ _ hb1]
      ring
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0
    simp at this
  have hA : a s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hC : c s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have ha : a = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hA
    · exact (hw' w hv).1
  have hc : c = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hC
    · exact (hw' w hv).2
  simp [ha, hc]


open NumberField IsDedekindDomain TensorProduct in
theorem _root_.GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} x →
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} y →
      SplitPlace.loc s n x = SplitPlace.loc s n y → x = y := by
  intro L _ _ _ n s x y hx hy hxy
  have triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z → ∀ w, w ≠ s.v → ∀ i j,
      _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro z hz w hw i j
    have := hz w (by simpa using hw)
    exact congrFun (congrFun this i) j
  have hinv : SplitPlace.loc s n x⁻¹ = SplitPlace.loc s n y⁻¹ := by simp [map_inv, hxy]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s
  · intro w hw
    rw [map_sub, triv x hx w hw, triv y hy w hw, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry,
      map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]

end GlobalTheory.SplitLocEq
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  first | exact @GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | exact GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod | (intros; apply GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod <;> assumption)
end

section

open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn : ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W → DifferentiableOn ℂ g W → Set.InjOn g W → ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  first | exact @GlobalTheory.InjHol.exists_local_inverse_of_injOn | exact GlobalTheory.InjHol.exists_local_inverse_of_injOn | (intros; apply GlobalTheory.InjHol.exists_local_inverse_of_injOn <;> assumption)
end
