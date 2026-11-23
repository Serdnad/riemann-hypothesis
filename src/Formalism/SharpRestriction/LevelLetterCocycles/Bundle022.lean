module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019
public import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKerSum
public import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section Kill

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def step1Kill_roots (c : ZMod n) (M h a : ℕ) : Finset ℤ :=
  ((jumpSetL W T c M h) ×ˢ Finset.Icc (((0 : ℕ) : ℤ) + 1) (a : ℤ)).image (fun p : ℤ × ℤ => p.1 + p.2)

theorem step1Kill_xList (c : ZMod n) (M h a : ℕ) :
    xListL W T c M h 0 a = (step1Kill_roots W T c M h a).sort (· ≤ ·) := rfl

theorem step1Kill_cO (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) :
    ∃ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) ∧
      cO 0 = 0 ∧ ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ) := by
  classical
  have hc : ∀ j : ℤ, ((PD.p : ℕ) : LL) = 0 → Formalism.MainNotions.CrystallineLiftingInputs.cR W j = 0 := by
    intro j h0
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    simp [h0]
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := hRN.2 1 0 (by norm_num)
    rw [hc 1 h0, hc 0 h0, sub_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have hnn : ∀ x : ℤ, 0 ≤ v (Formalism.MainNotions.CrystallineLiftingInputs.cR W x) := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hRN.1, AddValuation.map_zero]
      exact le_top
    · have h := hRN.2 x 0 hx
      rw [hRN.1, sub_zero] at h
      rw [h]
      first
        | exact WithTop.coe_nonneg.mpr (by positivity)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by positivity))
  have hex : ∀ x : ℤ, ∃ o : O, algebraMap O LL o = Formalism.MainNotions.CrystallineLiftingInputs.cR W x := fun x => hV.2.1 _ (hnn x)
  refine ⟨fun x => Classical.choose (hex x), ?_, ?_, ?_⟩
  · intro x
    apply hV.1
    rw [map_mul, map_natCast, Classical.choose_spec (hex x), map_sub, map_one]
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    first
      | (rw [div_neg, mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hp0, neg_sub])
      | (field_simp; ring)
      | field_simp
  · apply hV.1
    rw [Classical.choose_spec (hex 0), hRN.1, map_zero]
  · intro x hx
    have h := hRN.2 x 0 hx
    rw [hRN.1, sub_zero] at h
    rw [Classical.choose_spec (hex x), h]
    first
      | exact WithTop.coe_natCast _
      | (norm_cast; done)
      | (simp; done)
      | (push_cast; rfl)

theorem step1Kill_kill [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ)
    (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) (c : ZMod n) (cO : ℤ → O)
    (hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) (hc0 : cO 0 = 0)
    (a : ℕ) {y₀ : W.DD T} (hy : QLattice W T c a y₀) :
    Polynomial.aeval (derivationOnWachModule W T)
      (X * ∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀ ∈ W.N T := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hA.2.1]
    simp
  have hyNl : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ ∈ W.Nl T c := by
    have h1 : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ = (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀) := by
      rw [smul_smul, mul_comm, ← smul_smul, hy.1.1]
    rw [h1]
    exact Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hy.2
  obtain ⟨seq, h0, hstep, hN⟩ := hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO c 0 a y₀
    (Nat.zero_le a) hyNl hy.1.2
  have hseq := Formalism.MainNotions.LiftingTheory.lifta_seq W T (uniformizerInverse W) (algebraMap_uniformizer_mul_inverse hU) cO _ seq hstep
  rw [h0] at hseq
  have hNs : seq (xListL W T c (Mi c) (hi c) 0 a).length ∈ W.N T :=
    Formalism.MainNotions.LiftingTheory.liftb_Nl_le W T c (by simpa using hN)
  rw [hseq] at hNs
  have hprod : ((xListL W T c (Mi c) (hi c) 0 a).map
      fun x => (X - C (cO x) : Polynomial O)).prod =
      ∏ x ∈ step1Kill_roots W T c (Mi c) (hi c) a, (X - C (cO x)) := by
    rw [step1Kill_xList, ← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [hprod, ← Finset.prod_filter_mul_prod_filter_not _ (fun x => x ≠ 0)] at hNs
  by_cases h0m : (0 : ℤ) ∈ step1Kill_roots W T c (Mi c) (hi c) a
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h0m, rfl⟩
    rw [hf, Finset.prod_singleton, hc0, map_zero, sub_zero, mul_comm] at hNs
    exact hNs
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, not_not, iff_false, not_and]
      rintro hx rfl
      exact h0m hx
    rw [hf, Finset.prod_empty, mul_one] at hNs
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    have hQ : QLattice W T c 0 (Polynomial.aeval (derivationOnWachModule W T)
        (∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀) :=
      ⟨invariantLetter_polynomial_derivation W T hπΔ hU _ hy.1, by simpa [derivationOnWachModule] using hNs⟩
    simpa using (qLattice_derivation W T hDS hA hT c 0 hQ).2

theorem step1Kill_norm (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hvp : v (PD.p : LL) = 1) (cO : ℤ → O)
    (hcv : ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ))
    (Sx : Finset ℤ) (hS0 : (0 : ℤ) ∉ Sx) (s : ℕ) (hs : ∑ x ∈ Sx, padicValInt PD.p x ≤ s) :
    ∃ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s := by
  classical
  have hcoef : ∀ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = w * ∏ x ∈ Sx, -(cO x) := by
    intro w
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  have hval : ∀ S : Finset ℤ, (0 : ℤ) ∉ S →
      v (algebraMap O LL (∏ x ∈ S, -(cO x))) = ((∑ x ∈ S, padicValInt PD.p x : ℕ) : WithTop ℚ) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp
    · intro a S ha ih h0
      have ha0 : a ≠ 0 := fun h => h0 (by rw [← h]; exact Finset.mem_insert_self a S)
      have hS0' : (0 : ℤ) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, AddValuation.map_mul, map_neg,
        AddValuation.map_neg, hcv a ha0, ih hS0', Nat.cast_add]
  have hvc := hval Sx hS0
  have hc0 : algebraMap O LL (∏ x ∈ Sx, -(cO x)) ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hvc
    exact WithTop.natCast_ne_top _ hvc.symm
  have hvps : v (((PD.p : ℕ) : LL) ^ s) = ((s : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have aux : ∀ r : WithTop ℚ, r + ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : WithTop ℚ) = ((s : ℕ) : WithTop ℚ) →
      0 ≤ r := by
    intro r hr
    induction r using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at hr
      have hq : ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
      first
        | exact WithTop.coe_nonneg.mpr (by linarith)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by linarith))
  have hw'0 : 0 ≤ v (((PD.p : ℕ) : LL) ^ s / algebraMap O LL (∏ x ∈ Sx, -(cO x))) := by
    apply aux
    rw [← hvc, ← AddValuation.map_mul, div_mul_cancel₀ _ hc0, hvps]
  obtain ⟨w, hw⟩ := hV.2.1 _ hw'0
  refine ⟨w, ?_⟩
  rw [hcoef]
  apply hV.1
  rw [map_mul, hw, div_mul_cancel₀ _ hc0, map_pow, map_natCast]

end Kill

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def π0N (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O ↥(NDl W T i) :=
  ((NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T))).comap (NDl W T i).subtype

def IsRed (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T i) →ₗ[O] (Fin r → O)) : Prop :=
  Function.Surjective red ∧ LinearMap.ker red = π0N W T i

theorem length_coker_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
    (QQ : Matrix (Fin r) (Fin r) O) (l : O) (hl : l ≠ 0) (V : ℕ) (hd : QQ.det ∣ l ^ V) :
    Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) ≤
      (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
  classical
  have hdet0 : QQ.det ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hd
    exact pow_ne_zero V hl hd
  have hL := Formalism.KernelCokernelLengths.length_theorems_all_hold.1 O (Fin r → O) (Matrix.toLin' QQ) (by rwa [LinearMap.det_toLin'])
  rw [hL, LinearMap.det_toLin', ← Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow l hl V]
  have hle : Ideal.span {l ^ V} ≤ Ideal.span {QQ.det} := Ideal.span_singleton_le_span_singleton.2 hd
  first
    | exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    | exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ O hle).toLinearMap
        (Ideal.Quotient.factor_surjective hle)

theorem lemmaDN_core {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O))
    (hsurj : Function.Surjective red) (hker : LinearMap.ker red = π0N W T₂ i) {m' : ℕ} (hm' : m' ≤ m)
    (g : Fin m' → W.DD T₂) (hgN : ∀ j, g j ∈ NDl W T₂ i) (cols : Fin r → ↥(NDl W T₂ i))
    (hcols : ∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
      ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j)
    (V : ℕ) (hV : V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m)
    (hdet : (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V) :
    ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ NDl W T₂ i ∧
      ∃ L kO : ℕ, Module.length O (↥(NDl W T₂ i) ⧸
          ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧
        (L : ℝ) ≤ lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S * kO := by
  classical
  obtain ⟨hdom, hdvr, -⟩ := hS.2.2.2.1
  haveI := hdom
  haveI := hdvr
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  haveI : NeZero PD.p := ⟨by omega⟩
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := (hζ.neZero').out
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hpL
    have := congrArg (algebraMap O LL) h
    rwa [map_natCast, map_zero] at this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hlen1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
    rw [← hm]
    first
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal O).out)
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal O)))
  have hlenp : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) = (k : ℕ∞) := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ϖ hϖ.ne_zero k, hlen1, mul_one]
  let s : Finset (W.DD T₂) := Finset.univ.image g
  refine ⟨s, ?_, ?_, V * k, k, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hm')
  · intro x hx
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hgN j
  · set X := (((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) with hX
    have hkerX : LinearMap.ker red ≤ X := by
      rw [hker]
      exact Submodule.comap_mono (le_sup_left.trans le_sup_left)
    have hcolX : ∀ k', cols k' ∈ X := by
      intro k'
      rw [hX, Submodule.mem_comap, Submodule.coe_subtype]
      rcases hcols k' with h | ⟨j, hj⟩
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right h)
      · rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp [s]))
    let QQ : Matrix (Fin r) (Fin r) O := Matrix.of fun l k' => red (cols k') l
    let e := LinearMap.quotKerEquivOfSurjective red hsurj
    let f : (Fin r → O) →ₗ[O] (↥(NDl W T₂ i) ⧸ X) := (Submodule.factor hkerX) ∘ₗ e.symm.toLinearMap
    have hf : Function.Surjective f := (Submodule.factor_surjective hkerX).comp e.symm.surjective
    have hrange : LinearMap.range (Matrix.toLin' QQ) ≤ LinearMap.ker f := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have hv : Matrix.toLin' QQ v = red (∑ k', v k' • cols k') := by
        ext l'

        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_smul, QQ, mul_comm]
      have he : e.symm (red (∑ k', v k' • cols k')) =
          Submodule.Quotient.mk (∑ k', v k' • cols k') := by
        rw [LinearEquiv.symm_apply_eq]
        first
          | rfl
          | exact (LinearMap.quotKerEquivOfSurjective_apply_mk red hsurj _).symm
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hv, he,
        Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
      first
        | rw [Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
        | (change Submodule.Quotient.mk (p := X) (∑ k', v k' • cols k') = 0
           rw [Submodule.Quotient.mk_eq_zero])
      exact Submodule.sum_mem _ fun k' _ => Submodule.smul_mem _ _ (hcolX k')
    let g' := (LinearMap.range (Matrix.toLin' QQ)).liftQ f hrange
    have hg' : Function.Surjective g' := by
      intro z
      obtain ⟨y, rfl⟩ := hf z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    calc Module.length O (↥(NDl W T₂ i) ⧸ X)
        ≤ Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) :=
          Module.length_le_of_surjective g' hg'
      _ ≤ (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
          length_coker_le QQ _ hp0 V hdet
      _ = ((V * k : ℕ) : ℕ∞) := by rw [hlenp, Nat.cast_mul]
  · unfold Formalism.WeaklyAdmissibleFiltrations.lenOl
    exact hlenp
  · have hp1 : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (by omega : 1 < PD.p)
    have hcD : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      unfold Formalism.MainNotions.RamifiedCoefficientChains.cD
      have h1 : 0 < (PD.p : ℝ) - 1 := by linarith
      have h2 : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) + 1 := by positivity
      have := div_nonneg h2 h1.le
      linarith
    have hfl := Nat.floor_le hcD
    have hV' : (V : ℝ) ≤ (finrank LL T₂.V : ℝ) * S + 2 * m * Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      have h := (Nat.cast_le (α := ℝ)).2 hV
      push_cast at h
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [h, hfl, hm0]
    unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.lenC
    push_cast
    exact mul_le_mul_of_nonneg_right hV' (Nat.cast_nonneg k)

def DetColsE : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)) (_ : IsRed W T₂ i red)
        (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem lemmaDN_of_detE (h : DetColsE W) : LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨r, red, hred, m', hm', g, hgN, cols, hcols, V, hV, hdet⟩ := h d T₁ T₂ F b S η m hS i hi
  obtain ⟨hsurj, hker⟩ := hred
  exact lemmaDN_core W hS i red hsurj hker hm' g hgN cols hcols V hV hdet

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem normA_holds {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) : normA P K LL := by
  intro T₁ T₂ F r S η m h up b hA hJ
  unfold Formalism.MainNotions.ElementDenominator.HypA at hA
  obtain ⟨hc1, hc2, hon, _, hj1, hηb, hsum, hjh, hposition⟩ := hA
  have hT1 : ∀ τ, JumpsInV (P.PD K) T₁.ρ τ
      (deep (up τ) (min (b τ) (h + 1)) S ∪ Set.Icc (-((min η h : ℕ) : ℤ)) (min η h : ℕ)) := by
    intro τ a ha
    have ha1 := hj1 τ a ha
    have hah := hjh τ a ha
    simp only [Set.mem_Icc] at hah
    rcases ha1 with h1 | h1
    · left
      unfold deep at h1 ⊢
      split_ifs at h1 ⊢ <;> simp only [Set.mem_Icc] at h1 ⊢ <;> push_cast <;> omega
    · right
      simp only [Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hj2h : ∀ τ, JumpsInV (P.PD K) T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ => hJ τ _ (hjh τ)
  refine ⟨min η h, h + S + 1, fun τ => min (b τ) (h + 1), min_le_left _ _, le_rfl, ?_⟩
  refine ⟨hc1, hc2, hon, hT1, fun τ => hJ τ _ (hT1 τ), fun τ => ?_, fun τ => ?_, by omega,
    fun τ => ?_, hposition⟩
  · have := hηb τ
    show min η h < min (b τ) (h + 1)
    omega
  · show min (b τ) (h + 1) + S ≤ h + S + 1
    omega
  · refine le_of_eq_of_le ?_ (hsum τ)
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      push_cast at hx
      omega
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      push_cast at hx'
      have hnj : ¬ IsJumpV (P.PD K) T₂.ρ τ x := by
        intro hj
        have h2 := hj2h τ x hj
        simp only [Set.mem_Icc] at h2
        omega
      unfold IsJumpV at hnj
      push_neg at hnj
      unfold multV
      rw [hnj, sub_self]

theorem normR_holds (D : D7) : normR D := by
  intro l _ _ K LL _
  exact normA_holds (D.loc l) K LL

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def KapPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → kapPiR D HW

end Formalism.MainNotions.N.Ln34

end
end
