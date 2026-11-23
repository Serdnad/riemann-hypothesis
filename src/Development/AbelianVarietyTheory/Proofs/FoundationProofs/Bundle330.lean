module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle008
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle300
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameter
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kummerBettiModule_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  first | exact @GlobalTheory.KZ.B_free_finite | exact GlobalTheory.KZ.B_free_finite | (intros; apply GlobalTheory.KZ.B_free_finite <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  first | exact @GlobalTheory.KZ.exists_pot_rel_of_mem_bSet | exact GlobalTheory.KZ.exists_pot_rel_of_mem_bSet | (intros; apply GlobalTheory.KZ.exists_pot_rel_of_mem_bSet <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E → ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) → y = 0 := by
  first | exact @GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv <;> assumption)
end

section

open scoped MatrixGroups
open Matrix GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.CyclotomicQExpansion.ThnEx

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_coe (σ : SL(2, ℤ)) : toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL σ := by
  have h : (0 : ℤ) < (σ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  unfold toGQ
  rw [dite_eq_left h]
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [ofSL]

theorem kmap_SL_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ : SL(2, ℤ)) :
    ∀ a ∈ X.A l, X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv a ∈ X.A l := by
  apply KmapA.kmap_mem_A
  intro W hW
  refine ⟨fun c => ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl _ (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl _ X.jK ∈ W
    rw [toGQ_coe, X.j_inv]; exact hW.2

private theorem exists_isDiam_of_coprime {N l d : ℕ} (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨e, heN, hel⟩ := Nat.chineseRemainder hNl d 1
  have hcop : Nat.Coprime e (N * l) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq heN]; exact hd
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hel]; simp
  have hbez := Nat.gcd_eq_gcd_ab e (N * l)
  rw [hcop.gcd_eq_one] at hbez
  refine ⟨⟨!![Nat.gcdA e (N * l), -Nat.gcdB e (N * l); ((N * l : ℕ) : ℤ), (e : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; push_cast at hbez ⊢; linear_combination -hbez
  · refine Subgroup.mem_inf.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr ?_, CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
    · simp
    · simp
  · simp only [en]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Int.cast_natCast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heN

private theorem conj_mem_Gamma1_of_mem_Gamma0 {N : ℕ} {σ γ : SL(2, ℤ)} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  have hg0 : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hγ0) (Subgroup.inv_mem _ hσ)
  have h1 : (⟨γ, hγ0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem]
    exact (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have h2 : (⟨σ * γ * σ⁻¹, hg0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N :=
    (CongruenceSubgroup.Gamma0Map N).normal_ker.conj_mem _ h1 ⟨σ, hσ⟩
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h2)

private theorem kmap_kmap_eq_kmap_trans (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.coe_restrictScalars]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  rfl

private theorem act_act_eq_act_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  funext u
  change X.kmap l (X.sl (toGQ (τ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ (mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))) =
    X.kmap l (X.sl (toGQ ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (b (mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
  have hm : mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) * mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) := by
    simp only [mZl, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  have hs : (X.sl (ofSL σ * ofSL τ)).toRingEquiv =
      (X.sl (ofSL σ)).toRingEquiv.trans (X.sl (ofSL τ)).toRingEquiv := by
    ext f; exact X.sl_mul _ _ f
  rw [kmap_kmap_eq_kmap_trans, toGQ_coe, toGQ_coe, toGQ_coe, map_mul, Matrix.mulVec_mulVec, hm, hs]

theorem diam_BSet (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.BSet N l w := by
  have hσ : IsDiam N l d (sgD N l d) := Classical.epsilon_spec (exists_isDiam_of_coprime hNl hd)
  obtain ⟨hpol, hinv⟩ := hb
  refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (kmap_SL_A X l (sgD N l d)) b hpol, ?_⟩
  intro γ hγ
  obtain ⟨hσN, hσl⟩ := Subgroup.mem_inf.mp hσ.1
  obtain ⟨hγN, hγl⟩ := Subgroup.mem_inf.mp hγ
  have hconj : sgD N l d * γ * (sgD N l d)⁻¹ ∈ Gam N l :=
    Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1_of_mem_Gamma0 hσN hγN,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσl hγl) (Subgroup.inv_mem _ hσl)⟩
  have hswap : sgD N l d * γ = sgD N l d * γ * (sgD N l d)⁻¹ * sgD N l d :=
    (inv_mul_cancel_right _ _).symm
  rw [act_act_eq_act_mul X l _ _ b, hswap, ← act_act_eq_act_mul X l (sgD N l d * γ * (sgD N l d)⁻¹) (sgD N l d) b,
    hinv _ hconj]

theorem diam_B (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  have hle : X.B N l w ≤ (X.B N l w).comap (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span (diam_BSet X N l w d hN hNl hd x hx))
  exact hle hb

end GlobalTheory.CyclotomicQExpansion.ThnEx

namespace GlobalTheory.CyclotomicQExpansion

theorem thN_isThB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime],
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧
      IsLat 1 (thN X A N l n d b) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : l.Prime := Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hb' := ThnEx.diam_B X N l w d (by omega) hNl hd b hb
  exact thN_spec X A N l n d b (GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l (IsAlgClosure.isAlgebraic (R := ℚ)) hj hl2 hlN (by omega) hlA n w hw _ hb')

end GlobalTheory.CyclotomicQExpansion
end
end

section

noncomputable section

namespace GlobalTheory.VolumeRatioTypings

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
open GlobalTheory.VolRatioCompare (reLat)
open scoped TensorProduct Matrix ENNReal

theorem rightInvariant_of_finite_covolume {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) : μ.IsMulRightInvariant := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  refine ⟨fun g => ?_⟩
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨(measurable_mul_const g).aemeasurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [e, h2, one_smul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volMeas_unique (V : HSp D) {P Q : ℕ} {μ μ' : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (h' : IsVolMeas D V P Q μ') : μ' = μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have := D.cd.haar P Q
  have := h.1
  have := h'.1
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  obtain ⟨U, hU1, hU, hfin⟩ := (D.cd.cd P Q).exists_isOpen_measure_lt_top 1
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨A, hA⟩ := (h.2.2 θ hθ).1
  have h1 := (h.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  have h2 := (h'.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  rw [e, Measure.smul_apply, smul_eq_mul, h1] at h2
  have h3 := (ENNReal.mul_left_inj (Finset.prod_ne_zero_iff.2 fun _ _ => hU.measure_ne_zero _ ⟨1, hU1⟩)
    (ENNReal.prod_ne_top fun _ _ => hfin.ne)).1 (h2.trans (one_mul _).symm)
  rw [e, h3, one_smul]

theorem isVol_of_pair (V : HSp D) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ) {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {x : ℝ} (hx : 0 < x) (e : μ 𝓕 = ENNReal.ofReal x) : IsVol D V P Q x := by
  refine ⟨hx, ⟨μ, h⟩, fun μ' h' => ?_⟩
  obtain rfl := volMeas_unique V h h'
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓖 h𝓖 => ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ'
  have h𝓖' : IsFundamentalDomain (GQ V) 𝓖 μ' := h𝓖
  exact (h𝓖'.measure_eq h𝓕).trans e

theorem exists_conj (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : ∃ k ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) := by
  obtain ⟨γ, hfin, hγ⟩ := GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host D V L h1 h2
  obtain ⟨k, hk, hkv⟩ := GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial D V γ hfin
  refine ⟨k, hk, fun y => ?_⟩
  refine (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E V y).trans (Iff.trans ?_
    (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E (reLat V L h1 h2) _).symm)
  refine forall_congr' fun v => (hγ v _).trans (iff_of_eq ?_)
  congr 1
  rw [← hkv v]
  funext i
  exact (RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v)
    (AlgHom.id D.host.F D.host.E)).toRingHom _ y i).symm

theorem isVolMeas_reLat (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (hr : μ.IsMulRightInvariant) : IsVolMeas D (reLat V L h1 h2) P Q μ := by
  obtain ⟨k, hk, hkL⟩ := exists_conj V L h1 h2
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  refine ⟨h.1, h.2.1, fun θ hθ => ⟨(h.2.2 θ hθ).1, fun A hA B hB => ?_⟩⟩
  rw [← (h.2.2 θ hθ).2 A hA B hB, ← measure_preimage_mul μ k⁻¹, ← measure_preimage_mul_right μ k]
  refine congrArg μ (Set.ext fun (g : GA D V) => and_congr ?_ ?_)
  · show (∀ y : Fin V.rank → _, y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) ↔
        (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2))) ↔
      ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram (k⁻¹ * (g * k))).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)
    have hm : ∀ (a b : GA D V) y, (finMat D.sp.cm.sig V.gram (a * b)).mulVec y =
        (finMat D.sp.cm.sig V.gram a).mulVec ((finMat D.sp.cm.sig V.gram b).mulVec y) := fun a b y => by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, Matrix.mulVec_mulVec]
    have ho : ∀ y, (finMat D.sp.cm.sig V.gram k).mulVec ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y) = y := fun y => by
      rw [← hm, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]
    constructor
    · intro hg y
      refine (hkL y).trans (Iff.trans (hg _) (Iff.trans (iff_of_eq ?_) (hkL _).symm))
      rw [hm, ho, hm]
    · intro hg y
      have := hg ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y)
      have := (hkL _).symm.trans (this.trans (hkL _))
      rw [hm, hm, ho, ho] at this
      exact this
  · have hk1 : ∀ a ∈ GfC V, ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := fun a ha ρ => by
      have ha' : infHom V a = 1 := ha
      rw [GlobalTheory.SmoothForms.RealPts.infMat_eq V, ha', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    refine forall_congr' fun ρ => ?_
    have e : infMat D.sp.cm.sig V.gram (θ ρ) (k⁻¹ * (g * k)) = infMat D.sp.cm.sig V.gram (θ ρ) g := by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, hk1 k hk, hk1 _ (inv_mem hk), one_mul, mul_one]
    exact iff_of_eq (congrArg (fun m : Matrix (Fin (reLat V L h1 h2).rank) (Fin (reLat V L h1 h2).rank) ℂ =>
      ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * m) e.symm)

theorem tMap_unimod (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    Formalism.HermitianLatticesTheory.IsUnimodular V'.hT (tMap e V.L0) := by
  have h : ∀ x, (∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔ x ∈ V.L0 := fun x => by
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  ext x
  rw [mem_tMap, ← h]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    mem_tMap]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H (e y) (by simpa using hy)
    rwa [← e.apply_symm_apply x, he] at this
  · rw [← isoSymm e he]
    exact H _ hy

theorem isVol_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y)
    {P Q : ℕ} {x : ℝ} (h : IsVol D V P Q x) : IsVol D V' P Q x := by
  obtain ⟨hx, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  let V₁ := reLat V' (tMap e V.L0) (tMap_lattice e _ V.standardTuple_isLattice) (tMap_unimod V V' e he)
  obtain ⟨φ, hc, hc', hQ, hφ⟩ := GlobalTheory.T.exists_volume_transport_of_lattice_isometry D V V₁ e he fun x => by
    show _ ↔ e x ∈ tMap e V.L0
    rw [mem_tMap, e.symm_apply_apply]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V₁.rank V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V₁) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  let ψ : GA D V ≃ᵐ GA D V₁ := ⟨φ.toEquiv, hc.measurable, hc'.measurable⟩
  have hν := hφ P Q μ hμ
  have := hν.1
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 μ := h𝓕
  have h𝓖 : IsFundamentalDomain (GQ V₁) (φ.symm ⁻¹' 𝓕) (μ.map φ) :=
    h𝓕'.preimage_of_equiv (f := φ.symm)
      (MeasurePreserving.symm ψ ⟨ψ.measurable, rfl⟩).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  have hvol : μ.map φ (φ.symm ⁻¹' 𝓕) = ENNReal.ofReal x := by
    rw [← hv 𝓕 h𝓕]
    refine (ψ.map_apply _).trans (congrArg μ ?_)
    ext g
    exact iff_of_eq (congrArg (· ∈ 𝓕) (φ.symm_apply_apply g))
  have hr := rightInvariant_of_finite_covolume (GQ V₁) (μ.map φ) h𝓖 (hvol ▸ ENNReal.ofReal_ne_top)
  exact isVol_of_pair V' (isVolMeas_reLat V₁ V'.L0 V'.standardTuple_isLattice V'.baseLattice_isUnimodular hν hr) h𝓖 hx hvol

end GlobalTheory.VolumeRatioTypings
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.pullB_th0_mem_tr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | exact GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | (intros; apply GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionTranslatesSpan_taylorCoeffs_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, Differentiable ℂ F ∧ CoefIn D F Qbar := by
  first | exact @GlobalTheory.ThetaConj.translates_coef_algebraic | exact GlobalTheory.ThetaConj.translates_coef_algebraic | (intros; apply GlobalTheory.ThetaConj.translates_coef_algebraic <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.ordinaryEisensteinEigenfunctional_exists : GlobalTheory.EisM.CuspidalUnitaryTwistsClaim := by
  first | exact @GlobalTheory.EisM.chapterM_holds | exact GlobalTheory.EisM.chapterM_holds | (intros; apply GlobalTheory.EisM.chapterM_holds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteIdeleChar_at_determinantRoots : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  first | exact @GlobalTheory.DetRootChar.exists_finite_char | exact GlobalTheory.DetRootChar.exists_finite_char | (intros; apply GlobalTheory.DetRootChar.exists_finite_char <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nthRoot_idele_finitePart_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  first | exact @GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one | exact GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one | (intros; apply GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x = 1) → ∀ x, c x = 1 := by
  first | exact @GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite | exact GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite | (intros; apply GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.sigmaStar_addition_formula_padic_modelParameter : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicSigmaAdditionFormula D := by
  first | exact @GlobalTheory.SigmaAdd.sigma_add_param | exact GlobalTheory.SigmaAdd.sigma_add_param | (intros; apply GlobalTheory.SigmaAdd.sigma_add_param <;> assumption)
end
