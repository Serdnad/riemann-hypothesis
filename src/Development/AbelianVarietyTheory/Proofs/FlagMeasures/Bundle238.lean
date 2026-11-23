module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContribution
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbits
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSection
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
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.BaseModule

@[to_additive addRelIndex_mul_measure
]
theorem relIndex_mul_measure' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  classical
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hfin : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (L : Set G) = ⋃ a : s, ((a : L) : G) • (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      have hy : (⟨x, hx⟩ : L) ∈ s * ((H.subgroupOf L : Subgroup L) : Set L) := by
        rw [hs.mul_eq]; exact Set.mem_univ _
      obtain ⟨a, ha, h, hh, hah⟩ := hy
      refine ⟨⟨a, ha⟩, (h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
      have := congrArg Subtype.val hah
      simpa using this
    · rintro ⟨a, z, hz, rfl⟩
      exact L.mul_mem (a : L).2 (hHL hz)
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => ((a : L) : G) • (H : Set G)) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩
    apply hab
    have key := hs.1 (a₁ := (a, ⟨⟨z₁, hHL hz₁⟩, Subgroup.mem_subgroupOf.mpr hz₁⟩))
      (a₂ := (b, ⟨⟨z₂, hHL hz₂⟩, Subgroup.mem_subgroupOf.mpr hz₂⟩)) (Subtype.ext (by simpa using he.symm))
    exact congrArg Prod.fst key
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ (((a : L) : G) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ L := by
        rw [hU, measure_iUnion hdisj (fun _ => hH.const_smul _)]

theorem modK_algebraMap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ ϖ : 𝒪[F], Irreducible ϖ → Nat.card 𝓀[F] = resQ ϖ ∧ ∀ x : F, x ≠ 0 → M.modK (algebraMap F E x) = (resQ ϖ : ℝ) ^ (-(2 * vE M.L ϖ (algebraMap F E x))) := by
  intro F _ _ _ E _ _ _ _ M hM ϖ hϖ
  have := hM.loc
  have := hM.char0
  have := hM.borel
  have := hM.haar.haar
  obtain ⟨hTR, hT2, hLC, hSC, hCS, -, -, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have hq2 : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  intro x hx
  have : IsTopologicalAddGroup E := inferInstance
  have : M.mu.Regular := inferInstance
  have hsmul : ∀ (a : F) (y : E), a ∈ 𝒪[F] → y ∈ M.L.O → a • y ∈ M.L.O := fun a y ha hy => by
    rw [Algebra.smul_def]
    exact M.L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff M.L a).mpr ha) hy
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOT : M.mu (M.L.O : Set E) ≠ ⊤ := hOc.measure_lt_top.ne

  have hunit : ∀ u : (𝒪[F])ˣ, distribHaarChar E (Units.mk0 ((u : 𝒪[F]) : F) (by simp)) = 1 := by
    intro u
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = ((u : 𝒪[F]) : F)⁻¹ := by
      have h1 : ((((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) : 𝒪[F]) : F) = ((1 : 𝒪[F]) : F) := by
        rw [u.inv_mul]
      rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hset : Units.mk0 ((u : 𝒪[F]) : F) (by simp) • (M.L.O : Set E) = M.L.O := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hy
        have h2 := hsmul ((u : 𝒪[F]) : F) _ (u : 𝒪[F]).2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ (by simp)] at h2
        exact h2
      · intro hy
        have h2 := hsmul (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) y (u⁻¹ : (𝒪[F])ˣ).1.2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, ← hinv]
        exact h2
    rw [hset]
    simp

  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hwO : algebraMap F E (ϖ : F) ∈ M.L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff M.L _).mpr ϖ.2
  have hI : Ideal.span {y : M.L.O | (y : E) = algebraMap F E ((ϖ : F) ^ 1)} =
      Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)} := by
    congr 1
    ext y
    simp [Subtype.ext_iff]
  have hcard : Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}) = resQ ϖ ^ 2 := by
    have h := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.1 1
    rw [hI, mul_one] at h
    exact h
  have hfinj : Function.Injective (M.L.O.subtype.toAddMonoidHom) := Subtype.val_injective
  have hrange : (⊤ : AddSubgroup M.L.O).map M.L.O.subtype.toAddMonoidHom = M.L.O.toAddSubgroup := by
    ext z
    simp
  have hrel : ((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).relIndex M.L.O.toAddSubgroup = resQ ϖ ^ 2 := by
    rw [← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj, AddSubgroup.relIndex_top_right]
    exact hcard
  have hHK : (Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom ≤ M.L.O.toAddSubgroup := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  have hHset : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) = Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨(a : E), a.2, ?_⟩
      simp [Algebra.smul_def, mul_comm]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b, hb⟩ * ⟨algebraMap F E (ϖ : F), hwO⟩,
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl), ?_⟩
      simp [Algebra.smul_def, mul_comm]
  have hHm : MeasurableSet (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) := by
    rw [hHset]
    exact (hOo.smul _).measurableSet
  have : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).addSubgroupOf M.L.O.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change AddSubgroup.relIndex _ _ ≠ 0
    rw [hrel]
    exact pow_ne_zero _ (by omega)
  have key := addRelIndex_mul_measure _ _ hHK hHm M.mu
  rw [hrel, hHset] at key
  have key2 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) * M.mu (Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)) =
      M.mu (M.L.O : Set E) := key
  have hΔp : distribHaarChar E (Units.mk0 (ϖ : F) hϖ0) = ((resQ ϖ : NNReal) ^ 2)⁻¹ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have h0 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (by omega)
    have hT : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hc : (((((resQ ϖ : NNReal) ^ 2)⁻¹ : NNReal)) : ENNReal) = ((resQ ϖ ^ 2 : ℕ) : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by exact_mod_cast pow_ne_zero _ (by omega))]
      push_cast
      rfl
    rw [hc]
    rw [← key2, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation M.L ϖ hϖ).2.2.2 x hx
  have hgx : Units.mk0 x hx = Units.mk0 (ϖ : F) hϖ0 ^ (vE M.L ϖ (algebraMap F E x)) *
      Units.mk0 ((u : 𝒪[F]) : F) (by simp) := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact hu
  have himg : (fun y => algebraMap F E x * y) '' (M.R : Set E) = Units.mk0 x hx • (M.R : Set E) := by
    rw [← Set.image_smul]
    congr 1
    funext y
    rw [Units.smul_def, Units.val_mk0, Algebra.smul_def]
  unfold Formalism.MainNotions.S.Loc.Model.modK
  rw [himg, ← distribHaarChar_mul M.mu, hM.haar.volR, mul_one, hgx, map_mul, map_zpow, hunit u, mul_one,
    hΔp, ENNReal.coe_toReal]
  push_cast
  rw [← zpow_natCast, ← zpow_neg, ← zpow_mul]
  congr 1
  push_cast
  ring

end GlobalTheory.BaseModule
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_param_maxCompact {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    ∃ κ : Formalism.REAL.KG ε → Mx k r, Continuous κ ∧ (∀ x, κ x ∈ GG k r) ∧ κ 1 = 1 ∧
      (∀ x y, κ (x * y) = κ x * κ y) ∧
      ∀ g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _),
        ∃ x, κ x = g := by
  obtain ⟨⟨-, hPJ⟩, hPU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcong : ∀ A B : Mx k r, (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * (A * B) * P := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
  have hherm : ∀ A : Mx k r, (Pᴴ * A * P)ᴴ = Pᴴ * Aᴴ * P := by
    intro A
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hJ : Formalism.QuantumDeterminants.Hpk k r = Pᴴ * Formalism.REAL.Jm ε * P := hPJ.symm
  refine ⟨fun x => Pᴴ * Formalism.REAL.toMK x * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : Formalism.REAL.KG ε => Formalism.REAL.toMK x) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  · intro x
    have hx : (Formalism.REAL.toMK x)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK x = Formalism.REAL.Jm ε :=
      (x : Formalism.REAL.UJ ε).2
    show (Pᴴ * Formalism.REAL.toMK x * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * Formalism.REAL.toMK x * P) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [hJ, hherm, hcong, hcong, hx]
  · show Pᴴ * Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) * P = 1
    rw [show Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 from rfl, Matrix.mul_one, h1]
  · intro x y
    show Pᴴ * Formalism.REAL.toMK (x * y) * P = (Pᴴ * Formalism.REAL.toMK x * P) * (Pᴴ * Formalism.REAL.toMK y * P)
    rw [hcong]
    rfl
  · rintro g ⟨hgH, hgU⟩
    have hgH' : gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P := by
      have h : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hgH
      rw [← hPJ] at h
      exact h
    have g1 : gᴴ * g = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    have g2 : g * gᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    set M := P * g * Pᴴ with hM
    have hMH : Mᴴ = P * gᴴ * Pᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have M1 : Mᴴ * M = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc gᴴ g, g1, Matrix.one_mul, h2]
    have M2 : M * Mᴴ = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc g gᴴ, g2, Matrix.one_mul, h2]
    have MJ : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := by
      calc Mᴴ * Formalism.REAL.Jm ε * M = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
            rw [hMH, hM]
            simp only [Matrix.mul_assoc]
        _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hgH']
        _ = Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Matrix.mul_one]
    have MK : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
      calc M * Formalism.REAL.Jm ε = M * (Mᴴ * Formalism.REAL.Jm ε * M) := by rw [MJ]
        _ = (M * Mᴴ) * Formalism.REAL.Jm ε * M := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * M := by rw [M2, Matrix.one_mul]
    have MU : M ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact M2
    let u : (Mx k r)ˣ := ⟨M, Mᴴ, M2, M1⟩
    have hu : u ∈ Formalism.REAL.UJ ε := MJ
    have hk : (⟨u, hu⟩ : Formalism.REAL.UJ ε) ∈ Formalism.REAL.KG ε := (⟨MU, MK⟩ : M ∈ Formalism.REAL.Kset ε)
    refine ⟨⟨⟨u, hu⟩, hk⟩, ?_⟩
    show Pᴴ * M * P = g
    rw [hM]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, Matrix.mul_one]

theorem exists_kFin_ne_zero_of_cwCont : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → (∃ v ∈ R.sm, Bm v ≠ 0) → ∃ x, R.KFin x ∧ Bm x ≠ 0 := by
  intro hKS k r ε mu R hR V _ _ _ _ Bm hadd hsmul hcw hex
  obtain ⟨v, hv, hBv⟩ := hex
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hP, -⟩ := hR.2
  obtain ⟨κ, hκc, hκG, hκ1, hκm, hκs⟩ := exists_param_maxCompact hP
  obtain ⟨hmul, hone, -, -, -, -, -, -, hσc⟩ := rep_basic_of_isDS hKS k r ε mu R hR
  have hBc := (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1
  have hf : Continuous (fun x => Bm (R.σ (κ x) v)) := hBc.comp_continuous hκc hκG
  have hw : Continuous (fun x => R.σ (κ x) v) := (hσc v).comp_continuous hκc hκG
  have hint : ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      Integrable (fun x => q x • R.σ (κ x) v) (Formalism.REAL.muK ε) := fun q hq =>
    (hq.smul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsig : ∀ y, ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)) =
        ∫ x, q (y⁻¹ * x) • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := by
    intro y q hq
    calc R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε))
        = ∫ x, R.σ (κ y) (q x • R.σ (κ x) v) ∂(Formalism.REAL.muK ε) :=
          ((R.σ (κ y)).integral_comp_comm (hint q hq)).symm
      _ = ∫ x, (fun z => q (y⁻¹ * z) • R.σ (κ z) v) (y * x) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [hκm, hmul _ (hκG y) _ (hκG x)]
      _ = _ := integral_mul_left_eq_self (μ := Formalism.REAL.muK ε) (fun z => q (y⁻¹ * z) • R.σ (κ z) v) y
  let φ : C(Formalism.REAL.KG ε, ℂ) := ⟨fun x => ⟪Bm v, Bm (R.σ (κ x) v)⟫_ℂ, continuous_const.inner hf⟩
  have hφ : φ = 0 := by
    refine KHolExt.eq_zero_of_orth φ (fun p hp => ?_)
    obtain ⟨ι, _, a, b, -, hab⟩ := hp
    obtain ⟨u, hu⟩ : ∃ u, u = ∫ x, p x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ι → R.H, ∀ i, c i = ∫ x, b i x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) :=
      ⟨_, fun _ => rfl⟩
    have hdec : ∀ y, R.σ (κ y) u = ∑ i, a i y • c i := by
      intro y
      rw [hu, hsig y p p.continuous]
      have hx : ∀ x, p (y⁻¹ * x) • R.σ (κ x) v = ∑ i, a i y • (b i x • R.σ (κ x) v) := by
        intro x
        rw [hab, Finset.sum_smul]
        simp only [mul_smul]
      simp_rw [hx]
      rw [integral_finsetSum Finset.univ (f := fun i x => a i y • (b i x • R.σ (κ x) v))
        (fun i _ => (hint _ (b i).continuous).smul (a i y))]
      simp only [integral_smul, hc]
    have hFT : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
    let S := Submodule.span ℂ (Set.range fun y => R.σ (κ y) u)
    have hST : S ≤ Submodule.span ℂ (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      show R.σ (κ y) u ∈ Submodule.span ℂ (Set.range c)
      rw [hdec y]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hKF : R.KFin u := by
      unfold BranchingSupport.Rep.KFin PI.UpqRep.IsKFinHpk
      refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
      · have h1 : R.σ (κ 1) u ∈ S := Submodule.subset_span ⟨1, rfl⟩
        rwa [hκ1, hone] at h1
      · intro g hg x hx
        obtain ⟨y', rfl⟩ := hκs g hg
        have hmap : S.map (R.σ (κ y') : R.H →ₗ[ℂ] R.H) ≤ S := by
          rw [Submodule.map_span_le]
          rintro _ ⟨y, rfl⟩
          refine Submodule.subset_span ⟨y' * y, ?_⟩
          simp [hκm, hmul _ (hκG y') _ (hκG y)]
        exact hmap (Submodule.mem_map_of_mem hx)
    have hus : u ∈ R.sm := hKS k r ε mu R.H R.σ hR.1 hR.2 u hKF
    have hB0 : Bm u = 0 := hcon u hKF
    have hI := GlobalTheory.T.cwCont_integral_comm_alt hKS k r ε mu R hR V Bm hadd hsmul hcw (Formalism.REAL.KG ε) (Formalism.REAL.muK ε) κ p
      hκc hκG p.continuous v hv (hu ▸ hus)
    have hfi : Integrable (fun x => p x • Bm (R.σ (κ x) v)) (Formalism.REAL.muK ε) :=
      (p.continuous.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ x, p x * φ x ∂(Formalism.REAL.muK ε)
        = ∫ x, innerSL ℂ (Bm v) (p x • Bm (R.σ (κ x) v)) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [φ, inner_smul_right]
      _ = innerSL ℂ (Bm v) (∫ x, p x • Bm (R.σ (κ x) v) ∂(Formalism.REAL.muK ε)) :=
          (innerSL ℂ (Bm v)).integral_comp_comm hfi
      _ = 0 := by rw [← hI, ← hu, hB0, map_zero]
  have h1 := DFunLike.congr_fun hφ 1
  change ⟪Bm v, Bm (R.σ (κ 1) v)⟫_ℂ = 0 at h1
  rw [hκ1, hone, inner_self_eq_zero] at h1
  exact hBv h1

end GlobalTheory
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.mirClass_diag1_eq_sum | exact GlobalTheory.GLm.mirClass_diag1_eq_sum | (intros; apply GlobalTheory.GLm.mirClass_diag1_eq_sum <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsUnimodMod H (latL N.F N.F' Λ) (uPerp N.F N.F') (II N.F N.F') ∧ IsUnimodMod H (latL N.F' N.F Λ) (uPerp N.F N.F') (II N.F N.F') ∧ (∀ t : K, t • N.F.z ∈ latL N.F N.F' Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ (∀ t : K, t • N.F'.z ∈ latL N.F' N.F Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ Submodule.IsLattice K (N.Ref (latL N.F N.F' Λ)) ∧ N.Ref (latL N.F N.F' Λ) ⊓ rs (𝓞 K) (V0 N.F N.F') = N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') := by
  first | exact @GlobalTheory.DegCnt.InnerLat.main | exact GlobalTheory.DegCnt.InnerLat.main | (intros; apply GlobalTheory.DegCnt.InnerLat.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  first | exact @GlobalTheory.FlagMeas.gaugeSubEx | exact GlobalTheory.FlagMeas.gaugeSubEx | (intros; apply GlobalTheory.FlagMeas.gaugeSubEx <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  first | exact @GlobalTheory.FlagPieces.flag_pieces | exact GlobalTheory.FlagPieces.flag_pieces | (intros; apply GlobalTheory.FlagPieces.flag_pieces <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lineLatticeClassMean_covolume_function : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  first | exact @GlobalTheory.FlagBase.MeanCov.latMean_covAt | exact GlobalTheory.FlagBase.MeanCov.latMean_covAt | (intros; apply GlobalTheory.FlagBase.MeanCov.latMean_covAt <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.OrbitTerm.orbit_term | exact GlobalTheory.OrbitTerm.orbit_term | (intros; apply GlobalTheory.OrbitTerm.orbit_term <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → latMean E (k + 1) (fun L => w (covAt E (k + 1) L) * ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) = ∑' 𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥}, ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ} => ∃ γ : GL (Fin k) E, ∀ y, (γ : Matrix (Fin k) (Fin k) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1), covol {x | x ∈ autGL E (k + 1) (Lf 𝔞.1 (Quot.out c).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞.1 (Quot.out c).1) g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} := by
  exact @GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.siegel_height_bound_section : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧ (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  first | exact @GlobalTheory.Amp.SecBound.section_coord_le | exact GlobalTheory.Amp.SecBound.section_coord_le | (intros; apply GlobalTheory.Amp.SecBound.section_coord_le <;> assumption)
end
