module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
import Formalism.LocalToGlobal.Columns.LevGCount
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.SelfDualDetNorm

theorem star_eq_conj (D : D7) (x : D.host.E) :
    (letI := D.host.cmStar; star x) = D.host.conj x := by
  letI := D.host.cmStar
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isSdLat_of_isSDLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) : Formalism.L2.Col.IsSdLat (E := E) L := by
  obtain ⟨hfg, hsp, hd⟩ := hL
  refine ⟨Submodule.IsLattice.of_fg E hfg, ?_⟩
  ext y
  rw [hd y]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem detId_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  intro D N L hL
  letI := D.host.cmStar
  obtain ⟨J, hJ, hIJ⟩ := GlobalTheory.CharValCompare.normOne_detI (isSdLat_of_isSDLat L hL)
  refine ⟨J, fun x => by rw [hJ, star_eq_conj]; exact Iff.rfl, ?_⟩
  exact hIJ

end GlobalTheory.SelfDualDetNorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnLattice_comap_eq_standardLattice : ∀ {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K),
    (Formalism.L2.DIV.colLat B).comap ((Matrix.mulVecLin B.1).restrictScalars (𝓞 K)) = Formalism.L2.Pj.stdLat K n := by
  first | exact @GlobalTheory.ColStd.colLat_comap_eq_stdLat | exact GlobalTheory.ColStd.colLat_comap_eq_stdLat | (intros; apply GlobalTheory.ColStd.colLat_comap_eq_stdLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerClassSum


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (h0 : ν K ≠ 0) (h1 : ν K ≠ ⊤) (a : G) :
    {γ : Γ | a⁻¹ * (γ : G) * a ∈ K}.Finite := by
  set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def
  set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def
  have hT : ν T = ν K := measure_preimage_mul ν a⁻¹ K
  have hsum := h𝓖.measure_eq_tsum' T
  have hδT : ∀ δ ∈ S, δ • T = T := by
    intro δ hδ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul,
      Subgroup.coe_inv]
    have hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K := by
      have := K.inv_mem hδ
      simpa [mul_assoc] using this
    constructor
    · intro hx
      have := K.mul_mem (K.inv_mem hk) hx
      simpa [mul_assoc] using this
    · intro hx
      have := K.mul_mem hk hx
      simpa [mul_assoc] using this
  have hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖) := by
    intro δ hδ γ
    rw [← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]
  by_contra hinf
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← hT, hsum]
    simp [hall]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0)
    (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  have htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤ := by
    rw [tsum_congr (fun δ : S => hinv δ δ.2 γ0)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hγ0
  rw [htop, ← hsum, hT] at hle
  exact h1 (top_le_iff.1 hle)


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.integral_inner_eq_adInner {G H W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G)
    [ν.IsMulLeftInvariant]
    (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J.comap π) = 1)
    (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) (χ : J →* ℂˣ)
    (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : _root_.Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    (∀ i, Finite (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i))) ∧
      ∀ f ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν =
          _root_.Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' := by
  set K : Subgroup G := J.comap π with hK_def
  choose a ha using fun i => hπ (y i)
  have hmem : ∀ i (γ : Γ), γ ∈ _root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i) ↔ (a i)⁻¹ * (γ : G) * a i ∈ K := by
    intro i γ
    unfold _root_.Formalism.IndefR.Bridge.stab
    simp [hK_def, Subgroup.mem_comap, MulAut.conj_apply, ← ha i, map_mul, map_inv]
  have hK0 : ν K ≠ 0 := by rw [h1]; exact one_ne_zero
  have hKt : ν K ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ K}.Finite := fun i =>
    _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ K h𝓖 hK0 hKt (a i)
  refine ⟨fun i => ((hfin i).subset fun γ hγ => (hmem i γ).1 hγ).to_subtype, ?_⟩
  intro f hf f' hf'
  have hf0 : ∀ (γ : Γ) (h : H) (k : J), f (π γ * h * k) = (χ k : ℂ) • ρ γ (f h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf
    exact hf
  have hf0' : ∀ (γ : Γ) (h : H) (k : J), f' (π γ * h * k) = (χ k : ℂ) • ρ γ (f' h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf'
    exact hf'
  set Fψ : G → ℂ := fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) with hFψ
  have hFψ' : ∀ h, Fψ h = inner ℂ (f (π h)) (f' (π h)) := fun h => hρ _ _ _
  have hleft : ∀ γ ∈ Γ, ∀ x : G, Fψ (γ * x) = Fψ x := by
    intro γ hγ x
    have e := hf0 ⟨γ, hγ⟩ (π x) 1
    have e' := hf0' ⟨γ, hγ⟩ (π x) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at e e'
    rw [hFψ', hFψ', map_mul, e, e', hρ]
  have hright : ∀ k ∈ K, ∀ x : G, Fψ (x * k) = Fψ x := by
    intro k hk x
    have e := hf0 1 (π x) ⟨π k, hk⟩
    have e' := hf0' 1 (π x) ⟨π k, hk⟩
    simp only [OneMemClass.coe_one, map_one, one_mul, Module.End.one_apply] at e e'
    rw [hFψ', hFψ', map_mul, e, e', inner_smul_left, inner_smul_right, ← mul_assoc,
      Complex.conj_mul', hχ, Complex.ofReal_one, one_pow, one_mul]
  have hreps : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a i * k := by
    intro x
    obtain ⟨i, ⟨γ, k, hk⟩, huniq⟩ := hy (π x)
    refine ⟨i, ⟨γ, γ.2, (a i)⁻¹ * (γ : G)⁻¹ * x, ?_, by group⟩, ?_⟩
    · change π ((a i)⁻¹ * (γ : G)⁻¹ * x) ∈ J
      have hk' : π x = π γ * y i * k := hk
      rw [map_mul, map_mul, map_inv, map_inv, ha i, hk']
      simpa [mul_assoc] using k.2
    · rintro j ⟨γ', hγ', k', hk', hx⟩
      refine huniq j ⟨⟨γ', hγ'⟩, ⟨π k', hk'⟩, ?_⟩
      change π x = π γ' * y j * π k'
      rw [hx, map_mul, map_mul, ha j]
  have hmain := _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ K 𝓖 h𝓖 ho hKt I a hreps
    (fun i => by
      have := (hfin i).image (fun γ : Γ => (γ : G))
      refine this.subset ?_
      rintro z ⟨hz, hzK⟩
      exact ⟨⟨z, hz⟩, hzK, rfl⟩) Fψ hleft hright
  obtain ⟨-, hint, heq⟩ := hmain
  refine ⟨hint, ?_⟩
  change ∫ h in 𝓖, Fψ h ∂ν = _
  rw [heq, h1]
  unfold _root_.Formalism.IndefR.Bridge.adInner
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : {γ | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ K}.ncard =
      Nat.card (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i)) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hmem i _).2 z.2.2⟩
        invFun := fun γ => ⟨γ.1.1, γ.1.2, (hmem i _).1 γ.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hFψ', ha i, hcard]

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private lemma norm_character_eq_one_of_finite {A : Type} [Group A] [Finite A] (φ : A →* ℂˣ) (a : A) :
    ‖((φ a : ℂˣ) : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card A) _ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.norm_levFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) (L : _root_.Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) :
    ‖(_root_.Formalism.L2.DIV.levFn β L x : ℂ)‖ = 1 := by
  unfold _root_.Formalism.L2.DIV.levFn _root_.Formalism.L2.DIV.ext1
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_character_eq_one_of_finite,
    Finset.prod_const_one, mul_one]
  split_ifs
  · exact norm_character_eq_one_of_finite _ _
  · simp

end GlobalTheory.InnerClassSum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.mulVec_lamHat_bound | exact GlobalTheory.LatMatch.mulVec_lamHat_bound | (intros; apply GlobalTheory.LatMatch.mulVec_lamHat_bound <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricLiftDet

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta Formalism.MainNotions.S Formalism.IndefR.Mult MeasureTheory

variable {D : D7} {n : ℕ}

theorem finite_maximalSpectrum_kP (P : Pl D.host.E) : Finite (MaximalSpectrum (kP P)) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  exact Finite.of_subsingleton

theorem exists_detOne_lift (P : Pl D.host.E) (k : GL (Fin n) (kP P)) (hk : Matrix.GeneralLinearGroup.det k = 1) :
    ∃ Y : Matrix (Fin n) (Fin n) (𝓞 D.host.E), Y.map (Ideal.Quotient.mk P.asIdeal) = k.1 ∧ Y.det = 1 := by
  haveI := finite_maximalSpectrum_kP P
  have hk' : k.1.det = 1 := by
    have := congrArg Units.val hk
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  obtain ⟨Y, hY⟩ := GlobalTheory.specialLinearGroup_map_surjective (n := Fin n) (f := Ideal.Quotient.mk P.asIdeal)
    Ideal.Quotient.mk_surjective ⟨k.1, hk'⟩
  exact ⟨Y.1, congrArg Subtype.val hY, Y.2⟩

theorem idem_mul_pow {A : Type} [CommRing A] {p : A} (hp : p * p = p) (m : ℕ) : p * p ^ m = p := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, hp]

theorem idem_mul_det {A : Type} [CommRing A] {m : ℕ} {p : A} (hp : p * p = p) {a b : Matrix (Fin m) (Fin m) A}
    (h : p • a = p • b) : p * a.det = p * b.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin] at h1
  have hpow : p * p ^ m = p := idem_mul_pow hp m
  calc p * a.det = p * p ^ m * a.det := by rw [hpow]
    _ = p * p ^ m * b.det := by rw [mul_assoc, h1, ← mul_assoc]
    _ = p * b.det := by rw [hpow]



theorem exists_local_lift_det : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D},
    Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 →
    ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧
      (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  intro D V β Λ N hB P e he k hk
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet1⟩ := exists_detOne_lift P k hk
  have hdet : Ideal.Quotient.mk P.asIdeal Y₀.det ≠ 0 := by
    rw [hdet1, map_one]; exact one_ne_zero
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hYdet : Y.det = 1 := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet1, map_one]
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hκd := hκ
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ

  have hD : e * (mt V κ).det = e := by
    have he2 : finSw D e * finSw D e = finSw D e := by rw [← RingHom.map_mul, he.1.1]
    have h1 := idem_mul_det he2 hκd
    have e1 : (finE V κ).1 = (mt V κ).map (finSw D) := rfl
    have e2 : (β.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
        one_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hYdet, map_one]
    rw [e1, e2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_one, ← RingHom.map_mul] at h1
    have h2 : finPart D (e * (mt V κ).det) = finPart D e := (swp_bij (F := D.host.F) (E := D.host.E)).1 h1
    refine GlobalTheory.SplitScalar.adele_ext ?_ h2
    rw [RingHom.map_mul, GlobalTheory.PlaceModelSum.infPart_split he.1, zero_mul]
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_, ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
    exact Matrix.ext fun i j => resS_oToS P _
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · show ((1 : (AE D)ˣ) : AE D) = e * (mt V κ).det + (1 - e)
    rw [hD, Units.val_one]
    ring

end GlobalTheory.ParahoricLiftDet

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.PrincLevChar

theorem castDict_apply {D : D7} {Y : Type} {V W : HSp D} (hV : V = W) (μ : GA D V → Y) (k : GA D W) :
    castDict hV μ k = μ (cast (congrArg (GA D) hV.symm) k) := by
  subst hV
  rfl



theorem char_eq_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hpb i σ hσ hV k hk
  rw [castDict_apply]
  exact GlobalTheory.T.dictionary_character_trivial_on_principal_level T R κ v₀ hL ht hpb i (res T σ) hσ hV _
    (((GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hpb i σ hσ hV).1 k).1 hk)

end GlobalTheory.HolDict.PrincLevChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothStable

theorem rep_mem_sm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w ∈ M.sm τ, M.rep τ g w ∈ M.sm τ := by
  intro D V S M τ g hg w hw
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have e : M.sm τ = GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) :=
    Submodule.span_eq (GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
  rw [e] at hw ⊢
  exact GlobalTheory.SmVec.rep_mem (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ))
    (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hσ) hw hg

end GlobalTheory.SmoothStable
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.torusLattice_standard_points_scaled_embedding : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b), x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) → ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧ x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  first | exact @GlobalTheory.LaStdEntries.La_std_rep | exact GlobalTheory.LaStdEntries.La_std_rep | (intros; apply GlobalTheory.LaStdEntries.La_std_rep <;> assumption)
end
