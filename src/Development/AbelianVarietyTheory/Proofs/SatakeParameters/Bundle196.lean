module

public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

theorem _root_.GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
  first | exact @GlobalTheory.InfDiagExt.ideleMap_infDiag | exact GlobalTheory.InfDiagExt.ideleMap_infDiag | (intros; apply GlobalTheory.InfDiagExt.ideleMap_infDiag <;> assumption)
end

section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  first | exact @GlobalTheory.ContraPair.iso_of_common_functional | exact GlobalTheory.ContraPair.iso_of_common_functional | (intros; apply GlobalTheory.ContraPair.iso_of_common_functional <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc

theorem goodModelTwo_scaleOne : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[2], ∃ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W ∧
      ‖W.a₁‖ = 1 := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  obtain ⟨hsq, -, hcm⟩ := LocJets.data ha hd lam hlam hok
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨c, hc, W', ⟨e2, e3⟩, ⟨h1, h2, h3, h4, h6, hΔ⟩, ha1⟩ := hIn.modelTwo D.host.d L hsq h8 hcm ι
  have hL1 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hlat]; rfl
    obtain ⟨f2, f3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
    rw [← f2, ← f3]
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have hh := Formalism.L2.Th1.F.homogeneity L c hc
  have s2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hh.2.2.2.2.2.2.2.2.2.1
  have s3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hh.2.2.2.2.2.2.2.2.2.2
  have g2W : W'.c₄ / 12 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := e2
  have g3W : W'.c₆ / 216 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := e3
  set u : ℂ_[2] := ι c with hu
  have hu0 : u ≠ 0 := by simpa [hu] using hc

  have hW'Δ : W'.Δ = (u ^ 12)⁻¹ := by
    have hrel := W'.c_relation
    have hc4 : W'.c₄ = 12 * ((u ^ 4)⁻¹ * ι L.g₂) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s2, ← g2W]; ring
    have hc6 : W'.c₆ = 216 * ((u ^ 6)⁻¹ * ι L.g₃) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s3, ← g3W]; ring
    have hι1 : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hL1, map_one]
    rw [hc4, hc6] at hrel
    have h1728 : (1728 : ℂ_[2]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hrel]
    field_simp
    linear_combination (1728 : ℂ_[2]) * hι1
  have hun : ‖u‖ = 1 := by
    rw [hW'Δ, norm_inv, norm_pow] at hΔ
    have h12 : ‖u‖ ^ 12 = 1 := by
      have hpos : 0 < ‖u‖ ^ 12 := pow_pos (norm_pos_iff.2 hu0) _
      field_simp at hΔ; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  let C : WeierstrassCurve.VariableChange ℂ_[2] := ⟨(Units.mk0 u hu0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) = u := by simp [C]
  refine ⟨C • W', ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (C • W').c₄ / 12 = ι L.g₂
    rw [WeierstrassCurve.variableChange_c₄, hCu, mul_div_assoc, g2W, s2, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · show (C • W').c₆ / 216 = ι L.g₃
    rw [WeierstrassCurve.variableChange_c₆, hCu, mul_div_assoc, g3W, s3, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hun, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hCu]
    simp only [C, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hun, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hun,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hun, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hCu, norm_mul, norm_pow, hun, one_pow, one_mul]; exact hΔ
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact ha1

end GlobalTheory.ThLoc
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.KLift

theorem isOpen_map_restrictScalars {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [FiniteDimensional K L]
    (N : Subgroup (Ω ≃ₐ[L] Ω)) (hN : IsOpen (N : Set (Ω ≃ₐ[L] Ω))) :
    IsOpen ((N.map (AlgEquiv.restrictScalarsHom K)) : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨E', hE', hsub⟩ := (krullTopology_mem_nhds_one_iff L Ω _).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional K E' := Module.Finite.trans L E'
  haveI : FiniteDimensional K (E'.restrictScalars K) := this
  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (E'.restrictScalars K))
  intro g hg
  have hfix : ∀ x ∈ E', g x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg x hx
  let g' : Ω ≃ₐ[L] Ω := { g.toRingEquiv with commutes' := fun l => hfix _ (E'.algebraMap_mem l) }
  refine ⟨g', hsub ?_, ?_⟩
  · exact (IntermediateField.mem_fixingSubgroup_iff E' g').2 hfix
  · ext x; rfl

end GlobalTheory.KLift


open GlobalTheory.KLift in
theorem GlobalTheory.KLift.exists_cm_lift : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω), IsOpen (N : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' u → _root_.ReciprocityTheory.Gal.Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : _root_.Formalism.ConjugateSelfDual.G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  intro Ω _ E _ _ _ _ _ v N hN
  classical
  haveI hFE : Algebra.IsAlgebraic (maximalRealSubfield E) E := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω :=
    Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI hcF : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.finite_decompositionGroups_cover_openQuotient Ω (maximalRealSubfield E) v
    (N.map (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))) (isOpen_map_restrictScalars N hN)
  refine ⟨T, hvT, ?_⟩
  intro F₁ hfd hgal hsolv hreal hdec
  have hre : ∀ z ∈ F₁, ∀ φ : Ω →+* ℂ, star (φ z) = φ z := by
    intro z hz φ
    have h := ComplexEmbedding.isReal_iff.1 (hreal (φ.comp F₁.val.toRingHom))
    have := RingHom.congr_fun h ⟨z, hz⟩
    rw [ComplexEmbedding.conjugate_coe_eq] at this
    simpa using this
  let M : IntermediateField E Ω := IntermediateField.adjoin E (F₁ : Set Ω)
  have hF₁M : ∀ z ∈ F₁, z ∈ M := fun z hz => IntermediateField.subset_adjoin E _ hz
  have hfix : ∀ g : _root_.Formalism.ConjugateSelfDual.G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z := by
    intro g
    constructor
    · intro h z hz; exact h ⟨z, hF₁M z hz⟩
    · intro h x
      have hle : M ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        intro z hz
        rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        intro f hf
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
        exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := g)).2 (h z hz) k
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) g (Subgroup.mem_zpowers g)
  haveI : Normal (maximalRealSubfield E) F₁ := hgal.to_normal
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  haveI : Normal (maximalRealSubfield E) Ω := IsAlgClosure.normal _ Ω
  have hmap : ∀ σ : Ω →ₐ[E] Ω, ∀ z ∈ F₁, σ z ∈ F₁ := by
    intro σ z hz
    exact IntermediateField.normal_iff_forall_map_le.1 inferInstance
      (σ.restrictScalars (maximalRealSubfield E)) ((IntermediateField.mem_map _).2 ⟨z, hz, rfl⟩)
  haveI hMn : Normal E M := by
    refine IntermediateField.normal_iff_forall_map_le.2 fun σ => ?_
    show (IntermediateField.adjoin E (F₁ : Set Ω)).map σ ≤ IntermediateField.adjoin E (F₁ : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hF₁M _ (hmap σ z hz)
  haveI hMfd : FiniteDimensional E M := by
    let b := Module.finBasis (maximalRealSubfield E) F₁
    let S : Set Ω := Set.range (fun i => ((b i : F₁) : Ω))
    haveI : Finite S := (Set.finite_range _).to_subtype
    have hint : ∀ x ∈ S, IsIntegral E x := fun x _ => Algebra.IsIntegral.isIntegral x
    haveI := IntermediateField.finiteDimensional_adjoin hint
    have hle : M ≤ IntermediateField.adjoin E S := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      have h2 := congrArg (fun y : F₁ => (y : Ω)) hsum
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h2
      have : z = ∑ i, algebraMap E Ω ((b.repr ⟨z, hz⟩ i : maximalRealSubfield E) : E) * ((b i : F₁) : Ω) := by
        refine h2.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E Ω]
        rfl
      rw [SetLike.mem_coe, this]
      exact sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).toRingHom.injective
  haveI : NumberField M := NumberField.of_module_finite E M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  haveI : IsGalois E M := ⟨⟩
  have hCM : IsCMField M := (GlobalTheory.T.cm_subfields_compositum_closed Ω E).2.2 M (F₁ : Set Ω) (fun x hx φ => by
      have := hre x hx φ
      rw [Complex.star_def] at this
      exact Complex.conj_eq_iff_im.1 this) rfl
  haveI : Group.IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) := hsolv
  have hsolvM : IsSolvable (M ≃ₐ[E] M) := by
    let ψ : (Ω ≃ₐ[E] Ω) →* (M ≃ₐ[E] M) := AlgEquiv.restrictNormalHom M
    let φ : (Ω ≃ₐ[E] Ω) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (AlgEquiv.restrictNormalHom F₁).comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))
    have hψ : Function.Surjective ψ := AlgEquiv.restrictNormalHom_surjective Ω
    have hker : ψ.ker = φ.ker := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      have e1 : ψ g = 1 ↔ ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        refine forall_congr' fun x => ?_
        rw [← (algebraMap M Ω).injective.eq_iff]
        show algebraMap M Ω (AlgEquiv.restrictNormal g M x) = _ ↔ _
        rw [AlgEquiv.restrictNormal_commutes]
      have e2 : φ g = 1 ↔ ∀ z ∈ F₁, g z = z := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        constructor
        · intro h z hz
          have := congrArg (algebraMap F₁ Ω) (h ⟨z, hz⟩)
          rw [show φ g ⟨z, hz⟩ = AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ ⟨z, hz⟩
            from rfl, AlgEquiv.restrictNormal_commutes] at this
          exact this
        · intro h y
          apply (algebraMap F₁ Ω).injective
          show algebraMap F₁ Ω (AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ y) = _
          rw [AlgEquiv.restrictNormal_commutes]
          exact h y y.2
      rw [e1, e2, hfix]
    let ρ : (M ≃ₐ[E] M) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (QuotientGroup.kerLift φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom)
    have hinj : Function.Injective ρ :=
      (QuotientGroup.kerLift_injective φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.injective)
    exact solvable_of_solvable_injective hinj
  refine ⟨M, inferInstance, inferInstance, hCM, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨inferInstance, hsolvM, ?_⟩, hfix, ?_⟩
  · intro g
    obtain ⟨u, hu, A', hA', x, hx, n', hn', hgx⟩ :=
      hT (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hn'
    have hxF : ∀ z ∈ F₁, x z = z := fun z hz =>
      (IntermediateField.mem_fixingSubgroup_iff F₁ x).1 (hdec u hu A' hA' hx) z hz
    have hyx : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (g * n⁻¹) = x := by
      rw [map_mul, map_inv, hgx, mul_inv_cancel_right]
    have hyM : ∀ m : M, (g * n⁻¹) (algebraMap M Ω m) = algebraMap M Ω m :=
      (hfix (g * n⁻¹)).2 fun z hz => (DFunLike.congr_fun hyx z).trans (hxF z hz)
    refine ⟨{ (g * n⁻¹) with commutes' := hyM }, n, hn, ?_⟩
    ext w
    show g w = (g * n⁻¹) (n w)
    simp
  · intro z hz
    refine ⟨⟨z, hF₁M z hz⟩, ?_, rfl⟩
    intro φ
    letI : Algebra M ℂ := φ.toAlgebra
    let ψ : Ω →ₐ[M] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : φ ⟨z, hF₁M z hz⟩ = ψ z := (ψ.commutes ⟨z, hF₁M z hz⟩).symm
    rw [h1]
    exact hre z hz ψ.toRingHom
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3Split

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem isLabElt_of_isTEnv : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → _root_.GlobalTheory.Hk3.IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → _root_.GlobalTheory.Hk3.IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  intro D V Pl0 pl ok i x
  refine ⟨fun hk h => ?_, fun h => ?_, splitLab_pairwise _ _⟩
  · obtain ⟨α, ⟨e, ϖ, he, h1, h2, hα⟩, hx⟩ := h hk
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    obtain ⟨hf1, hf2, -⟩ := H.2.2.1 _ _ _ hI
    obtain ⟨⟨L, hL⟩, -⟩ := H.1 _ hf1 hf2
    exact ⟨e, e + cA D e, ϖ, α⁻¹, hI, h1, h2, inv_mem hα.1, hx, (hL _).1 (inv_mem ((hL _).2 hα.2.1)),
      GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V _ e ϖ _ α he h1 h2 hk hα⟩
  · obtain ⟨e, α, he, hα, hs, hx⟩ := h
    exact ⟨e, e + cA D e, α, Or.inl ⟨he, rfl⟩, hα, hx, hs⟩

end GlobalTheory.Hk3Split
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), (∀ d R, SphOp V P d R → R.card = (rep V P d).card ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R, π γ u = opOf π P (Finsupp.single d 1) u) ∧ (∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u) ∧ (IsLab V P (List.replicate V.rank 0) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (List.replicate V.rank 0) 1) u = u) ∧ (∀ d, (IsLab V P d ↔ IsLab V P (dualLab d)) ∧ (rep V P (dualLab d)).card = (rep V P d).card) ∧ ∀ e f g, IsPrimeIdem P e f → SuppF V f g → ∃ d, IsLab V P d ∧ (∀ γ ∈ rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g * k₂) ∧ ∀ γ ∈ rep V P (dualLab d), ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g⁻¹ * k₂ := by
  first | exact @GlobalTheory.SphLabelOps.label_operators | exact GlobalTheory.SphLabelOps.label_operators | (intros; apply GlobalTheory.SphLabelOps.label_operators <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST (by first | exact hN | exact hN.1)
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

theorem _root_.GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) = infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  first | exact @GlobalTheory.GalReal.ideleMap_ideleNorm_infId | exact GlobalTheory.GalReal.ideleMap_ideleNorm_infId | (intros; apply GlobalTheory.GalReal.ideleMap_ideleNorm_infId <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.elementary_divisors_inv_hecke_element_split_place : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  first | exact @GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt | exact GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt | (intros; apply GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt <;> assumption)
end
