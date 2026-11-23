module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInner
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle274
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle288
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle427
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle277
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.petersson_stepZeroScalarForms_eq_pos_mul_inner : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := by
  first | exact @GlobalTheory.StepZeroNorm.integral_rd_eq_inner | exact GlobalTheory.StepZeroNorm.integral_rd_eq_inner | (intros; apply GlobalTheory.StepZeroNorm.integral_rd_eq_inner <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_thetaLiftSpaces_positiveIndex_with_lineNorms : ∀ (D : D7) (u : D.what₂.Word), (∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) → (∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (b : BesAt V (D.sp.X j) ρ), V.rank = D.R.rankY j ∧ V.SigOK ∧ (∀ τ, V.sig τ = sigYD D.R j) ∧ (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)) ∧ ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (_ : JacAt V (D.sp.X (j + 1)) ρ), V.rank = D.R.rankY (j + 1) ∧ V.SigOK ∧ ∀ τ, V.sig τ = sigYD D.R (j + 1) := by
  first | exact @GlobalTheory.SeeSaw.YRat.spaces_of_index | exact GlobalTheory.SeeSaw.YRat.spaces_of_index | (intros; apply GlobalTheory.SeeSaw.YRat.spaces_of_index <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem isCompact_ginfC_of_ontoUni (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hθ : IsInfFam θ) (hr : OntoUni (fun k : GinfC V => inB θ V B k.1)) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hB : ∀ τ, IsUnit (B τ).det := by
    intro τ
    by_contra hn
    have h0 := hr.uni 1 τ
    have e : inB (Formalism.IndefR.Eqv.thetaC D) V B (1 : GinfC V).1 τ = 0 := by
      simp only [inB, Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.zero_mul]
    rw [e] at h0
    have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 0 := by
      have := Matrix.mem_unitaryGroup_iff.mp h0
      simpa using this.symm
    have hB1 : B τ = 1 := by
      calc B τ = B τ * 1 := (Matrix.mul_one _).symm
        _ = 0 := by rw [h1, Matrix.mul_zero]
        _ = 1 := h1.symm
    exact hn (by rw [hB1, Matrix.det_one]; exact isUnit_one)
  have hconj : ∀ τ (M : Matrix (Fin V.rank) (Fin V.rank) ℂ), B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = M := by
    intro τ M
    calc B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = (B τ * (B τ)⁻¹) * M * (B τ * (B τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [Matrix.mul_nonsing_inv _ (hB τ), Matrix.one_mul, Matrix.mul_one]
  have hU : ∀ u : D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ,
      Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) := by
    intro u
    obtain ⟨k, hk⟩ := hr.onto (fun τ => (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)) (fun τ => (u τ).2)
    have e : (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) =
        fun τ => infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) (k : GA D V) := by
      funext τ
      have := congrFun hk τ
      rw [← this]
      exact hconj τ _
    rw [e]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V _
  have : CompactSpace (unitaryGroup (Fin V.rank) ℂ) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.isCompact_unitaryGroup _ _)
  let Ψ : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) → GA D V := fun u => Formalism.IndefR.Eqv.famH D V _ (hU u)
  have hg : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
      fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹ :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_subtype_val.comp (continuous_apply τ))).matrix_mul
      continuous_const
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact GlobalTheory.HaarReal.continuous_famM.comp hg
    · have hi : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
          fun τ => Formalism.IndefR.Eqv.ginv D V τ (B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) :=
        continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
          continuous_const
      exact GlobalTheory.HaarReal.continuous_famM.comp hi
  have hsub : (GinfC V : Set (GA D V)) ⊆ Set.range Ψ := by
    intro g hg
    refine ⟨fun τ => ⟨inB (Formalism.IndefR.Eqv.thetaC D) V B g τ, hr.uni ⟨g, hg⟩ τ⟩, ?_⟩
    refine (Formalism.IndefR.Eqv.famH_unique D V _ (hU _) g hg fun τ => ?_).symm
    exact (hconj τ _).symm
  exact (isCompact_range hΨ).of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hsub

end GlobalTheory.SeeSaw

namespace GlobalTheory.SeeSaw

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → OntoUni (fun k : GinfC V => inB θ V B k.1) → BorelSpace (GinfC V) ∧ CompactSpace (GinfC V) ∧ (∀ g ∈ GfC V, ∀ k ∈ GinfC V, g * k = k * g) ∧ ∃ ν : Measure (GinfC V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (v : Vol V) (U : Subgroup (GA D V)) (cl : Type) [Fintype cl] (h : cl → GA D V), IsReps V U h → 0 < volLev v U ∧ (∀ a, 0 < stabOrd U (h a)) ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ κ ∈ U, ∀ g, Φ (g * κ) = Φ g) → ∫ g in v.𝓕, Φ g ∂v.μ = (volLev v U : ℂ) * ∑ a, ((stabOrd U (h a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h a * k.1) ∂ν := by
  intro D θ V B hθ hr
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  have hK : IsCompact (GinfC V : Set (GA D V)) := isCompact_ginfC_of_ontoUni D θ V B hθ hr
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hcf : ∀ {a b : GA D V}, a ∈ GinfC V → b ∈ GfC V → a * b = b * a := fun ha hb =>
    Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb
  refine ⟨inferInstance, inferInstance, fun g hg k hk => (hcf hk hg).symm, ?_⟩
  let ν : Measure (GinfC V) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν :=
    ⟨by simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))))⟩
  refine ⟨ν, inferInstance, inferInstance, ?_⟩
  intro v U cl _ h hU
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hmemK : ∀ g, g ∈ K ↔ ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ := fun g => by
    rw [← SetLike.mem_coe, hKset]; rfl
  have hvol : volLev v U = (v.μ K).toReal := by
    simp only [volLev]
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hU.cpt
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      hU.opn.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho
    rw [hmemK]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  have huniq : ∀ x : GA D V, ∃! i, ∃ γ ∈ GQ V, ∃ k ∈ K, x = γ * h i * k := by
    intro x
    obtain ⟨γ, hγ, c, k, hk, κ, hκ, e⟩ := hU.dec x
    refine ⟨c, ⟨γ, hγ, k * κ, (hmemK _).2 ⟨k, hk, κ, hκ, rfl⟩, by rw [e]; group⟩, ?_⟩
    rintro c' ⟨γ', hγ', k', hk', e'⟩
    obtain ⟨k₁, hk₁, κ₁, hκ₁, rfl⟩ := (hmemK _).1 hk'
    refine (hU.uniq c c' (γ'⁻¹ * γ) (mul_mem (inv_mem hγ') hγ) (k * k₁⁻¹) (mul_mem hk (inv_mem hk₁)) (κ * κ₁⁻¹)
      (mul_mem hκ (inv_mem hκ₁)) ?_).symm
    have hc1 : k₁⁻¹ * (κ * κ₁⁻¹) = (κ * κ₁⁻¹) * k₁⁻¹ := hcf (inv_mem hk₁) (hU.le (mul_mem hκ (inv_mem hκ₁)))
    have e2 : h c' = γ'⁻¹ * x * (k₁ * κ₁)⁻¹ := by rw [e']; group
    rw [e2, e, _root_.mul_inv_rev]
    calc γ'⁻¹ * (γ * (h c * k) * κ) * (κ₁⁻¹ * k₁⁻¹) = γ'⁻¹ * γ * (h c * k) * ((κ * κ₁⁻¹) * k₁⁻¹) := by group
      _ = γ'⁻¹ * γ * (h c * k) * (k₁⁻¹ * (κ * κ₁⁻¹)) := by rw [hc1]
      _ = γ'⁻¹ * γ * (h c * (k * k₁⁻¹)) * (κ * κ₁⁻¹) := by group
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite := by
    intro i
    have hC : IsCompact ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V))) :=
      hKc.image ((continuous_const.mul continuous_id).mul continuous_const)
    have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have hTc : IsCompact (((↑) : GQ V → GA D V) ⁻¹' ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V)))) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hTc.finite_of_discrete.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hk⟩
    exact ⟨⟨γ, hγ⟩, ⟨_, hk, by group⟩, rfl⟩
  have hst : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard = stabOrd U (h i) := by
    intro i
    have hs : {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K} =
        Subtype.val '' {γ : GQ V | ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h i = h i * k * κ} := by
      ext γ
      constructor
      · rintro ⟨hγ, hk⟩
        obtain ⟨k, hk, κ, hκ, e⟩ := (hmemK _).1 hk
        refine ⟨⟨γ, hγ⟩, ⟨k, hk, κ, hκ, ?_⟩, rfl⟩
        calc γ * h i = h i * ((h i)⁻¹ * γ * h i) := by group
          _ = h i * k * κ := by rw [e, mul_assoc]
      · rintro ⟨γ, ⟨k, hk, κ, hκ, e⟩, rfl⟩
        refine ⟨γ.2, (hmemK _).2 ⟨k, hk, κ, hκ, ?_⟩⟩
        calc (h i)⁻¹ * γ.1 * h i = (h i)⁻¹ * (γ.1 * h i) := by group
          _ = k * κ := by rw [e]; group
    rw [hs, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨by rw [hvol]; exact ENNReal.toReal_pos hKpos.ne' hKfin, fun a => ?_, ?_⟩
  · rw [← hst]
    exact (Set.ncard_pos (hfin a)).mpr ⟨1, (GQ V).one_mem, by simpa using K.one_mem⟩
  intro Φ hΦc hΦl hΦr
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) v.μ (GQ V) K U v.𝓕 v.fund hKo hKfin
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val
    (fun k hk => by
      obtain ⟨a, ha, κ, hκ, rfl⟩ := (hmemK _).1 hk
      exact ⟨κ, hκ, ⟨a, ha⟩, hcf ha (hU.le hκ)⟩)
    (fun k hk w => (hcf w.2 (hU.le hk)).symm) cl h huniq hfin Φ hΦc hΦl hΦr
  rw [he, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hst i]
  rfl

end GlobalTheory.SeeSaw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]


open Formalism.IndefR.Eqv in
theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finsetSum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni


open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in
theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
end
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.AbsRange
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRangeUniform

theorem abs_range_constants_first : ∀ Cg cb Cu cT CT C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl C0 hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dite_eq_left (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dite_eq_left l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRangeUniform
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  first | exact @GlobalTheory.BiJoinDeriv.dLine_join | exact GlobalTheory.BiJoinDeriv.dLine_join | (intros; apply GlobalTheory.BiJoinDeriv.dLine_join <;> assumption)
end
