module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  first | exact @GlobalTheory.VacCocycle.psi_half_symp_add | exact GlobalTheory.VacCocycle.psi_half_symp_add | (intros; apply GlobalTheory.VacCocycle.psi_half_symp_add <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ThetaLineDeriv

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)
open scoped Matrix Classical

variable {F : Type} [Field F] [NumberField F]

theorem comp_mem_schA {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem decay_majorant {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ c : (Fin N → F) → ℝ, Summable c ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨fun ξ => C * c ξ, hcs.mul_left C, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

theorem schA_majorant {κ : Type} [Fintype κ] (hF : IsTotallyReal F)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ω : Set (κ → AF F)) (hω : IsCompact ω) :
    ∃ c : (κ → F) → ℝ, Summable c ∧
      ∀ ξ : κ → F, ∀ y ∈ ω, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  let σ := Fintype.equivFin κ
  have hc : Continuous fun y : κ → AF F => y ∘ σ.symm := continuous_pi fun i => continuous_apply _
  obtain ⟨c, hcs, hcb⟩ := decay_majorant hF
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (comp_mem_schA σ hΦ)) _ (hω.image hc)
  refine ⟨fun ξ => c (ξ ∘ σ.symm), (Equiv.arrowCongr σ (Equiv.refl F)).summable_iff.2 hcs, fun ξ y hy => ?_⟩
  have h := hcb (ξ ∘ σ.symm) _ ⟨y, hy, rfl⟩
  have e : (rat (ξ ∘ σ.symm) + y ∘ σ.symm) ∘ σ = (fun i => algebraMap F (AF F) (ξ i)) + y := by
    funext i
    simp [rat]
  rwa [e] at h

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd : Continuous (realAd F) :=
  Continuous.prodMk (continuous_ofMixed.comp (continuous_algebraMap ℝ _)) continuous_const

theorem realAd_add (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add (f := _)]

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]

theorem schr_smul_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v : (κ → R) × (κ → R)) (a b : R) (Φ : (κ → R) → ℂ) (z : κ → R) :
    schr ψ ((a + b) • v) Φ z = schr ψ (a • v) (schr ψ (b • v) Φ) z := by
  simp only [schr, Prod.smul_fst, Prod.smul_snd, ← mul_assoc, ← AddChar.map_add_eq_mul, add_smul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  first
    | linear_combination (a * b * (v.1 ⬝ᵥ v.2)) * invOf_mul_self (2 : R)
    | linear_combination (-(a * b * (v.1 ⬝ᵥ v.2))) * invOf_mul_self (2 : R)

variable [Invertible (2 : AF F)] {κ : Type} [Fintype κ]

theorem hasDerivAt_schr (ψ : AddChar (AF F) ℂ) (v : (κ → AF F) × (κ → AF F))
    {Φ Φ' : (κ → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0)
    (z : κ → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (schr ψ (realAd F t • v) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) (schr ψ (realAd F t • v) Φ' z) (t - t) := by
    have e : (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) = fun h =>
        ψ (z ⬝ᵥ (realAd F t • v).2 + ⅟(2 : AF F) * ((realAd F t • v).1 ⬝ᵥ (realAd F t • v).2)) *
          schr ψ (realAd F h • v) Φ (z + (realAd F t • v).1) := by
      funext h
      rw [realAd_add, schr_smul_add]
      rfl
    rw [e, sub_self]
    exact (hd _).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

theorem hasDerivAt_thetaSum_schr (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (v : (κ → AF F) × (κ → AF F)) {Φ Φ' : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΦ' : Φ' ∈ schA F κ)
    (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0) (w : (κ → AF F) × (κ → AF F)) :
    HasDerivAt (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) (thetaSum F (schr ψ w Φ')) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : realAd F 0 • v = 0 := by rw [realAd_zero, zero_smul]
  set ω : Set (κ → AF F) := (fun s : ℝ => w.1 + (realAd F s • v).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image
    (continuous_const.add (continuous_pi fun i => continuous_realAd.mul (continuous_const (y := v.1 i))))
  obtain ⟨c, hcs, hcb⟩ := schA_majorant hF hΦ' ω hωc
  obtain ⟨c₀, hcs₀, hcb₀⟩ := schA_majorant hF hΦ {w.1} isCompact_singleton
  set r : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i) with hr
  set ph : (κ → F) → ℂ := fun ξ => ψ (r ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) =
      fun t => ∑' ξ : κ → F, ph ξ * schr ψ (realAd F t • v) Φ (r ξ + w.1) := rfl
  have h0 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (realAd F 0 • v) Ψ = Ψ := fun Ψ => by
    rw [hM0]
    funext z
    simp [schr]
  have hv : thetaSum F (schr ψ w Φ') = ∑' ξ : κ → F, ph ξ * schr ψ (realAd F 0 • v) Φ' (r ξ + w.1) := by
    rw [h0]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected hcs isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr ψ v hd (r ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (realAd F t • v).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, schr, norm_mul, hnorm, one_mul, add_assoc]
    exact this
  · refine Summable.of_norm_bounded hcs₀ fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simp only [h0, ph, norm_mul, hnorm, one_mul]
    exact this

end SlopeTestRemainingChoices

end GlobalTheory.ThetaLineDeriv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

theorem GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  intro F _ _ U _ _ B κ _ co ψ hF hψ u Φ hΦ Φ' hΦ' hd w
  simp only [Darboux.rho, map_smul] at hd ⊢
  exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr ψ hF hψ (co.e u) hΦ hΦ' hd (co.e w)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

noncomputable section

namespace GlobalTheory.GaussUnr

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

theorem gauss_mul_unram : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ), (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ ∧
      ∃ y : (Fv F v)ˣ, gauss ψ (ν₀ * ξ) = (((ξ y)⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ := by
  intro F _ _ ψ v ν₀ ξ hξ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hunit : ∀ x : (Fv F v)ˣ, valuation (Fv F v) (x : Fv F v) = 1 → ξ x = 1 := fun x hx => by
    apply hξ x
    · exact (val_le_one_iff v _).1 hx.le
    · apply (val_le_one_iff v _).1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hce : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, CondLE]
    refine forall₂_congr fun x hx => ?_
    rw [MonoidHom.mul_apply, hunit x hx.1, mul_one]
  refine ⟨hce, ?_⟩
  unfold gauss
  rw [hce]
  generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ = c
  rcases Nat.eq_zero_or_pos c with h0 | hc1
  · subst h0
    have hsu : ∀ a b : (Res (Fv F v) 0)ˣ, a = b := fun a b =>
      Units.ext ((Ideal.Quotient.subsingleton_iff.2 (by simp)).elim _ _)
    classical
    rw [Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim), Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim)]
    by_cases h : ((Quotient.out (1 : (Res (Fv F v) 0)ˣ).1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · refine ⟨1, ?_⟩
      rw [dite_eq_left h, dite_eq_left h, mul_zero]
    · refine ⟨Units.mk0 _ h, ?_⟩
      rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, mul_inv, Units.val_mul, mul_comm (((ν₀ _)⁻¹ : ℂˣ) : ℂ),
        mul_assoc]
  · refine ⟨1, ?_⟩
    rw [map_one, inv_one, Units.val_one, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, hunit _ (val_rep_unit hϖ hc1 y), mul_one]

end GlobalTheory.GaussUnr
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.triple_local_gl_embedding_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ g : GL (Fin a') (Fv F v),
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (chrW X.ν t (GlobalTheory.SplitFlip.gdet g) : ℂ) ^ 2 ∨
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (((chrW X.ν t (GlobalTheory.SplitFlip.gdet g))⁻¹ : ℂˣ) : ℂ) ^ 2 := by
  first | exact @GlobalTheory.SiegelValGood.siegel_factor_eq_sq | exact GlobalTheory.SiegelValGood.siegel_factor_eq_sq | (intros; apply GlobalTheory.SiegelValGood.siegel_factor_eq_sq <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.adelicPoisson_summation_anyHaar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  first | exact @GlobalTheory.PoissonReindex.poisson_any | exact GlobalTheory.PoissonReindex.poisson_any | (intros; apply GlobalTheory.PoissonReindex.poisson_any <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.lintegral_adelicHaar_split_archimedean_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul | exact GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul | (intros; apply GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewSig

open Matrix

theorem conjTranspose_eq_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : Mᴴ = M := by
  obtain ⟨hn, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    simp [hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hDh : Dᴴ = D := by
    simp [hD, Matrix.fromBlocks_conjTranspose]
  have hAh : Aᵀ * Mᴴ * A.map star = D := by
    have a1 : (A.map star)ᴴ = Aᵀ := by ext; simp [conjTranspose_apply]
    have a2 : (Aᵀ)ᴴ = A.map star := by ext; simp [conjTranspose_apply]
    have : (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star := by
      rw [conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]
    rw [← this, hA, hDh]
  have e : Fin r ⊕ Fin s ≃ Fin n := (finSumFinEquiv).trans (finCongr hn)
  have k1 : M * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (M * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k2 : Mᴴ * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (Mᴴ * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k3 : (A.map star * D * Aᵀ) * M = 1 := mul_eq_one_comm.1 k1
  calc Mᴴ = Mᴴ * ((A.map star * D * Aᵀ) * M) := by rw [k3, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, k2, Matrix.one_mul]

theorem exists_left_inverse {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (h : Function.Injective ι.mulVec) :
    ∃ P : Matrix (Fin k) (Fin m) ℂ, P * ι = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := LinearMap.ker_eq_bot.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' ι.mulVecLin = ι := LinearMap.toMatrix'_toLin' ι
  rwa [e] at this

theorem transpose_mulVec_eq_zero {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (v : Fin m → ℂ)
    (h : ∀ u, (ι *ᵥ u) ⬝ᵥ v = 0) : ιᵀ *ᵥ v = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct] at this
  simpa using this

theorem hasSig_complement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj
  set c := X ⬝ᵥ M *ᵥ star Y with hc
  set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'
  have hsY : star Y' = c⁻¹ • star Y := by
    rw [hY', star_smul, star_inv₀, star_star]
  have hXY' : X ⬝ᵥ M *ᵥ star Y' = 1 := by
    rw [hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]
  have hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0 := by
    rw [hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]; simp
  have hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0 := transpose_mulVec_eq_zero ι _ fun u => (horth u).1
  have hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0 := by
    rw [hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]
  obtain ⟨P, hP⟩ := exists_left_inverse ι hinj
  exact GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs)
    hXX hYY' hXY' hιX hιY hP hs

end GlobalTheory.PlaneSkewSig
end
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaInj.main | exact GlobalTheory.ThetaInj.main | (intros; apply GlobalTheory.ThetaInj.main <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.self_dual_lattice_invariant_vector : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | exact GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | (intros; apply GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any <;> assumption)
end
