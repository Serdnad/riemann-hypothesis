module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle231
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem norm_sq_toLp_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

def phi (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : X.B.I.GA → ℂ :=
  fun x => ev (MP R) (vecOf R X c y) S
    (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)

theorem vecOf_update [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau)
    (z : Wsub R X c τ) :
    vecOf R X c (Function.update y τ z) =
      Function.update (vecOf R X c y) τ ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    simp [vecOf]
  · simp [vecOf, Function.update_of_ne hσ]

theorem phi_add [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (z₁ + z₂)) =
      phi R X h t c S (Function.update y τ z₁) + phi R X h t c S (Function.update y τ z₂) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.add_apply]
  have e : (⟨(c τ).symm ((z₁ + z₂ : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (z₁ + z₂)⟩ :
      (MP R).sm τ) = ⟨(c τ).symm (z₁ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₁⟩ +
        ⟨(c τ).symm (z₂ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₂⟩ :=
    Subtype.ext (by simp)
  rw [e, S.map_update_add]
  rfl

theorem phi_smul [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (a • z)) =
      (starRingEnd ℂ a) • phi R X h t c S (Function.update y τ z) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.smul_apply]
  have e : (⟨(c τ).symm ((a • z : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (a • z)⟩ :
      (MP R).sm τ) = (starRingEnd ℂ a) • ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ :=
    Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ])
  rw [e, S.map_update_smul]
  rfl

end GlobalTheory.RowEvalHHNorm

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem phi_memLp_integral (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (K : ℝ)
    (hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K)
    (y : ∀ τ, Wsub R X c τ) :
    MemLp (phi R X h t c S y) 2 (muX X) ∧
      ∫ x, ‖phi R X h t c S y x‖ ^ 2 ∂(muX X) = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  by_cases h0 : ∃ τ, (y τ : X.B.H (X.pl.symm τ)) = 0
  · obtain ⟨τ, hτ⟩ := h0
    have hv : vecOf R X c y τ = 0 := Subtype.ext (by simp [vecOf, hτ])
    have hz : phi R X h t c S y = 0 := by
      funext x
      simp only [phi, ev_apply, S.map_coord_zero τ hv]
      rfl
    have hp : ∏ σ, ‖(y σ : X.B.H (X.pl.symm σ))‖ ^ 2 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [hτ])
    rw [hz, hp]
    refine ⟨MeasureTheory.MemLp.zero, ?_⟩
    simp
  · push Not at h0
    have hn : ∀ τ, ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = ‖(y τ : X.B.H (X.pl.symm τ))‖ :=
      fun τ => LinearIsometryEquiv.norm_map _ _
    have hpos : ∀ τ, 0 < ‖(y τ : X.B.H (X.pl.symm τ))‖ := fun τ => norm_pos_iff.2 (h0 τ)
    let u : (MP R).Vec := fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹ : ℝ) : ℂ) • vecOf R X c y τ
    have hu : ∀ τ, ‖(u τ : (MP R).H τ)‖ = 1 := by
      intro τ
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      show |‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹| * ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = 1
      rw [hn, abs_of_pos (inv_pos.2 (hpos τ)), inv_mul_cancel₀ (hpos τ).ne']
    have hvec : vecOf R X c y = fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) • u τ := by
      funext τ
      apply Subtype.ext
      simp only [u, Submodule.coe_smul, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hpos τ).ne', Complex.ofReal_one, one_smul]
    set a : ℂ := ∏ τ, ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) with ha
    have hphi : phi R X h t c S y = fun x => a * ev (MP R) u S
        (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) := by
      funext x
      simp only [phi, ev_apply]
      rw [hvec, S.map_smul_univ]
      rfl
    obtain ⟨hm, hi⟩ := hK u hu
    have hna : ‖a‖ = ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ := by
      rw [ha, norm_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hphi]
    refine ⟨hm.const_mul a, ?_⟩
    simp only [norm_mul, mul_pow]
    rw [integral_const_mul, hi, hna, Finset.prod_pow]
    ring

theorem evF_multilinear_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ∀ S ∈ EP R F, ∃ (f : MultilinearMap (RingHom.id ℂ) (fun τ => ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)) (L2X X)) (K : ℝ), (∀ y, f y = GlobalTheory.RowEvalHH.evF R X h t c S y) ∧ ∀ y, ‖f y‖ ^ 2 = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t c ht S hS
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hL hG hM t ht
  set K : ℝ := c0 * (ipM (MP R) R.ν0 R.fd0 S S).re with hKdef
  have hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K := fun v₀ hv =>
    ⟨(hc0 v₀ hv S hS).1, (hc0 v₀ hv S hS).2.1⟩
  have hmem : ∀ y, MemLp (phi R X h t c S y) 2 (muX X) := fun y =>
    (phi_memLp_integral R X h t c S K hK y).1
  let L : (∀ τ, Wsub R X c τ) → L2X X := fun y => (hmem y).toLp (phi R X h t c S y)
  have hL_add : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ),
      L (Function.update y τ (z₁ + z₂)) = L (Function.update y τ z₁) + L (Function.update y τ z₂) := by
    intro _ y τ z₁ z₂
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_add R X h t c S y τ z₁ z₂) x)
  have hL_smul : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ),
      L (Function.update y τ (a • z)) = (starRingEnd ℂ a) • L (Function.update y τ z) := by
    intro _ y τ a z
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_smul R X h t c S y τ a z) x)
  let f : MultilinearMap (RingHom.id ℂ) (fun τ => ↥(Wsub R X c τ)) (L2X X) :=
    { toFun := fun y => conjL (muX X) (L y)
      map_update_add' := fun y τ z₁ z₂ => by
        rw [hL_add, map_add (f := _)]
      map_update_smul' := fun y τ a z => by
        rw [hL_smul, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply, RingHom.id_apply] }
  refine ⟨f, K, fun y => ?_, fun y => ?_⟩
  · show conjL (muX X) (L y) = evF R X h t c S y
    unfold evF
    split
    · rfl
    · exact absurd (hmem y) ‹_›
  · show ‖conjL (muX X) (L y)‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map, norm_sq_toLp_eq]
    exact (phi_memLp_integral R X h t c S K hK y).2

end GlobalTheory.RowEvalHHNorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  first | exact @GlobalTheory.dsModel_of_onb_cart | exact GlobalTheory.dsModel_of_onb_cart | (intros; apply GlobalTheory.dsModel_of_onb_cart <;> assumption)
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

end

end GlobalTheory.KFinDual
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ConjEquivReal



theorem conjMap_update_real : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod hhost hιE t c ht hconj hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, hreal, -⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivReal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPlaces_not_isConjPlace_realDat : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.SeeConjPlaces.pg_not_isConjPl | exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl | (intros; apply GlobalTheory.SeeConjPlaces.pg_not_isConjPl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isHarishChandraParam_gridVertexRealParameter : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.Grid.isHCParam_parV | exact GlobalTheory.Grid.isHCParam_parV | (intros; apply GlobalTheory.Grid.isHCParam_parV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.Grid.isHCParam_parP | exact GlobalTheory.Grid.isHCParam_parP | (intros; apply GlobalTheory.Grid.isHCParam_parP <;> assumption)
end
