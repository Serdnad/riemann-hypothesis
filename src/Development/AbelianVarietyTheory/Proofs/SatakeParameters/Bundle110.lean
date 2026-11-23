module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle417
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle101
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_placeOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x)]
  have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
  rw [this, ← IsScalarTower.algebraMap_apply]

end

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (hc : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal) :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  classical
  haveI := v.isMaximal
  haveI := v'.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 L ⧸ v'.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal) :=
    (Ideal.quotientMap v'.asIdeal (algebraMap (𝓞 K) (𝓞 L)) hc.ge).toAlgebra
  refine ⟨Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal), ?_⟩
  simp only [normV, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank
end GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem restrictScalars_mem_Dec {A : ValuationSubring Ω} {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    (σ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hσ

theorem actsAs_restrictScalars {A : ValuationSubring Ω} {σ : G L Ω} {q f a b : ℕ} (hσ : _root_.GlobalTheory.WeilDeligne.ActsAs A (q ^ f) σ a b) :
    _root_.GlobalTheory.WeilDeligne.ActsAs A q (σ.restrictScalars K : G K Ω) (f * a) (f * b) := by
  refine ⟨restrictScalars_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [← pow_mul, ← pow_mul] at this
  exact this

theorem restrictScalars_mem_Ine_iff {A : ValuationSubring Ω} {σ : G L Ω} :
    (σ.restrictScalars K : G K Ω) ∈ Ine (F := K) A ↔ σ ∈ Ine (F := L) A := Iff.rfl

end

theorem exists_weil_restrict : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ'
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  obtain ⟨a, b, hab⟩ := (mem_Weil h').mp σ'.2
  rw [hf] at hab
  refine ⟨⟨(σ' : G L Ω).restrictScalars K, (mem_Weil h).mpr ⟨_, _, actsAs_restrictScalars hab⟩⟩, fun z => rfl, ?_⟩
  rw [deg_eq_zero_iff, deg_eq_zero_iff]
  exact restrictScalars_mem_Ine_iff
end GlobalTheory.AboveL
end

section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem eig_pow_of_rep {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) (σ : Weil h) (k : ℕ) :
    x.eig (σ ^ k) = (x.eig σ).map (· ^ k) := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.eig_mk, WD.eig_mk, map_pow]
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n k
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (a.ρ σ))
  rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
  exact h2

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

open Pointwise

end GlobalTheory.AboveL
end

section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem trace_eq_of_trace_mul_pow {n m : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (B T : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : ∀ i : ℕ, 1 ≤ i → (S * A ^ i).trace = (T * B ^ i).trace) : S.trace = T.trace := by
  set P := A.charpoly * B.charpoly with hP
  have hPA : Polynomial.aeval A P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hPB : Polynomial.aeval B P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  have eA := congrArg (fun M => (S * M).trace) hPA
  have eB := congrArg (fun M => (T * M).trace) hPB
  simp only [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_zero, Matrix.trace_zero] at eA eB
  rw [Finset.sum_range_succ'] at eA eB
  have hs : ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (S * A ^ (i + 1)).trace =
      ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (T * B ^ (i + 1)).trace :=
    Finset.sum_congr rfl fun i _ => by rw [h (i + 1) (by omega)]
  rw [hs] at eA
  have e0 : P.coeff 0 * (S * A ^ 0).trace = P.coeff 0 * (T * B ^ 0).trace := by linear_combination eA - eB
  simp only [pow_zero, Matrix.mul_one] at e0
  have hc : P.coeff 0 ≠ 0 := by
    rw [hP, Polynomial.mul_coeff_zero]
    refine mul_ne_zero (fun h0 => hA.ne_zero ?_) (fun h0 => hB.ne_zero ?_)
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  exact mul_left_cancel₀ hc e0

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem charpoly_eq_toMatrix' {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    f.charpoly = (LinearMap.toMatrix' f).charpoly := by
  rw [← LinearMap.charpoly_toMatrix f (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']

theorem trace_eq_of_charpoly_eq {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℂ} (e : M.charpoly = M'.charpoly) :
    M.trace = M'.trace := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]

theorem charPol_eq_of_deg_ne_zero : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (x y : WD h), (∀ σ : Weil h, deg σ ≠ 0 → x.charPol σ = y.charPol σ) → ∀ σ : Weil h, x.charPol σ = y.charPol σ := by
  intro K Ω _ _ _ _ _ A v h x y hxy σ
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  simp only [WD.charPol_mk] at hxy ⊢
  have hnm : n = m := by
    have e := congrArg Polynomial.natDegree (hxy (frob h) (by rw [deg_frob]; exact one_ne_zero))
    rwa [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at e
  subst hnm
  by_cases hσ : deg σ = 0
  swap
  · exact hxy σ hσ

  have hMA : ∀ τ : Weil h, LinearMap.toMatrix' (a.ρ τ) = (a.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL a τ).symm
  have hMB : ∀ τ : Weil h, LinearMap.toMatrix' (b.ρ τ) = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL b τ).symm
  have hne : ∀ τ : Weil h, deg τ ≠ 0 →
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ hτ
    refine trace_eq_of_charpoly_eq ?_
    rw [← hMA, ← hMB, ← charpoly_eq_toMatrix', ← charpoly_eq_toMatrix']
    exact hxy τ hτ
  have hall : ∀ τ : Weil h,
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ
    by_cases hτ : deg τ = 0
    swap
    · exact hne τ hτ
    refine trace_eq_of_trace_mul_pow (a.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      (b.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      ((Matrix.isUnit_iff_isUnit_det _).1 (a.toGL (frob h)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).1 (b.toGL (frob h)).isUnit) fun i hi => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
      ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    refine hne _ ?_
    rw [deg_mul, deg_pow, hτ, deg_frob]
    omega
  rw [charpoly_eq_toMatrix', charpoly_eq_toMatrix', hMA, hMB]
  refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun j => ?_
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  exact hall _

end GlobalTheory.AboveL
end

section

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResEx

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem res_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Dec (F := K) A :=
  GlobalTheory.DelEps.WeilRes.mem_Dec_iff.2 fun x => GlobalTheory.DelEps.WeilRes.mem_Dec_iff.1 hσ x

theorem res_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Ine (F := K) A :=
  ⟨res_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem res_mem_Weil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') :
    AlgEquiv.restrictScalarsHom K (σ : G L Ω) ∈ Weil h := by
  obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
  have hQ : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
    rw [GlobalTheory.DelEps.WeilRes.normV_eq_pow (K := K) v', GlobalTheory.DelEps.WeilRes.under_eq h h']
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K) * a, v'.asIdeal.inertiaDeg (𝓞 K) * b, res_mem_Dec hab.1,
    fun x hx => ?_⟩
  have h2 := hab.2 x hx
  rw [hQ, ← pow_mul, ← pow_mul] at h2
  exact h2

def resW (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalarsHom K (σ : G L Ω), res_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

def resI : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K).comp (Ine (F := L) A).subtype).codRestrict (Ine (F := K) A)
    fun σ => res_mem_Ine σ.2

theorem continuous_resI : Continuous (resI (K := K) (L := L) (Ω := Ω) (A := A)) :=
  ((UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω).comp continuous_subtype_val).subtype_mk _

theorem resW_ineIncl (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (τ : Ine (F := L) A) :
    resW h h' (ineIncl h' τ) = ineIncl h (resI τ) := Subtype.ext rfl

def resRep (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {n : ℕ} (a : WDRep h (Fin n → ℂ)) :
    WDRep h' (Fin n → ℂ) where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := by
    show IsOpen {τ : Ine (F := L) A | a.ρ (resW h h' (ineIncl h' τ)) = 1}
    simp_rw [resW_ineIncl]
    exact a.smooth.preimage continuous_resI
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have hR := normV_zpow_deg_eq σ (resW h h' σ) (fun z => rfl)
    have hC : ((normV v' : ℕ) : ℂ) ^ deg σ = ((normV v : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hR
      push_cast at this
      exact this
    show a.ρ (resW h h' σ) * a.N = _ • (a.N * a.ρ (resW h h' σ))
    rw [hC]
    exact a.comm _

end GlobalTheory.AboveL.ResEx

namespace GlobalTheory.AboveL

end GlobalTheory.AboveL

end
end

section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem weil_rep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  intro K Ω _ _ _ _ _ A v h n m a b hc
  have ha := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule a.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h n a)
  have hb := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule b.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h m b)
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt ℂ (Weil h) _ _ a.ρ b.ρ ha hb hc
  exact ⟨e, fun σ z => LinearMap.congr_fun (he σ) z⟩

end GlobalTheory.AboveL
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tempered_direct_sum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_lpSum | exact GlobalTheory.WeilDeligne.WD.tempered_lpSum | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_lpSum <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tempered_special_of_unit_eigen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | exact GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 <;> assumption)
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  first | exact @GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | exact GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | (intros; apply GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_T1_and_J1_mem_window_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  intro D L C j ε τ φ hR
  have hT : (pageWord L j ε τ φ).T1 := by
    intro i u hu
    exact GlobalTheory.T.twistedDualJumps_mem_windows (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.Sc L.etaSz
      (fun a => L.cloud_v _ a) (fun a => L.be_close _ a j) u hu
  refine ⟨hT, GlobalTheory.T.jumps_mem_box_neg_M_h _ (fun i => ?_) hT⟩
  have h := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2 i
  exact le_trans (Int.natCast_nonneg _) h.le

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem twistedDualPageWord_small_jumps_card : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  intro D L C j ε τ φ hR
  have hbox := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2
  have hcount : ∀ i, (((pageWord L j ε τ φ).J2 i).filter
      fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
    intro i
    refine GlobalTheory.T.card_filter_abs_le_jT2_eq_rank (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.etaSz ?_ ?_ (hbox i)
    · intro a
      have h := (L.cloud_v (D.eTau.symm ⟨plc (letter τ φ i), plc_mem _⟩) a).1
      exact_mod_cast h
    · intro a
      exact L.be_close _ a j
  refine ⟨fun i => ⟨fun u hu => ?_, (hcount i).le⟩, fun i => ⟨?_, hcount i⟩⟩
  · exact Multiset.mem_of_le
      ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.2 hu
  · exact ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.1

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  first | exact @GlobalTheory.HTW.pageWord_thickOr | exact GlobalTheory.HTW.pageWord_thickOr | (intros; apply GlobalTheory.HTW.pageWord_thickOr <;> assumption)
end
