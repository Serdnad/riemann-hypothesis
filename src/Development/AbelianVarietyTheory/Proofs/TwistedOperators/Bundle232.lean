module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjRowLevel

private theorem inner_R_eq_inner_R_inv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : X.B.I.GA)
    (x z : X.B.I.L2 X.B.μf X.B.fund) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  let L : X.B.I.L2 X.B.μf X.B.fund →ₗᵢ[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
    { toLinearMap := (X.B.R a⁻¹ : X.B.I.L2 X.B.μf X.B.fund →ₗ[ℂ] X.B.I.L2 X.B.μf X.B.fund)
      norm_map' := hnorm a⁻¹ }
  have hback : X.B.R a⁻¹ (X.B.R a z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, h1]
    rfl
  calc ⟪x, X.B.R a z⟫_ℂ = ⟪L x, L (X.B.R a z)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
      show ⟪X.B.R a⁻¹ x, X.B.R a⁻¹ (X.B.R a z)⟫_ℂ = _
      rw [hback]

private theorem e_inv_mul_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2)
    (y : X.B.I.Gf) : X.B.e (k⁻¹ * y) = X.chi2 k * X.B.e y := by
  classical
  obtain ⟨_, hmulK, hinvK, hchi, hnorm⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have he : ∀ z, X.B.e z = if z ∈ X.K2 then star (X.chi2 z) / ((X.B.μf X.K2).toReal : ℂ) else 0 :=
    X.e_eq
  have hunit : X.chi2 k * star (X.chi2 k) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hnorm k hk]
    norm_num
  by_cases hy : y ∈ X.K2
  · have hky : k⁻¹ * y ∈ X.K2 := hmulK _ (hinvK _ hk) _ hy
    have hsplit : X.chi2 y = X.chi2 k * X.chi2 (k⁻¹ * y) := by
      rw [← hchi _ hk _ hky, mul_inv_cancel_left]
    rw [he, he, if_pos hky, if_pos hy, hsplit, star_mul']
    linear_combination (-(star (X.chi2 (k⁻¹ * y)) / ((X.B.μf X.K2).toReal : ℂ))) * hunit
  · have hky : k⁻¹ * y ∉ X.K2 := fun h => hy (by simpa using hmulK _ hk _ h)
    rw [he, he, if_neg hky, if_neg hy, mul_zero]

theorem reg_comp_Re {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  ext1 y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_R_eq_inner_R_inv X, X.B.Re_spec.2, X.B.Re_spec.2]
  have hstep : ∀ g : X.B.I.Gf,
      ⟪X.B.R (1, k)⁻¹ x, X.B.R (1, g) y⟫_ℂ = ⟪x, X.B.R (1, k * g) y⟫_ℂ := by
    intro g
    have hprod : (((1 : X.B.I.Ginf), k * g) : X.B.I.GA) = (1, k) * (1, g) := by simp
    rw [hprod, hmul, ContinuousLinearMap.comp_apply]
    exact (inner_R_eq_inner_R_inv X (1, k) x _).symm
  simp_rw [hstep]
  have hinv := integral_mul_left_eq_self (μ := X.B.μf)
    (fun g' => X.B.e (k⁻¹ * g') * ⟪x, X.B.R (1, g') y⟫_ℂ) k
  simp only [inv_mul_cancel_left] at hinv
  rw [hinv]
  simp_rw [e_inv_mul_eq_chi2_mul X k hk, mul_assoc]
  exact integral_const_mul _ _
private theorem contRep_mul_right_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Φ : X.B.Hs →L[ℂ] L2X X)
    (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) (v : X.B.Hs) {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ v) ψ) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ∀ z, ψ (z * ((1 : X.B.I.Ginf), κ)) = X.chi2 κ * ψ z := by
  obtain ⟨A, -, hA⟩ := Submodule.mem_map.1 hΦ
  have hΦv : Φ v = X.B.Re (A v) := by
    rw [← hA]
    rfl
  have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1 : X.B.I.Ginf), κ)
  have hR : X.B.R ((1 : X.B.I.Ginf), κ) (Φ v) = X.chi2 κ • Φ v := by
    rw [hΦv, ← ContinuousLinearMap.comp_apply, reg_comp_Re X κ hκ, ContinuousLinearMap.smul_apply]
  rw [hR] at h1
  have h2 := Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 κ) hψ
  have heq := Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 h2
  intro z
  simpa using congrFun heq z

theorem conjMap_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ _ _ t c _ hconj _ Φ hΦ hcont u k hk g
  obtain ⟨ψ, hψ⟩ := hcont u
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hmem, hval⟩ := hconj k
  have hk' : ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧
      ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hmem.1 hk
  have hv := hval hk
  obtain ⟨hp1, hp2⟩ := hk'
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 := ⟨_, rfl⟩
  have hq : (iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹) = ((1 : X.B.I.Ginf), κ) := Prod.ext hp1 hκdef.symm
  have hκ : κ ∈ X.K2 := by
    rw [hκdef]
    exact hp2
  have hv' : star (X.chi2 κ) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k := by
    rw [hκdef]
    exact hv
  have hsplit : (iotaX X h).toMulEquiv (g * k * t⁻¹) =
      (iotaX X h).toMulEquiv (g * t⁻¹) * ((1 : X.B.I.Ginf), κ) := by
    rw [← hq]
    calc (iotaX X h).toMulEquiv (g * k * t⁻¹)
        = (iotaX X h).toMulEquiv (g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹)) := by
          rw [show g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹) = g * k * t⁻¹ by group]
      _ = _ := map_mul _ _ _
  change star (ψ ((iotaX X h).toMulEquiv (g * k * t⁻¹))) = _ * star (ψ ((iotaX X h).toMulEquiv (g * t⁻¹)))
  rw [hsplit, contRep_mul_right_eq_chi2_mul X Φ hΦ _ hψ κ hκ, star_mul', hv']

end GlobalTheory.ConjRowLevel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPlaces

theorem pg_not_isConjPl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ PP hP PP' hP'
  exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg PP hP PP' hP'

end GlobalTheory.SeeConjPlaces
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.FrameTransfer

open Formalism.L2.DIV Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem entry_mem {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) (i j : Fin n) :
    ((β⁻¹ * β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have key := (hβ (β'.1 *ᵥ Pi.single j 1)).1 ((hβ' _).2 (by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _)) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at key
  exact key

theorem exists_int {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), intGL F E n y = β⁻¹ * β' := by
  set φ := (Formalism.L2.Herm.intAf F E).subtype
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) φ) := fun a b h => by
    ext i j; exact congrArg Subtype.val (Subtype.ext (congrFun (congrFun h i) j))
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ hβ' i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ' hβ i j⟩
  have hM : RingHom.mapMatrix φ M = ((β⁻¹ * β' : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have hM' : RingHom.mapMatrix φ M' = ((β'⁻¹ * β : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have e1 : M * M' = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  have e2 : M' * M = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

theorem st_le {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β' ≤ St β := by
  obtain ⟨y, hy⟩ := exists_int hβ hβ'
  rintro x ⟨z, rfl⟩
  refine ⟨y * z * y⁻¹, ?_⟩
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hy]
  group

theorem st_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β = St β' :=
  le_antisymm (st_le hβ' hβ) (st_le hβ hβ')

section Lev

variable [StarRing E] {LL : Type} [CommRing LL]

theorem mem_parLev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ parLev hc J β D ↔ x ∈ parLev hc J β' D := by
  simp only [parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah, hSt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, hg PP hP x ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, hq PP hP x ▸ (h4 PP hP).2⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, (hg PP hP x).symm ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, (hq PP hP x).symm ▸ (h4 PP hP).2⟩⟩

theorem rTup_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    rTup β D x = rTup β' D x := by
  funext PP
  simp only [rTup, hg PP.1 PP.2 x]

theorem mem_lev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ lev hc J β D ↔ x ∈ lev hc J β' D := by
  show (x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H) ↔ (x ∈ parLev hc J β' D ∧ rTup β' D x ∈ D.P.H)
  rw [mem_parLev_iff hSt hg hq, rTup_eq hg]

theorem levFn_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : levFn β D x = levFn β' D x := by
  unfold levFn
  rw [rTup_eq hg]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => by rw [hg PP hP x]
  · exact Finset.prod_congr rfl fun PP hP => by rw [hq PP hP x]

end Lev

end GlobalTheory.FrameTransfer

theorem GlobalTheory.levS_levChi_of_frames : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  intro D V β β' Λ L hβ hβ' hg hq κ
  have hSt := GlobalTheory.FrameTransfer.st_eq hβ hβ'
  refine ⟨?_, ?_⟩
  · show κ ∈ levG V β L ↔ κ ∈ levG V β' L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [GlobalTheory.FrameTransfer.mem_lev_iff hSt hg hq]
  · unfold levChi
    rw [GlobalTheory.FrameTransfer.levFn_eq hg hq]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FrameConj

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {T : G} (hT : T ∈ H) (x : G) :
    T * x * T⁻¹ ∈ H ↔ x ∈ H := by
  rw [Subgroup.mul_mem_cancel_right H (H.inv_mem hT), Subgroup.mul_mem_cancel_left H hT]

theorem frGL_mul_left (T β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y) :
    frGL (T * β) y = T * frGL β y * T⁻¹ := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_mem_St_iff (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    T * x * T⁻¹ ∈ St (T * β) ↔ x ∈ St β := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [frGL_mul_left] at hy
    exact mul_left_cancel (mul_right_cancel hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, frGL_mul_left T β y⟩

theorem redFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (T * β) PP (T * x * T⁻¹) = redFn β PP x := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := hx
    rw [← frGL_mul_left, redFn_frGL, redFn_frGL]
  · have h' : T * x * T⁻¹ ∉ St (T * β) := fun h => hx ((conj_mem_St_iff T β x).1 h)
    unfold redFn ext1
    rw [dite_eq_right hx, dite_eq_right h']

variable {LL : Type} [CommRing LL]

theorem rTup_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    rTup (T * β) L (T * x * T⁻¹) = rTup β L x := by
  funext PP
  show upperLeftBlock L.hr (redFn (T * β) PP.1 (T * x * T⁻¹)) = upperLeftBlock L.hr (redFn β PP.1 x)
  rw [redFn_conj]

theorem levFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    levFn (T * β) L (T * x * T⁻¹) = levFn β L x := by
  unfold levFn
  simp only [rTup_conj, redFn_conj]

theorem conj_mem_lev_iff [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E}
    {T : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hT : T ∈ UA hc J) (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (L : LevDat E LL n) : T * x * T⁻¹ ∈ lev hc J (T * β) L ↔ x ∈ lev hc J β L := by
  rw [mem_lev, mem_lev, mem_parLev, mem_parLev, conj_mem_iff _ hT, conj_mem_St_iff, rTup_conj]
  simp only [redFn_conj]

end Gen

theorem levS_conj_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V),
    t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧
      levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  intro D V β L t ht k
  have hfin : finE V (t * k * t⁻¹) = finE V t * finE V k * (finE V t)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨?_, ?_⟩
  · show k ∈ levG V β L ↔ t * k * t⁻¹ ∈ levG V (finE V t * β) L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [conj_mem_iff _ ht, hfin, conj_mem_lev_iff (GlobalTheory.LevSplit.finE_mem_UA V t)]
  · unfold levChi
    rw [hfin, levFn_conj]

end GlobalTheory.FrameConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem parD_entry_int (D : D7) (τ : D.what₂.Tau) (i j : ℕ) {x : ℚ × Bool} (hx : x ∈ (grid D τ).parD i j) :
    ∃ z : ℤ, x.1 = z := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hs : ∃ d : ℕ, sLen D = 2 * d + 1 := ⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩
  obtain ⟨d, hd⟩ := hs
  rcases GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩
  · obtain ⟨i', -, -, h⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, h⟩
  · exact ⟨-(grid D τ).b l, by push_cast; rfl⟩
  · simp only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3
    obtain ⟨a', -, h⟩ := h3
    refine ⟨-((grid D τ).e l) + c - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
    rw [ht]; push_cast; ring
  · simp only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4
    obtain ⟨a', -, h⟩ := h4
    refine ⟨(grid D τ).cen l + d - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).s : ℚ) = 2 * d + 1 := by exact_mod_cast hd
    rw [ht]; push_cast; ring

theorem even_rkV_iff (D : D7) (i j : ℕ) : Even (rkV D i j) ↔ Odd (i + j) := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  obtain ⟨u, hu⟩ : ∃ u, a + b = u + 1 := ⟨a + b - 1, by omega⟩
  have hr : D.R.r = 2 * u + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i) := by
    unfold rkV sLen; rw [hr, hc]; ring
  rw [e, Nat.even_add, Nat.odd_add]
  simp only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]
  simp only [Nat.odd_iff, Nat.even_iff]; omega

theorem isHCParam_parV : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i j _ _ _ τ n lam ε hn hE
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ parV D i j τ := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  obtain ⟨z, hz⟩ := parD_entry_int D τ i j hx
  have hpar := even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho] at *
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rkV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho] at *
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.Grid
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem isHCParam_parP : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : q a ∈ (grid D τ).weightX 0 := by
    have h0 : (q a, ε a) ∈ parP D i τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rcases GridData.mem_parPi.1 h0 with ⟨l, hl, h⟩ | ⟨h1, _⟩ | ⟨l, h1, h2, h3, _⟩
    · exact GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨l, hl, (Prod.ext_iff.1 h).1⟩))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inl h1))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inl ⟨l, by omega, h2, h3⟩)))
  have hs : Odd (grid D τ).s := GlobalTheory.ChiGrid.odd_sLen D
  obtain ⟨z, hz⟩ := GlobalTheory.ChiGrid.inCoset_weightX_zero hs _ hmem
  obtain ⟨u, hu⟩ := GlobalTheory.ChiGrid.even_rankP D i
  have hn' : (n : ℝ) = (u : ℝ) + u := by
    have : n = u + u := hn.trans hu
    rw [this]; push_cast; ring
  refine ⟨z + 1 - u, ?_⟩
  rw [hq a, hz, hn']
  push_cast
  ring

end GlobalTheory.Grid
end
end
