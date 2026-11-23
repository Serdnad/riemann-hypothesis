module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
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
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.UaF

open Formalism.UG GlobalTheory.DefU GlobalTheory.SplitPts

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem cLoc_eq (u : Plc L) (x : UA L n) :
    cLoc u x = GeneralLinearGroup.map (pLoc L u) (GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl

private theorem ext_all {x y : UA L n} (h1 : cInf x = cInf y) (h2 : ∀ u, cLoc u x = cLoc u y) : x = y := by
  refine Subtype.ext (ga_ext h1 (Units.ext (matAf_ext fun u => ?_)))
  have := congrArg Units.val (h2 u)
  exact this

private theorem cInf_ext {x y : UA L n} (h : ∀ τ : L →+* ℂ, cEmb τ x = cEmb τ y) : cInf x = cInf y := by
  refine Units.ext (Matrix.ext fun i j => GlobalTheory.IsoPull.ext_coord fun τ => ?_)
  exact congrArg (fun g : GL (Fin n) ℂ => g.val i j) (h τ)

private theorem cLoc_of_inf {k : UA L n} (hk : k ∈ infU L n) (u : Plc L) : cLoc u k = 1 := by
  have h : GeneralLinearGroup.map (pFin L) k.1 = 1 := hk
  rw [cLoc_eq, h, map_one]

private theorem inf_of_cLoc {k : UA L n} (h : ∀ u : Plc L, cLoc u k = 1) : k ∈ infU L n := by
  change GeneralLinearGroup.map (pFin L) k.1 = 1
  refine Units.ext (matAf_ext fun u => ?_)
  have := congrArg Units.val (h u)
  rw [Units.val_one] at this ⊢
  rw [map_one]
  exact this

private noncomputable def fp (x : UA L n) : UA L n :=
  ⟨finGL L n (GeneralLinearGroup.map (pFin L) x.1), finGL_mem_UA _ fun u => comp_eq x u⟩

private theorem fp_fin (x : UA L n) : fp x ∈ finU (E := L) (n := n) := pInf_finGL _

private theorem cLoc_fp (u : Plc L) (x : UA L n) : cLoc u (fp x) = cLoc u x :=
  (cLoc_finGL u _ _).trans (cLoc_eq u x).symm

private theorem under_iff (w u : Plc L) : un u = un w ↔ u = w ∨ u = conjSrc (conjE L) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE L) w u → u = conjSrc (conjE L) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  refine ⟨fun h => ((key u).1 h).imp_right (h2 u), ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact (key _).2 (Or.inr (conjPl_self_conjSrc w))

private theorem cut (w : Plc L) (x : UA L n) (hx : x ∈ finU (E := L) (n := n)) :
    ∃ a ∈ locU n w, ∀ u, un u = un w → cLoc u a = cLoc u x := by
  classical
  set T : Finset (Plc L) := {w, conjSrc (conjE L) w} with hT
  have memT : ∀ u, u ∈ T ↔ un u = un w := fun u => by
    rw [under_iff]; simp [hT]
  have memC : ∀ u, conjSrc (conjE L) u ∈ T ↔ u ∈ T := fun u => by
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · right; rw [← h, conjSrc_conjSrc_cm]
      · left; exact conjSrc_injective _ h
    · rintro (rfl | rfl)
      · right; rfl
      · left; exact conjSrc_conjSrc_cm w
  set g := GeneralLinearGroup.map (pFin L) x.1 with hg
  have hU : finGL L n (GlobalTheory.EulerTw.prjG L n T g) ∈ UA L n := by
    refine finGL_mem_UA _ fun u => ?_
    rw [GlobalTheory.EulerTwKU.pLoc_prjG, GlobalTheory.EulerTwKU.pLoc_prjG]
    by_cases hu : u ∈ T
    · rw [if_pos hu, if_pos ((memC u).2 hu)]
      exact comp_eq x u
    · rw [if_neg hu, if_neg (fun h => hu ((memC u).1 h))]
      simp
  have hc : ∀ u, cLoc u (⟨_, hU⟩ : UA L n) = if u ∈ T then cLoc u x else 1 := fun u => by
    rw [cLoc_finGL, GlobalTheory.EulerTwKU.pLoc_prjG, cLoc_eq]
  refine ⟨⟨_, hU⟩, Subgroup.mem_inf.2 ⟨pInf_finGL _, Subgroup.mem_iInf.2 fun u =>
    Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, fun u hu => ?_⟩
  · rw [hc, if_neg (fun h => hu ((memT u).1 h))]
  · rw [hc, if_pos ((memT u).2 hu)]

private theorem K_conj (x : UA L n) (u : Plc L) (h : cLoc (conjSrc (conjE L) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE L) u) (n := n)) :
    cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := by
  have hv := (GlobalTheory.EulerTwKU.mem_KGL_iff_val _).1 h
  set g := cLoc (conjSrc (conjE L) u) x with hg
  set c := conjLoc (conjE L) u with hc
  set g' := GeneralLinearGroup.map c g with hg'
  have e1 : (g'.val)ᵀ * (cLoc u x).val = 1 := comp_eq x u
  have e2 : (cLoc u x).val * (g'.val)ᵀ = 1 := mul_eq_one_comm.1 e1
  have e3 : ((cLoc u x)⁻¹).val = (g'.val)ᵀ := Units.inv_eq_of_mul_eq_one_right e2
  have e4 : (cLoc u x).valᵀ * g'.val = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e5 : (g'⁻¹).val = (cLoc u x).valᵀ := Units.inv_eq_of_mul_eq_one_left e4
  have e6 : (g'⁻¹).val = (GeneralLinearGroup.map c g⁻¹).val := by rw [map_inv]
  refine (GlobalTheory.EulerTwKU.mem_KGL_iff_val _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (cLoc u x).val i j = c ((g⁻¹).val j i) := by
      have := congrFun (congrFun (e5.symm.trans e6) j) i
      exact this
    rw [this, (conjLoc_spec _ u).2.2]
    exact hv.2 j i
  · have : ((cLoc u x)⁻¹).val i j = c (g.val j i) := congrFun (congrFun e3 i) j
    rw [this, (conjLoc_spec _ u).2.2]
    exact hv.1 j i

end UpperTheory.V.Z.Sym.Dict.Br.UaF

open UpperTheory.V.Z.Sym.Dict.Br.UaF in
theorem UpperTheory.V.Z.Sym.Dict.Br.uaFacts :
    UAFacts := by
  intro L _ _ _ n
  refine ⟨fun w hw => ?_, fun w x hx y hy => ?_, fun x => ?_, fun f hf k hk => ?_, fun x y h1 h2 => ?_, fun x => ?_,
    fun w x hx => cut w x hx, fun w hw x hK u hu => ?_⟩
  · obtain ⟨a, b, c, d⟩ := UpperTheory.V.Z.Sym.Al.secSpec L n w hw
    exact ⟨a, b, d, fun x hx => (c x hx).symm⟩
  · have hi : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h : un u = un w
    · rw [hy u h, one_mul, mul_one]
    · have : cLoc u x = 1 := MonoidHom.mem_ker.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) h)
      rw [this, one_mul, mul_one]
  · refine ⟨fp x, fp_fin x, (fp x)⁻¹ * x, inf_of_cLoc fun u => ?_, by group⟩
    rw [map_mul, map_inv, cLoc_fp, inv_mul_cancel]
  · have hi : cInf f = 1 := hf
    refine ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_
    rw [map_mul, map_mul, cLoc_of_inf hk, one_mul, mul_one]
  · exact ext_all (cInf_ext h2) h1
  · refine ⟨⟨fun hx τ => ?_, fun h => ?_⟩, ⟨fun hx w => cLoc_of_inf hx w, inf_of_cLoc⟩⟩
    · have hi : cInf x = 1 := hx
      change GeneralLinearGroup.map (coord τ) (cInf x) = 1
      rw [hi, map_one]
    · change cInf x = 1
      rw [cInf_ext (y := 1) fun τ => by rw [h τ, map_one], map_one]
  · rcases (under_iff w u).1 hu with rfl | rfl
    · exact hK
    · refine K_conj x _ ?_
      rw [GlobalTheory.SplitPts.conjSrc_conjSrc_cm]
      exact hK
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def phiG {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    U3 R.Δ →* GL (Fin 3) L :=
  (GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)).comp Unitary.toUnits

private theorem phiG_coe {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    (phiG R γ : Matrix (Fin 3) (Fin 3) L) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => R.e x := rfl

private theorem phiG_unitary {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ * (phiG R γ : Matrix (Fin 3) (Fin 3) L) = 1 := by
  have h : star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) * (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp γ.2
  have e1 : ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ =
      (star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ))).map fun x => R.e x := by
    ext i j
    simp [phiG_coe, Matrix.star_apply, R.e_star]
  rw [e1, phiG_coe]
  have e2 := congrArg (fun m => m.map (R.e : Lsq (Lp L) R.Δ →+* L)) h
  simp only [Matrix.map_mul] at e2
  simpa using e2

theorem UpperTheory.V.Z.Sym.Dict.Br.rGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : U3 R.Δ ≃* ratU L 3, (∀ γ w, mL w (r γ : UA L 3) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 3) : Matrix (Fin 3) (Fin 3) ℂ) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hU : ∀ γ : U3 R.Δ, ratGL L 3 (phiG R γ) ∈ UA L 3 := fun γ =>
    (ratFacts L 3 (phiG R γ)).1.mpr (phiG_unitary R γ)
  let f : U3 R.Δ →* ratU L 3 :=
    { toFun := fun γ => ⟨⟨ratGL L 3 (phiG R γ), hU γ⟩, Subgroup.mem_subgroupOf.mpr ⟨phiG R γ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ratGL L 3 (phiG R a) = ratGL L 3 (phiG R b) := congrArg Subtype.val (congrArg Subtype.val hab)
    have h2 := (ratFacts L 3 1).2.1 h1
    have h3 : (phiG R a : Matrix (Fin 3) (Fin 3) L) = phiG R b := congrArg Units.val h2
    apply Subtype.ext
    exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h3 i) j)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, hr⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hr
    change ratGL L 3 g = x at hg
    subst hg
    have hc := (ratFacts L 3 g).1.mp hx
    let M : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 3) (Fin 3) L).map fun x => R.e.symm x
    have hM : star M * M = 1 := by
      have e1 : star M = (((g : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ).map fun x => R.e.symm x := by
        refine Matrix.ext fun i j => R.e.injective ?_
        simp [M, Matrix.star_apply, R.e_star]
      have e2 := congrArg (fun m => m.map (R.e.symm : L →+* Lsq (Lp L) R.Δ)) hc
      simp only [Matrix.map_mul] at e2
      rw [e1]
      simpa [M] using e2
    refine ⟨⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩, ?_⟩
    have hp : phiG R ⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩ = g := by
      apply Units.ext
      ext i j
      simp [phiG_coe, M]
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (ratGL L 3) hp
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).1 w
  · intro γ τ
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).2.1 τ
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_map {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    ((x.map R.e).map (IsCMField.complexConj L))ᵀ = (star x).map R.e := by
  ext i j
  simp [Matrix.star_apply, R.e_star]

private theorem map_mul' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x y : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x * y).map R.e = x.map R.e * y.map R.e :=
  map_mul (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix x y

private theorem map_one' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e = 1 :=
  map_one (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix

private theorem map_det' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x.map R.e).det = R.e x.det :=
  ((R.e : Lsq (Lp L) R.Δ →+* L).map_det x).symm

theorem UpperTheory.V.Z.Sym.Dict.Br.rSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : SU R.Δ ≃* ↥(ratU L 2 ⊓ SUA L), (∀ γ w, mL w (r γ : UA L 2) = (mt (γ : DX R.Δ)).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 2) : Matrix (Fin 2) (Fin 2) ℂ) = (mt (γ : DX R.Δ)).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hrf := ratFacts L 2
  obtain ⟨hs1, hs2⟩ := suIff (Lp L) R.Δ
  let E : GL (Fin 2) (Lsq (Lp L) R.Δ) →* GL (Fin 2) L :=
    GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)
  have hEc : ∀ g, (E g : Matrix (Fin 2) (Fin 2) L) = (g : Matrix (Fin 2) (Fin 2) _).map R.e := fun g => rfl
  have hdet1 : ∀ γ : SU R.Δ, (mt (γ : DX R.Δ)).det = 1 := by
    intro γ
    have h : GeneralLinearGroup.det ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1 := γ.2
    simpa using congrArg Units.val h
  have hstar : ∀ γ : SU R.Δ, star (mt (γ : DX R.Δ)) * mt (γ : DX R.Δ) = 1 := by
    intro γ
    rw [(hs1 γ).1, hdet1, one_smul]
  have hdetE : ∀ γ : SU R.Δ, GeneralLinearGroup.det (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) = 1 := by
    intro γ
    apply Units.ext
    have : (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
      rw [hEc, map_det', hdet1, map_one]
    simpa using this
  have hmem : ∀ γ : SU R.Δ, ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) ∈ UA L 2 := by
    intro γ
    rw [(hrf _).1, hEc, star_map, ← map_mul', hstar, map_one']
  let φ1 : SU R.Δ →* UA L 2 :=
    ((ratGL L 2).comp (E.comp ((DX R.Δ).subtype.comp (SU R.Δ).subtype))).codRestrict (UA L 2) hmem
  have hφ1 : ∀ γ, ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) := fun _ => rfl
  have hmem2 : ∀ γ, φ1 γ ∈ ratU L 2 ⊓ SUA L := by
    intro γ
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
    · show GeneralLinearGroup.det ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1
      rw [hφ1]
      exact (((hrf _).2.2 (hmem γ)).2.2).2 (hdetE γ)
  let φ2 : SU R.Δ →* ↥(ratU L 2 ⊓ SUA L) := φ1.codRestrict _ hmem2
  have hinj : Function.Injective φ2 := by
    intro a b hab
    have h1 : ((φ1 a : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ((φ1 b : UA L 2) : GlobalTheory.CuspRep.GA L 2) :=
      congrArg (fun x : ↥(ratU L 2 ⊓ SUA L) => ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2)) hab
    rw [hφ1, hφ1] at h1
    have h2 := (hrf (E 1)).2.1 h1
    have h3 : mt (a : DX R.Δ) = mt (b : DX R.Δ) := by
      have h4 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h2
      simp only [hEc] at h4
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h4 i) j)
    exact Subtype.ext (Subtype.ext (Units.ext h3))
  have hsurj : Function.Surjective φ2 := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hx1
    have hgU : ratGL L 2 g ∈ UA L 2 := hg ▸ x.2
    have hdx : GeneralLinearGroup.det ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1 := hx2
    have hdg : GeneralLinearGroup.det g = 1 := by
      apply ((hrf g).2.2 hgU).2.2.1
      rw [hg]; exact hdx
    have hconj := ((hrf g).1).1 hgU
    let m : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 2) (Fin 2) L).map R.e.symm
    have hm : m.map R.e = g := by
      ext i j; simp [m]
    have hms : star m * m = 1 := by
      have h1 : (star m * m).map R.e = (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e := by
        rw [map_mul', ← star_map, hm, hconj, map_one']
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h1 i) j)
    have hmd : m.det = 1 := by
      apply R.e.injective
      rw [← map_det', hm, map_one]
      simpa using congrArg Units.val hdg
    obtain ⟨h, hh⟩ := hs2 m hms hmd
    have hSU : h ∈ SU R.Δ := by
      show GeneralLinearGroup.det (h : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1
      apply Units.ext
      have : (mt h).det = 1 := hh ▸ hmd
      simpa using this
    refine ⟨⟨h, hSU⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ratGL L 2 (E (h : GL (Fin 2) (Lsq (Lp L) R.Δ))) = _
    rw [← hg]
    congr 1
    apply Units.ext
    rw [hEc]
    show (mt h).map R.e = _
    rw [hh, hm]
  refine ⟨MulEquiv.ofBijective φ2 ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    have := ((hrf _).2.2 (hmem γ)).1 w
    exact this.trans (by rw [hEc]; ext i j; rfl)
  · intro γ τ
    have := ((hrf _).2.2 (hmem γ)).2.1 τ
    exact this.trans (by rw [hEc]; ext i j; rfl)
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open scoped WithZero

private theorem exists_unr {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (c : ℂˣ) :
    ∃ χ : Kˣ →* ℂˣ, (∀ u : Oˣ, χ (Units.map (algebraMap O K : O →* K) u) = 1) ∧
      ∀ (ϖ : O) (x : Kˣ), Irreducible ϖ → (x : K) = algebraMap O K ϖ → χ x = c := by
  let w : HeightOneSpectrum O := IsDiscreteValuationRing.maximalIdeal O
  let f : Kˣ →* Multiplicative ℤ :=
    (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
      (Units.map ((w.valuation K : Valuation K ℤᵐ⁰) : K →* ℤᵐ⁰))
  have hf : ∀ (x : Kˣ) (n : Multiplicative ℤ), w.valuation K (x : K) = (n : ℤᵐ⁰) → f x = n := by
    intro x n h
    apply WithZero.coe_injective
    exact (WithZero.coe_unitsWithZeroEquiv_eq_units_val _).trans h
  refine ⟨(zpowersHom ℂˣ c⁻¹).comp f, fun u => ?_, fun ϖ x hϖ hx => ?_⟩
  · have h1 : w.valuation K (Units.map (algebraMap O K : O →* K) u : K) = ((1 : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [Units.coe_map, MonoidHom.coe_coe, HeightOneSpectrum.valuation_of_algebraMap, WithZero.coe_one,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
    rw [MonoidHom.comp_apply, hf _ _ h1, map_one]
  · have h1 : w.valuation K (x : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [hx, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq]
      rfl
    rw [MonoidHom.comp_apply, hf _ _ h1]
    simp [zpowersHom_apply]

private theorem delta_ne {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) : R.Δ ≠ 0 := by
  intro h
  have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) * QuadraticAlgebra.omega = 0 := by
    ext <;> simp [h]
  have h2 : R.e QuadraticAlgebra.omega = 0 := by
    have := congrArg R.e h1
    rw [map_mul, map_zero] at this
    exact mul_self_eq_zero.1 this
  have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) = 0 := by
    exact (map_eq_zero_iff R.e R.e.injective).1 h2
  have := congrArg QuadraticAlgebra.im h3
  simp at this

private theorem hs_one {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

private theorem hs_neg {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {D : K} (L : IsLoc O D) (hD : ¬ IsSquare D) {p : O} (hp : Irreducible p) : hs D (algebraMap O K p) = -1 := by
  haveI := L.frac
  obtain ⟨ε, s, hs0, rfl⟩ := L.even
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  refine if_neg fun ⟨a, b, e⟩ => L.not_even hp ?_
  have e' : a ^ 2 - algebraMap O K ε * (s * b) ^ 2 = algebraMap O K p := by rw [← e]; ring
  exact e' ▸ L.even_of_norm ε (fun ⟨r, hr⟩ => hD ⟨r * s, by rw [hr]; ring⟩) (e' ▸ hp')

end UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence in
theorem UpperTheory.V.Z.Sym.Dict.Br.chiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ χ : ∀ v : Pl (Lp L), (Kv v)ˣ →* ℂˣ, (∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) (χ v)) := by
  intro L _ _ _ R
  have key : ∀ v : Pl (Lp L), ∃ χ : (Kv v)ˣ →* ℂˣ,
      (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) χ := by
    intro v
    obtain ⟨hf, -, hfin, -⟩ := locBase (Lp L) v
    haveI := hf
    haveI := hfin
    have hq : (Nat.card (IsLocalRing.ResidueField (Ov v)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    by_cases hsq : IsSquare (cv v R.Δ)
    · haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
      have hΔ : cv v R.Δ ≠ 0 := (map_ne_zero _).2 (delta_ne R)
      obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero one_ne_zero hq))
      refine ⟨χ, fun _ => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      rw [h2 ϖ x hϖ hx, hs_one hΔ hsq]
      rfl
    · obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v)
        (Units.mk0 _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hq))
      refine ⟨χ, fun h => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      have hL := R.loc v (h.resolve_right hsq)
      rw [h2 ϖ x hϖ hx, hx, hs_neg hL hsq hϖ]
      rfl
  choose χ hχ using key
  exact ⟨χ, hχ⟩
end
