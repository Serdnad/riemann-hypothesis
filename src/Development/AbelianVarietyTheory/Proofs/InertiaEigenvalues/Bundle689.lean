module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle591
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeLayerCoverBasisModPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle664
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodNoChiTr

open Polynomial

theorem not_root_of_good (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) (h : Formalism.CyclotomicNorms.IsGood N g f χ) (v : PP) (j : J) :
    ¬ (f v).IsRoot (χ v j : ZMod g) := by
  intro hr
  have hne : f v ≠ 0 := (h.1 v).1.ne_zero
  have hmem : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) ∈ Formalism.CyclotomicNorms.rootsBar (f v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne), Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.eval₂_hom, hr.eq_zero, map_zero]
  obtain ⟨ℓ, hℓ, hℓg⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ g := by
    by_cases h2 : g = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun e => h2 e.symm⟩
  exact h.2.2.2.1 ℓ hℓ hℓg v j _ hmem rfl

theorem conv_mirC_eC : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  intro hS D G _ _ Pl0 T A Ks _ _ _ R F hG i PP a ha b ε hε x
  obtain ⟨eR, plg, iso, hcoef, hdiv, hrec⟩ := hG.core.grp.record
  obtain ⟨kv0, rfl⟩ := plg.surjective PP
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have heC : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := by
    intro g
    rw [← hcoef g]
    unfold RealDat.eC sg0
    rw [sgAt_mk _ R.hv0]
  rw [Finset.sum_congr rfl (fun y _ => by rw [GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement D G Pl0 T A Ks R eR plg iso hrec i kv0 a b ε y, heC])]
  refine GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero D G eR kv0 _ ?_ x
  intro a' hgood
  obtain ⟨L, hL, c, hc, hcc⟩ := GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes D G Pl0 T A Ks R hG.types kv0.1 kv0.2 i (plg kv0).1 (hdiv kv0) (iso kv0) ε hε
  rw [← D.ntypes.eSer_central, hL]
  have h1 := not_root_of_good _ _ _ _ (hgood kv0.1).1 kv0.2 i
  have h2 := not_root_of_good _ _ _ _ (hgood kv0.1).2 kv0.2 i
  have ha' : (fun j => (iso kv0).symm (a j)) ≠ 0 := by
    intro h; apply ha; funext j
    have := congrArg (iso kv0) (congrFun h j)
    simpa using this
  refine hS _ L _ _ _ c hc ?_ ?_ _ b ha'
  · rcases hcc with rfl | rfl
    · exact h1
    · exact h2
  · rcases hcc with rfl | rfl
    · rw [← Units.val_inv_eq_inv_val]; exact h2
    · rw [Units.val_inv_eq_inv_val, inv_inv]; exact h1

end GlobalTheory.GoodNoChiTr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  first | exact @GlobalTheory.RawLift.Eig.zop_eigen | exact GlobalTheory.RawLift.Eig.zop_eigen | (intros; apply GlobalTheory.RawLift.Eig.zop_eigen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite.LiftOp
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_datVt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : GA D (Vc D i)) :
    levChi (Vc D i) (R.βV i) (R.datVt i t) κ = levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  have h := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.datVt i t).P (finE (Vc D i) κ)
  have h1 : Formalism.L2.DIV.ext1 (R.datVt i t).P.H (R.datVt i t).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ)) = 1 := by
    unfold Formalism.L2.DIV.ext1; split_ifs with hm
    · have : (⟨_, hm⟩ : (R.datVt i t).P.H) = 1 := Subtype.ext (Subgroup.mem_bot.1 hm)
      rw [this, map_one]
    · rfl
  unfold levChi
  rw [show R.datVt i t = withP (R.datVt i t) (R.datVt i t).P from rfl, h, h1, one_mul]
  rfl

theorem chF_mul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ₁ κ₂ : GA D (Vc D i)}
    (h₁ : finE (Vc D i) κ₁ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (h₂ : finE (Vc D i) κ₂ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ₁ * κ₂) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₁ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₂ := by
  unfold levChi
  rw [map_mul, levFn_flag_mul h₁ h₂, Units.val_mul]

theorem parLev_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    finE (Vc D i) 1 ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
  rw [map_one]; exact Subgroup.one_mem _

theorem chF_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have h := chF_mul R i t (parLev_one R i t) (parLev_one R i t)
  rw [mul_one] at h
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (1 : GA D (Vc D i))
  have : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem chF_inv (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (h : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ := by
  have hi : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ h
  have e := chF_mul R i t h hi
  rw [mul_inv_cancel, chF_one] at e
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  field_simp
  rw [mul_comm]; exact e.symm

theorem conj_mem_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ j : GA D (Vc D i)} (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (hj : j ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) : κ * j * κ⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
  refine ⟨(GfC (Vc D i)).mul_mem ((GfC (Vc D i)).mul_mem hκG hj.1) ((GfC (Vc D i)).inv_mem hκG), ?_⟩
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2
  have hki : (finE (Vc D i) κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) :=
    Subgroup.inv_mem _ hκ
  show finE (Vc D i) (κ * j * κ⁻¹) ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)
  rw [map_mul, map_mul, map_inv]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hκ hj2.1) hki, ?_⟩
  have h1 : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) j) = 1 := Subgroup.mem_bot.1 hj2.2
  rw [Formalism.L2.DIV.rTup_mul (Subgroup.mul_mem _ hκ hj2.1) hki, Formalism.L2.DIV.rTup_mul hκ hj2.1, h1,
    Formalism.L2.DIV.rTup_inv hκ, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem typeVec_move (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {κ : GA D (Vc D i)}
    (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) : TypeVec R i t (R.ωP i t (κ⁻¹, 1) φ) := by
  refine ⟨(hP i t).datum.om_pres _ φ hφ.1, fun j hj => ?_⟩
  have hc := conj_mem_lev R i t hκG hκ hj
  have e : ((j, 1) : GA D (Vc D i) × GA D (Wc D i)) * (κ⁻¹, 1) = (κ⁻¹, 1) * (κ * j * κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2.1
  have hki : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ hκ
  have hchi : levChi (Vc D i) (R.βV i) (R.datVt i t) (κ * j * κ⁻¹) = levChi (Vc D i) (R.βV i) (R.datVt i t) j := by
    rw [levChi_datVt, levChi_datVt, chF_mul R i t (by rw [map_mul]; exact Subgroup.mul_mem _ hκ hj2) hki,
      chF_mul R i t hκ hj2, chF_inv R i t hκ]
    have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
    field_simp
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hφ.2 _ hc, map_smul, hchi]

theorem levG_flag1 (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) = levG (Vc D i) (R.βV i) (R.datVt i t) := rfl

theorem pi_lift_indep (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {g0 : Formalism.L2.DIV.G0 (R.datVt i t).Pg (R.datVt i t).r}
    {κ κ' : GA D (Vc D i)} (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ')
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) :
    (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ')⁻¹ • R.ωP i t (κ'⁻¹, 1) φ =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.ωP i t (κ⁻¹, 1) φ := by
  have hd : κ⁻¹ * κ' ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
    have h0 := lift_div_mem hκ hκ'
    rw [levG_flag1] at h0
    exact h0
  have hdi : (κ⁻¹ * κ')⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := Subgroup.inv_mem _ hd
  have hm := typeVec_move R i t hP hκ.1 hκ.2.1 hφ
  have e : ((κ'⁻¹, 1) : GA D (Vc D i) × GA D (Wc D i)) = ((κ⁻¹ * κ')⁻¹, 1) * (κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hdp : finE (Vc D i) (κ⁻¹ * κ') ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hd.2.1
  have hc : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ' =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ') := by
    rw [← chF_mul R i t hκ.2.1 hdp, mul_inv_cancel_left]
  rw [e, map_mul, Module.End.mul_apply, hm.2 _ hdi, levChi_datVt, chF_inv R i t hdp, hc, smul_smul]
  congr 1
  have h1 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  have h2 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ')
  field_simp

end GlobalTheory.DownLift.GenFinite.LiftOp

namespace GlobalTheory.DownLift.GenFinite
open LiftOp

theorem cleanSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ ∧ GlobalTheory.DownLift.GenFinite.Clean R i t φ} ∪ GlobalTheory.DownLift.GenFinite.AvgIm R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hf
  by_cases hex : ∃ κ : G → GA D (Vc D i), IsLifts R i t κ
  swap
  · exact Submodule.subset_span (Or.inl ⟨hf, fun PP a _ tr ε _ κ hκ => absurd ⟨κ, hκ⟩ hex⟩)
  obtain ⟨κ, hκ⟩ := hex
  let S : Submodule ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    { carrier := {φ | TypeVec R i t φ}
      add_mem' := fun {a b} ha hb => ⟨theta_add ha.1 hb.1, fun j hj => by rw [map_add (f := _), ha.2 j hj, hb.2 j hj, smul_add]⟩
      zero_mem' := ⟨by simpa using theta_smul (0 : ℂ) hf.1, fun j hj => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c a ha => ⟨theta_smul c ha.1, fun j hj => by
        rw [map_smul, ha.2 j hj, smul_comm]⟩ }
  have hSm : ∀ φ, φ ∈ S ↔ TypeVec R i t φ := fun _ => Iff.rfl
  let π : G → Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1)
  have hπ : ∀ g φ, π g φ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1) φ :=
    fun _ _ => rfl
  have hS : ∀ g, ∀ v ∈ S, π g v ∈ S := by
    intro g v hv
    rw [hπ]; exact S.smul_mem _ ((hSm _).2 (typeVec_move R i t hP (hκ g).1 (hκ g).2.1 ((hSm _).1 hv)))
  have hlift1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG 1) 1 :=
    ⟨Subgroup.one_mem _, parLev_one R i t, by rw [map_one, Formalism.L2.DIV.rTup_one, map_one]; rfl⟩
  have h1 : ∀ v ∈ S, π 1 v = v := by
    intro v hv
    rw [hπ, pi_lift_indep R i t hP hlift1 (hκ 1) ((hSm _).1 hv), chF_one, inv_one, one_smul, inv_one,
      ← Prod.one_eq_mk, map_one]
    rfl
  have hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v) := by
    intro g h v hv
    have hl : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG (g * h)) (κ g * κ h) := by
      refine ⟨(GfC (Vc D i)).mul_mem (hκ g).1 (hκ h).1, ?_, ?_⟩
      · rw [map_mul]; exact Subgroup.mul_mem _ (hκ g).2.1 (hκ h).2.1
      · rw [map_mul, Formalism.L2.DIV.rTup_mul (hκ g).2.1 (hκ h).2.1, (hκ g).2.2, (hκ h).2.2, map_mul]; rfl
    rw [hπ, pi_lift_indep R i t hP hl (hκ (g * h)) ((hSm _).1 hv), hπ, hπ, map_smul, smul_smul,
      ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, chF_mul R i t (hκ g).2.1 (hκ h).2.1, _root_.mul_inv_rev,
      _root_.mul_inv_rev]
  let C : Set (G → ℂ) := {c | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ),
    (ε = 1 ∨ ε = -1) ∧ c = mirC R i PP a tr ε}
  have hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C := by
    rintro c ⟨PP, a, ha, tr, ε, hε, rfl⟩ x
    obtain ⟨a', ha', he⟩ := GlobalTheory.T.mirabolicDetCharacterFunction_conj D G Pl0 T A Ks R i PP a ha tr ε x
    exact ⟨PP, a', ha', tr, ε, hε, funext he⟩
  have havg : ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ) (κ' : G → GA D (Vc D i)), IsLifts R i t κ' →
      ∀ w ∈ S, avgW R i t PP a tr ε κ' w = ∑ g, mirC R i PP a tr ε g • π g w := by
    intro PP a tr ε κ' hκ' w hw
    unfold avgW
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hπ, ← pi_lift_indep R i t hP (hκ g) (hκ' g) ((hSm _).1 hw), smul_smul]
  have key := GlobalTheory.T.mem_span_annihilated_union_class_averages S π hS h1 hmul C hC f hf
  refine Submodule.span_mono ?_ key
  rintro w (⟨hwS, hw⟩ | ⟨c, ⟨PP, a, ha, tr, ε, hε, rfl⟩, w', hw'S, rfl⟩)
  · exact Or.inl ⟨hwS, fun PP a ha tr ε hε κ' hκ' => by
      rw [havg PP a tr ε κ' hκ' w hwS]; exact hw _ ⟨PP, a, ha, tr, ε, hε, rfl⟩⟩
  · exact Or.inr ⟨PP, a, ha, tr, ε, hε, κ, hκ, w', hw'S.1, (havg PP a tr ε κ hκ w' hw'S).symm⟩

end GlobalTheory.DownLift.GenFinite
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

theorem ops_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∃ B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) ∧ (∀ γ, ‖B γ‖ ≤ 1) ∧ B 1 = 1 ∧ ∀ γ k, k ∈ GlobalTheory.UpInj.KR R i → B (γ * k) = B γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL
  choose B hBn hBp using fun γ : GfC (Wc D i) => hTL.2.2.1 γ γ.2
  refine ⟨B, fun γ x y => hBp γ x y, hBn, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp 1 x y, ContinuousLinearMap.one_apply]
    exact hTL.2.2.2.2.2 x y
  · intro γ k hk
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp, ← hBp]
    have := hTL.2.2.2.1 γ γ.2 1 (Subgroup.one_mem _) k (Subgroup.mem_subgroupOf.1 hk) x y
    rwa [one_mul] at this

theorem coef_mult_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T), FinMult R i t → LocSmall R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ v (g h : GfC (Wc D i)), GlobalTheory.UpInj.cf (Wc D i) v g = 1 → GlobalTheory.UpInj.cf (Wc D i) v h = h → coef R i t μ 𝓕 ((g * h : GfC (Wc D i)) : GA D (Wc D i)) = coef R i t μ 𝓕 g * coef R i t μ 𝓕 h) ∧ ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (GfC (Wc D i))), (∀ g ∈ C, GlobalTheory.UpInj.cf (Wc D i) v g = g ∧ g ∉ GlobalTheory.UpInj.KR R i) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ GlobalTheory.UpInj.KR R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hFM hLS μ 𝓕 hμ
  refine ⟨fun v g h hg hh => ?_, ?_⟩
  · exact hFM μ 𝓕 hμ v _ (GlobalTheory.UpInj.isFinIdem_fE v) g g.2 (GlobalTheory.UpInj.trivAt_of_cf_eq_one _ v g hg) h
      ((GlobalTheory.UpInj.cf_eq_self_iff _ v h).1 hh)
  · obtain ⟨s, hs, hs1, hsb⟩ := hLS μ 𝓕 hμ
    refine ⟨s, hs, hs1, fun v C hC hCd => ?_⟩
    have := hsb v _ (GlobalTheory.UpInj.isFinIdem_fE v) (C.map (Function.Embedding.subtype _)) ?_ ?_
    · simpa [Finset.sum_map] using this
    · intro g hg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      exact ⟨(GlobalTheory.UpInj.cf_eq_self_iff _ v g).1 (hC g hgC).1, fun h => (hC g hgC).2 (Subgroup.mem_subgroupOf.2 h)⟩
    · intro g hg g' hg' hgg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      obtain ⟨g', hgC', rfl⟩ := Finset.mem_map.1 hg'
      refine congrArg _ (hCd g hgC g' hgC' (Subgroup.mem_subgroupOf.2 ?_))
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgg



theorem coef_biinv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → VecNe R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ g k k', k ∈ levW R i → k' ∈ levW R i → coef R i t μ 𝓕 (k * g * k') = coef R i t μ 𝓕 g) ∧ coef R i t μ 𝓕 1 = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hVN μ 𝓕 hμ
  have hv : ∀ k ∈ levW R i, R.ωP i t (1, k) (R.vP i t) = R.vP i t := fun k hk => by
    have := hLF k hk 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hW := hL.thP.ωP i t
  refine ⟨fun g k k' hk hk' => ?_, GlobalTheory.RawLift.Model.coef_one R i t hVN μ 𝓕 hμ⟩
  rw [GlobalTheory.RawLift.Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk']
  unfold coef
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  calc thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.vP i t)
      = thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.ωP i t (1, k) (R.vP i t)) := by rw [hv k hk]
    _ = thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) :=
      GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hμ (1, k) _ _ (hW.om_pres _ _ hth) hth

theorem injective_of_inner_eq {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : H →ₗ[ℂ] E) (W : H →L[ℂ] H) (a0 : ℝ) (ha0 : 0 < a0)
    (key : ∀ x y, ⟪L x, L y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ) (hW : Function.Injective W) : Function.Injective L := by
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have sym : ∀ x y, ⟪x, W y⟫_ℂ = ⟪W x, y⟫_ℂ := by
    intro x y
    have h2 : (a0 : ℂ) * ⟪x, W y⟫_ℂ = (a0 : ℂ) * ⟪W x, y⟫_ℂ := by
      rw [← key, ← inner_conj_symm, key, map_mul, Complex.conj_ofReal, inner_conj_symm]
    exact mul_left_cancel₀ ha0' h2
  intro x x' hxx'
  have hz : L (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  have h3 := key (x - x') (W (x - x'))
  rw [hz, inner_zero_left] at h3
  have h4 : ⟪x - x', W (W (x - x'))⟫_ℂ = 0 := (mul_eq_zero.1 h3.symm).resolve_left ha0'
  rw [sym] at h4
  have hWz : W (x - x') = 0 := inner_self_eq_zero.1 h4
  exact sub_eq_zero.1 (hW (hWz.trans (map_zero W).symm))


theorem upInj_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → LevProd R i → TransLaws R i → UpInj R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hFS hFM hLF hVN hLS _ hTL
  classical
  obtain ⟨⟨p, hp⟩, -⟩ := (hL.thP.vP i t).1.2.norm
  obtain ⟨hinv, h1⟩ := coef_biinv D G Pl0 T A Ks R F hL i t hLF hVN p.1 p.2 hp
  obtain ⟨hmul, s, hs, hs1, hsm⟩ := coef_mult_small D G Pl0 T A Ks R i t hFM hLS p.1 p.2 hp
  obtain ⟨B, hB, hBn, hB1, hBK⟩ := ops_exist D G Pl0 T A Ks R i hTL
  obtain ⟨hrep, hhk⟩ := GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity D G Pl0 T A Ks R i hTL B hB
  let a : GfC (Wc D i) → ℂ := fun g => coef R i t p.1 p.2 g
  have hmem := GlobalTheory.UpInj.kr_mem_iff R i
  have hfin := GlobalTheory.UpInj.kr_finite R i
  have hidem : ∀ v g, GlobalTheory.UpInj.cf (Wc D i) v (GlobalTheory.UpInj.cf (Wc D i) v g) = GlobalTheory.UpInj.cf (Wc D i) v g :=
    fun v g => GlobalTheory.UpInj.cf_cf (Wc D i) v g
  have horth : ∀ v w g, v ≠ w → GlobalTheory.UpInj.cf (Wc D i) w (GlobalTheory.UpInj.cf (Wc D i) v g) = 1 :=
    fun v w g h => GlobalTheory.UpInj.cf_orth (Wc D i) h g
  obtain ⟨e, he⟩ := GlobalTheory.T.quotient_equiv_restrictedComponentFamilies _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) hmem hfin hidem horth
  have ha_bi : ∀ g k k', k ∈ GlobalTheory.UpInj.KR R i → k' ∈ GlobalTheory.UpInj.KR R i → a (k * g * k') = a g := by
    intro g k k' hk hk'
    exact hinv g k k' (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hk')
  have ha_right : ∀ g k, k ∈ GlobalTheory.UpInj.KR R i → a (g * k) = a g := by
    intro g k hk
    have := ha_bi g 1 k (Subgroup.one_mem _) hk
    rwa [one_mul] at this
  have hfac := GlobalTheory.T.rightInvariant_mul_eq_finprod_components _ _ _ _ a hmem hfin hidem horth ha_right h1 hmul
  have hloc := fun v => GlobalTheory.T.hasSum_localEulerFactor_heckeOperators _ (GlobalTheory.UpInj.KR R i) (GlobalTheory.UpInj.cf (Wc D i) v) _ a B (s v) (hidem v) ha_bi hBK hBn
    (hsm v) (hrep v) (hhk v)
  obtain ⟨W, hWi, hW⟩ := GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) _ a B s e he hmem hidem horth ha_right h1 hfac
    hBn hB1 hBK hs hs1 hsm hloc
  intro th hth
  obtain ⟨a0, ha0, hsum⟩ := hFS th hth p.1 p.2 hp
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have key : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ := by
    intro x y
    have h2 := (hW x y).mul_left (a0 : ℂ)
    have e : (fun q : GfC (Wc D i) ⧸ GlobalTheory.UpInj.KR R i => (a0 : ℂ) * (a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ)) =
        fun q => (a0 : ℂ) * (coef R i t p.1 p.2 (Quotient.out q : GfC (Wc D i)) *
          trPair R i (Quotient.out q : GfC (Wc D i)) x y) := by
      funext q; rw [hB]
    rw [e] at h2
    exact (hsum x y).unique h2
  exact injective_of_inner_eq _ W a0 ha0 key hWi

end GlobalTheory.UpInj

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → LinearIndependent ℚ_[l] b → (∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ c : ℕ, (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → ∀ (n N : ℕ), n ≤ N → (∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ N • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹) → ∀ (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, Continuous (ρs k)) → (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∀ cs : Fin m → Om l, (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (L k).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb P N ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  first | (exact @GlobalTheory.CovLayer.layer) | (exact GlobalTheory.CovLayer.layer) | (intros; apply GlobalTheory.CovLayer.layer  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ n : ℕ, (dpS a e n : ZMod a → K⟦X⟧) ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, frobTot K a l (dpS a e n) = (dpS a e n : ZMod a → K⟦X⟧) ^ l + (l : ZMod a → K⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.dpS_frob_good | exact GlobalTheory.CrysPrism.dpS_frob_good | (intros; apply GlobalTheory.CrysPrism.dpS_frob_good <;> assumption)
end
