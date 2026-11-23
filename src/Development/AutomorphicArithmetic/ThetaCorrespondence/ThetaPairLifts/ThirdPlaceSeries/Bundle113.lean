module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle384
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle085
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ExpZeroAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
    ∑ k, c k • evW p.nexp p.v₀ j (g k).val = 0 → ∑ k, τ (c k) • evW p.nexp p.v₀ j (g k).val = 0
theorem bigOn_expZero : _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j τ hτ n c g h0 => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact conj_sum_zero _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ j hU hW (Z.vec j) hK τ hτ n c g h0
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
end
end
end

section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
section Generic
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end Generic

theorem descent_of_reading_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν rd => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w))
    (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL), (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z = ∑ k, a k • rd (y k) := by
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y hy hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  apply hRinj

  rw [hinc, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
    hrd _ (hy k), mul_smul]
end GlobalTheory.BigOn.Exp
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TwAdmProof
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
open GlobalTheory.BigOn.Exp.TwAdmProof in
theorem GlobalTheory.BigOn.Exp.twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ w hw _ => ?_⟩⟩
  have hmu := (p.tw_iff w).1 hw
  obtain ⟨-, N0, S, hG⟩ := hR.ties.twist
  obtain ⟨-, hall⟩ := hG w hmu
  have h1 := hall 1 (by simp)
  rw [zpow_one] at h1
  have hpsi := h1.1
  refine ⟨?_, ?_, GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ _ (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois w hmu⟩
  · have h2 := Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt ((Fm.ex x hx i).nch.sd w) (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hpsi)
    rw [psiAt_comp, Formalism.MainNotions.psiAt_psiAt] at h2
    exact h2
  · intro P hP
    obtain ⟨-, hin, he⟩ := hpsi.1 P hP
    exact exists_splitK_of P hin he
end
end

section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
section ScalarGeneric
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end ScalarGeneric

theorem scalar_of_reading_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y κ N hy hN hint hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have hS : R (∑ k, a k • rd (y k)) = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
      hrd _ (hy k), mul_smul]
  have hRHS : ∀ b : ((Fm.ex x hx i).nch.Oe w), ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) b) •
      ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun b => by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, smul_smul, mul_assoc]
  by_cases hT0 : ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0
  · exact ⟨0, by rw [hRHS, hz, hT0, smul_zero, smul_zero]⟩
  · obtain ⟨b₀, hb₀⟩ := readExt_scalar_mem_range _ e hL hF
      (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z)
      (∑ k, a k • rd (y k)) κ (by rw [hinc, hS, hz]) (by rwa [hS])
    obtain ⟨m, hmI⟩ := hint
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_isIntegral e b₀ N hN m (by rwa [hb₀])
    exact ⟨b, by rw [hRHS, hz, hb, hb₀]⟩
end GlobalTheory.BigOn.Exp
end
end
end

section



section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
structure FamilyConstants where
  ε : ℕ → a.ι → 𝓀[a.k]ˣ
  op : ∀ j, BiOp (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1))
  r : ℕ → a.ι → ℝ
  e : ℕ → a.ι → ℤ
  cG : ℕ → ℂ
  sc : W.P.T → ℕ → ℂ
variable {a} (k : _root_.GlobalTheory.Fam.FamilyConstants a)
abbrev FamilyConstants.v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) := (a.v.withT (a.o.S k.ε) k.op).withCG k.cG
variable {row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
structure ColumnOutputCondition (w₀ w : ∀ t, VTup ((a.fam row col).t t))
    (F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) : Prop where
  ok : (a.fam row col).ColOK
  pins : ∀ t, (F t).Pins (w₀ t)
  same : ∀ t, (w t).Q = (w₀ t).Q ∧ (w t).eQ = (w₀ t).eQ ∧ (w t).eQT = (w₀ t).eQT ∧ (w t).cQ = (w₀ t).cQ ∧ (w t).FY = (w₀ t).FY ∧
    (w t).FT = (w₀ t).FT
  laws : ∀ t, QLaw a.v (w t) ∧ QLast a.v (w t) ∧ QFin a.v (w t)
  lev : ∀ t, _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) (F t)
  vec : ∀ t, _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) (w₀ t)
  FY : ∀ t j f, f ∈ (w₀ t).FY j ↔ ∀ i, ((F t).Q i).Typed j f
  FT : ∀ t f, f ∈ (w₀ t).FT
  FX : ∀ t j, j + 2 ≤ D.R.m → ∀ ψ ∈ (col t).Ram j, ∀ α y, (col t).rd j α ψ y ∈ (w t).FX j α
  atQ : ∀ t j, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w t).dQ j α γ)
  e : ∀ t j α, (col t).e j α = ((w t).ε j α).mapDomain (· * a.g.b j) ∧
    ∀ g ∈ ((w t).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ (w₀ t).Q)
  eT : ∀ t n h β, (col t).eT n h β = ((w t).εT n h β).mapDomain (· * a.g.bT) ∧
    ∀ g ∈ ((w t).εT n h β).support, g ∈ GlobalTheory.FinPl.grpAt D.sp.X' (· ∈ (w₀ t).Q)
  dd : ∀ t j, j < D.R.m → ∀ α γ f, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ f → comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((col t).dd j α γ) f =
    comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((w t).dQ j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f))
  read : ∀ t, ∃ S₀, ReadS a.o ((a.fam row col).t t) k.ε S₀
  sc : ∀ t, (w t).sc = k.sc t
  cT : ∀ t j ρ h, (w t).cT j = a.o.mono (k.r j) (k.e j) ((row t).sBF j ρ h).χW
  cv : ∀ t, CVEq k.v (w t)
  cK : ∀ t j, j < D.R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((col t).cK j) ((col W.P.A3.A.μ0).cK j)
  cP : ∀ t, UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) (col t).cP (col W.P.A3.A.μ0).cP
  zero : _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col)
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def LevelCondition' (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg ∧ (∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ↔ PP ∈ (B.primes X).vGs) ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z W).xiH t = I.xi (W.P.I.tup t)
structure AllFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  pk : _root_.GlobalTheory.Fam.PackageHypotheses W
  tr : _root_.GlobalTheory.Fam.ValidRealPackage W
  tq : _root_.GlobalTheory.Fam.GeometricFamilyConditions W
  tw : _root_.GlobalTheory.AdForm.TwStdAlt W
  lev : _root_.GlobalTheory.Fam.LevelCondition' W
  rc : Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q)
end True
end GlobalTheory.Fam
end
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem linkZero_of_chartZero_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), _root_.GlobalTheory.MiTop.ChartAtZeroCondition f → (∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, d.B.lev = f.c.B 0 D.R.rS h₀) → d.b = (show GA D (D.sp.Y 0) from f.g.b 0) → _root_.GlobalTheory.MiTop.LinkVanishes f d := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hc hl hb n h₀ t φ
  obtain ⟨α₀, h1, h2, h3, -⟩ := hc t
  refine ⟨(h3 φ).1, fun G y v => ?_⟩
  obtain rfl : n = D.R.rS := by
    have : D.R.rS = D.R.m / 2 - 1 := rfl
    omega
  have e : ∀ g : GA D (Yc D 0) → ℂ, trc (Finsupp.single (f.g.b 0) 1) g = rTrans (f.g.b 0) g := fun g => by
    unfold trc
    rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  unfold _root_.GlobalTheory.MiTop.BottomData.per Tup.per Tup.perF
  rw [Finset.sum_eq_single α₀ (fun b _ hb => absurd (h1 b) hb) (by simp)]
  beta_reduce
  rw [h2, (h3 φ).2 y, hb]
  exact besLev_per_congr (hl h₀).symm _ HEq.rfl (heq_of_eq (e _))
end GlobalTheory.MiTop
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_rational_eigen_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  first | exact @_root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | exact _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | (intros; apply _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt <;> assumption)
end
end
