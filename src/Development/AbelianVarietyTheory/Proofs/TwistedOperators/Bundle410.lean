module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem fixed_of_forall_finLoc_mem : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  intro D V W _ _ σ hσ K' hK' x hx g hg
  have fl_self : ∀ a (y : GLoc D.sp.cm.sig V.gram a), finLoc V a (locFin V a y) = y :=
    fun a y => proj_emb_self _ _ a y
  have fl_ne : ∀ v a, v ≠ a → ∀ (y : GLoc D.sp.cm.sig V.gram a), finLoc V v (locFin V a y) = 1 :=
    fun v a h y => proj_emb_ne _ _ h y
  let St : Subgroup (GfC V) :=
    { carrier := {k | σ k x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : σ a⁻¹ (σ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at e }
  have hSt : IsOpen (St : Set (GfC V)) := hσ x
  let U : Subgroup (GA D V) := St.comap (toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hSt.preimage (continuous_toFin V)
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig V.gram (frameLat V) U hU
  have key : ∀ k : GfC V, (∀ v ∈ S, finLoc V v k = 1) → (∀ v, v ∉ S → finLoc V v k ∈ Kv V v) → σ k x = x := by
    intro k h1 h2
    have hk : (k : GA D V) ∈ levelOff D.sp.cm.sig V.gram (frameLat V) S := mem_levelOff.2 ⟨k.2, h1, h2⟩
    have h := hS hk
    have e : toFin V (k : GA D V) = k := toFin_coe k
    change σ (toFin V (k : GA D V)) x = x at h
    rwa [e] at h
  have step : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ k : GfC V, (∀ v, finLoc V v k ∈ K' v) →
      (∀ v ∈ S, v ∉ T → finLoc V v k = 1) → σ k x = x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k hk h1
      exact key k (fun v hv => h1 v hv (Finset.notMem_empty v)) (fun v _ => hK' v (hk v))
    | insert a T ha ih =>
      intro k hk h1
      set k' := locFin V a (finLoc V a k)⁻¹ * k with hk'
      have hfix : σ k' x = x := by
        refine ih k' (fun v => ?_) (fun v hv hvT => ?_)
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact hk v
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact h1 v hv (by simp [h, hvT])
      have hkk : k = locFin V a (finLoc V a k) * k' := by
        simp [k', ← mul_assoc, ← map_mul]
      rw [hkk, map_mul, Module.End.mul_apply, hfix]
      exact hx a _ (hk a)
  exact step S g hg (fun v hv hvS => absurd hv hvS)

end GlobalTheory.TrIdem
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct


theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_self : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) v) = (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).val.map (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E) := by
  first | exact @GlobalTheory.FinLocSelf.finE_locFin_map_prV | exact GlobalTheory.FinLocSelf.finE_locFin_map_prV | (intros; apply GlobalTheory.FinLocSelf.finE_locFin_map_prV <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_finset_localComponent_copies_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  first | exact @GlobalTheory.FinMultAway.exists_finset_fixed_away | exact GlobalTheory.FinMultAway.exists_finset_fixed_away | (intros; apply GlobalTheory.FinMultAway.exists_finset_fixed_away <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct


theorem _root_.GlobalTheory.T.mem_localLatticeCompletion_iff_comm_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ (fun i => Algebra.TensorProduct.comm F (Fv F v) E (y i)) ∈ Formalism.L2.Herm.locL v L := by
  first | exact @GlobalTheory.TwistLat.mem_latLoc_iff_comm_mem_locL | exact GlobalTheory.TwistLat.mem_latLoc_iff_comm_mem_locL | (intros; apply GlobalTheory.TwistLat.mem_latLoc_iff_comm_mem_locL <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  first | exact @GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | exact GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | (intros; apply GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.integral_finiteIndicator_smul_archFunction : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  first | exact @GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | exact GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | (intros; apply GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  first | exact @GlobalTheory.LocIsoConj.exists_locIso | exact GlobalTheory.LocIsoConj.exists_locIso | (intros; apply GlobalTheory.LocIsoConj.exists_locIso <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_finiteGroupAction_principalLevelFixedVectors : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))), ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  first | exact @GlobalTheory.PrinFixedRep.main | exact GlobalTheory.PrinFixedRep.main | (intros; apply GlobalTheory.PrinFixedRep.main <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  first | exact @GlobalTheory.InvPairing.exists_intertwiner | exact GlobalTheory.InvPairing.exists_intertwiner | (intros; apply GlobalTheory.InvPairing.exists_intertwiner <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.schur_admissible_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := by
  first | exact @GlobalTheory.SchurAdm.schur_admissible | exact GlobalTheory.SchurAdm.schur_admissible | (intros; apply GlobalTheory.SchurAdm.schur_admissible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

def hA (T : HSp D) (y z : Fin T.rank → AE D) : AE D := ∑ k, cA D (z k) * (gA T *ᵥ y) k

theorem pairS_eq_sum (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) :
    pairS T x x' = ∑ p, hA T (fun k => x k p) (fun k => x' k p) := by
  simp only [pairS, hA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem mxAt_of_mem_depLat {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {p : Pair T}
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) : MxAt (fun _ => True) u :=
  GlobalTheory.FinPl.LatMem.latO_mxAt hu.1

end GlobalTheory.CharXFB
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Fib (Xo : Moduli Dw l) {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : Over (Sp K) :=
  (Over.pullback x).obj Xo.univ.t.G

variable {Xo : Moduli Dw l} {c : Coeff l}

def Lin {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') : Prop :=
  ∀ a : 𝓞 E, (Over.pullback x).map (Xo.univ.t.act.act a) ≫ f = f ≫ (Over.pullback x').map (Xo.univ.t.act.act a)

def IsPair (N : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) : Prop :=
  IsMonHom f ∧ IsMonHom f' ∧ f ≫ f' = 𝟙 _ ^ N ∧ f' ≫ f = 𝟙 _ ^ N ∧ Lin f ∧ Lin f'

def HkWith (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) (f : Fib Xo y.x ⟶ Fib Xo z.x)
    (f' : Fib Xo z.x ⟶ Fib Xo y.x) : Prop :=
  IsPair (p ^ 2) f f' ∧ (∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j)) ∧
    IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s

def HkOver (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) : Prop :=
  AllRat Xo y.x (p ^ 2) ∧ AllRat Xo z.x (p ^ 3) ∧ ∃ f f', HkWith p y z f f'

def IsBC {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}
    (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') : Prop :=
  w = spMap φ ≫ x ∧ w' = spMap φ ≫ x' ∧
    ∀ (π : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom x)
      (π' : pullback Xo.univ.t.G.hom w' ⟶ pullback Xo.univ.t.G.hom x'),
      π ≫ pullback.fst _ _ = pullback.fst _ _ → π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      π' ≫ pullback.fst _ _ = pullback.fst _ _ → π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      (g.left : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom w') ≫ π' =
        π ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')

def Ext {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') (F : G.G ⟶ G'.G) : Prop :=
  ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ ψ.left ≫ n₂.φ = m₂.φ ≫ F.left ∧
    ∀ (g : t.G.left ⟶ pullback Xo.univ.t.G.hom x) (g' : t'.G.left ⟶ pullback Xo.univ.t.G.hom x'),
      g ≫ pullback.fst _ _ = m₁.φ → g ≫ pullback.snd _ _ = t.G.hom →
      g' ≫ pullback.fst _ _ = n₁.φ → g' ≫ pullback.snd _ _ = t'.G.hom →
      g ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = ψ.left ≫ g'

def Reg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))) : Prop :=
  ∃ σ, PullbackSections.SecTie I (M ^ 2) (PullbackSections.zCast Xo.univ.t.G (PullbackSections.natCast_sq M) F) σ

def IsTransl (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ a, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (fun u => u ^ (M ^ 2) = 1) s a F

def IsPullOf (M : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (a : K)
    (s' : LB.Sec (PPx x')) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) ((M : ℤ) ^ 2))) (s'' : LB.Sec (PPx x')),
    IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β ∧ (∀ i, s''.f i = scal x' a i * s'.f i) ∧
      IsCarried Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β s'' t

def IsTranslSum (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))),
    (∀ i, IsTransl M s (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

end GlobalTheory.HkIntegral
end
end
