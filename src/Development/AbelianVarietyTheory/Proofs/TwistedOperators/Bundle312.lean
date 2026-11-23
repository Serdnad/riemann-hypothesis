module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle296
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle250
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem conj_mem_and_char_eq_of_levelConjugation {H : Type} [Group H] (t s : H) (J J' : Set H) (χ χ' : H → ℂ)
    (hc : ∀ k, (k ∈ J ↔ t⁻¹⁻¹ * k * t⁻¹ ∈ J') ∧ (k ∈ J → χ' (t⁻¹⁻¹ * k * t⁻¹) = χ k)) (hs : s ∈ J') :
    t⁻¹ * s * t ∈ J ∧ χ (t⁻¹ * s * t) = χ' s := by
  have e : t⁻¹⁻¹ * (t⁻¹ * s * t) * t⁻¹ = s := by group
  have h := hc (t⁻¹ * s * t)
  rw [e] at h
  exact ⟨h.1.2 hs, (h.2 (h.1.2 hs)).symm⟩

theorem conj_mul_eq_mul_conj_group {H : Type} [Group H] (t a b : H) : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by
  group

theorem rowLevelMatchAt_of_conjLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hPin hE0 ht hConj hFrame
  obtain ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ := hPin
  refine ⟨(R.eG.trans cG).symm, fun k => cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))), ?_, ?_, ?_⟩
  · intro k hk
    have e2 : (iotaX X h).toMulEquiv ((iotaX X h).symm (1, k)) = (1, k) :=
      (iotaX X h).toMulEquiv.apply_symm_apply (1, k)
    have hs : (iotaX X h).symm (1, k) ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} := by
      rw [Set.mem_preimage, e2]; exact ⟨rfl, hk⟩
    have hA := conj_mem_and_char_eq_of_levelConjugation (H := GA D (Yc D 0)) t ((iotaX X h).symm (1, k)) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) (fun k' => hConj k') hs
    refine ⟨hA.1, hA.2.trans ?_⟩
    show star (X.chi2 ((iotaX X h).toMulEquiv ((iotaX X h).symm (1, k))).2) = _
    rw [e2]
  · obtain hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame
    refine ⟨⟨GlobalTheory.T.goodAt_reduction_conjugated_unitary_element R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame, ?_,
      GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame,
      GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame⟩, ?_⟩
    · intro k hk k' hk'
      have e1 : (iotaX X h).symm (1, k * k') = (iotaX X h).symm (1, k) * (iotaX X h).symm (1, k') := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have e : kap X h t (k * k') = kap X h t k * kap X h t k' := by
        unfold kap; rw [e1]; exact conj_mul_eq_mul_conj_group (H := GA D (Yc D 0)) t _ _
      show cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t (k * k')))) = cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) * cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k')))
      rw [e, map_mul, Formalism.L2.DIV.rTup_mul (hl k hk).2 (hl k' hk').2]
      exact map_mul cG _ _
    · intro k hk T hT v g
      rw [GlobalTheory.T.rightTranslate_compactLift_acts_by_reduction R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame k hk T hT v g]
      have e3 : R.eG ((R.eG.trans cG).symm (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))) = rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)) := by
        rw [MulEquiv.symm_trans_apply]
        exact (congrArg (fun y => R.eG (R.eG.symm y)) (cG.symm_apply_apply _)).trans (R.eG.apply_symm_apply _)
      rw [e3]
  · intro γ
    unfold RealDat.eC
    rw [hE0 γ, hcoef, MulEquiv.apply_symm_apply]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  first | exact @GlobalTheory.coefA_dual_coef_continuousOn | exact GlobalTheory.coefA_dual_coef_continuousOn | (intros; apply GlobalTheory.coefA_dual_coef_continuousOn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix
open scoped Topology

noncomputable section




namespace GlobalTheory.WeilLevelStab

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho GlobalTheory.Mem.CoefInv

variable {D : D7}

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem actO_one_mul (S T : HSp D) (k k' : GA D T) (x : WO S T) :
    actO S T 1 (k * k') x = actO S T 1 k (actO S T 1 k' x) := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, Matrix.mul_assoc]

theorem actO_nsmul (S T : HSp D) (g : GA D S) (h : GA D T) (c : ℕ) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x :=
  map_nsmul (GlobalTheory.LatLevel.actHom S T g h) c x

def MovesMod (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) (k : GA D T) : Prop :=
  ∀ x ∈ L, ∃ l ∈ L, actO S T 1 k x = x + c • l

theorem movesMod_one (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : MovesMod S T L c 1 :=
  fun x _ => ⟨0, zero_mem _, by rw [actO_one_one, smul_zero, add_zero]⟩

theorem movesMod_mul {S T : HSp D} {L : AddSubgroup (WO S T)} {c : ℕ} {k k' : GA D T}
    (hk : MovesMod S T L c k) (hk' : MovesMod S T L c k') : MovesMod S T L c (k * k') := by
  intro x hx
  obtain ⟨l', hl', e'⟩ := hk' x hx
  obtain ⟨l, hl, e⟩ := hk x hx
  obtain ⟨l'', hl'', e''⟩ := hk l' hl'
  refine ⟨l + (l' + c • l''), add_mem hl (add_mem hl' (AddSubgroup.nsmul_mem _ hl'' c)), ?_⟩
  rw [actO_one_mul, e', GlobalTheory.LatNhds.actO_add, actO_nsmul, e, e'']
  simp only [smul_add]
  abel

def stabK (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : Subgroup (GA D T) where
  carrier := {k | MovesMod S T L c k ∧ MovesMod S T L c k⁻¹}
  one_mem' := ⟨movesMod_one S T L c, by rw [inv_one]; exact movesMod_one S T L c⟩
  mul_mem' := fun ha hb => ⟨movesMod_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact movesMod_mul hb.2 ha.2⟩
  inv_mem' := fun ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isOpen_stabK (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (c : ℕ) (hc : 0 < c) :
    IsOpen ((stabK S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) c : Subgroup (GA D T)) : Set (GA D T)) := by
  have h := eventually_mod ΛS ΛT hS hT c hc
  have ht : Filter.Tendsto (fun k : GA D T => ((1 : GA D S), k)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const (y := (1 : GA D S))).prodMk continuous_id).tendsto (1 : GA D T)
    exact this
  have ti : Filter.Tendsto (fun k : GA D T => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D T)).tendsto 1
    rwa [inv_one] at this
  have h1 := ht.eventually h
  have h2 := ti.eventually h1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [h1, h2] with k hk hk'
  exact ⟨hk, hk'⟩

theorem exists_level_stab_of_selfDual (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧
      (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 →
        actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
        actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧
          ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hLdef
  obtain ⟨n, hn, hnU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  obtain ⟨hdual, happrox, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  refine ⟨L.map (nsmulAddMonoidHom n), stabK S T L (2 * n * n), ?_,
    isOpen_stabK S T ΛS ΛT hS hT (2 * n * n) (by positivity), ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hnU u hu
  · intro x
    obtain ⟨ρ, hρ, u, hu, hf⟩ := happrox (x - realIdem D • x) (fin_part x)
    refine ⟨ρ, hρ, ?_⟩
    rintro _ ⟨l, hl, rfl⟩ -
    have hnl : n • l ∈ L := AddSubgroup.nsmul_mem _ hl n
    have e : x - ρ = (realIdem D • x + (x - realIdem D • x - ρ - u)) + u := by abel
    show ψ (symplO S T (x - ρ) (n • l)) = 1
    rw [e, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      symplO_real_fin S T (real_part x) (latO_fin hnl), symplO_real_fin S T hf (latO_fin hnl), zero_add, zero_add]
    exact (hdual u (latO_fin hu)).1 hu _ hnl
  · rintro k ⟨hk, -⟩ - _ ⟨l, hl, rfl⟩ -
    obtain ⟨l', hl', e⟩ := hk l hl
    have hm : l + (2 * n * n) • l' ∈ L := add_mem hl (AddSubgroup.nsmul_mem _ hl' _)
    have e2 : actO S T 1 k (n • l) = n • (l + (2 * n * n) • l') := by rw [actO_nsmul, e]
    refine ⟨⟨_, hm, e2.symm⟩, ?_⟩
    show (actO S T 1 k (n • l)).map (infPart D) = 0
    rw [e2]
    exact latO_fin (AddSubgroup.nsmul_mem _ hm n)
  · rintro k ⟨hk, -⟩ hkf w hw
    have hw' : ∀ l ∈ L, ψ (symplO S T (n • w) l) = 1 := fun l hl => by
      rw [symplO_nsmul]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))
    have hff : (n • w - realIdem D • (n • w)).map (infPart D) = 0 := fin_part _
    have hfL : n • w - realIdem D • (n • w) ∈ L := GlobalTheory.LatVac.mem_of_char hψ hS hT hff fun u hu => by
      rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_real_fin S T (real_part _) (latO_fin hu), sub_zero]
      exact hw' u hu
    obtain ⟨l, hl, e⟩ := hk _ hfL
    have hreal := actO_real (one_mem (GfC S)) hkf (real_part (n • w))
    have e1 : actO S T 1 k w = w + 2 • (n • l) := by
      refine nsmul_cancel hn ?_
      rw [← actO_nsmul, show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel,
        GlobalTheory.LatNhds.actO_add, hreal, e, ← add_assoc, ← show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel]
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      ring
    have hd : actO S T 1 k w - w = 2 • (n • l) := by rw [e1, add_sub_cancel_left]
    refine ⟨⟨2 • l, AddSubgroup.nsmul_mem _ hl 2, ?_⟩, ?_, ?_⟩
    · rw [hd]
      exact smul_comm n 2 l
    · rw [hd]
      exact latO_fin (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl n) 2)
    · rw [hd, two_nsmul, symplOH_add_right, symplOH_add_self]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))

theorem exists_level_stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  intro D ψ S T hψ U hU
  exact exists_level_stab_of_selfDual ψ S T hψ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) U hU

end GlobalTheory.WeilLevelStab

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem conj_mem_flag1 {g0 : G0 L.Pg L.r} {κ k : GA D V} (hκ : IsLevelLift V β L g0 κ)
    (hk : k ∈ levG V β (flag1L L)) :
    κ⁻¹ * (k * κ) ∈ levG V β (flag1L L) ∧
      levChi V β (flag1L L) (κ⁻¹ * (k * κ)) = levChi V β (flag1L L) k := by
  obtain ⟨hκf, hκp, hκr⟩ := hκ
  rw [levG, mem_levA, Formalism.L2.DIV.mem_lev] at hk
  obtain ⟨hkf, hkp, hkr⟩ := hk

  have hxp : finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := hkp
  have hx1 : Formalism.L2.DIV.rTup β L (finE V k) = 1 := Subgroup.mem_bot.mp hkr
  have hfin : finE V (κ⁻¹ * (k * κ)) = (finE V κ)⁻¹ * (finE V k * finE V κ) := by
    rw [map_mul, map_mul, map_inv]
  have hcp : (finE V κ)⁻¹ * (finE V k * finE V κ) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp)
  refine ⟨?_, ?_⟩
  · rw [levG, mem_levA, Formalism.L2.DIV.mem_lev, hfin]
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hκf) (Subgroup.mul_mem _ hkf hκf), hcp, ?_⟩
    have hr : Formalism.L2.DIV.rTup β L ((finE V κ)⁻¹ * (finE V k * finE V κ)) = 1 := by
      rw [Formalism.L2.DIV.rTup_mul (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp),
        Formalism.L2.DIV.rTup_inv hκp, Formalism.L2.DIV.rTup_mul hxp hκp, hx1, one_mul, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr hr
  ·
    show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V (κ⁻¹ * (k * κ))) : ℂˣ) : ℂ) =
      ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ)
    rw [levFn_flag1, levFn_flag1, hfin]
    have hA : finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hκp, Subgroup.mem_top _⟩
    have hX : finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hxp, Subgroup.mem_top _⟩
    let A : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V κ, hA⟩
    let X : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V k, hX⟩
    have hc : Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) (A⁻¹ * (X * A)) =
        Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) X := by
      rw [map_mul, map_mul, map_inv]
      exact inv_mul_cancel_comm_assoc _ _
    have e1 := Formalism.L2.DIV.levChar_apply (A⁻¹ * (X * A))
    have e2 := Formalism.L2.DIV.levChar_apply X
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (e1.symm.trans (hc.trans e2))

theorem finiteGroupAction_preserves_principalFlagMultiplicity : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), IsInfFam θ → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ U : MMap M, (∀ v, U v = actG0 V β L g0 (T v)) → U ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  intro D V S θ M _ β L g0 T hT U hU
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  ·
    have hκ : IsLevelLift V β L g0 hk.choose := hk.choose_spec
    have hEq : U = (levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T := by
      ext v h
      rw [hU v, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      unfold actG0
      rw [dite_eq_left hk]
      congr 1
      show T v (h * hk.choose) = ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (h * γ)
      rw [Finset.sum_singleton]
    rw [hEq]
    refine GlobalTheory.MultMem.isMultMap_smul _ (GlobalTheory.SphericalOps.isMultMap_heckeOn hT ?_ ?_)
    · intro k hk'
      rw [Finset.mem_singleton.mp hk']
      exact hκ.1
    · intro v k hkJ g
      show ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * k * γ) =
        levChi V β (flag1L L) k * ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * γ)
      rw [Finset.sum_singleton, Finset.sum_singleton]
      obtain ⟨hmem, hchi⟩ := conj_mem_flag1 hκ hkJ
      have hl := hT.lev v _ hmem (g * hk.choose)
      rw [hchi] at hl
      rw [← hl]
      congr 1
      simp [mul_assoc]
  ·
    have hEq : U = 0 := by
      ext v h
      rw [hU v]
      unfold actG0
      rw [dite_eq_right hk]
      rfl
    rw [hEq]
    exact GlobalTheory.MultMem.isMultMap_zero

end GlobalTheory.FlagAction

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  first | exact @GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | exact GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | (intros; apply GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  first | exact @GlobalTheory.GoodProjEval.goodOp_star_ev | exact GlobalTheory.GoodProjEval.goodOp_star_ev | (intros; apply GlobalTheory.GoodProjEval.goodOp_star_ev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.RowEvalHH in
theorem GlobalTheory.RowEvalHH.conj_eval_mem_HH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c v₀ ht hLM hc hv S hS φ hφ
  classical
  obtain ⟨hDS, -, -, -, -, hloc⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  obtain ⟨hinj, hran⟩ := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
    X.B.e X.B.Re X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => (hDS v).2.2.2) (fun v => (X.low v).1) hloc X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens X.B.tens_spec

  let u : (∀ τ, ↥(Wsub R X c τ)) → X.B.Hs := fun y => tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))
  obtain ⟨f, K, hfe, hfn⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_multilinear_norm_sq R F X h hLev hGrp hMod t c ht S hS
  have hfi := GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner f K hfn
  have hgram : ∀ a b, ⟪evF R X h t c S a, evF R X h t c S b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ := by
    intro a b
    rw [← hfe a, ← hfe b, hfi a b, tensT_inner]
    rfl
  have hdense : Dense (Submodule.span ℂ (Set.range u) : Set X.B.Hs) :=
    GlobalTheory.T.dense_span_tensor_of_dense_subspaces' (tensT X) (Wsub R X c) (tensT_inner X) (tensT_dense X) (Wsub_dense R X c)
  obtain ⟨Aop, hA⟩ := GlobalTheory.T.exists_clm_of_gram_eq_smul' u (evF R X h t c S) K hgram hdense
  have hHom : Aop ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    intro g
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy1, hy2⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup R F X h hLev hGrp hMod hHost hιE t c ht hc S hS g y
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change Aop (X.B.σs g (u y)) = X.B.R (g, 1) (Aop (u y))
    rw [← hy1]
    change Aop (u y') = _
    rw [hA, hA, hy2]
  have hRe : X.B.Re.comp Aop = Aop := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hA]
    exact GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  have heHom : Aop ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re :=
    Submodule.mem_map.2 ⟨Aop, hHom, hRe⟩

  let y₀ : ∀ τ, ↥(Wsub R X c τ) := fun τ => ⟨c τ (v₀ τ), Submodule.mem_map_of_mem (v₀ τ).2⟩
  have hu0 : u y₀ = X.B.tens X.B.w := by
    have : (fun τ => ((y₀ τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ))) = fun τ => X.B.w (X.pl.symm τ) := by
      funext τ
      exact hv τ
    change tensT X _ = _
    rw [this, tensT_w]
  have hvec : vecOf R X c y₀ = v₀ := by
    funext τ
    apply Subtype.ext
    exact (c τ).symm_apply_apply (v₀ τ)
  obtain ⟨c', -, hnorm⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  have hunit : ∀ τ, ‖((v₀ τ : (MP R).H τ))‖ = 1 := by
    intro τ
    rw [← (c τ).norm_map, hv τ]
    exact (X.low _).1
  obtain ⟨hmem, -, -⟩ := hnorm v₀ hunit S hS
  have hval : Aop (X.B.tens X.B.w) = star φ := by
    rw [← hu0, hA]
    delta evF
    rw [hvec, dite_eq_left hmem]
    congr 1
    exact (Lp.ext (hφ.trans hmem.coeFn_toLp.symm)).symm
  have hmemHH : star φ ∈ Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund X.B.Re X.Rph := by
    rw [← hran]
    exact ⟨⟨Aop, heHom⟩, hval⟩
  exact hmemHH
end
