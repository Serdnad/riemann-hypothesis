module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle296
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

@[expose] public section

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix

theorem core (I : AutInst) (g : ℕ) {r : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (hz0 : z0 ∈ I.Lf)
    (hzz : ZMod' I g (hA I z0 z0 + 1)) (hze : ∀ a, ZMod' I g (hA I (e0 a) z0))
    (x : I.Gf) (hxK : x ∈ I.Kset) (hxz : InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0))
    (v v' : VA I) (hv : InAt I g g (v - z0)) (hv' : InAt I g g (v' - z0))
    (ε c c₂ : I.E ⊗[I.F] Af I.F) (hε : ε ∈ IntAf I.F I.E) (hc : c ∈ IntAf I.F I.E) (hc₂ : c₂ ∈ IntAf I.F I.E)
    (hyp : ε • (c • (I.fmat x *ᵥ v')) = ε • (c₂ • v)) :
    ∃ N : ℕ, N.Coprime g ∧ ZMod' I g (ε * (c - c₂) * (N : I.E ⊗[I.F] Af I.F)) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨n', hn', hnv'⟩ := hv'
  refine ⟨n * n', Nat.Coprime.mul_left hn hn', ?_⟩

  have hQ : Mo I g (Set.range e0) ≤ Qs I g z0 := by
    refine sup_le (Submodule.span_le.2 ?_) (mL_Qs I g hz0)
    rintro _ ⟨a, rfl⟩
    show ZMod' I g (hA I z0 (e0 a))
    rw [hA_symm]; exact Z_sig I g (hze a)
  have hmL : mL I g ≤ Qs I g z0 := mL_Qs I g hz0
  have hxmL : ∀ w ∈ mL I g, I.fmat x *ᵥ w ∈ mL I g := fun w hw =>
    pres I hxK g ∅ (mL I g) (by simp) (by simp) le_rfl w (mL_Mo I hw)
  have hNint : ∀ m : ℕ, ((m : I.E ⊗[I.F] Af I.F)) ∈ IntAf I.F I.E := fun m => natCast_mem _ m

  have hA1 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ v') + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : I.fmat x *ᵥ v' = z0 + (I.fmat x - 1) *ᵥ z0 + I.fmat x *ᵥ (v' - z0) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ (v' - z0)) =
        (n : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0))) := by
      rw [Matrix.mulVec_smul, hA_smul_right, Nat.cast_mul]; ring
    have h2 : ZMod' I g (hA I z0 ((I.fmat x - 1) *ᵥ z0)) := hQ hxz
    have h3 : ZMod' I g (hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0)))) := hmL (hxmL _ hnv')
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g (Z_add I g h1 (Z_smul I g (hNint (n * n')) h2)) (Z_smul I g (hNint n) h3)
    rw [e, hA_add_right, hA_add_right]
    convert this using 1
    rw [← e2]; ring
  have hA2 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 v + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : v = z0 + (v - z0) := by abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (v - z0) =
        (n' : I.E ⊗[I.F] Af I.F) * hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0)) := by
      rw [hA_smul_right, Nat.cast_mul]; ring
    have h3 : ZMod' I g (hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0))) := hmL hnv
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g h1 (Z_smul I g (hNint n') h3)
    rw [e, hA_add_right]
    convert this using 1
    rw [← e2]; ring

  have key : ε * (c * hA I z0 (I.fmat x *ᵥ v')) = ε * (c₂ * hA I z0 v) := by
    have := congrArg (fun w => hA I z0 w) hyp
    simp only [hA_smul_right] at this
    exact this
  have := Z_sub I g (Z_smul I g (mul_mem hε hc) hA1) (Z_smul I g (mul_mem hε hc₂) hA2)
  convert this using 1
  linear_combination (-((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) * key

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem res_eq {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) (g : ℕ) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (N : ℕ) (hN : N.Coprime g)
    (hZ : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (ε * (c - c₂) * (N : Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨t, ht, he⟩ := hZ
  have hs : (⟨ε, hε⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (⟨c, hc⟩ - ⟨c₂, hc₂⟩) * (N : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (g : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨t, ht⟩ := Subtype.ext (by
    push_cast
    exact he)
  have hr := congrArg (Formalism.L2.DIV.resS D.host.F PP) hs
  simp only [map_mul, map_sub, map_natCast, hε1, one_mul] at hr
  have hg0 : ((g : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    show ((g : 𝓞 D.host.E) : 𝓞 D.host.E ⧸ PP.asIdeal) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hg
  have hN0 : ((N : ℕ) : Formalism.L2.DIV.kP PP) ≠ 0 := by
    intro h0
    have hNm : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h0
    have hco : IsCoprime ((N : ℤ) : 𝓞 D.host.E) ((g : ℤ) : 𝓞 D.host.E) :=
      (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 D.host.E))
    obtain ⟨a, b, hab⟩ := hco
    push_cast at hab
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hNm) (Ideal.mul_mem_left _ _ hg)
  rw [hg0, zero_mul] at hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 hr).resolve_right hN0)

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem finE_inv_val {D : D7} (y : GA D (D.sp.Y 0)) :
    ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (((Formalism.IndefR.RationalEmbedding.iota D) y).2)⁻¹ :=
  (congrArg Units.val (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) (show GA D (Yc D 0) from y)).symm).trans
    ((GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) (y⁻¹ : GA D (D.sp.Y 0))).symm.trans
      (congrArg (fun p : (Formalism.IndefR.RationalEmbedding.inst D).GA => (Formalism.L2.SG.InstExistsPf.instOf D).fmat p.2) (map_inv (Formalism.IndefR.RationalEmbedding.iota D) y)))

theorem core_res {D : D7} {r : ℕ} (e0 : Fin r → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (g : ℕ) (hz0 : z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf)
    (hzz : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1)) (hze : ∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hxK : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hxz : InMod (Formalism.L2.SG.InstExistsPf.instOf D) g (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0))
    (v v' : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hv : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v - z0)) (hv' : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v' - z0))
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (w w' : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D)
    (hM : M = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x) (hw : w = v) (hw' : w' = v')
    (hyp : ε • (c • (M *ᵥ w')) = ε • (c₂ • w)) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  subst hM hw hw'
  obtain ⟨N, hN, hZ⟩ := core (Formalism.L2.SG.InstExistsPf.instOf D) g e0 z0 hz0 hzz hze x hxK hxz w w' hv hv' ε c c₂ hε hc hc₂ hyp
  exact res_eq PP g hg ε c c₂ hε hε1 hc hc₂ N hN hZ



theorem frame_facts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = (Formalism.L2.SG.InstExistsPf.instOf D)) (hId : _root_.GlobalTheory.Core.Mi.IdE X) :
    ∃ (e0 : Fin D.R.rS → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)), z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ∧ ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1) ∧
      (∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0)) ∧
      (∀ κ ∈ rowJ X h, ∃ x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf, ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = x ∧ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
        InMod (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0)) ∧
      ∀ u : D.what₂.Word, ∃ (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)),
        ((Formalism.IndefR.RationalEmbedding.iota D) ((iotaX X h).symm (1, X.xu u))).2 = x ∧
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r)))) = z ∧
        InAt (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (D.host.g 0 * D.host.g 1) ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z - z0) := by
  have hi : ∀ u, (iotaX X h) ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) := fun u => (iotaX X h).apply_symm_apply _
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan, e_eq, xu, xu_fix, xu_z, xu_one, xu_K⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hs : ∀ y : D.host.E, ιE.symm y = y := fun y => by
    have := eq_of_heq (hId (ιE.symm y))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e0, z0, vectorsInLattice.2.1, formsAtZero.1, fun a => (formsAtZero.2 a).1, fun κ hκ => ?_, fun u => ?_⟩
  · have hk : ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 ∈ K2set (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw := hκ.2
    exact ⟨_, rfl, hk.1, hk.2.2.1⟩
  · refine ⟨xu u, incl (Formalism.L2.SG.InstExistsPf.instOf D) (crdOf (Formalism.L2.SG.InstExistsPf.instOf D) ιE bas (zu u)), congrArg Prod.snd (hi u), ?_, xu_z u⟩
    funext r
    show algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE (ιE.symm (bas.repr (zu u) r))) =
      algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE.symm (bas.repr (zu u) r))
    rw [RingEquiv.apply_symm_apply, hs]

theorem inv_mulVec_eq {D : D7} (y : GA D (D.sp.Y 0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hx : ((Formalism.IndefR.RationalEmbedding.iota D) y).2 = x)
    (w : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hz : w = z) :
    Matrix.mulVec ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val w =
      ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) := by
  subst hx hz
  exact congrArg (fun M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D) => Matrix.mulVec M w) (finE_inv_val y)



theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : _root_.GlobalTheory.Core.Mi.IdE X)
    (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ rowJ X h)
    (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hE : ε • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u' (Fin.cast (rank_eq X h) r)))))) = ε • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r))))))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨e0, z0, hz0, hzz, hze, hK, hu⟩ := frame_facts X h hId
  obtain ⟨x, hx, hxK, hxz⟩ := hK κ hκ
  obtain ⟨y, z, hy, hz, hv⟩ := hu u
  obtain ⟨y', z', hy', hz', hv'⟩ := hu u'
  have e1 : (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x :=
    (GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) κ).symm.trans (congrArg (Formalism.L2.SG.InstExistsPf.instOf D).fmat hx)
  have e2 := inv_mulVec_eq _ y hy _ z hz
  have e3 := inv_mulVec_eq _ y' hy' _ z' hz'
  exact core_res e0 z0 _ hz0 hzz hze x hxK hxz _ _ hv hv' PP hg ε c c₂ hε hε1 hc hc₂ _ _ _ e1 e2 e3 hE

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

end GlobalTheory.CongFlag
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SmallVac

theorem smallVec_vac_sph : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f := by
  classical
  intro D ψ θ A H χA om sA sH hθ hη hω hsA hsH hr β Z hZ βH f₀ f hβH h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC A)
    (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC H) hr h
  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨hvac, e, he, hth⟩ := h
  have hle : latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z) ≤
      latO A H (frameLat A) (frameLat H) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hlat := hvac.2.lat
  have hZu : ∀ PP ∈ (prinDat A Z).Pg ∪ ∅, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ under Z := by
    intro PP hPP
    rw [Finset.union_empty] at hPP
    unfold under
    exact Finset.mem_image_of_mem _ hPP
  have fix : ∀ u ∈ latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z), heisO ψ A H u f₀ = f₀ →
      heisO ψ A H u f = f := fun u hu h0 =>
    GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ A H e _ 1 f₀ _ f hth u
      (GlobalTheory.FockSph.idemSum_mul_of he (fun PP hPP hn => hn (hZu PP hPP)) hu) h0
  exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
    fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩

end GlobalTheory.Core.Rk.SmallVac

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActRight

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid GlobalTheory.BiTransfer

variable {D : D7}

theorem conjSource_conjAdjoint_apply {S A' : HSp D} (omb : Om S A') (g : GA D S) (h : GA D A') (f : WO S A' → ℂ)
    (y : WO A' S) :
    conjSource (conjAdjoint omb) (negGA A' h, g) (fun y' => f (dagger A' S y')) y = omb (g, h) f (dagger A' S y) := by
  have e1 : conjSource (conjAdjoint omb) (negGA A' h, g) =
      cjEnd (Equiv.refl (WO A' S)) (cjEnd (daggerEquiv S A') (omb (g, h))) := by
    simp only [conjSource, conjAdjoint, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.id_apply, Prod.map]
    rfl
  have e2 : (fun y' => f (dagger A' S y')) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (Equiv.refl (WO A' S)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (daggerEquiv S A') f) := by
    funext y'; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]
  rw [e1, e2, cjEnd_cj, cjEnd_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]

theorem resS_symm_swap {W A B : HSp D} (d : OrthDec W A B) (T : HSp D) (u : WO A T) (y : WO B T) :
    (d.symm.resS T).symm (y, u) = (d.resS T).symm (u, y) :=
  add_comm (y ⬝ d.pB) (u ⬝ d.pA)

theorem isBiTheta_act_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χS' χA' : (AE D)ˣ →* Circle) (omb : Om S A'), IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → ∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v := by
  intro D ψ A S A' χS' χA' omb hω C hC q
  obtain ⟨g, h⟩ := q
  have hw1 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std S A').conj_adjoint χS' χA' omb hω).1
  have hw2 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std A' S).conj_source χA' χS' (conjAdjoint omb) hw1).1
  let d := sumDec A (negSp A')
  have hG := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ (negSp A') A S d.symm _ _ (conjSource (conjAdjoint omb)) hw2 _ (isThetaFunO_join d hC)
    Unit 0 (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) (negGA A' h, g)).1
  refine isBiTheta_of_join d ?_
  convert hG using 1
  funext x
  have hs : d.symm.resS S x = ((d.resS S x).2, (d.resS S x).1) := by
    apply (d.symm.resS S).symm.injective
    calc
      _ = x := (d.symm.resS S).symm_apply_apply x
      _ = (d.resS S).symm (d.resS S x) := ((d.resS S).symm_apply_apply x).symm
      _ = _ := (resS_symm_swap d S _ _).symm
  simpa [join, hs, resS_symm_swap] using
    (conjSource_conjAdjoint_apply omb g h (C (d.resS S x).1) (d.resS S x).2).symm

end GlobalTheory.BiActRight

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvzVal

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_eq_lamT_hcW {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem evz_mem_valC : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (ψ : ColT I l u a B.R.m), ψ ∈ (I.fm l u a).Fi B.R.m → ∀ c, (fun y : FrN (I.rec7 l Z) (B.R.N B.R.m) => (I.per l u a).evz ψ c ⟨y.1, y.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m) := by
  intro B X I hI hP l Z u a ψ hψ c
  have h1 := (hψ ((I.perIn u a).tilC c)).1
  have h2 := GlobalTheory.Mem.Col2.Law.tr_mem (I.stp u a B.R.m) B.fields.emb B.embLL _ (I.perIn u a).b0
    ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) h1
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 h2
  rw [lamT_eq_lamT_hcW I l Z u B.R.m]
  exact ⟨P, hP, funext fun y => congrFun e ⟨y.1, y.2⟩⟩

end GlobalTheory.EvzVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

theorem isBiTheta_act_left : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS : (AE D)ˣ →* Circle) (oma : Om A S), IsWeilDatumO ψ A S χA χS oma → ∀ C, IsBiTheta ψ A S A' C → ∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  intro D ψ A S A' χA χS oma H C hC p
  let d := sumDec A (GlobalTheory.ChiGrid.negSp A')
  have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A _ S d χA χS oma H _ (isThetaFunO_join d hC) Unit 0 (fun _ => 0) (fun _ => 0)
    measurable_const (integrable_zero _ _ _) p).1
  simp only [join_symm] at h
  exact isBiTheta_of_join d h

end GlobalTheory.BiTransfer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwDat.Is

theorem stp_top_idx_eq {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)
    (b b' : (I.stp u a B.R.m).β) : b = b' := by
  show (b : Idx I.sel (I.tup a) (I.idx a) B.R.m) = b'
  obtain ⟨x, hx⟩ := b
  obtain ⟨y, hy⟩ := b'
  have h1 : x = none := by simpa using hx
  have h2 : y = none := by simpa using hy
  subst h1; subst h2; rfl

theorem chOf_top_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (c₀ : (I.stp u a B.R.m).Cl) (β : Ch₀ B.R.m), A.chOf B.R.m c₀ = β := by
  intro B X I _ _ l Z u a Ch₀ A hA c₀ β
  obtain ⟨c, rfl⟩ := hA.chOf_onto B.R.m le_rfl β
  exact ((hA.reads B.R.m le_rfl).key c₀ c).2
    ⟨stp_top_idx_eq I u a _ _, GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _⟩

end GlobalTheory.AdForm.TwDat.Is
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  first | exact @GlobalTheory.StdUnn.CartanMove.cartan_move_std | exact GlobalTheory.StdUnn.CartanMove.cartan_move_std | (intros; apply GlobalTheory.StdUnn.CartanMove.cartan_move_std <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_standardCartanInvolution_commute_compact : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | exact GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | (intros; apply GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K <;> assumption)
end
