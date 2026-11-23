module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle096
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle282
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Duality
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjIdem

theorem natCast_cpt_lt {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (g : EAf D)) < 1 := by
  have h0 : resS D.host.F PP ((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) = 0 := by
    refine (map_natCast (resS D.host.F PP) g).trans ?_
    refine (map_natCast (Ideal.Quotient.mk PP.asIdeal) g).symm.trans ?_
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hg
  have h1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).1 h0
  have e : (((g : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) : EAf D) = (g : EAf D) := map_natCast (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D).subtype g
  rwa [e] at h1

theorem mulVec_add_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (i : Fin n) :
    (M *ᵥ (x + y)) i = (M *ᵥ x) i + (M *ᵥ y) i := by
  rw [Matrix.mulVec_add, Pi.add_apply]

theorem mulVec_smul_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (c : R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ (c • y)) i = c * (M *ᵥ y) i := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

theorem mulVec_zero_apply {n : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (M *ᵥ (0 : Fin n → R)) i = 0 := by
  rw [Matrix.mulVec_zero, Pi.zero_apply]

theorem coord_mL {D : D7} (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : GlobalTheory.PlaceModel.latFrame (Yc D 0) = GlobalTheory.NormSum.AdLattice.lat β) (w : VA (II D)) (hw : w ∈ mL (II D) g) :
    ∀ i, ∃ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, ((β⁻¹).val *ᵥ (w : Fin (Yc D 0).rank → EAf D)) i = (g : EAf D) * a := by
  have hL : ∀ x : VA (II D), x ∈ (II D).Lf → ∀ i, ((β⁻¹).val *ᵥ (x : Fin (Yc D 0).rank → EAf D)) i ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D := by
    intro x hx
    have h1 : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := (GlobalTheory.ConjPlaceRed.mem_Lf D x).2 hx
    rw [hβ] at h1
    exact (GlobalTheory.AdIsom.mem_hat_lat β x).1 h1
  unfold mL at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    refine ⟨((β⁻¹).val *ᵥ (y : Fin (Yc D 0).rank → EAf D)) i, hL y hy i, ?_⟩
    have e1 : (((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) = (g : EAf D) :=
      map_natCast (IntAf (II D).F (II D).E).subtype g
    have e2 := mulVec_smul_apply (β⁻¹).val (show EAf D from ((g : IntAf (II D).F (II D).E) : (II D).E ⊗[(II D).F] Af (II D).F)) (y : Fin (Yc D 0).rank → EAf D) i
    rw [e1] at e2
    exact e2
  | zero => intro i; exact ⟨0, zero_mem _, (mulVec_zero_apply (β⁻¹).val i).trans (mul_zero _).symm⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    obtain ⟨b, hb, eb⟩ := hy i
    refine ⟨a + b, add_mem ha hb, ?_⟩
    refine (mulVec_add_apply (β⁻¹).val (x : Fin (Yc D 0).rank → EAf D) y i).trans ?_
    rw [ea, eb, mul_add]
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha, ea⟩ := hx i
    refine ⟨(show EAf D from c.1) * a, mul_mem c.2 ha, ?_⟩
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c.1) (x : Fin (Yc D 0).rank → EAf D) i).trans ?_
    rw [ea]
    ring

end GlobalTheory.SeeConjIdem

namespace GlobalTheory.SeeConjIdem

theorem rank_pos (D : D7) : 0 < (Yc D 0).rank := by
  have h := Formalism.L2.SG.InstExistsPf.rank_eq D
  have h2 : (Yc D 0).rank = D.R.r := h
  obtain ⟨j, hj⟩ := D.R.m_even
  have := D.R.two_le_m
  rw [h2]
  simp only [Formalism.BasicNotions.Ranks.r]
  omega

theorem cpt_lt_of_smul_mem {D : D7} (g : ℕ) (PP : Pl D.host.E) (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal)
    (c : (II D).E ⊗[(II D).F] Af (II D).F) (hy : ∀ y ∈ (II D).Lf, c • y ∈ mL (II D) g) :
    Valued.v (GlobalTheory.StdFrames.cpt PP (show EAf D from c)) < 1 := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdIsom.exists_eq_lat (GlobalTheory.AdIsom.selfDual_isFullLattice
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)))
  let i0 : Fin (Yc D 0).rank := ⟨0, rank_pos D⟩
  let y : Fin (Yc D 0).rank → EAf D := β.val *ᵥ Pi.single i0 1
  have hby : (β⁻¹).val *ᵥ y = Pi.single i0 1 := by
    simp only [y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let yv : VA (II D) := y
  have hyL : yv ∈ (II D).Lf := by
    refine (GlobalTheory.ConjPlaceRed.mem_Lf D y).1 ?_
    rw [hβ]
    refine (GlobalTheory.AdIsom.mem_hat_lat β y).2 fun i => ?_
    rw [hby, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨a, ha, ea⟩ := coord_mL g β hβ _ (hy yv hyL) i0
  have e3 : ((β⁻¹).val *ᵥ ((c • yv : VA (II D)) : Fin (Yc D 0).rank → EAf D)) i0 = (show EAf D from c) := by
    refine (mulVec_smul_apply (β⁻¹).val (show EAf D from c) y i0).trans ?_
    rw [hby, Pi.single_eq_same, mul_one]
  have ea' : (show EAf D from c) = (g : EAf D) * a := e3.symm.trans ea
  rw [ea', map_mul, Valuation.map_mul, mul_comm]
  exact mul_lt_one_of_nonneg_of_lt_one_right ((GlobalTheory.AdIsom.mem_OA a).1 ha PP) zero_le (natCast_cpt_lt g PP hg)

theorem resS_of_idem {D : D7} (PP : Pl D.host.E) (e s : EAf D) (he : e * e = e) (hs : s * s = s) (hes : e * s = 0)
    (hei : e ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) (hsi : s ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D)
    (key : Valued.v (GlobalTheory.StdFrames.cpt PP (1 - e - s)) < 1) :
    (GlobalTheory.StdFrames.cpt PP e = 1 → resS D.host.F PP ⟨e, hei⟩ = 1 ∧ resS D.host.F PP ⟨s, hsi⟩ = 0) ∧
      (GlobalTheory.StdFrames.cpt PP e ≠ 1 → resS D.host.F PP ⟨e, hei⟩ = 0 ∧ resS D.host.F PP ⟨s, hsi⟩ = 1) := by
  have he' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP e = GlobalTheory.StdFrames.cpt PP e := by
    rw [← map_mul, he]
  have hs' : GlobalTheory.StdFrames.cpt PP s * GlobalTheory.StdFrames.cpt PP s = GlobalTheory.StdFrames.cpt PP s := by
    rw [← map_mul, hs]
  have hes' : GlobalTheory.StdFrames.cpt PP e * GlobalTheory.StdFrames.cpt PP s = 0 := by
    rw [← map_mul, hes, map_zero]
  have i01 : ∀ x : PP.adicCompletion D.host.E, x * x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have : x * (x - 1) = 0 := by rw [mul_sub, hx, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have r0 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 0 → resS D.host.F PP t = 0 :=
    fun t h => (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP t).2 (by rw [h, map_zero]; exact zero_lt_one)
  have r1 : ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D, GlobalTheory.StdFrames.cpt PP (t : EAf D) = 1 → resS D.host.F PP t = 1 := by
    intro t h
    have := r0 (1 - t) (by
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, h, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  constructor
  · intro h1
    have hf0 : GlobalTheory.StdFrames.cpt PP s = 0 := by
      rw [h1, one_mul] at hes'; exact hes'
    exact ⟨r1 ⟨e, hei⟩ h1, r0 ⟨s, hsi⟩ hf0⟩
  · intro hne
    have he0 : GlobalTheory.StdFrames.cpt PP e = 0 := (i01 _ he').resolve_right hne
    have hf1 : GlobalTheory.StdFrames.cpt PP s = 1 := by
      rcases i01 _ hs' with h | h
      · exfalso
        have h1 : GlobalTheory.StdFrames.cpt PP (1 - e - s) = 1 := by
          rw [map_sub (GlobalTheory.StdFrames.cpt PP), map_sub (GlobalTheory.StdFrames.cpt PP), map_one, he0, h, sub_zero, sub_zero]
        rw [h1, Valuation.map_one] at key
        exact lt_irrefl _ key
      · exact h
    exact ⟨r0 ⟨e, hei⟩ he0, r1 ⟨s, hsi⟩ hf1⟩

theorem resS_idem_conj : ∀ {D : D7} (g : ℕ) (ew : (II D).E ⊗[(II D).F] Af (II D).F), ew * ew = ew → ew * sigA (II D) ew = 0 → ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → (∀ y ∈ (II D).Lf, (1 - ew - sigA (II D) ew) • y ∈ mL (II D) g) → ∀ PP : Pl D.host.E, ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h2 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (GlobalTheory.StdFrames.cpt PP ew = 1 → resS D.host.F PP ⟨ew, h1⟩ = 1 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 0) ∧ (GlobalTheory.StdFrames.cpt PP ew ≠ 1 → resS D.host.F PP ⟨ew, h1⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 1) := by
  intro D g ew hid hperp hint hy PP hg
  have hs : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hint
  have hss : sigA (II D) ew * sigA (II D) ew = sigA (II D) ew := by rw [← map_mul, hid]
  exact ⟨hint, hs, resS_of_idem PP ew (sigA (II D) ew) hid hss hperp hint hs (cpt_lt_of_smul_mem g PP hg _ hy)⟩

end GlobalTheory.SeeConjIdem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeConjRead
open Classical

theorem cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ} (f : Fin m → Formalism.L2.SG.HidaSetting.VA I)
    (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
  subst h
  exact hf a

theorem cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
  subst h
  exact hv

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M)
    (z : M) (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
    flagV ρ k n e f b z i ∈ S := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, h0]

theorem colMat_entry {D : D7} {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (M * colMat w) i j = Matrix.mulVec M (w j) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]

theorem flag_pair_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β₀ hL PP i j
  have hF : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hL ▸ GlobalTheory.StdFrames.isFrame_lat β₀
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
      Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro v hv
    rw [hLf] at hv
    exact (hF v).1 hv i
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
  refine ⟨?_, ?_⟩
  · rw [colMat_entry]
    apply key
    unfold flagAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
  · rw [colMat_entry]
    apply key
    unfold pairAt
    split_ifs
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
    · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j

end GlobalTheory.SeeConjRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjProd
open Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.L2.SG.HidaSetting
open scoped TensorProduct
variable {D : D7}

theorem sigInt_oToS (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem conjRes_mk (PP : Pl D.host.E) (x : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (Ideal.Quotient.mk PP.asIdeal x) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cO D x) := rfl

theorem conj_res_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) (oToS D.host.F D.host.E a))) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a := by
  rw [sigInt_oToS, resS_oToS, conjRes_mk, GlobalTheory.IdemSupport.cO_cO]

theorem resS_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F (GlobalTheory.IdemSupport.cP PP) s =
      GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) s)) := by
  set f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
    (GlobalTheory.SeeConjChar.conjRes PP).toRingHom.comp ((resS D.host.F PP).comp (sigInt (instOf D))) with hf
  have hf0 : ∀ x, f1 x = GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) x)) := fun x => rfl
  have hf1 : ∀ a, f1 (oToS D.host.F D.host.E a) = Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a :=
    fun a => (hf0 _).trans (conj_res_oToS PP a)
  have hker : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker f1 := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hf1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  obtain ⟨a, ha⟩ := (cmpS_bij (F := D.host.F) (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cP PP).ne_bot).2
    (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have e : Ideal.Quotient.mk (idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal) s =
      Ideal.Quotient.mk _ (oToS D.host.F D.host.E a) := ha.symm
  have hd : s - oToS D.host.F D.host.E a ∈ idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal := Ideal.Quotient.eq.1 e
  have hker2 : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker (resS D.host.F (GlobalTheory.IdemSupport.cP PP)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  have h2 : resS D.host.F (GlobalTheory.IdemSupport.cP PP) s = resS D.host.F (GlobalTheory.IdemSupport.cP PP) (oToS D.host.F D.host.E a) := by
    have := hker2 hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  have h1 : f1 s = f1 (oToS D.host.F D.host.E a) := by
    have := hker hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact h2.trans ((resS_oToS _ a).trans ((hf1 a).symm.trans (h1.symm.trans (hf0 s))))

theorem exists_addChar_ne_one (k : Type) [Field k] [Finite k] : ∃ ψ : AddChar k ℂ, ψ ≠ 1 := by
  have h1 : Multiplicative.ofAdd (1 : k) ≠ 1 := by
    intro h
    exact one_ne_zero (congrArg Multiplicative.toAdd h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative k) ℂ h1
  let ψ : AddChar k ℂ :=
    { toFun := fun x => ((φ (Multiplicative.ofAdd x) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [ofAdd_add] }
  refine ⟨ψ, fun h => hφ (Units.ext ?_)⟩
  have := congrArg (fun χ : AddChar k ℂ => χ 1) h
  simpa [ψ] using this

theorem addChar_comp_ne_one {k k' : Type} [Field k] [Field k'] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0)
    (e : k' ≃+* k) : ψ.compAddMonoidHom ((AddMonoidHom.mulLeft a).comp e.toAddMonoidHom) ≠ 1 := by
  intro h
  apply hψ
  ext t
  have := congrArg (fun χ : AddChar k' ℂ => χ (e.symm (a⁻¹ * t))) h
  change ψ (a * e (e.symm (a⁻¹ * t))) = (1 : AddChar k' ℂ) (e.symm (a⁻¹ * t)) at this
  rw [RingEquiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.one_apply] at this
  rw [this, AddChar.one_apply]

theorem cP_cP (P : Pl D.host.E) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem sigInt_sigInt (s : Formalism.L2.Herm.intAf D.host.F D.host.E) : sigInt (instOf D) (sigInt (instOf D) s) = s :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA (instOf D) s.1)

theorem conjRes_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) =
      resS D.host.F (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (sigInt (instOf D) s) := by
  rw [resS_cP (GlobalTheory.IdemSupport.cP PP) (sigInt (instOf D) s), sigInt_sigInt]


open Classical in
theorem core (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hdiv : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hcov : ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') :
    ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
      ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
        psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) =
          ∏ PP ∈ Pg, ψ PP (resS D.host.F PP s) *
            ψ (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | rfl⟩ := hcov Q hQ
    · exact (hs _ hPP).1
    · exact (resS_cP PP s).trans (by rw [(hs _ hPP).2]; exact map_zero _)
  choose ψ0 hψ0 using fun P : Pl D.host.E => exists_addChar_ne_one (kP P)
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ψ0 (fun PP _ => hψ0 PP)
    (fun s t => (congrArg psiEf (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans
      (hadd _ _))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) = 1
      rw [this, hint t ht])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hdiv hnc (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1)
      fun Q hQ => GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ)
  have hout : ∀ PP ∈ Pg, GlobalTheory.IdemSupport.cP PP ∉ Pg := fun PP hPP h =>
    hnc PP hPP _ h ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
  let ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ := fun P =>
    if P ∈ Pg then (ψ0 P).compAddMonoidHom ((AddMonoidHom.mulLeft (a₁ P)).comp (RingEquiv.refl (kP P)).toAddMonoidHom)
    else if GlobalTheory.IdemSupport.cP P ∈ Pg then (ψ0 (GlobalTheory.IdemSupport.cP P)).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP P))).comp (GlobalTheory.SeeConjChar.conjRes P).toAddMonoidHom)
    else 1
  have hψ1 : ∀ PP ∈ Pg, ψ PP = (ψ0 PP).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₁ PP)).comp (RingEquiv.refl (kP PP)).toAddMonoidHom) := fun PP hPP => if_pos hPP
  have hψ2 : ∀ PP ∈ Pg, ψ (GlobalTheory.IdemSupport.cP PP) = (ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP))).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)))).comp
        (GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP)).toAddMonoidHom) := fun PP hPP => by
    have h2 : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP) ∈ Pg := by rw [cP_cP]; exact hPP
    exact (if_neg (hout PP hPP)).trans (if_pos h2)
  refine ⟨ψ, fun PP hPP => ⟨?_, ?_⟩, fun s => ?_⟩
  · rw [hψ1 PP hPP]
    exact addChar_comp_ne_one _ (hψ0 PP) _ (ha PP hPP).1 _
  · rw [hψ2 PP hPP]
    refine addChar_comp_ne_one _ (hψ0 _) _ ?_ _
    rw [cP_cP]
    exact (ha PP hPP).2
  · refine (hχ s).trans (Finset.prod_congr rfl fun PP hPP => ?_)
    refine (AddChar.map_add_eq_mul (ψ0 PP) _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [hψ1 PP hPP]
      rfl
    rw [hψ2 PP hPP]
    show _ = ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) *
      GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s))
    rw [conjRes_cP]
    have key : ∀ Q : Pl D.host.E, Q = PP → ψ0 Q (a₂ Q * resS D.host.F Q (sigInt (instOf D) s)) =
        ψ0 PP (a₂ PP * resS D.host.F PP (sigInt (instOf D) s)) := by
      rintro Q rfl
      rfl
    exact (key _ (cP_cP PP)).symm

theorem chiS_eq_prod : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  intro D X h Pg hdiv hcov hnc
  have key : ∀ (I : AutInst) (hI : I = instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
      (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
        ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
          psiEf (divN I g (cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) hI).symm c)) =
            ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) *
              ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
    intro I hI g hg psiEf hadd hint hrat
    subst hI hg
    obtain ⟨ψ, hψ, hprod⟩ := core psiEf hadd hint hrat Pg hdiv hcov hnc
    refine ⟨ψ, hψ, fun c hc => ?_⟩
    have e1 : ∀ P : Pl D.host.E, GlobalTheory.SeeConjChar.resT P c = resS D.host.F P ⟨c, hc⟩ := fun P => dif_pos hc
    simp only [e1, cast_eq]
    exact hprod ⟨c, hc⟩
  exact key X.B.I h X.B.g X.g_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat

end GlobalTheory.SeeConjProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f : Fin X.rank → EAf D), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ f → IsBasePair X u π L₀ fun w => idem w • f := by
  first | exact @GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | exact GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | (intros; apply GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec <;> assumption)
end
