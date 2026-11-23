module

import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.FilCrisTriv
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  apply Formalism.MainNotions.N.Ln03.Pf.norm_chiQ <;> assumption

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

variable [IsDomain O]

theorem horTr_exists (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol)
    (M : ℕ) : ∃ κ : ℕ, ∃ Hh : Fin d → W.DD T, ∀ k, IsHorTr W T b sol M κ k (Hh k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hHc := hH hCA T hTc c'
  have hBd := (hHc.2.2.2.2 d b hb.1 sol hb.2).1
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hBd k r m)
  refine ⟨Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r •
    Formalism.MainNotions.LiftingTheory.vecB W T b (fun m => ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M -
      Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m), fun k => ⟨_, fun r hr m => ?_, rfl⟩⟩
  have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
  simp only [map_mul, map_pow, map_natCast, hg]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem horTr_mem (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (hπ : W.π₀ ∈ W.AΔ)
    (R κ e : ℕ) (k : Fin d) {H : W.DD T} (h : IsHorTr W T b sol R κ k H) :
    ((W.φD T) ^ e) H ∈ Pp W T c' e := by
  obtain ⟨y, -, rfl⟩ := h

  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun r _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul]
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (W.AΔ.pow_mem hπ r) e) ?_
  unfold Formalism.MainNotions.LiftingTheory.vecB
  refine ⟨?_, ?_⟩
  · refine ⟨(W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), fun δ hδ => ?_⟩

    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (hb.1 m).1.2 δ hδ]
  · refine ⟨∑ m, y r m • b m, (W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm, Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2]

theorem yM_gen (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hπ : W.π₀ ∈ W.AΔ) (h5p : 5 ≤ PD.p)
    (A : ArcP n) (hA : A.OK) (a : ZMod n) (e : ℕ) :
    ∃ ν ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ A.M PD.p = W.π₀ * abelian₂ W A a e ^ 2 * ν := by
  obtain ⟨u, hu, u', -, -, hT⟩ := (hTr hCA).2.1 e (A.M PD.p)
  have hlt := Formalism.MainNotions.UnusedSlot80.ArcC.two_h_lt A h5p
  have hM : 1 ≤ A.M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  have hle : ∀ s, 2 * A.Hs a e s ≤ (PD.p - 1) * A.M PD.p := fun s => by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_le_h A hA a e s; omega
  refine ⟨u * W.π₀ ^ (A.M PD.p - 1) * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s),
    W.AΔ.mul_mem (W.AΔ.mul_mem hu (W.AΔ.pow_mem hπ _)) (W.AΔ.prod_mem fun s _ =>
      W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _), ?_⟩
  rw [hT]
  have e1 : W.π₀ ^ A.M PD.p = W.π₀ * W.π₀ ^ (A.M PD.p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  have e2 : ∏ k ∈ Finset.range e, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * A.M PD.p) =
      abelian₂ W A a e ^ 2 * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s) := by
    unfold abelian₂
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.ArcC.pk_eq_ps, ← pow_mul, ← pow_add]
    congr 1
    have := hle s
    omega
  rw [e1, e2]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

section Mod

variable (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
  (Rst : Finset (Fin d))

theorem inFr1_add {f g : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) (hg : InFr W c 1 (abelian₂ W A c e) g) :
    InFr W c 1 (abelian₂ W A c e) (f + g) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_add W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hg))

theorem inFr1_smul (o : O) {f : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) :
    InFr W c 1 (abelian₂ W A c e) (o • f) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_smul W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) o)

theorem inFr1_zero : InFr W c 1 (abelian₂ W A c e) 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

def Msub : Submodule O (Fin d → W.EE) where
  carrier := {f | (∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) ∧ ∀ k ∉ Rst, f k = 0}
  add_mem' := fun {f g} hf hg => ⟨fun k => inFr1_add W A c e (hf.1 k) (hg.1 k),
    fun k hk => by simp [hf.2 k hk, hg.2 k hk]⟩
  zero_mem' := ⟨fun _ => inFr1_zero W A c e, fun _ _ => rfl⟩
  smul_mem' := fun o f hf => ⟨fun k => inFr1_smul W A c e o (hf.1 k), fun k hk => by simp [hf.2 k hk]⟩

def Isub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧ InvNL W T c e (abelian₂ W A c e) b f}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    refine ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [mul_add, ← hfg k, ← hfg' k]; ring
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    refine ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hfg k, mul_smul_comm]

theorem inFr1_of_pi0Lam {f : W.EE} (hf : InFr W c (W.π₀ * abelian₂ W A c e) 1 f) :
    InFr W c 1 (abelian₂ W A c e) f := by
  obtain ⟨w, hw, hfw⟩ := hf
  have hΛm : abelian₂ W A c e ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
    (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
  refine ⟨abelian₂ W A c e * (W.π₀ * abelian₂ W A c e) * w,
    W.AΔ.mul_mem (W.AΔ.mul_mem hΛm (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hΛm)) hw, ?_⟩
  rw [map_one, one_mul] at hfw
  rw [hfw, ← map_mul]; congr 1; ring

end Mod

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ k, c₀ k • dv W T e b (Pi.single k 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]
  unfold dv
  rfl

theorem dvO_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c : Fin d → O) :
    dvO W T e b c = ∑ k, algebraMap O LL (c k) • dv W T e b (Pi.single k 1) := by
  unfold dvO; rw [dv_sum]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (o : O) (c : Fin d → O) :
    dvO W T e b (fun k => o * c k) = algebraMap O LL o • dvO W T e b c := by
  rw [dvO_sum, dvO_sum, Finset.smul_sum]
  simp only [map_mul, mul_smul]

theorem coef_eq {M : Type} [AddCommGroup M] [Module LL M] {dY : ℕ} (u : Fin dY → M)
    (hu : LinearIndependent LL u) (x y : Fin dY → LL) (h : ∑ j, x j • u j = ∑ j, y j • u j) : x = y := by
  funext j
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu (fun j => x j - y j)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j)

include W in
theorem int_vec (hV : ValRing (LL := LL) O v) {ι₀ : Type} [Fintype ι₀] (ρ : ι₀ → LL) :
    ∃ (m : ℕ) (r : ι₀ → O), ∀ i, algebraMap O LL (r i) = (PD.p : LL) ^ m * ρ i := by
  choose mm oo hoo using fun i => Formalism.MainNotions.UnusedSlot80.ArcF.exists_pow_mul W hV (ρ i)
  refine ⟨∑ i, mm i, fun i => ((PD.p : ℕ) : O) ^ (∑ j, mm j - mm i) * oo i, fun i => ?_⟩
  have hle : mm i ≤ ∑ j, mm j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [map_mul, hoo, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem letter_pull [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (τ₀ : K₀ →ₐ[Qp] LL)
    {ξ : T₂.V ⊗[Qp] B} (hξ : ξ ∈ Dcris PD T₂.ρ) (h : crisMap B ι.f ξ ∈ DcrisL PD Y.ρ τ₀) :
    ξ ∈ DcrisL PD T₂.ρ τ₀ := by
  have hinj := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hL := (Strict.mem_DcrisL_iff PD τ₀ _).1 h
  rw [Strict.mem_DcrisL_iff]
  refine ⟨hξ, fun c => ?_⟩
  have hm : mulVB (LL := LL) (V := T₂.V) (B := B) c ξ - τ₀ c • ξ ∈ Dcris PD T₂.ρ :=
    (Dcris PD T₂.ρ).sub_mem (mulVB_Dcris PD c hξ) ((Dcris PD T₂.ρ).smul_mem _ hξ)
  exact sub_eq_zero.1 (hinj _ hm (by rw [map_sub, map_smul, Strict.crisMap_mulVB, hL.2 c, sub_self]))

variable [IsDomain O]

theorem pull_vec [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL))
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (α : ℕ → ℤ) (cY : Fin dY → O) (hN : ∀ s < e, dvO W Y e bY cY ∈ FilS W Y a s (-(α s)))
    (hpol : ∃ s < e, α s < 0) :
    ∃ (m : ℕ) (r : Fin d → O), (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cY j) ∧
      ∀ s < e, α s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α s)) := by
  have hpull : ∀ s < e, α s < 0 → ∃ ξ ∈ Dcris PD T₂.ρ, ξ ∈ FilS W T₂ a s (-(α s)) ∧
      crisMap B ι.f ξ = dvO W Y e bY cY := by
    intro s hs hneg
    obtain ⟨ν, hν, hνlam⟩ := Submodule.mem_map.1 (hN s hs)
    obtain ⟨μ, hμ, hμν⟩ := fil_pull PD W hK h9 T₂ Y ι π hses h2 hY (-(α s)) (by omega) _ hν
    refine ⟨((φVB PD (LL := LL) (V := T₂.V)) ^ s) μ, φVB_pow_Dcris PD s hμ.1.1, ⟨μ, hμ, rfl⟩, ?_⟩
    rw [crisMap_φVB_pow, hμν]
    exact hνlam
  obtain ⟨s₀, hs₀, hneg₀⟩ := hpol
  obtain ⟨ξ, hξD, -, hξlam⟩ := hpull s₀ hs₀ hneg₀
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hall : ∀ s < e, α s < 0 → ξ ∈ FilS W T₂ a s (-(α s)) := by
    intro s hs hneg
    obtain ⟨ξ', hξ'D, hξ'F, hξ'lam⟩ := hpull s hs hneg
    have h0 : ξ' - ξ = 0 := hinjD _ ((Dcris PD T₂.ρ).sub_mem hξ'D hξD) (by rw [map_sub, hξ'lam, hξlam, sub_self])
    rw [← sub_eq_zero.1 h0]
    exact hξ'F
  have hlamL : dvO W Y e bY cY ∈ DcrisL PD Y.ρ (W.emb a) := by
    rw [← hspanY, dvO_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hξL := letter_pull W hK h9 T₂ Y ι π hses h2 hY (W.emb a) hξD (by rw [hξlam]; exact hlamL)
  rw [← hspan2] at hξL
  obtain ⟨ρ, hρ⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hξL
  obtain ⟨m, r, hr⟩ := int_vec W hV ρ
  have hdvr : dvO W T₂ e b r = (PD.p : LL) ^ m • ξ := by
    rw [dvO_sum, ← hρ, Finset.smul_sum]
    simp only [hr, mul_smul]
  refine ⟨m, r, fun j => ?_, fun s hs hneg => ?_⟩
  · have h1 : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, (∑ k, algebraMap O LL (r k) * algebraMap O LL (o k j)) •
        dv W Y e bY (Pi.single j 1) := by

      rw [dvO_sum, map_sum]
      simp only [map_smul, ho, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2' : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, ((PD.p : LL) ^ m * algebraMap O LL (cY j)) •
        dv W Y e bY (Pi.single j 1) := by
      rw [hdvr, map_smul, hξlam, dvO_sum, Finset.smul_sum]
      simp only [smul_smul]
    have := congrFun (coef_eq _ hindY _ _ (h1.symm.trans h2')) j
    apply hinj

    rw [map_sum, map_mul, map_pow, map_natCast]
    simpa only [map_mul] using this
  · rw [hdvr]
    exact Submodule.smul_mem _ _ (hall s hs hneg)

theorem o_inj [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (ρ : Fin d → LL) (hρ : ∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) : ρ = 0 := by
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  set ξ := ∑ k, ρ k • dv W T₂ e b (Pi.single k 1) with hξ
  have hξD : ξ ∈ Dcris PD T₂.ρ := by
    have : ξ ∈ DcrisL PD T₂.ρ (W.emb a) := by
      rw [← hspan2]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact ((Strict.mem_DcrisL_iff PD _ ξ).1 this).1
  have h0 : crisMap B ι.f ξ = 0 := by

    rw [hξ, map_sum]
    simp only [map_smul, ho, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hρ, zero_smul, Finset.sum_const_zero]
  have hξ0 := hinjD ξ hξD h0
  funext k
  exact Fintype.linearIndependent_iff.1 hind2 ρ (by rw [← hξ, hξ0]) k


include W in
theorem right_inv (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL)) {d dY : ℕ}
    (o : Fin d → Fin dY → O)
    (hinjo : ∀ ρ : Fin d → LL, (∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) → ρ = 0) :
    ∃ (q : ℕ) (D : Fin dY → Fin d → O), ∀ k m, ∑ j, o k j * D j m =
      if k = m then ((PD.p : ℕ) : O) ^ q else 0 := by
  let oL : Matrix (Fin d) (Fin dY) LL := fun k j => algebraMap O LL (o k j)
  let f : (Fin d → LL) →ₗ[LL] (Fin dY → LL) := Matrix.vecMulLinear oL
  have hf : ∀ ρ j, f ρ j = ∑ k, ρ k * algebraMap O LL (o k j) := fun ρ j => by
    show (Matrix.vecMul ρ oL) j = _
    rfl
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot'.2 fun ρ hρ =>
    hinjo ρ fun j => by rw [← hf, hρ]; rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let Dl : Fin dY → Fin d → LL := fun j m => g (Pi.single j 1) m
  have key : ∀ k m, ∑ j, algebraMap O LL (o k j) * Dl j m = if k = m then 1 else 0 := by
    intro k m
    have hv : f (Pi.single k 1) = ∑ j, algebraMap O LL (o k j) • (Pi.single j 1 : Fin dY → LL) := by
      funext j'
      rw [hf, Finset.sum_apply]
      simp [Pi.single_apply]
    have h1 := congrArg (fun φ : (Fin d → LL) →ₗ[LL] (Fin d → LL) => φ (Pi.single k 1)) hg

    simp only [LinearMap.comp_apply, LinearMap.id_apply, hv, map_sum, map_smul] at h1
    have h2 := congrFun h1 m
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [h2]
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [Ne.symm hkm, hkm]
  obtain ⟨q, D, hD⟩ := int_vec W hV fun x : Fin dY × Fin d => Dl x.1 x.2
  refine ⟨q, fun j m => D (j, m), fun k m => hinj ?_⟩

  rw [map_sum]
  simp only [map_mul, hD]
  have : ∑ j, algebraMap O LL (o k j) * ((PD.p : LL) ^ q * Dl j m) =
      (PD.p : LL) ^ q * ∑ j, algebraMap O LL (o k j) * Dl j m := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, key]
  split_ifs <;> simp

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def GCoordProp (W : LocWach PD LL O v n) : Prop :=
  ∀ (T : LocLat G Qp LL O) (i : ZMod n) (h c : ℕ) {r : ℕ} (e e' : Fin r → W.DD T)
    (_ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (P Z : Matrix (Fin r) (Fin r) (PowerSeries O)),
    (∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ h • W.φD T (e' k) = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P m k) • e m) →
    PowerSeries.constantCoeff W.π₀₁ = 0 →
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) →
    ∀ (k : Fin r), Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k ∈ W.N T →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k) →
      ∀ (a : Fin r → PowerSeries O),
        Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a l) • e l →
        ∀ l, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l = (P * Z) l k

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
end
end
