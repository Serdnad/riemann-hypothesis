module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle030
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle029
public import Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem first_lift_of_uniformizer_clause [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W)
    (hK : Sh.LemK W) (hFD : Sh.FilDim W) (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W :=
  first_lift_of_hypotheses W hV h9 hRN (rToolMod_dStab W hP9) hD hEx hER hK hFD hB hE hC hQ

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

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

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem φ_Pp (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) :
    ∀ y ∈ Pp W T c' e, W.φD T y ∈ Pp W T c' (e + 1) := by
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' e _ (by simpa using (Pp W T c' (e + 1)).zero_mem)
    (fun x y hx hy => by rw [map_add (f := _)]; exact (Pp W T c' (e + 1)).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Pp W T c' (e + 1)).neg_mem hx) ?_
  intro a ha x hx
  rw [φD_smulA, ← pow_apply_succ]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' (e + 1) (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ha) hx

theorem φ_InFP (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (F : LetA O n) {y : W.DD T}
    (h : InFP W T c' e F y) : InFP W T c' (e + 1) (W.φA F) (W.φD T y) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨W.φD T p, φ_Pp W T c' e p hp, by rw [φD_smulA]⟩

theorem φA_lA (t : ℕ) : W.φA (lA W ^ t) = lA W ^ t := by
  rw [map_pow]; unfold lA; rw [map_natCast]

theorem φE_alg (a : LetA O n) : W.φE (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (W.φA a) :=
  W.φE_ext a

theorem φA_π₀ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w ∈ W.AΔ, W.φA W.π₀ = w * W.π₀ * ps W 0 ^ (PD.p - 1) := by
  obtain ⟨-, w, hw⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have hc : W.π₀ * ps W 0 ^ (PD.p - 1) ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hp0Δ _)
  have hqP : Formalism.MainNotions.WachCoordinates.qP W = ps W 0 := by rw [ps_zero]; rfl
  have hc0 : ∀ i, (W.π₀ * ps W 0 ^ (PD.p - 1)) i ≠ 0 := by
    intro i
    rw [Pi.mul_apply, Pi.pow_apply, ← hqP]
    exact mul_ne_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) (pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0 i))
  refine ⟨(w : LetA O n), Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hc hc0 ?_, by rw [hw]⟩
  rw [show W.π₀ * ps W 0 ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ by rw [hw]; ring]
  exact Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hR.1

theorem transport (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (N : ℕ) (hN : A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 ≤ N) {vv : LetA O n} (hv : vv ∈ W.AΔ) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T x)) ∧
    RepVV W T c' (e + 1) M (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      ((ps W 0 ^ N * vv) • W.φD T x)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) ∧
    ∀ k, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1))
      (algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) := by
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  set u : LetA O n := ps W 0 ^ N * vv with hudef
  have hlam : abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) = ps W 0 ^ H * W.φA Λ := lam_succ W A c' e
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have huΔ : u ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv
  have hupΔ : u * ps W 0 ^ H ∈ W.AΔ := W.AΔ.mul_mem huΔ (W.AΔ.pow_mem hp0Δ H)
  have hmain : ∀ z : W.DD T, abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T z) =
      (u * ps W 0 ^ H) • W.φD T (Λ • z) := by
    intro z
    rw [hlam, φD_smulA, smul_smul, smul_smul]
    congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp, hxp⟩ := hx
    rw [one_smul] at hxp
    refine ⟨(u * ps W 0 ^ H) • W.φD T p, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) hupΔ _
      (φ_Pp W T c' e p hp), ?_⟩
    rw [one_smul, hmain, hxp]
  · rw [repVV_iff] at hrep ⊢
    obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
    refine ⟨κ, Hh, hHh, κ', fun k => u * ps W 0 ^ H * W.φA (aa k), fun k =>
      ⟨W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (haa k).1), ?_⟩, ?_⟩
    · have h1 := congrArg W.φE (haa k).2
      rw [map_mul, φE_alg, φE_alg] at h1
      rw [hlam, map_mul (algebraMap (LetA O n) W.EE) (u * ps W 0 ^ H), ← h1, hudef]
      simp only [map_mul]
      ring
    · obtain ⟨w, hw, hφπ⟩ := φA_π₀ W hR hp0
      have hP' := φ_InFP W T c' e _ hP
      obtain ⟨q, hq, hqe⟩ := hP'
      have hE : W.φD T (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, aa k • ((W.φD T) ^ e) (Hh k))) =
          lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x - ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k)) := by

        rw [φD_smulA, φA_lA, map_sub, φD_smulA, φA_lA, φD_smulA, map_sum]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [φD_smulA, pow_apply_succ]
      rw [hE] at hqe
      have hkey : lA W ^ κ' • (lA W ^ κ • abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T x) -
          ∑ k, (u * ps W 0 ^ H * W.φA (aa k)) • ((W.φD T) ^ (e + 1)) (Hh k)) =
          (u * ps W 0 ^ H) • (lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x -
            ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k))) := by
        rw [hlam]
        simp only [smul_sub, Finset.smul_sum, smul_smul]
        congr 1
        · congr 1; ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          congr 1; ring
      rw [hkey, hqe, smul_smul]
      have hexp : H + H ≤ N + H + (PD.p - 1) := by omega
      refine ⟨(vv * w * ps W 0 ^ (N + H + (PD.p - 1) - (H + H))) • q,
        Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem hv hw)
          (W.AΔ.pow_mem hp0Δ _)) q hq, ?_⟩
      rw [smul_smul, hlam, map_mul, map_pow, hφπ]
      congr 1
      have e2 : ps W 0 ^ (N + H + (PD.p - 1)) = ps W 0 ^ (H + H) *
          ps W 0 ^ (N + H + (PD.p - 1) - (H + H)) := by
        rw [← pow_add, Nat.add_sub_cancel' hexp]
      rw [hudef]
      linear_combination (vv * w * W.π₀ * W.φA Λ ^ 2) * e2
  · intro k
    obtain ⟨t, ht, hft⟩ := hfr k
    refine ⟨u * ps W 0 ^ H * W.φA t, W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ht), ?_⟩
    have h1 := congrArg W.φE hft
    rw [map_mul, φE_alg, φE_alg] at h1
    have hl : W.φA (letE (c' + (e : ZMod n)) : LetA O n) = letE (c' + ((e + 1 : ℕ) : ZMod n)) := by
      have := φA_letE W (c' + ((e + 1 : ℕ) : ZMod n))
      rwa [show c' + ((e + 1 : ℕ) : ZMod n) - 1 = c' + (e : ZMod n) by push_cast; ring] at this
    simp only [map_mul, mul_one, hl] at h1
    rw [hlam]
    simp only [map_mul, map_pow, mul_one]
    linear_combination (algebraMap (LetA O n) W.EE (ps W 0) ^ H * algebraMap (LetA O n) W.EE u) * h1

theorem piLam_of_sec (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hsatP : SATPcore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b)
    (x : W.DD T) (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) (h : Fin d → W.EE)
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x h)
    (hh : ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1 (h k)) :
    InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x := by
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  rw [repVV_iff] at hrep
  obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
  choose u hu hhu using hh
  have haa' : ∀ k, aa k = W.π₀ * Λ ^ 2 * (letE (c' + (e : ZMod n)) * u k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2]
    have := hhu k
    rw [map_one, one_mul] at this
    rw [this, ← map_mul]
    congr 1; ring
  have hS : InFP W T c' e (W.π₀ * Λ ^ 2) (∑ k, aa k • ((W.φD T) ^ e) (Hh k)) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sum W T c' e _ _ _ fun k _ => ?_
    rw [haa' k, mul_smul]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hu k)) _
      (horTr_mem W T c' b sol hb hR.1 M κ e k (hHh k)))
  have h2 : InFP W T c' e (W.π₀ * Λ ^ 2) (Λ • (lA W ^ (κ + κ') • x)) := by
    have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ hP
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κ') hS)
    rw [smul_sub, sub_add_cancel] at this
    rwa [lA_smul_smul, smul_comm] at this
  obtain ⟨p, hp, hpe⟩ := h2
  have hcan : lA W ^ (κ + κ') • x = (W.π₀ * Λ) • p := by
    refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T (lam_unit W hR A (c' + (e : ZMod n)) e) ?_
    rw [hpe, smul_smul]
    congr 1
    rw [← hΛdef]
    ring
  exact hsatP hCA T c' e (W.π₀ * Λ) Λ hTc (piLam_piPs W A _ e) (lam_piPs W A _ e) x hx
    ⟨κ + κ', p, hp, hcan⟩

theorem inN_of_piLam (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (hup : ∀ y ∈ Pp W T c' e, InFNc W T (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e • y))
    (x : W.DD T) (hx : InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨y, hy, hyl, hye⟩ := hup p hp
  rw [one_smul] at hye
  refine ⟨W.π₀ • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hπ hy, by rw [smul_comm, hyl], ?_⟩
  rw [one_smul, mul_smul, hye]

end Formalism.MainNotions.UnusedSlot80.LevC
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

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem secOfP' (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : Λ • x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  have hcoef : ∀ k, algebraMap (LetA O n) W.EE Λ *
      (((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k)) = algebraMap (LetA O n) W.EE (aa k) := by
    intro k
    rw [← hU, ← mul_assoc, Units.mul_inv, one_mul]
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  refine ⟨κ, fun k => ((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), aa,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨haa k, hcoef k⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by rw [hcoef k, haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [pow_zero, one_smul, hsum, smul_comm Λ, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hw m) (hb.1.1 m))

theorem pOfSec' (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (A : ArcP n) (c' : ZMod n) (e M : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k)) :
    ∃ (κ : ℕ) (x : W.DD T), InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x) ∧
      RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x (fun k => lE W κ * f k) := by
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W hO2 hH hCA T hTc c' b sol hb M
  choose u hu hfu using hf
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  let aa : Fin d → LetA O n := fun k => letE (c' + (e : ZMod n)) * 1 * u k
  have haa : ∀ k, aa k ∈ W.AΔ := fun k =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) W.AΔ.one_mem) (hu k)
  set z : W.DD T := ∑ k, aa k • ((W.φD T) ^ e) (Hh k) with hz
  have hzP : z ∈ Pp W T c' e := AddSubgroup.sum_mem _ fun k _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e (haa k) _ (horTr_mem W T c' b sol hb.1 hR.1 M κ e k (hHh k))
  have hΛz : Λ • (((U⁻¹ : W.EEˣ) : W.EE) • z) = z := by
    rw [← algebraMap_smul W.EE Λ, ← hU, smul_smul, Units.mul_inv, one_smul]
  refine ⟨κ, ((U⁻¹ : W.EEˣ) : W.EE) • z, ⟨z, hzP, by rw [hΛz, one_smul]⟩, κ, 0, Hh,
    fun k => lA W ^ κ * aa k, hHh, fun k => ⟨W.AΔ.mul_mem (lA_mem W κ) (haa k), ?_⟩, ?_⟩
  · rw [mul_left_comm, hfu k]
    show lE W κ * _ = algebraMap (LetA O n) W.EE (lA W ^ κ * aa k)
    rw [map_mul (algebraMap (LetA O n) W.EE) (lA W ^ κ), map_pow]
    unfold lE lA
    rw [map_natCast]
  · rw [hΛz, pow_zero, one_smul, hz]
    simp only [Finset.smul_sum, mul_smul, sub_self]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _

end Formalism.MainNotions.UnusedSlot80.LevC
end
end
