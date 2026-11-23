module

public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle018
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
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
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem gamma_lift_along_arc [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W)
    (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (e : ℕ) (hje : A.j ≤ e) (hel : e ≤ A.len c) (T : LocLat G Qp LL O) (hT : Win W A T)
    (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hhor : IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (f k))
    (hinv : InvNL W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b f) :
    ∃ u, InI W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) u ∧
      InFP W T (c - ((A.len c : ℕ) : ZMod n)) e 1
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e • u) ∧
      RepVV W T (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p)
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol u
        (fun k => lE W (A.σ PD.p) * f k) := by
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hAC := (hArc hCA h5 A hA c hc e hje hel).2 T hT
  set c' := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a := c' + (e : ZMod n) with ha
  set Λ := abelian₂ W A a e with hΛdef
  obtain ⟨hP1, hP2, -, hF⟩ := hAC
  obtain ⟨-, -, hlift, -, hNL, hzero, -⟩ := hF d b sol hhor
  have hΛmem : Λ ∈ W.AΔ := lam_mem W A a e
  obtain ⟨u, huP, huR⟩ := hlift f hf
  obtain ⟨p0, hp0, hup0⟩ := huP
  rw [one_smul] at hup0
  have hlet : InLet W T a u := by
    show (letE a : LetA O n) • u = u
    refine lam_cancel W hR A a e T ?_
    rw [smul_comm, hup0]
    exact Relay2.Pp_letter W T c' e p0 hp0
  have hΔ : IsΔ W T u := by
    intro δ hδ
    refine lam_cancel W hR A a e T ?_
    have h1 : W.γD T δ (Λ • u) = Λ • W.γD T δ u := by
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hΛmem δ hδ]
    rw [← h1, hup0, Relay2.Pp_Δ W T c' e p0 hp0 δ hδ]
  obtain ⟨w, hw, w', hw', hww, hγΛ⟩ := lam_γ W hS A a e
  obtain ⟨u0, hu0, hγπ⟩ := hP
  have hπΛ : ∃ t, W.γA W.gam (W.π₀ * Λ ^ 2) = t * (W.π₀ * Λ ^ 2) ∧ t ∈ W.AΔ :=
    ⟨u0 * w ^ 2, by rw [map_mul, map_pow, hγπ, hγΛ]; ring, W.AΔ.mul_mem hu0 (W.AΔ.pow_mem hw _)⟩
  have hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c' x' →
      InFP W T c' e (W.π₀ * Λ ^ 2) (((W.φD T) ^ e) (W.π₀ ^ A.M PD.p • x')) :=
    fun x' hx' => jj_lam W hR h5 A hA a e T c' hx'
  have hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k) := fun k => (hhor.2 k).1
  have hγu := repVV_γ W hsol hJJ hw hw' hww hγΛ hπΛ huR
  obtain ⟨g, hgNL, hg⟩ := hinv
  obtain ⟨y, hyN, hyR⟩ := hNL g hgNL
  have hπy := repVV_smul W hyR hπ
  have hz := repVV_sub W hinj (repVV_sub W hinj hγu huR) hπy
  have hz0 : (((fun k => W.γE W.gam (lE W (A.σ PD.p) * f k)) - fun k => lE W (A.σ PD.p) * f k) -
      fun k => algebraMap (LetA O n) W.EE W.π₀ * (lE W (A.σ PD.p) * g k)) = 0 := by
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply, map_mul]
    have hl : W.γE W.gam (lE W (A.σ PD.p)) = lE W (A.σ PD.p) := by
      unfold lE; rw [map_pow, map_natCast]
    rw [hl, ← mul_sub, hg k]
    ring
  rw [hz0] at hz
  have hγΛu : InFP W T c' e 1 (Λ • W.γ T u) := by
    have h1 : Λ • W.γ T u = w' • W.γ T (Λ • u) := by
      show _ = w' • W.γD T W.gam (Λ • u)
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hγΛ, smul_smul, ← mul_assoc, hww, one_mul]
      rfl
    refine ⟨w' • W.γ T p0, Relay2.Pp_smul W T c' _ hw' _ (Relay2.Pp_γ W T c' _ p0 hp0), ?_⟩
    rw [one_smul, h1, hup0]
  have hΛu : InFP W T c' e 1 (Λ • u) := ⟨p0, hp0, by rw [one_smul, hup0]⟩
  have hΛy : InFP W T c' e 1 (Λ • (W.π₀ • y)) := by
    rw [smul_comm]
    exact Relay2.inMultiple_smul W T c' _ _ hπ (hP2 y hyN)
  have hΛz : InFP W T c' e 1 (Λ • (W.γ T u - u - W.π₀ • y)) := by
    rw [smul_sub, smul_sub]
    exact Relay2.inMultiple_sub W T c' _ _ (Relay2.inMultiple_sub W T c' _ _ hγΛu hΛu) hΛy
  obtain ⟨p1, hp1, hzp⟩ := hzero _ hΛz hz
  obtain ⟨y2, hy2, hy2c, hy2e⟩ := hP1 p1 hp1
  obtain ⟨y1, hy1, hy1c, hy1e⟩ := hyN
  rw [one_smul] at hy2e hy1e
  refine ⟨u, ⟨hlet, hΔ, y1 + y2, (W.NΔ T).add_mem hy1 hy2, ?_, ?_⟩, ⟨p0, hp0, by rw [one_smul, hup0]⟩,
    huR⟩
  · rw [smul_add, hy1c, hy2c]
  · have : W.γ T u - u = (W.γ T u - u - W.π₀ • y) + W.π₀ • y := by abel
    rw [this, hzp, mul_smul, hy2e, hy1e, smul_add, add_comm]

end Core

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_first (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl5 : 5 ≤ PD.p)
    (hArc : ArcCore W) (hFL : ArcFilLowCore W) (A : ArcP n) (hOK : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (hlen : A.len c = 3) (hj : A.j = 1) {b₁ w' : ℕ} (hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up b₁)
    (hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down w')
    {T₂ : LocLat G Qp LL O} (hW₂ : Win W A T₂) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 b₁)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 1 lam) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol (A.M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2
      (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ (A.σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) := by
  classical
  have hj2 : A.j ≤ 2 := by rw [hj]; norm_num
  have h2l : 2 ≤ A.len c := by rw [hlen]; norm_num
  obtain ⟨⟨u, hu, hJJ⟩, hT⟩ := hArc hcase hl5 A hOK c hc 2 hj2 h2l
  obtain ⟨-, -, -, hfr⟩ := hT T₂ hW₂
  obtain ⟨-, -, hc3, -, -, -, hcrit⟩ := hfr d bb sol hbb
  have hFL' := hFL hcase hl5 A hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) 1 (by norm_num)
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a : ZMod n := c' + ((2 : ℕ) : ZMod n) with ha_def
  have ha : a = c - 1 := by rw [ha_def, hc', hlen]; push_cast; ring
  set Λ : LetA O n := abelian₂ W A a 2 with hΛdef
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hHs0 : A.Hs a 2 0 = A.h := by
    unfold ArcP.Hs
    rw [if_neg]
    push Not
    refine ⟨?_, by rw [hj]; norm_num⟩
    rw [Nat.cast_zero, sub_zero, ha, hty1]
    intro h; cases h
  have hHs1 : A.Hs a 2 1 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by rw [hj]))]
  have hΛ : Λ = qA W ^ A.h * ps W 1 ^ A.G₀ := by
    rw [hΛdef, abelian₂, Finset.prod_range_succ, Finset.prod_range_one, hHs0, hHs1, hps0]
  have hb1h : b₁ + A.S ≤ A.h := by
    have := hOK.2.2.2.2.2.2.2.1 (c - 1) (by rw [hty1]; rfl)
    rwa [hty1] at this
  have hw'η : A.η < w' := by
    have := hOK.2.2.2.2.1 (c - 2)
    rwa [hty2] at this
  have hqmem : qA W ∈ W.AΔ := by rw [← hps0]; exact TypesA.ps_mem W 0
  set R : LetA O n := qA W ^ (A.h - b₁) * ps W 1 ^ (A.G₀ + (w' + A.S)) with hRdef
  have hRmem : R ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
  have hΛs : (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) R := by
    have hq : qA W ^ A.h = qA W ^ (A.h - b₁) * qA W ^ b₁ := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    calc (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s) := by
          rw [hΛ, hq]; simp only [map_mul]; ring
      _ = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * (algebraMap (LetA O n) W.EE) (ps W 1 ^ (w' + A.S)) := by rw [hs]
      _ = (algebraMap (LetA O n) W.EE) R := by rw [hRdef]; simp only [pow_add, map_mul]; ring
  have hΛx : Λ • (s • lam) = R • lam := by
    rw [← algebraMap_smul W.EE Λ (s • lam), smul_smul, hΛs, algebraMap_smul]
  have hInFP : InFP W T₂ c' 2 1 (Λ • (s • lam)) := by
    rw [hΛx]
    obtain ⟨y, hy, rfl⟩ := hlam
    exact ⟨R • y, TypesA.Pp_smul W hRmem hy, by rw [one_smul, one_smul]⟩
  have hΛmem : Λ ∈ W.AΔ := TypesA.Ps_mem W (TC.lam_mem_Ps W A a 2)
  have hletmem : (letE a : LetA O n) ∈ W.AΔ := TypesD.letE_mem W a

  obtain ⟨-, -, κ₁, κ₁', Hh1, a1, hHh1, -, -⟩ := hc3 (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) else 0) (by
    intro k
    by_cases hk : k = k₀
    · simp only [if_pos hk]
      exact ⟨Λ, hΛmem, by rw [← map_mul]; congr 1; ring⟩
    · simp only [if_neg hk]
      exact ⟨0, W.AΔ.zero_mem, by simp⟩)
  set σ := A.σ PD.p with hσdef
  obtain ⟨κ', y, hy, hyeq⟩ := h4a
  rw [hj] at hJJ
  have hJJ' : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) = W.π₀ * Λ ^ 2 * u := by
    rw [← hJJ]; simp
  have hlet2 : (letE a : LetA O n) • ((W.φD T₂) ^ 2) Hh = ((W.φD T₂) ^ 2) Hh :=
    TypesD.φDpow_letter W (TypesD.horTr_letter W hbb hHh) 2
  have hφl : ((W.φD T₂) ^ 2) (lA W ^ κ₁ • Hh) = lA W ^ κ₁ • ((W.φD T₂) ^ 2) Hh := by
    rw [← TypesA.pO_smul, map_smul, TypesA.pO_smul]
  have hRep : RepVV W T₂ c' 2 (A.M PD.p) Λ bb sol (lA W ^ 0 • (s • lam))
      (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    refine ⟨κ + κ₁, κ', fun k => if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k,
      fun k => if k = k₀ then letE a * R * lA W ^ σ else 0, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = k₀
      · subst hk; simp only [if_pos rfl]; exact TypesA.IsHorTr_smul W κ₁ hHh
      · simp only [if_neg hk]; rw [add_comm]; exact TypesA.IsHorTr_smul W κ (hHh1 k)
    · intro k
      by_cases hk : k = k₀
      · simp only [if_pos hk]
        refine ⟨W.AΔ.mul_mem (W.AΔ.mul_mem hletmem hRmem) (TypesA.lA_pow_mem W σ), ?_⟩
        rw [TC.lE_eq W σ]
        rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
        simp only [map_mul]; ring
      · simp only [if_neg hk]; exact ⟨W.AΔ.zero_mem, by simp⟩
    · have hsum : ∑ k, (if k = k₀ then letE a * R * lA W ^ σ else 0) •
          ((W.φD T₂) ^ 2) (if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k) =
          (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh := by
        rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp only [if_neg hk, zero_smul]) (by simp)]
        rw [if_pos rfl, if_pos rfl]
        rw [hφl, smul_smul, show letE a * R * lA W ^ σ * lA W ^ κ₁ = (R * lA W ^ σ * lA W ^ κ₁) * letE a by ring,
          mul_smul, hlet2]
      rw [hsum, pow_zero, one_smul, hΛx]
      refine ⟨(u * (R * lA W ^ κ₁)) • y, TypesA.Pp_smul W (W.AΔ.mul_mem hu (W.AΔ.mul_mem hRmem
        (TypesA.lA_pow_mem W κ₁))) hy, ?_⟩
      have e1 : lA W ^ κ' • (lA W ^ (κ + κ₁) • R • lam - (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh) =
          (R * lA W ^ κ₁) • (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ σ • ((W.φD T₂) ^ 2) Hh)) := by
        simp only [smul_sub, smul_smul]
        congr 2 <;> ring
      rw [e1, hyeq, hJJ', smul_smul, smul_smul]
      congr 1
      ring
  have hfr : ∀ m, InFr W a 1 Λ (if m = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    intro m
    by_cases hm : m = k₀
    · simp only [if_pos hm]
      refine ⟨R * lA W ^ σ, W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W σ), ?_⟩
      rw [TC.lE_eq W σ]
      rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
      simp only [map_mul, map_one]; ring
    · simp only [if_neg hm]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
  have hN : InFNc W T₂ a 1 (s • lam) := by
    refine (hcrit (s • lam) 0 _ hInFP hRep hfr).2 ⟨0, 1, fun _ => (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s,
      fun _ => Pi.single k₀ 1, fun _ t => if t = 0 then -(b₁ : ℤ) else ((w' + A.S : ℕ) : ℤ),
      fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
    · refine ⟨lA W ^ σ, TypesA.lA_pow_mem W σ, ?_⟩
      have e1 : (-(b₁ : ℤ)).toNat = 0 := by omega
      have e2 : (-(-(b₁ : ℤ))).toNat = b₁ := by omega
      have e3 : (((w' + A.S : ℕ) : ℤ)).toNat = w' + A.S := by omega
      have e4 : (-(((w' + A.S : ℕ) : ℤ))).toNat = 0 := by omega
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_ne_zero, ↓reduceIte,
        e1, e2, e3, e4, pow_zero, one_mul, mul_one, hps0]
      rw [TC.lE_eq W σ]
      simp only [map_mul]
      rw [show (algebraMap (LetA O n) W.EE) (qA W ^ b₁) * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s)
        by ring, hs]
      ring
    · intro t ht
      interval_cases t
      · simp only [↓reduceIte, neg_neg]
        rw [hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthTwo.dv_succ] at hFil
        rw [ArcLengthTwo.dvO_single]
        exact ArcLengthTwo.filS_φ_inv W T₂ (by rw [ha]; push_cast; ring) hFil
      · simp only [one_ne_zero, ↓reduceIte]
        refine hFL'.1 _ fun x hx => ?_
        have e : a - ((1 : ℕ) : ZMod n) = c - 2 := by rw [ha]; push_cast; ring
        rw [e, hty2] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
        push_cast
        omega
    · simp only [Fin.sum_univ_one, lE, pow_zero, one_mul]
      by_cases hk : k = k₀
      · subst hk; simp
      · simp [if_neg hk, Pi.single_apply, hk]
  obtain ⟨y, hyΔ, hyl, hxy⟩ := hN
  rw [← ha, hxy, one_smul]
  exact ⟨hyΔ, ⟨y, hyΔ.1, by simpa using hyl⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem ArcLengthFourSecond.isUnit_ps (W : LocWach PD LL O v n) (hR : GS.RD W) (t : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W t)) := by
  have hp : PD.p.Prime := by
    first
      | exact PD.hp.out
      | exact PD.hp
      | exact PD.p_prime
      | exact PD.prime
      | exact PD.hprime
      | exact Fact.out
  obtain ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩, -, -⟩ := hR
  have hπ0 : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw1, map_mul, map_pow]
    exact (w1.isUnit.map _).mul (W.EE_π.pow _)
  have hq0 : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := by
    have h := congrArg (algebraMap (LetA O n) W.EE) hw2
    rw [map_mul, map_mul, map_pow] at h
    have hφ : IsUnit (algebraMap (LetA O n) W.EE (W.φA W.π₀)) := by
      rw [show algebraMap (LetA O n) W.EE (W.φA W.π₀) = W.φE (algebraMap (LetA O n) W.EE W.π₀) from
        (W.φE_ext W.π₀).symm]
      exact hπ0.map W.φE
    rw [h] at hφ
    have h3 := isUnit_of_mul_isUnit_right hφ
    exact (isUnit_pow_iff (by have := hp.two_le; omega)).1 h3
  induction t with
  | zero => simpa [ps] using hq0
  | succ t ih =>
    have e : algebraMap (LetA O n) W.EE (ps W (t + 1)) = W.φE (algebraMap (LetA O n) W.EE (ps W t)) := by
      rw [ps, ps, pow_succ', AlgHom.mul_apply]
      exact (W.φE_ext _).symm
    rw [e]
    exact ih.map W.φE

theorem ArcLengthFourSecond.cst_add [IsDomain O] [IsDiscreteValuationRing O] {W : LocWach PD LL O v n} (Br : PhiBridge W)
    (F G : PowerSeries O) : Br.cst (F + G) = Br.cst F + Br.cst G := by
  show (fun _ => Br.ι (F + G) : LetA O n) = (fun _ => Br.ι F : LetA O n) + (fun _ => Br.ι G : LetA O n)
  rw [map_add (f := _)]
  rfl

theorem exists_fraction_in_frame [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : ZMod n) (wa Bn η s : ℕ) (hBn : 1 ≤ Bn) (x₀ : O) :
    ∃ (fa : W.EE) (si : ℕ), InFr W c 1 (ps W 2 ^ wa) fa ∧
      InFr W c (ps W 1 ^ Bn * ps W 0 ^ η) (ps W 2 ^ wa)
        (lE W s * fa - lE W (s - si) * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) ∧
      (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 - 1 ≤ si := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set y : ℝ := (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 with hy
  set si : ℕ := ⌊y⌋₊ with hsi
  have hk : eO (O := O) PD.p * si ≤
      ⌈(eO (O := O) PD.p : ℝ) * ((wa : ℝ) - Bn / PD.p - η / (PD.p : ℝ) ^ 2)⌉₊ := by
    rw [← hy]
    by_cases h0 : 0 ≤ y
    · have h1 : (si : ℝ) ≤ y := Nat.floor_le h0
      have h2 : ((eO (O := O) PD.p * si : ℕ) : ℝ) ≤ (eO (O := O) PD.p : ℝ) * y := by
        push_cast; exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      exact_mod_cast h2.trans (Nat.le_ceil _)
    · have : si = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [this, mul_zero]; exact Nat.zero_le _
  have hmem := Br.P.c3b hϖ wa Bn η (Or.inl hBn) (eO (O := O) PD.p * si) hk
  have hspan := span_C_l_pow hϖ Br.P.hl0 si
  obtain ⟨r, hr⟩ : ∃ r : PowerSeries O,
      r * (PowerSeries.C ((PD.p : ℕ) : O)) ^ si = (PowerSeries.C ϖ) ^ (eO (O := O) PD.p * si) := by
    have : (PowerSeries.C ϖ : PowerSeries O) ^ (eO (O := O) PD.p * si) ∈
        Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ si} := by
      rw [hspan]; exact Ideal.subset_span rfl
    exact Ideal.mem_span_singleton'.mp this
  obtain ⟨α', β, hαβ⟩ := Ideal.mem_span_pair.mp hmem
  have hD : ps W 2 ^ wa = lA W ^ si * Br.cst (α' * r) + ps W 1 ^ Bn * ps W 0 ^ η * Br.cst β := by
    have e0 : ps W 0 = qA W := by simp [ps]
    have e2 : Br.cst (Br.P.p 2 ^ wa) =
        Br.cst ((α' * r) * PowerSeries.C ((PD.p : ℕ) : O) ^ si + β * (Br.P.p 1 ^ Bn * PowerSeries.X ^ η)) := by
      rw [← hαβ, ← hr]; congr 1; ring
    simp only [ArcLengthFourSecond.cst_add, Br.cst_mul, Br.cst_pow] at e2
    rw [← Br.ps_eq, ← Br.ps_eq, ← Br.qA_eq, ← Br.lA_eq, ← e0] at e2
    rw [e2, Br.cst_mul]; ring
  set e₄ := s - si with he₄
  set t := e₄ + si - s with ht
  have hexp : lA W ^ s * lA W ^ t = lA W ^ e₄ * lA W ^ si := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hUn : IsUnit (algebraMap (LetA O n) W.EE (ps W 2 ^ wa)) := by
    rw [map_pow]; exact (ArcLengthFourSecond.isUnit_ps W hR 2).pow _
  set u : LetA O n := lA W ^ t * (algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) with hu
  have hu_mem : u ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem t) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _))
  set fa : W.EE := ((hUn.unit⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (letE c * 1 * u) with hfa
  have hfaD : algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa = algebraMap (LetA O n) W.EE (letE c * 1 * u) := by
    rw [hfa, ← mul_assoc, IsUnit.mul_val_inv hUn, one_mul]
  set u₂ : LetA O n := -(lA W ^ e₄ * (algebraMap O (LetA O n) x₀ * Br.cst β)) with hu₂
  have hu₂_mem : u₂ ∈ W.AΔ :=
    W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem e₄) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _)))
  refine ⟨fa, si, ⟨u, hu_mem, hfaD⟩, ⟨u₂, hu₂_mem, ?_⟩, ?_⟩
  · calc algebraMap (LetA O n) W.EE (ps W 2 ^ wa) *
          (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀))
        = lE W s * (algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa) -
            lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by ring
      _ = algebraMap (LetA O n) W.EE (lA W ^ s) * algebraMap (LetA O n) W.EE (letE c * 1 * u) -
            algebraMap (LetA O n) W.EE (lA W ^ e₄) * (algebraMap (LetA O n) W.EE (letE c) *
              algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x₀)) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by
          rw [hfaD, ArcLengthFourSecond.lE_eq, ArcLengthFourSecond.lE_eq, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x₀]
      _ = algebraMap (LetA O n) W.EE (lA W ^ s * (letE c * 1 * u) -
            lA W ^ e₄ * (letE c * algebraMap O (LetA O n) x₀) * ps W 2 ^ wa) := by
          simp only [map_mul, map_sub]
      _ = algebraMap (LetA O n) W.EE (letE c * (ps W 1 ^ Bn * ps W 0 ^ η) * u₂) := by
          congr 1
          rw [hD, hu, hu₂]
          linear_combination ((letE c : LetA O n) * algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) * hexp
  · have := Nat.lt_floor_add_one y
    rw [← hsi] at this
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
