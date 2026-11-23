module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle003
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpPowSubOne
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle005

@[expose] public section

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Crit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def GamNΔ : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ ζ' : LL) (δ : W.Gam) (a : ℕ),
    IsPrimitiveRoot ζ PD.p → ζ' = ζ ^ a →
    ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL)) →
    ∀ (x : ↥(W.N T)) (hx : W.γD T δ (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γD T δ x, hx⟩ k = (algebraMap O LL (W.χΓ δ : O)) ^ k • W.levN T i ζ' x k

def PtTrans : Prop :=
  ∀ ζ ζ' : LL, IsPrimitiveRoot ζ PD.p → IsPrimitiveRoot ζ' PD.p → ∃ δ ∈ W.DelF, ∃ a : ℕ,
    ζ' = ζ ^ a ∧ ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL))

theorem gamΔ_of_tie {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamNΔ W := by
  intro T hT i ζ ζ' δ a hζ hζ' hv x hx k
  rw [C.levN_eq, C.levN_eq, C.levB_Γ T hT δ i ζ ζ' 1 a (by rwa [pow_one]) hv hζ' x hx k, map_smul]

theorem isExp_self (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T} (hx : x ∈ W.N T) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x (W.levN T i ζ ⟨x, hx⟩) := by
  have h1 : (1 : LetA O n) • x ∈ W.N T := by rwa [one_smul]
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨x, hx⟩
  refine ⟨⟨m, hm⟩, 1, h1, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • x, h1⟩ : ↥(W.N T)) = ⟨x, hx⟩ := Subtype.ext (one_smul _ _)
  rw [e, map_one, conv_eq, smulS_one hm]

theorem isExp_smulA (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d) (a' : LetA O n) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (a' • x) (smulS (W.lev i ζ a') d) := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  have hmem : a • (a' • x) ∈ W.N T := by rw [smul_comm]; exact (W.N T).smul_mem a' ha
  refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
  have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
  rw [e1, levN_smulS, funext he]
  show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
  rw [smulS_comm hm]

theorem expCritN_of [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hdom : IsDomain O)
    (hFr : IsFractionRing O LL) (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hΓ : GamNΔ W) (hΔ : PtTrans W) :
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x →
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d →
        ((∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T) →
          (x ∈ W.N T ↔ ∀ k, d k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k))) := by
  intro T hT i ζ hζ x d hDL hd ⟨k, hk⟩
  have hs : W.s = 1 := hA.2.1
  haveI := hdom
  have hp := p_ne_zero_LL W
  have hFl : Antitone (Formalism.MainNotions.WachCoordinates.FilLev W T i 0) := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0
  constructor
  · intro hx j
    rw [isExp_unique W T i ζ hd (isExp_self W T i ζ hx)]
    exact (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 ⟨x, hx⟩ j
  · intro hcoef
    obtain ⟨w, hw⟩ := hR.2.2.2.2.1
    rw [eat_qp] at hw
    have hQ : W.Q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by rw [MC.Q_eq_q W hs, hw]
    have hQk : W.Q ^ k • x ∈ W.N T := by
      rw [hQ, mul_pow, mul_smul]; exact (W.N T).smul_mem _ hk
    refine memCrit_of W hA hFr h1 h3 h4 h5 hD T hT i x k hQk hDL.1 fun ζ' hζ' j => ?_

    obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
    have hlevQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
    obtain ⟨m, hm⟩ := hd.1
    have hEQ : W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ = smulS ((PowerSeries.X * u) ^ k) d := by
      have := isExp_unique W T i ζ (isExp_self W T i ζ hQk) (isExp_smulA W T i ζ hd (W.Q ^ k))
      rw [this, map_pow, hlevQ]
    have hDgζ : ∀ j : ℤ, W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := by
      intro j
      rw [hEQ, mul_pow, smulS_mul hm, smulS_X_pow (LB_smulS hm _)]
      have := Dg_smulS hFl hm (s := 0) (fun j => by simpa using hcoef j) (u ^ k) (j - k)
      simp only at this ⊢
      rwa [show (0 : ℤ) - (j - (k : ℤ)) = (k : ℤ) - j by ring] at this

    obtain ⟨δ, hδ, a, hζa, hv⟩ := hΔ ζ' ζ hζ' hζ
    have hγy : W.γD T δ (W.Q ^ k • x) ∈ W.N T := W.N_Γ T δ _ hQk
    obtain ⟨vv, hvv, hvu⟩ := gam_q W δ
    obtain ⟨vU, rfl⟩ := hvu
    have hγQ : W.γA δ W.Q = W.Q * vU := by rw [MC.Q_eq_q W hs]; exact hvv
    have eγ : W.γD T δ (W.Q ^ k • x) = ((vU : LetA O n) ^ k) • (W.Q ^ k • x) := by
      rw [RL.γD_smulA, map_pow, hDL.2 δ hδ, hγQ, mul_pow, mul_comm, mul_smul]
    have eback : W.Q ^ k • x = (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • W.γD T δ (W.Q ^ k • x) := by
      rw [eγ, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hsub : (⟨W.Q ^ k • x, hQk⟩ : ↥(W.N T)) =
        (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • (⟨W.γD T δ (W.Q ^ k • x), hγy⟩ : ↥(W.N T)) :=
      Subtype.ext eback
    have htr : ∀ j, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j =
        (algebraMap O LL (W.χΓ δ : O)) ^ j • W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j :=
      fun j => hΓ T hT i ζ' ζ δ a hζ' hζa hv ⟨W.Q ^ k • x, hQk⟩ hγy j
    have hDg' : ∀ j : ℤ, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := fun j => by
      rw [htr j]; exact Submodule.smul_mem _ _ (hDgζ j)
    obtain ⟨m', hm'⟩ := W.levN_supp T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩
    rw [hsub, levN_smulS]
    exact Dg_smulS hFl hm' hDg' _ j

end Crit

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Trans

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_eq_unit (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ U : (LetA O n)ˣ, Formalism.MainNotions.LiftingTheory.qp W = (U : LetA O n) * W.Q := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))
      W.π₀ = Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]
  rw [hE] at hw
  refine ⟨w⁻¹, ?_⟩
  rw [Q_eq_q W hs, hw, ← mul_assoc, Units.inv_mul, one_mul]

theorem trans_d [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (c : ZMod n)
    (δ : W.Gam) (hδ : δ ∈ W.DelF) (ζ ζ' : LL) (χ : LL) (hχ0 : χ ≠ 0)
    (hΔN : ∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ' x k)
    (hΔA : ∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ' f))
    {w : W.DD T} (hwΔ : W.γD T δ w = w) {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T)
    (u u' : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu' : W.lev c ζ' W.q = X * u')
    (hu0 : constantCoeff u ≠ 0)
    {dz dz' : ℤ → T.V ⊗[Qp] BdR} (hdz : ∃ m, LB m dz) (hdz' : ∃ m, LB m dz')
    (ez : W.levN T c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dz)
    (ez' : W.levN T c ζ' ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u') ^ K) dz') :
    dz = resc χ dz' := by
  obtain ⟨m, hm⟩ := hdz
  obtain ⟨m', hm'⟩ := hdz'
  have hQ : W.Q = W.q := Q_eq_q W hs
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hxeq : Formalism.MainNotions.LiftingTheory.qp W ^ K • w = (U : LetA O n) ^ K • (W.Q ^ K • w) := by
    rw [hU, mul_pow, mul_smul]
  have hxN : Formalism.MainNotions.LiftingTheory.qp W ^ K • w ∈ W.N T := by
    rw [hxeq]; exact (W.N T).smul_mem _ hK
  have hxΔ : W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ K • w) = Formalism.MainNotions.LiftingTheory.qp W ^ K • w := by
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, (qp_mem_AΔ W hR) δ hδ, hwΔ]
  set x : ↥(W.N T) := ⟨Formalism.MainNotions.LiftingTheory.qp W ^ K • w, hxN⟩ with hxdef
  have hγx : W.γD T δ (x : W.DD T) ∈ W.N T := by rw [hxdef]; simp only; rw [hxΔ]; exact hxN
  have h1 : W.levN T c ζ x = resc χ (W.levN T c ζ' x) := by
    funext k
    simp only [resc]
    have hxx : (⟨W.γD T δ (x : W.DD T), hγx⟩ : ↥(W.N T)) = x := Subtype.ext hxΔ
    rw [← hΔN x hγx k, hxx]
  have hsplit : x = (U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T)) := Subtype.ext hxeq
  have h2 : ∀ (z : LL) (uz : PowerSeries LL) (dd : ℤ → T.V ⊗[Qp] BdR) (mm : ℤ), LB mm dd →
      W.levN T c z ⟨W.Q ^ K • w, hK⟩ = smulS ((X * uz) ^ K) dd →
      W.levN T c z x = smulS ((W.lev c z (U : LetA O n) * (X * uz)) ^ K) dd := by
    intro z uz dd mm hdd e
    rw [hsplit]
    have this : W.levN T c z ((U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T))) =
        smulS (W.lev c z ((U : LetA O n) ^ K)) (W.levN T c z ⟨W.Q ^ K • w, hK⟩) :=
      funext fun k => W.levN_smul T c z ((U : LetA O n) ^ K) ⟨W.Q ^ K • w, hK⟩ k
    rw [this, e, ← smulS_mul hdd, map_pow, ← mul_pow]
  have hz := h2 ζ u dz m hm ez
  have hz' := h2 ζ' u' dz' m' hm' ez'
  have hresc : PowerSeries.rescale χ (W.lev c ζ' (U : LetA O n) * (X * u')) =
      W.lev c ζ (U : LetA O n) * (X * u) := by
    have e1 : W.lev c ζ' (U : LetA O n) * (X * u') = W.lev c ζ' (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu']
    have e2 : W.lev c ζ (U : LetA O n) * (X * u) = W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu]
    rw [e1, e2, ← hΔA, (qp_mem_AΔ W hR) δ hδ]
  rw [h1, hz', ← smulS_rescale hm' χ hχ0, map_pow, hresc] at hz
  have hUc : constantCoeff (W.lev c ζ (U : LetA O n) * u) ≠ 0 := by
    rw [map_mul]
    refine mul_ne_zero ?_ hu0
    have hu1 : IsUnit (W.lev c ζ (U : LetA O n)) := (Units.isUnit U).map _
    exact (PowerSeries.isUnit_iff_constantCoeff.1 hu1).ne_zero
  have e3 : W.lev c ζ (U : LetA O n) * (X * u) = X * (W.lev c ζ (U : LetA O n) * u) := by ring
  rw [e3] at hz
  exact div_unique (m := min m m') (LB_mono hm (min_le_left _ _))
    (LB_mono (LB_resc hm' χ) (min_le_right _ _)) _ hUc K hz.symm

end Trans

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Fin

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F] [Algebra ℤ_[PD.p] O]

theorem evAt_γ (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O)) (a : ZMod n) (s : ℕ)
    (g : W.Gam) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ (W.γA g x) = evAt hlm F a s (powR F PD.p s (redU PD.p s (z g)) ζ) x := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have h0 := (W.γ₀_X g).1
  have h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) := by
    rw [(W.γ₀_X g).2, hz g]
  have hbs := Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W)
    (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1
  set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA
  have hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  rw [evAt_apply, evAt_apply]
  have e1 : (W.γA g x) a = W.γ₀ g (x a) := rfl
  have huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1 := by
    have e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1 := by
      rw [← hbs]; ring
    rw [e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]
  rw [e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0,
    evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]
  exact evR_congr PD.p (s + 1) hlm hyA _ rfl _


omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert (redU PD.p s (z W.gam))
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ := by
  obtain ⟨z0, hz0, hv⟩ := hγz
  have hzg : z W.gam = z0 := Units.ext (hZinj (by rw [hz, hz0]))
  have hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at hv; exact zero_ne_one hv
  have hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])
    rwa [pow_one] at this
  have hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2} := by
    intro h
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h
    rw [hv] at this; omega
  have htop := hGen PD.p hp2 s z0 hu1 hu2

  have hl2 := hpF.out.two_le
  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = PD.p - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

  have hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1 := by
    intro δ
    apply Units.ext
    apply hZinj
    rw [Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow,
      hexp δ δ.2, map_one]
    simp
  let zΔ : ↥W.DelF → DeltaT PD.p := fun δ => ⟨z δ, hzΔ δ⟩
  have hinj : Function.Injective zΔ := by
    intro δ δ' h
    have h1 : z δ = z δ' := congrArg Subtype.val h
    have h2 : W.χΓ δ = W.χΓ δ' := Units.ext (by rw [← hz, ← hz, h1])
    exact Subtype.ext (W.χΓ_inj h2)
  haveI : NeZero (PD.p - 1) := ⟨by omega⟩
  let e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p]) :=
    Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm
  haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm
  have hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF := by
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hcard]
    exact card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  rw [eq_top_iff, ← htop]
  apply Subgroup.closure_mono
  intro u hu
  rcases Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩
  · exact Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))
  · obtain ⟨δ, hδ⟩ := hsurj d
    refine Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩
    show redU PD.p s (z δ) = redU PD.p s d.1
    rw [← hδ]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of' (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert ((fun g => redU PD.p s (z g)) W.gam)
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ :=
  gen_of W z hz hZinj hγz hcard hp2 hGen s

def levBasics_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsAlgClosed F] [CharZero F]
    (hinjF : Function.Injective (algebraMap O F))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hχ : ∀ g : W.Gam, ∃ z : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (a : ZMod n) (s : ℕ) :
    LevBasics W a s where
  F := F
  fF := inferInstance
  algOF := inferInstance
  inj := hinjF
  hp := Nat.cast_ne_zero.2 hpF.out.ne_zero
  root := exists_prim _ (pow_pos hpF.out.pos _)
  ev := evAt hlm F a s
  ev_O ζ x := by
    rw [evAt_apply]
    exact (evR PD.p (s + 1) hlm (rs_root F s ζ)).commutes x
  ev_letE ζ := by
    rw [evAt_apply]
    simp [letE]
  ev_π ζ := by
    rw [evAt_apply]
    exact evR_X PD.p (s + 1) hlm (rs_root F s ζ)
  ev_ps ζ := (evAt_ps_iff W hlm F hR a s s ζ).2 rfl
  ev_pt t ht ζ := fun h => ht ((evAt_ps_iff W hlm F hR a s t ζ).1 h)
  σ g := redU PD.p s (Classical.choose (hχ g))
  ev_γ g ζ x := evAt_γ W hlm F (fun g => Classical.choose (hχ g))
    (fun g => Classical.choose_spec (hχ g)) a s g ζ x
  gen := gen_of' W (fun g => Classical.choose (hχ g)) (fun g => Classical.choose_spec (hχ g))
    hZinj hγz hcard hp2 hGen s

end Fin

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
