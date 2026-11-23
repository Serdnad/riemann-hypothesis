module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCongruenceLift
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle019
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle020
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LeValOneAddPowSub
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulEqZeroOfAevalProd
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.StepOneGG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

@[expose] public section

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

theorem arc_length_three_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam)) :
    ∃ (y₁ : W.DD T₁) (σ₁ : ℕ), ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) ∧
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ' : ℕ,
        InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ κ' • g • (lA W ^ (size (c - 1) + κ) • W.map F y₁ -
          lA W ^ (σ₁ + E + (arcOf b w S η up size).σ PD.p + size (c - 2) + S) • ((W.φD T₂) ^ 3) Hh)) := by
  obtain ⟨d, b₁, sol₁, c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, hb₁, hz₁, hn₁c, hR₀, hR₁, hσ₁, hyy, hX₁e, hX₁, hx₁, hγX, hy₁, hZ, hrel⟩ :=
    arc_length_three_build_first_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap
  obtain ⟨hI, hFc⟩ := arc_length_three_gamma_first_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap R₀ σ₁ κ₁ X₁ x₁ y₁ Z hR₀ hR₁ hX₁ hx₁ hγX hy₁ hZ hrel
  obtain ⟨g, hg, κ', hcong⟩ := arc_length_three_congruence_lift W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hP5 Cb hCb halt hsm hlen hD hOK hσ hy lam hlam hlamγ κ Hh hHh h4a n₁ E hn₁ hmap d b₁ sol₁ c₀ z₁ R₀ σ₁ κ₁ yy X₁ x₁ y₁ Z hb₁ hz₁ hn₁c hR₀ hR₁ hyy hX₁e hX₁ hx₁ hγX hy₁ hZ hrel
  exact ⟨y₁, σ₁, hσ₁, hy₁, hI, hFc, g, hg, κ', hcong⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

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

theorem section_in_ideal_of_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (he : 1 ≤ e) {d : ℕ} (b : Fin d → W.DD T)
    (h : Fin d → W.EE)
    (hlev : ∀ s < e, ∃ κ : ℕ, SecIn W a e
      (fun α c₀ => dvO W T e b c₀ ∈ FilS W T a s (-(α s))) (fun k => lE W κ * h k))
    (hlow : ∀ t < e, ∃ U : ℤ, ∀ u ≤ U, ∀ c₀ : Fin d → O, dvO W T e b c₀ ∈ FilS W T a t u) :
    ∃ κ : ℕ, SecIn W a e (condNN W T a e b) (fun k => lE W κ * h k) := by
  have hlev' : ∀ s : ℕ, ∃ κ : ℕ, ∃ I : ℕ, ∃ g : Fin I → W.EE, ∃ c₀ : Fin I → Fin d → O,
      ∃ α : Fin I → ℕ → ℤ, s < e →
        (∀ i, InId W a e (α i) (g i) ∧ dvO W T e b (c₀ i) ∈ FilS W T a s (-(α i s))) ∧
        ∀ k, lE W κ * h k = ∑ i, g i * algebraMap O W.EE (c₀ i k) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨κ, I, g, c₀, α, h1, h2⟩ := hlev s hs
      exact ⟨κ, I, g, c₀, α, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun h' => absurd h' hs⟩
  choose κs I g c₀ α hsec using hlev'
  have hlow' : ∀ t : ℕ, ∃ U : ℤ, t < e → ∀ u ≤ U, ∀ c : Fin d → O, dvO W T e b c ∈ FilS W T a t u := by
    intro t
    by_cases ht : t < e
    · obtain ⟨U, hU⟩ := hlow t ht
      exact ⟨U, fun _ => hU⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose U hU using hlow'
  set N : ℕ := ∑ s ∈ Finset.range e, ∑ i : Fin (I s), ∑ t ∈ Finset.range e,
    ((U t).natAbs + (α s i t).natAbs) with hN
  set κ : ℕ := ∑ s ∈ Finset.range e, κs s with hκ
  obtain ⟨m, ε, -, hεd, hsum⟩ :=
    exists_partition_of_l_pow_levels W hC N (Finset.range e) ⟨0, Finset.mem_range.2 (by omega)⟩
  choose! r hr hεr using hεd
  have hlE : ∀ j, lE W j = algebraMap (LetA O n) W.EE (lA W ^ j) := by
    intro j; simp [lE, lA]
  have hκs : ∀ s < e, κs s ≤ κ := fun s hs =>
    Finset.single_le_sum (f := κs) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  let σ := Σ s : Fin e, Fin (I s)
  let eqv := Fintype.equivFin σ
  let G' : σ → W.EE := fun p => algebraMap (LetA O n) W.EE
    ((∏ t ∈ (Finset.range e).erase (p.1 : ℕ), ps W t ^ N) * (r p.1 * lA W ^ (κ - κs p.1))) * g p.1 p.2
  let C' : σ → Fin d → O := fun p => c₀ p.1 p.2
  let A' : σ → ℕ → ℤ := fun p t => if t = (p.1 : ℕ) then α p.1 p.2 t else α p.1 p.2 t + N
  have hmono : ∀ p : σ, InId W a e (A' p) (G' p) ∧ condNN W T a e b (A' p) (C' p) := by
    rintro ⟨⟨s, hs⟩, i⟩
    have hx : r s * lA W ^ (κ - κs s) ∈ W.AΔ :=
      W.AΔ.mul_mem (hr s (Finset.mem_range.2 hs)) (l_pow_mem_invariants W _)
    refine ⟨inId_shift_levels W hR hs ((hsec s hs).1 i).1 hx, fun t ht => ?_⟩
    by_cases hts : t = s
    · subst hts
      simp only [A', if_true]
      exact ((hsec t hs).1 i).2
    · simp only [A', hts, if_false]
      refine hU t ht _ ?_ _
      have h1 : (U t).natAbs + (α s i t).natAbs ≤
          ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) :=
        Finset.single_le_sum (f := fun t' => (U t').natAbs + (α s i t').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 ht)
      have h2 : ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) ≤
          ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) :=
        Finset.single_le_sum (f := fun i' => ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 : ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) ≤ N :=
        Finset.single_le_sum (f := fun s' => ∑ i' : Fin (I s'), ∑ t' ∈ Finset.range e,
          ((U t').natAbs + (α s' i' t').natAbs)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
      have hN' : (((U t).natAbs : ℕ) : ℤ) + (((α s i t).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast h1.trans (h2.trans h3)
      rw [Int.natCast_natAbs, Int.natCast_natAbs] at hN'
      have e1 := neg_abs_le (U t)
      have e2 := neg_abs_le (α s i t)
      linarith
  refine ⟨m + κ, Fintype.card σ, fun j => G' (eqv.symm j), fun j => C' (eqv.symm j),
    fun j => A' (eqv.symm j), fun j => hmono (eqv.symm j), fun k => ?_⟩
  rw [Equiv.sum_comp eqv.symm (fun p => G' p * algebraMap O W.EE (C' p k)), Fintype.sum_sigma]
  calc lE W (m + κ) * h k
      = (∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s)) * (lE W κ * h k) := by

        rw [← map_sum, hsum, ← hlE, lE, lE, lE, pow_add]; ring
    _ = ∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : lE W κ = lE W (κ - κs s) * lE W (κs s) := by
          rw [lE, lE, lE, ← pow_add, Nat.sub_add_cancel (hκs s (Finset.mem_range.1 hs))]
        rw [this]; ring
    _ = ∑ s : Fin e, ∑ i : Fin (I s), G' ⟨s, i⟩ * algebraMap O W.EE (C' ⟨s, i⟩ k) := by
        rw [Finset.sum_range (fun s => algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k))]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [(hsec s s.2).2 k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [G', C']
        rw [hεr s (Finset.mem_range.2 s.2), hlE]
        simp only [map_mul]
        ring

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

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem LiftsAt.liftsAt_mono {f : W.EE} {e e' : ℕ} (he : e ≤ e') (h : LiftsAt W A F c b sol k₀ f e) :
    LiftsAt W A F c b sol k₀ f e' :=
  LiftsAtT.mono W A F c b sol k₀ he h

theorem LiftsAt.add_proof {f f' : W.EE} {e : ℕ} (h : LiftsAt W A F c b sol k₀ f e)
    (h' : LiftsAt W A F c b sol k₀ f' e) : LiftsAt W A F c b sol k₀ (f + f') e :=
  LiftsAtT.add W A F c b sol k₀ h h'

theorem liftsAt_thick_letter_type [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAt W A F c b sol k₀ f (rr + A.σ PD.p) :=
  N_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂
    hsur rr hrr hb hk₀ f hf hdown

theorem liftsAt_constants_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAt W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) :=
  constants_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL
    hW₁ hW₂ hsur rr hrr hb hk₀ b₁ sol₁ hb₁ c₁ hpr x

theorem liftsAt_thin_letter_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAt W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  C_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hW₁ hW₂ hb Si hSi
    b₁ sol₁ hb₁ c₁ s₀ hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem existsLiftMapEqPrimePowSmul (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (i : ZMod n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)

    (Ai ri : ℕ) (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))

    (bi S η : ℕ) (hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ i ((Set.Icc (bi : ℤ) (bi + S)) ∪ Set.Icc (-(η : ℤ)) η))
    (hb : 2 * (Ai + ri) + η + 1 ≤ bi)

    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))

    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))

    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))

    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (hgN₂ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧ W.γ T₂ x - x = W.π₀ • y)

    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)

    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) y))

    (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (lam : W.DD T₂)

    (hH1 : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (s • lam))
    (hH2 : ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ (Ai + ri)) • y) :
    ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x₁ ∧
      W.map F x₁ = (((PD.p : ℕ) : LetA O n) ^ EG PD.p (Ai + ri) S η bi) • (s • lam) := by
  classical
  have : Fact (PD.p).Prime := ⟨PD.hp⟩
  have : IsDomain O := Function.Injective.isDomain (algebraMap O LL) hinj
  obtain ⟨hπ, -, -⟩ := lemG_units W hcase hP9 hc₁ hO hOv hinj

  have hdM : imgSub W F i ≤ (imgSub W F i).comap dop₂ := fun z hz =>
    dop_inImg W hπ F i dop₁ hd₁ dop₂ hd₂ hgN₁ hz
  have hpow : ∀ (k : ℕ) (z : W.DD T₂), (((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ^ k)
      ((imgSub W F i).mkQ z) = (imgSub W F i).mkQ ((dop₂ ^ k) z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        show ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ((imgSub W F i).mkQ z) =
          (imgSub W F i).mkQ (dop₂ z) from rfl, ih]
  have haev : ∀ (p : O[X]) (z : W.DD T₂),
      aeval ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) p ((imgSub W F i).mkQ z) =
        (imgSub W F i).mkQ (aeval dop₂ p z) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro z; rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add (f := _)]
    | monomial k c =>
      intro z
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, hpow,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

  suffices hmain : InImg W F i ((((PD.p : ℕ) : O) ^ EG PD.p (Ai + ri) S η bi) • (s • lam)) by
    obtain ⟨x₁, h1, h2⟩ := hmain
    refine ⟨x₁, h1, ?_⟩
    rw [h2, ← algebraMap_smul (LetA O n), map_pow, map_natCast]
  rcases Nat.eq_zero_or_pos (Ai + ri) with ha0 | ha
  · have h := q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hH1
    rw [ha0, pow_zero, one_smul] at h
    exact inImg_smulO W F i _ h
  · have h₁ := step_i W hcase hP9 i F hc₁ hO hOv Ai ri hA hr bi (by omega) hgpi0 hA3 hA4 hl0 hinj hgN₁ hgN₂
      dop₁ hd₁ dop₂ hd₂ cc hcc s s' hs' hs lam hH1 hH2
    have h₂ := step_ii W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr dop₁ hd₁ dop₂ hd₂ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) hCONS hH1
    have hu : v (algebraMap O LL ((W.χΓ W.gam : Oˣ) : O) - 1) = 1 := by
      rw [W.gam_gen, hcase.2.1, Nat.cast_one]
    have hcA := cc_assoc v PD.p hcase.2.2 W.v_l hO hOv hinj (W.χΓ W.gam) hu cc hcc
    have hS₂ : TruncationIndexSet bi S η (Ai + ri) ⊆
        Finset.Icc ((bi : ℤ) + 1) ((bi : ℤ) + S + (Ai + ri : ℕ)) ∪
          Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + (Ai + ri : ℕ)) := by
      intro y hy
      simp only [TruncationIndexSet, winU, Finset.mem_image, Finset.mem_product, Finset.mem_union, Finset.mem_Icc] at hy
      obtain ⟨⟨u, j⟩, ⟨hu | hu, hj⟩, rfl⟩ := hy
      · simp only [Finset.mem_union, Finset.mem_Icc]; left; push_cast; omega
      · simp only [Finset.mem_union, Finset.mem_Icc]; right; push_cast; omega
    have hE : ⌊(((3 * (Ai + ri) + S + 2 * η : ℕ) : ℝ) - 2) / ((PD.p : ℝ) - 1) +
        Real.logb PD.p ((bi : ℝ) + η - 1)⌋₊ ≤ EG PD.p (Ai + ri) S η bi := by
      unfold EG; push_cast; exact le_rfl
    have key := lemmaG_lagr PD.p ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) cc hl0 hcA
      (Ai + ri) S η bi (EG PD.p (Ai + ri) S η bi) ha hb (TruncationIndexSet bi S η (Ai + ri)) hS₂
      ((imgSub W F i).mkQ (s • lam))
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₁)
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₂) hE
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key
    exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
