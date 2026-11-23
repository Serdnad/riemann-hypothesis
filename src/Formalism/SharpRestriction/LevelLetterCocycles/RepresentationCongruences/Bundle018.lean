module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeRepresentationOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulOMem
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
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

theorem arc_length_three_representation [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh))) :
    (∃ a₀ ∈ W.AΔ, algebraMap (LetA O n) W.EE (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) * f₂ = algebraMap (LetA O n) W.EE a₀) ∧
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1 (W.φD T₂ lam) ∧
      RepVV W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) ((arcOf b w S η up size).M PD.p) (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) bb sol (f₂ • W.φD T₂ lam)
        (fun k => if k = k₀ then lE W ((arcOf b w S η up size).σ PD.p) * f₂ else 0) :=
  arc_length_three_representation_of W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj
    hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb
    halt hsm hlen hD hOK hσ hy f₂ hf₂ lam hlam hlamγ κ Hh hHh h4a

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

theorem arc_length_three_build_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∃ (d : ℕ) (b₁ : Fin d → W.DD T₁) (sol₁ : Fin d → ℕ → Fin d → LL) (c₀ : Fin d → O) (z₁ : W.DD T₁)
      (R₀ σ₁ κ₁ : ℕ) (yy : ℕ → Fin d → O) (X₁ x₁ y₁ Z : W.DD T₁),
      IsHor W T₁ (c - 1) b₁ sol₁ ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) z₁ ∧ n₁ = Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ c₀ + W.π₀ • z₁ ∧
      size c + S ≤ (PD.p - 1) * R₀ ∧ 1 ≤ R₀ ∧ ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      (∀ r < R₀, ∀ m, algebraMap O LL (yy r m) = (PD.p : LL) ^ κ₁ * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m) ∧
      X₁ = ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₁ b₁ (yy r) ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁ ∧ Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁ ∧ W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁ ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InFP W T₁ (c - 1) 1 1 Z ∧
      lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁ := by
  obtain ⟨hp11, ⟨-, -, hηs, -⟩, -⟩ := hB
  have hl5 : 5 ≤ PD.p := by omega
  have hR := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.ringData_of_caseA_of_p9 W hcase hP9
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 _ hOK T₁ hW₁ (c - 1)
  obtain ⟨c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc.build W hcase hR hH hOv hinj hW₁.1 (c - 1) b₁ sol₁ hb₁ n₁ hn₁ (size c + S)
      (by have := hηs c; omega) hl5
  exact ⟨d₁, b₁, sol₁, c₀, z₁, R₀, σ₁, κ₁, yy, X₁, x₁, y₁, Z, hb₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13⟩

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

theorem arc_length_four_cost_bound (l : ℕ) (hl : 11 ≤ l) (b wm w S η : ℕ) (hb : 1 ≤ b) (B : ℝ) (s si rr σ : ℕ)
    (hs : (s : ℝ) ≤ max 1 ((w : ℝ) - B / l + 16 / 5 * Sg l (b + η + S) wm S η) + 1)
    (hsi : (w : ℝ) - B / l - η / (l : ℝ) ^ 2 - 1 ≤ si)
    (hrr : (rr : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) (hσ : (σ : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) :
    ((rr + 3 * σ + 1 + (s - si) : ℕ) : ℝ) ≤ 18 * Sg l (b + η + S) wm S η + 1 := by
  have h4 := max_sub_le_errorScale l hl b wm w S η hb B ((s : ℝ) - 1) (si : ℝ)
    (max_le (Nat.cast_nonneg _) hsi) (by linarith)
  obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge l (b + η + S) wm S η hl (by omega)
  have hsub : ((s - si : ℕ) : ℝ) ≤ max 0 ((s : ℝ) - 1 - si) + 1 := by
    rcases le_total si s with h | h
    · rw [Nat.cast_sub h]
      have := le_max_right (0:ℝ) ((s : ℝ) - 1 - si)
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      have := le_max_left (0:ℝ) ((s : ℝ) - 1 - si)
      simp only [Nat.cast_zero]
      linarith
  push_cast
  linarith

theorem sigma_eq_of_thick_letter {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) :
    Formalism.MainNotions.N.Ln17.Sg l b w S η size = Sg l (b + η + S) w S η := by
  unfold Formalism.MainNotions.N.Ln17.Sg Sg Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  rw [if_pos hT]

namespace ArcLengthFourSecond

section EEh
variable {W : LocWach PD LL O v n}

theorem lE_eq (k : ℕ) : lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp [lE, lA, map_pow, map_natCast]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c

theorem lA_mem : lA W ∈ W.AΔ := by
  exact natCast_mem _ _

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f) (hg : InFr W a num den g) :
    InFr W a num den (f - g) := by
  obtain ⟨u, hu, hf⟩ := hf
  obtain ⟨u', hu', hg⟩ := hg
  refine ⟨u - u', sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hg, ← map_sub, mul_sub]

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (k : ℕ) (hf : InFr W a num den f) :
    InFr W a num den (lE W k * f) := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨lA W ^ k * u, mul_mem (pow_mem lA_mem k) hu, ?_⟩
  rw [lE_eq, mul_left_comm, hf, ← map_mul]
  congr 1
  ring

theorem inFr_num_left {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₂ : n₂ ∈ W.AΔ) :
    InFr W a n₁ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₂ * u, mul_mem h₂ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_num_right {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₁ : n₁ ∈ W.AΔ) :
    InFr W a n₂ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₁ * u, mul_mem h₁ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_den_mul {a : ZMod n} {num d : LetA O n} (d' : LetA O n) {f : W.EE} (hf : InFr W a num d f) (hd' : d' ∈ W.AΔ) :
    InFr W a num (d' * d) f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨d' * u, mul_mem hd' hu, ?_⟩
  rw [map_mul, mul_assoc, hf, ← map_mul]
  congr 1
  ring

end EEh

end ArcLengthFourSecond

theorem ArcLengthFourSecond.inFr_sat [IsDomain O] [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL)) {c : ZMod n} {num den : LetA O n}
    (hnum : num ∈ PiPs W) {g : W.EE} (h1 : InFr W c 1 den g) (hK : ∃ K : ℕ, InFr W c num den (lE W K * g)) :
    InFr W c num den g := by
  obtain ⟨u₀, hu₀, e₀⟩ := h1
  obtain ⟨K, u₁, hu₁, e₁⟩ := hK
  have key : lA W ^ K * (1 * (letE c * u₀)) = num * (letE c * u₁) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (lA W ^ K * (1 * (letE c * u₀)))
        = lE W K * algebraMap (LetA O n) W.EE (letE c * 1 * u₀) := by
          rw [ArcLengthFourSecond.lE_eq, ← map_mul]; congr 1; ring
      _ = algebraMap (LetA O n) W.EE den * (lE W K * g) := by rw [← e₀]; ring
      _ = _ := by rw [e₁]; congr 1; ring
  obtain ⟨y, hy, hxy⟩ := saturation_fraction_ring W hcase hP9 hinj num 1 1 hnum (one_mem _) (one_mem _) (letE c * u₀)
    (by rw [one_mul]; exact W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₀)
    ⟨K, letE c * u₁, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₁, key⟩
  refine ⟨letE c * y, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hy, ?_⟩
  rw [e₀]
  congr 1
  have hidem : (letE c : LetA O n) * letE c = letE c := by
    unfold letE; rw [← Pi.single_mul, one_mul]
  linear_combination (letE c : LetA O n) ^ 2 * hxy - (((letE c : LetA O n) + 1) * u₀) * hidem

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filtration (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

theorem filtration_exhaustive (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filtration x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

end Gen

section Cores

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem finrank_eq_one_of_bijective_bis (hb : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 :=
  (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hb).finrank_eq.symm.trans (Module.finrank_self K₀)

theorem exists_horizontal_solutions (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) : ∃ sol, IsHor W T i b sol := by
  have h3 := (hH hA T hT i).2.2.1 d b hb 0
    ⟨0, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_zero W T i, (smul_zero _).symm⟩
  choose sol hsol using fun k : Fin d => (h3 (Pi.single k 1)).1
  refine ⟨sol, hb, fun k => ⟨(hsol k).1, ?_⟩⟩
  rw [(hsol k).2]
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [h]

theorem horizontal_frame_structure (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W := by
  intro hCA _ A _ T hT c
  have hmod := ((hP9 T hT.1 hCA.2.1 hCA.2.2).2.2 (finrank_eq_one_of_bijective_bis hCA.1)).2
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T c hmod
  obtain ⟨sol, hsol⟩ := exists_horizontal_solutions W hH hCA T hT.1 c b hb
  exact ⟨d, b, sol, hsol⟩

theorem exists_algHom_over_of_bijective_algebraMap (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

theorem frobenius_vector_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem frobenius_vector_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, frobenius_vector_succ, ih, pow_succ', Module.End.mul_apply]

theorem frobenius_vector_mem_dcris (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

theorem filtration_succ_of_not_jump (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

theorem filtration_up_to_jumps (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb i x) (hsurj : Function.Surjective (algebraMap K₀ K))
    {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb i)) (u : ℤ) (hx : x ∈ FilCris PD T.ρ u) :
    ∀ k : ℕ, (∀ a, IsJumpV PD T.ρ τ a → u ≤ a → u + k ≤ a) → x ∈ FilCris PD T.ρ (u + k) := by
  intro k
  induction k with
  | zero => intro _; simpa using hx
  | succ k ih =>
    intro hj
    have h1 := ih fun a ha hua => by have := hj a ha hua; push_cast at this; omega
    have := filtration_succ_of_not_jump W T i τ hover hsurj (u + k)
      (fun hja => by have := hj _ hja (by omega); push_cast at this; omega) hxD h1
    push_cast; rwa [← add_assoc]

theorem filtration_below_jumps (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb i x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (u : ℤ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → u ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb i)) : x ∈ FilCris PD T.ρ u := by
  obtain ⟨u₀, hu₀⟩ := filtration_exhaustive (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : u ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have := filtration_up_to_jumps W T i τ hover hsurj hxD u₀ hx0 (u - u₀).toNat
      (fun a ha _ => by have := hJ a ha; omega)
    rwa [show u₀ + ((u - u₀).toNat : ℤ) = u by omega] at this

theorem arc_filtration_low : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W := by
  intro hCA _ A hA c _ e _ _ T hT d b sol hb c₀ s hs
  have hbf := hb.1
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  have hi : i = c' + ((e - s : ℕ) : ZMod n) := by rw [hidef]; push_cast [Nat.cast_sub hs.le]; ring
  obtain ⟨τ, hτ, hover⟩ := exists_algHom_over_of_bijective_algebraMap W hCA.1 i
  have hyD : dvO W T (e - s) b c₀ ∈ DcrisL PD T.ρ (W.emb i) := by
    rw [hi]; exact frobenius_vector_mem_dcris W T c' b hbf (e - s) c₀
  have hye : ((φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T (e - s) b c₀) = dvO W T e b c₀ := by
    rw [← frobenius_vector_add, Nat.sub_add_cancel hs.le]
  refine ⟨fun u hu => ?_, fun bs hty hmem => ?_⟩
  · have hJ : ∀ a, IsJumpV PD T.ρ τ a → u ≤ a := fun a ha => hu a (hT.2 i τ hτ a ha)
    exact ⟨_, ⟨filtration_below_jumps W T i τ hover hCA.1.2 u hJ hyD, hyD⟩, hye⟩
  · obtain ⟨y, ⟨hyF, hyD'⟩, hye'⟩ := hmem
    have hok : A.η < bs := by have := hA.2.2.2.2.1 i; rw [hty] at this; exact this
    have hup := filtration_up_to_jumps W T i τ hover hCA.1.2 hyD' _ hyF (bs - (A.η + 1))
      (fun a ha hua => by
        have hw := hT.2 i τ hτ a ha
        rw [hty] at hw
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
        omega)
    rw [show (A.η : ℤ) + 1 + ((bs - (A.η + 1) : ℕ) : ℤ) = (bs : ℤ) by omega] at hup
    exact ⟨y, ⟨hup, hyD'⟩, hye'⟩

end Cores

end Formalism.MainNotions.N.Ln17
end
end
