module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle012
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentBoundLevelIdeal
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
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
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe

@[expose] public section

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
  {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL}

theorem RepVV_smulA {a₀ : LetA O n} (ha₀ : a₀ ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a₀ • x) (fun k => algebraMap (LetA O n) W.EE a₀ * f k) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun k => a₀ * a k, hH, fun k => ⟨W.AΔ.mul_mem ha₀ (ha k).1, ?_⟩,
    a₀ • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W ha₀ hy, ?_⟩
  · rw [map_mul, ← (ha k).2]
    ring
  · have hsum : ∑ k, (a₀ * a k) • ((W.φD T) ^ e) (Hh k) = a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [hsum]
    have e1 : lA W ^ κ' • (lA W ^ κ • Λ • a₀ • x - a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k)) =
        a₀ • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      rw [smul_comm Λ a₀ x, smul_comm (lA W ^ κ) a₀, ← smul_sub, smul_comm (lA W ^ κ') a₀]
    rw [e1, hxy, smul_comm]

theorem RepVV_smulO (o : O) {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (o • x) (fun k => algebraMap O W.EE o * f k) := by
  have h1 := RepVV_smulA W (W.AΔ.algebraMap_mem o) h
  have hx : o • x = algebraMap O (LetA O n) o • x := (algebraMap_smul (LetA O n) o x).symm
  have hf : (fun k => algebraMap O W.EE o * f k) =
      fun k => algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) o) * f k := by
    funext k
    rw [← IsScalarTower.algebraMap_apply]
  rw [hx, hf]
  exact h1

theorem RepVV_zero {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol 0 (fun _ => 0) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun _ => 0, hH, fun k => ⟨W.AΔ.zero_mem, by simp⟩,
    (0 : LetA O n) • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W W.AΔ.zero_mem hy, by simp⟩

theorem RepVV_sum (h0 : RepVV W T c' e M Λ b sol 0 (fun _ => 0)) {ι : Type} (s : Finset ι)
    (x : ι → W.DD T) (f : ι → Fin d → W.EE) (h : ∀ i ∈ s, RepVV W T c' e M Λ b sol (x i) (f i)) :
    RepVV W T c' e M Λ b sol (∑ i ∈ s, x i) (fun k => ∑ i ∈ s, f i k) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using h0) ?_
  intro j s hj ih h
  have := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.RepVV_add W (h j (Finset.mem_insert_self j s))
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  simpa [Finset.sum_insert hj] using this

theorem RepVV_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (W.γ T x) (fun k => W.γE W.gam (f k)) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  obtain ⟨R, hR, R', hR', hRR', hΛR⟩ := hΛ
  obtain ⟨u, hu, hu'⟩ := hpi0
  obtain ⟨u₂, hu₂, hM'⟩ := hM
  have hγH : ∀ k, ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W T c' z ∧ W.γ T (Hh k) = Hh k + W.π₀ ^ M • z := by
    intro k
    obtain ⟨yy, hyy, hHk⟩ := hH k
    obtain ⟨z, hz, hzeq⟩ := (hb.2 k).1 M κ yy hyy
    refine ⟨z, hz, ?_⟩
    rw [hHk]
    rw [smul_zero, sub_zero, sub_eq_iff_eq_add] at hzeq
    rw [hzeq, add_comm]
  choose z hz hγz using hγH
  have hZ : ∑ k, W.γA W.gam (a k) • ((W.φA ^ e) (W.π₀ ^ M) • ((W.φD T) ^ e) (z k)) =
      (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, hM', smul_smul, smul_smul]
    congr 1
    ring
  have h1 := congrArg (W.γ T) hxy

  simp only [γ_smul W, map_sub, map_sum, γA_lA W, γ_φpow W, hγz, map_add (f := _), φpow_smulA W, smul_add,
  Finset.sum_add_distrib, hΛR] at h1
  rw [hZ, map_mul, map_pow, hu', hΛR] at h1
  have hlA : lA W ∈ W.AΔ := by
    unfold lA
    exact W.AΔ.natCast_mem _
  refine ⟨κ, κ', Hh, fun k => R' * W.γA W.gam (a k), hH,
    fun k => ⟨W.AΔ.mul_mem hR' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1), ?_⟩,
    (R' * u * R ^ 2) • W.γ T y + lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k),
    AddSubgroup.add_mem _
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem hR' hu) (W.AΔ.pow_mem hR 2))
        (γ_Pp W hT hP2 hy))
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.pow_mem hlA κ')
        (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W hR' (AddSubgroup.sum_mem _ fun k _ =>
          Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1) hu₂)
            (AddSubgroup.subset_closure ⟨1, W.AΔ.one_mem, z k, hz k, (one_smul _ _).symm⟩)))), ?_⟩
  · have h2 := congrArg (W.γE W.gam) (ha k).2
    rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, hΛR, map_mul] at h2
    have h3 : algebraMap (LetA O n) W.EE R' * algebraMap (LetA O n) W.EE R = 1 := by
      rw [← map_mul, mul_comm, hRR', map_one]
    rw [map_mul, ← h2]
    linear_combination (-(algebraMap (LetA O n) W.EE Λ * W.γE W.gam (f k))) * h3
  · have hsH : ∑ k, (R' * W.γA W.gam (a k)) • ((W.φD T) ^ e) (Hh k) =
        R' • ∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    have hΛ1 : lA W ^ κ • Λ • W.γ T x = lA W ^ κ • ((R' * R) * Λ) • W.γ T x := by
      rw [mul_comm R' R, hRR', one_mul]
    rw [hsH, hΛ1]
    calc _ = R' • (lA W ^ κ' • (lA W ^ κ • (R * Λ) • W.γ T x -
            (∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) +
              (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)))) +
          (W.π₀ * Λ ^ 2) • (lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)) := by
          simp only [smul_sub, smul_add, smul_smul]
          ring_nf
          abel
      _ = _ := by
          rw [h1]
          simp only [smul_add, smul_smul]
          ring_nf

theorem RepVV_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (i : ℕ) :
    RepVV W T c' e M Λ b sol ((W.γ T)^[i] x) (fun k => (W.γE W.gam)^[i] (f k)) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have := RepVV_γ W hT hP2 hpi0 hb hΛ hM ih
    simpa [Function.iterate_succ_apply'] using this

theorem RepVV_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (P : Polynomial O) :
    RepVV W T c' e M Λ b sol (Polynomial.aeval (W.γ T) P x)
      (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) := by
  rw [aeval_eq W P x]
  have hf : (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) =
      fun k => ∑ i ∈ Finset.range (P.natDegree + 1),
        algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k) := by
    funext k
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Module.End.pow_apply, Algebra.smul_def]
    rfl
  rw [hf]
  exact RepVV_sum W (RepVV_zero W h) _ _ (fun i k => algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k))
    fun i _ => RepVV_smulO W (P.coeff i) (RepVV_iter W hT hP2 hpi0 hb hΛ hM h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
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

theorem arc_length_four_denominator [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (κ : ℕ) (x : O)
    (hx : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ s : ℕ, (s : ℝ) ≤ max 1 ((size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p + 16 / 5 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) + 1 ∧
      ((PD.p : ℕ) : O) ^ κ ∣ ((PD.p : ℕ) : O) ^ s * x := by
  obtain ⟨hp11, hset, h20w, h20η, -, -⟩ := hB
  obtain ⟨-, -, hη, -, -, hsz, -⟩ := hset
  have hl3 : (arcOf b w S η up size).len c = 3 := hlen
  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : ({d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} : Set ℕ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Nat.sInf_empty] at hlen'
    omega
  have hT2 : ¬ TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have hm := Nat.sInf_mem hne
    rw [hlen'] at hm
    have hm' : 1 ≤ 3 ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - ((3 : ℕ) : ZMod n) + 1) := hm
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rw [e] at hm'
    exact hm'.2
  have hT0 : TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra hnt
    have hmem : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨le_refl 1, ?_⟩
      simpa using hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hT1 : TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hnt
    have hmem : (2 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨by norm_num, ?_⟩
      have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
      rw [e]
      exact hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hu1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    rw [show c - 2 + 1 = c - 1 by ring, hU] at h
    simpa using h
  have hu0 : up c = true := by
    have h := (halt (c - 1)).1
    rw [sub_add_cancel, hu1] at h
    simpa using h
  have hh : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c, hT0⟩]
  obtain ⟨s₁, hs1, hs1le, hsB, hnot⟩ := exists_s1_bound_choice PD.p b w S η (size c) (size (c - 1))
    (size (c - 2)) hp11 (Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (by unfold Formalism.MainNotions.N.Ln17.Sg; rw [hh]) hsm h20w h20η
    (by have := hη (c - 2); omega) (hsz (c - 2) hT2) hT1.1 hT0.2
  refine ⟨s₁, hs1le, ?_⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₂ hW₂.1 hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hps : ∀ s, ps W s = (fun _ => Br.ι (Br.P.p s) : LetA O n) := by
    intro s
    induction s with
    | zero =>
      funext i
      simp [ps, qA, LocWach.π₀, lA, PhiData.p, Br.ι_X]
    | succ s ih =>
      have e : ps W (s + 1) = W.φA (ps W s) := by
        simp only [ps, pow_succ', AlgHom.mul_apply]
      rw [e, ih]
      funext i
      simp [LocWach.φA, letφ, PhiData.p, Function.iterate_succ_apply', Br.ι_φ]
  have hpsc : ∀ s, Br.ι (Br.P.p s) = ps W s c := fun s => by rw [hps s]
  have hX : Br.ι PowerSeries.X = ps W 0 c := hpsc 0
  have hCι : ∀ a : O, Br.ι (PowerSeries.C a) = PowerSeries.C a := fun a => Br.ι.commutes a
  have hN : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hl3]
    simp [Finset.prod_range_succ, arcOf, hu0, hu1, hU]
  have hf1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c) f := by
    unfold InFF at hf
    exact hf.1
  obtain ⟨u₀, hu₀, h0⟩ := hf1
  obtain ⟨u, hu, h1⟩ := hx
  have key : algebraMap (LetA O n) W.EE (letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u)) = 0 := by
    have hx' : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) :=
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE x
    have hl : lE W κ = ((PD.p : ℕ) : W.EE) ^ κ := rfl
    rw [hx', hl] at h1
    simp only [map_sub, map_mul, map_pow, map_natCast, map_one] at h0 h1 ⊢
    linear_combination h1 - ((PD.p : ℕ) : W.EE) ^ κ * h0
  have key2 : letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u) = 0 := W.EE_inj (key.trans (map_zero _).symm)
  have key3 := congrFun key2 c
  rw [hN] at key3
  simp only [letE, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply,
    Pi.single_eq_same, one_mul, Pi.algebraMap_apply] at key3
  have hAC : algebraMap O (PowerSeries O) x = PowerSeries.C x := rfl
  try rw [hAC] at key3
  haveI : Fact (Nat.Prime PD.p) := ⟨PD.hp⟩
  obtain ⟨U₁, hU₁⟩ := Br.range u₀ hu₀ c
  obtain ⟨U₂, hU₂⟩ := Br.range u hu c
  refine den_of_rel Br.P hϖ (D := Br.P.p 2 ^ size (c - 2) * PowerSeries.X ^ size c)
    (U₁ := U₁) (U₂ := U₂) (B := size (c - 1) + S) (s₁ := s₁) ?_ ?_
  · apply Br.inj
    simp only [map_mul, map_sub, map_pow, map_one, mul_one, hCι, map_natCast]
    rw [hX, hpsc 2, hpsc 1, ← hU₁, ← hU₂]
    linear_combination -key3
  · intro hmem
    exact hnot (content_bound_level_ideal (P := Br.P) hϖ (size (c - 2)) (size c) (size (c - 1) + S) s₁
      (by have := hη (c - 2); omega) hs1 hsB hmem)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
