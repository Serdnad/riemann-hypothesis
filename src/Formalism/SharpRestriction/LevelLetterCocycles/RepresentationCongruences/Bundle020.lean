module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCrystalline
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
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Std.Tactic.BVDecide.Normalize.Prop

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

theorem arc_length_three_gamma_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam))
    (R₀ σ₁ κ₁ : ℕ) (X₁ x₁ y₁ Z : W.DD T₁) (hR₀ : size c + S ≤ (PD.p - 1) * R₀) (hR₁ : 1 ≤ R₀)
    (hX₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁) (hx₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁)
    (hγX : W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁) (hy₁ : InFP W T₁ (c - 1) 1 1 y₁) (hZ : InFP W T₁ (c - 1) 1 1 Z)
    (hrel : lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁) :
    InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) := by
  have hT : IsCrys PD T₁.ρ := hW₁.1
  have hR : GS.RD W := NTB.ringData_of_crystalline W hcase hP9 T₁ hT
  obtain ⟨y, hyP, hyy⟩ := hy₁
  rw [one_smul] at hyy
  subst hyy
  obtain ⟨Zp, hZP, hZZ⟩ := hZ
  rw [one_smul] at hZZ
  subst hZZ
  have hLD := DYB.Pp_le_HLD W T₁ (c - 1) hyP
  rw [sub_add_cancel] at hLD

  have hup : up c = false := by
    have h1 := (halt (c - 2)).1
    have h2 := (halt (c - 1)).1
    have e1 : c - 2 + 1 = c - 1 := by ring
    rw [e1, hD] at h1
    rw [sub_add_cancel] at h2
    cases hc1 : up (c - 1) <;> simp_all

  have hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₁ (fun i => if up i then η else size i + S)
      (fun i => if up i then size i + S else η) := by
    intro τ i hτ a ha
    have h := hW₁.2 i τ hτ a ha
    have hok := hOK.2.2.2.2.1 i
    simp only [arcOf] at h hok
    cases hi : up i <;> simp [hi, Formalism.MainNotions.LocalTheoryWindows.LT.win, Formalism.MainNotions.LocalTheoryWindows.LT.ok] at h hok ⊢ <;> omega
  have h5 := (hP5 T₁ _ _ hT hJL).1 c
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h5
  have hring := ((hP9 T₁ hT hcase.2.1 hcase.2.2).2.2 (NTB.finrank_one W hcase)).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    have hQq : W.Q = W.q := by
      unfold LocWach.Q
      rw [hcase.2.1]
      simp
    rw [hQq, hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x → qA W ^ (size c + S) • W.φD T₁ x ∈ W.N T₁ := by
    intro x hx
    have h := h5 x hx.2
    rw [hQ, mul_pow, mul_smul] at h
    have h' := (W.N T₁).smul_mem (((wq⁻¹ : (LetA O n)ˣ) : LetA O n) ^ (size c + S)) h
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h'

  have hγP : W.γ T₁ y₁ - y₁ ∈ Pp W T₁ (c - 1) 1 := sub_mem (DYB.Pp_γ W T₁ (c - 1) hyP) hyP
  obtain ⟨w, hwΔ, hwφ⟩ := NTB.w_mem hR
  obtain ⟨u, huΔ, hγπ⟩ := GS.gamma_pi0_eq_pi0_mul_unit hR
  obtain ⟨r, rfl⟩ : ∃ r, R₀ = r + 1 := ⟨R₀ - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, (PD.p - 1) * (r + 1) = (size c + S) + t := ⟨_, (Nat.add_sub_of_le hR₀).symm⟩
  have hπΔ := GS.π₀_mem W
  have hqΔ := GS.qA_mem W
  have hlΔ : lA W ∈ W.AΔ := NTB.lA_mem'
  have ha₁ : lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlΔ _) (W.AΔ.pow_mem hwΔ _))
      (W.AΔ.pow_mem hπΔ _)) (W.AΔ.pow_mem hqΔ _)
  have hu' : (1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S) ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hqΔ))
      (W.AΔ.pow_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hπΔ)) _)
  have hbrP : (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
      (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z - Z) ∈
      Pp W T₁ (c - 1) 1 := by
    refine sub_mem (AddSubgroup.subset_closure ⟨_, ha₁, x₁, hx₁, by rw [pow_one]⟩)
      (sub_mem (DYB.Pp_smul W T₁ (c - 1) hu' (DYB.Pp_γ W T₁ (c - 1) hZP)) hZP)
  have e1 : W.γ T₁ (lA W ^ κ₁ • y₁) = lA W ^ κ₁ • W.γ T₁ y₁ := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have e2 : lA W ^ κ₁ • y₁ = lA W ^ σ₁ • W.φD T₁ X₁ - (W.π₀ * qA W ^ (size c + S)) • Z :=
    eq_sub_of_add_eq hrel
  have e3 : W.γ T₁ (W.φD T₁ X₁) =
      W.φD T₁ X₁ + ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) • W.φD T₁ x₁ := by
    have h1 : W.γ T₁ (W.φD T₁ X₁) = W.φD T₁ (W.γ T₁ X₁) := (W.φγ_comm T₁ W.gam X₁).symm
    rw [h1, ← hwφ, ← map_pow, ← DYB.φD_smulA, ← map_add (f := _), ← hγX, add_sub_cancel]
  have e4 : W.γ T₁ ((W.π₀ * qA W ^ (size c + S)) • Z) =
      ((W.π₀ * qA W ^ (size c + S)) * ((1 + (u : LetA O n) * qA W) *
        (1 + (u : LetA O n) * W.π₀) ^ (size c + S))) • W.γ T₁ Z := by
    rw [DYB.γ_smulA, map_mul, map_pow, hγπ, GS.γqA hγπ, mul_pow]
    congr 1
    ring
  have e5 : W.γ T₁ (lA W ^ σ₁ • W.φD T₁ X₁) = lA W ^ σ₁ • W.γ T₁ (W.φD T₁ X₁) := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have hscal : ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) =
      W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) := by
    rw [mul_pow, mul_pow, ← pow_mul, ht, pow_add]
    ring
  have hkey : lA W ^ κ₁ • (W.γ T₁ y₁ - y₁) = (W.π₀ * qA W ^ (size c + S)) •
      ((lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
        (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z -
          Z)) := by
    rw [smul_sub, ← e1, e2, map_sub, e5, e3, e4, hscal]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show lA W ^ σ₁ * (W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r *
        qA W ^ t)) = W.π₀ * qA W ^ (size c + S) * (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) *
        W.π₀ ^ r * qA W ^ t) by ring]
    abel
  have hfP : W.π₀ * qA W ^ (size c + S) ∈ PiPs W := by
    have h0 : ps W 0 = qA W := by simp [ps]
    exact (PiPs W).mul_mem (Submonoid.subset_closure (Set.mem_insert _ _))
      ((PiPs W).pow_mem (Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, h0⟩)) _)
  obtain ⟨tt, httP, htt⟩ := hSatP hcase T₁ (c - 1) 1 (W.π₀ * qA W ^ (size c + S)) 1 hT hfP
    (PiPs W).one_mem (W.γ T₁ y₁ - y₁) ⟨_, hγP, rfl⟩ ⟨κ₁, _, hbrP, hkey⟩
  have httq := DYB.Pp_qpow W T₁ (c - 1) _ hq httP
  have httL := DYB.Pp_le_HLD W T₁ (c - 1) httP
  rw [sub_add_cancel] at httL
  refine ⟨⟨hLD.1, hLD.2, qA W ^ (size c + S) • tt, httq, ?_, ?_⟩,
    qA W ^ (size c + S) • y₁, DYB.Pp_qpow W T₁ (c - 1) _ hq hyP, ?_, (one_smul _ _).symm⟩
  · rw [smul_smul, mul_comm, ← smul_smul, httL.1]
  · rw [htt, smul_smul]
  · rw [smul_smul, mul_comm, ← smul_smul, hLD.1]

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

def LetterCoprime (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, lA W ^ m = r * x + s * z

theorem l_pow_mem_invariants (m : ℕ) : lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

theorem Coprime_symm {x z : LetA O n} (h : LetterCoprime W x z) : LetterCoprime W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

theorem Coprime_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : LetterCoprime W x z) (h2 : LetterCoprime W y z) : LetterCoprime W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (l_pow_mem_invariants W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

theorem Coprime_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h : LetterCoprime W x z) : ∀ N : ℕ, LetterCoprime W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact Coprime_mul W (W.AΔ.pow_mem hx N) hz ih h

theorem Coprime_prod (s : Finset ℕ) (x : ℕ → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, LetterCoprime W (x i) z) :
    LetterCoprime W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact Coprime_mul W (W.AΔ.prod_mem fun i _ => hx i) hz
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s))

theorem level_mem_invariants (s : ℕ) : ps W s ∈ W.AΔ :=
  Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s

theorem exists_partition_of_l_pow_levels (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ m : ℕ, ∃ ε : ℕ → LetA O n, (∀ s, ε s ∈ W.AΔ) ∧
      (∀ s ∈ S, ∃ r ∈ W.AΔ, ε s = (∏ t ∈ S.erase s, ps W t ^ N) * r) ∧
      ∑ s ∈ S, ε s = lA W ^ m := by
  have hps := level_mem_invariants W
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with h0 | hne
    · subst h0
      refine ⟨0, fun _ => 1, fun _ => W.AΔ.one_mem, fun t ht => ⟨1, W.AΔ.one_mem, ?_⟩, ?_⟩
      · have h1 : t = a := by simpa using ht
        subst h1; simp
      · simp
    obtain ⟨m, ε, hεΔ, hεd, hsum⟩ := ih hne
    set P := ∏ t ∈ s, ps W t ^ N with hP
    have hPΔ : P ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) N
    have hcop : LetterCoprime W (ps W a ^ N) P := by
      refine Coprime_symm W (Coprime_prod W s _ (fun t => W.AΔ.pow_mem (hps t) N)
        (W.AΔ.pow_mem (hps a) N) fun t ht => ?_)
      have hta : t ≠ a := fun h => ha (h ▸ ht)
      obtain ⟨κ, x, hx, y, hy, hxy⟩ := hC t a hta
      have h1 : LetterCoprime W (ps W t) (ps W a) := ⟨κ, x, hx, y, hy, hxy⟩
      have h2 := Coprime_pow W (hps t) (hps a) h1 N
      exact Coprime_symm W
        (Coprime_pow W (hps a) (W.AΔ.pow_mem (hps t) N) (Coprime_symm W h2) N)
    obtain ⟨m', r, hr, q, hq, he⟩ := hcop
    refine ⟨m + m', fun t => if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N, ?_, ?_, ?_⟩
    · intro t
      by_cases h : t = a
      · simp only [h, if_true]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (l_pow_mem_invariants W m) hq) hPΔ
      · simp only [h, if_false]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (hεΔ t) hr) (W.AΔ.pow_mem (hps a) N)
    · intro t ht
      by_cases h : t = a
      · subst h
        refine ⟨lA W ^ m * q, W.AΔ.mul_mem (l_pow_mem_invariants W m) hq, ?_⟩
        simp only [if_true, Finset.erase_insert ha]
        ring
      · have hts : t ∈ s := by
          rcases Finset.mem_insert.1 ht with h' | h'
          · exact absurd h' h
          · exact h'
        obtain ⟨r₁, hr₁, he₁⟩ := hεd t hts
        refine ⟨r₁ * r, W.AΔ.mul_mem hr₁ hr, ?_⟩
        have hat : a ∉ s.erase t := fun h' => ha (Finset.mem_of_mem_erase h')
        simp only [h, if_false, Finset.erase_insert_of_ne (Ne.symm h), Finset.prod_insert hat, he₁]
        ring
    · rw [Finset.sum_insert ha]
      simp only [if_true]
      have hs2 : ∑ t ∈ s, (if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N) =
          ∑ t ∈ s, ε t * r * ps W a ^ N :=
        Finset.sum_congr rfl fun t ht => by
          have : t ≠ a := fun h' => ha (h' ▸ ht)
          simp [this]
      rw [hs2, ← Finset.sum_mul, ← Finset.sum_mul, hsum, pow_add, he]
      ring

theorem isUnit_algebraMap_ps_of_ringP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)
  simpa [ps, qA, lA] using this

theorem toNat_add_neg_identity (x : ℤ) (N : ℕ) :
    (x + N).toNat + (-x).toNat = x.toNat + N + (-(x + N)).toNat := by
  omega

theorem inId_shift_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : ZMod n} {e s N : ℕ}
    (hs : s < e) {α : ℕ → ℤ} {g : W.EE} (hg : InId W a e α g) {x : LetA O n} (hx : x ∈ W.AΔ) :
    InId W a e (fun t => if t = s then α t else α t + N)
      (algebraMap (LetA O n) W.EE ((∏ t ∈ (Finset.range e).erase s, ps W t ^ N) * x) * g) := by
  obtain ⟨u, hu, he⟩ := hg
  set α' : ℕ → ℤ := fun t => if t = s then α t else α t + N with hα'
  set D := ∏ t ∈ Finset.range e, ps W t ^ (-(α t)).toNat with hD
  set Nm := ∏ t ∈ Finset.range e, ps W t ^ (α t).toNat with hNm
  set D' := ∏ t ∈ Finset.range e, ps W t ^ (-(α' t)).toNat with hD'
  set Nm' := ∏ t ∈ Finset.range e, ps W t ^ (α' t).toNat with hNm'
  set Pz := ∏ t ∈ (Finset.range e).erase s, ps W t ^ N with hPzDef
  have hδ : ∏ t ∈ Finset.range e, ps W t ^ (if t = s then 0 else N) = Pz := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs)]
    simp only [if_true, pow_zero, one_mul]
    exact Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  have key : Nm' * D = Nm * Pz * D' := by
    rw [← hδ, hNm', hD, hNm, hD', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    simp only [hα']
    by_cases h : t = s
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
      exact toNat_add_neg_identity (α t) N
  have hDU : IsUnit (algebraMap (LetA O n) W.EE D) := by
    rw [hD, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun t _ => by
      rw [map_pow]; exact (isUnit_algebraMap_ps_of_ringP W hR t).pow _
  show ∃ u ∈ W.AΔ, algebraMap (LetA O n) W.EE D' * (algebraMap (LetA O n) W.EE (Pz * x) * g) =
    algebraMap (LetA O n) W.EE (letE a * Nm' * u)
  refine ⟨x * u, W.AΔ.mul_mem hx hu, ?_⟩
  apply hDU.mul_left_cancel
  have e1 : algebraMap (LetA O n) W.EE D * (algebraMap (LetA O n) W.EE D' *
      (algebraMap (LetA O n) W.EE (Pz * x) * g)) =
      algebraMap (LetA O n) W.EE D' * algebraMap (LetA O n) W.EE (Pz * x) *
        (algebraMap (LetA O n) W.EE D * g) := by ring
  rw [e1, he]
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  linear_combination (-(letE a * x * u)) * key

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

theorem N_typeT [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAtT W A F c b sol k₀ f (rr + A.σ PD.p) := by
  have hR := NTB.ringData_of_crystalline (hcase := hcase) (hP9 := hP9) (T := T₂) (hT := And.left hW₂)
  have hΔ := NTB.isUnit_prime_sub_one (W := W) (hl := hl) (hOv := hOv) (hinj := hinj)
  have hfnn := NTB.nn_of (hcase := hcase) (hP9 := hP9) (hinj := hinj) (hR := hR) (A := A) (c := c)
    (hthick := hthick) (f := f) (hf := hf) (hdown := hdown)
  exact NTB.ntype_core (hcase := hcase) (hl := hl) (hP9 := hP9) (A := A) (hA := hA) (c := c)
    (hc := hc) (F := F) (hArc := hArc) (hNN := hNN) (hW₁ := hW₁) (hW₂ := hW₂) (hΔ := hΔ) (rr := rr)
    (hrr := hrr c hc) (b := b) (sol := sol) (k₀ := k₀) (hb := hb) (hk₀ := hk₀) (f := f) (hfnn := hfnn)

theorem constants_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAtT W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) := by
  refine NTB.letter_const (A := A) (F := F) (c := c) (b := b) (sol := sol) (k₀ := k₀) (hb := hb)
    (x := x) (h := ?_)
  refine TC.C_typeT_of (hA := hA) (hc := hc) (hthick := hthick) (hcase := hcase) (hl := hl)
    (hP9 := hP9) (hSec := hSec) (hGL := hGL) (hFL := hFL) (hArc := hArc) (hW₁ := hW₁) (hW₂ := hW₂)
    (hb := hb) (Si := ∅) (hSi := by simp) (b₁ := b₁) (sol₁ := sol₁) (hb₁ := hb₁) (c₁ := c₁)
    (s₀ := rr) (hlt := by simp) (hpr := hpr) (hf := ?_) (hdown := ?_) (hup := ?_)
  · rw [Finset.prod_empty]
    unfold InFr
    refine ⟨algebraMap O (LetA O n) x, ?_, ?_⟩
    · simp
    · simp [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · intro s _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]
  · intro s _ _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
