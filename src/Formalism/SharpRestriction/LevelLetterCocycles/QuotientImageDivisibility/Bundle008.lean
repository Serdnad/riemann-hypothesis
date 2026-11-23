module

public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle006
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.PowerSeries.Binomial
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow
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
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX

@[expose] public section

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n)

theorem qp_mem_AΔ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem hR.1 (W.AΔ.natCast_mem _)

theorem inI_qpphi [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {c : ZMod n} {kB : ℕ} (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ kB • W.φD T z ∈ W.N T)
    {x : W.DD T} (hxN : x ∈ W.N T) (hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x) (pad : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T c (((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x)) := by
  obtain ⟨hN, -⟩ := cmp_qpphi W T hs hR h3 hM hxN hxD.1
  set z := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x) with hz
  have hzN : z ∈ W.N T := by
    rw [hz, ← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ hN
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    rw [hz, map_smul, Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', ← W.φγ_comm, hxD.2 δ hδ,
      (W.AΔ.pow_mem (qp_mem_AΔ W hR) kB) δ hδ]
  have hzl : (letE c : LetA O n) • z = z := by
    rw [hz, osmul_comm W T, aself_comm W T, letter_phi W T c hxD.1]
  refine ⟨⟨hzl, hzΔ⟩, ⟨0, 0, by simpa using hzN⟩, ?_⟩
  obtain ⟨x', hx', he⟩ := hmod.2 z ⟨hzN, hzΔ⟩
  exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

theorem exists_inI_inPN_pow_smul_sub_map [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) {d1 d2 d3 : T₂.V ⊗[Qp] B}
    {s₁ s₂ bb hh e pad : ℕ} {k : ℤ}
    (h1 : (PD.p : LL) ^ s₁ • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y =
      (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) d1)
    (h2 : (PD.p : LL) ^ bb • d1 = φVB PD (LL := LL) (V := T₂.V) d2)
    (h3 : (PD.p : LL) ^ s₂ • d2 = (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) d3)
    (hG : (PD.p : LL) ^ k • φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) ∈
      Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    (hexp : (e : ℤ) + hh = pad + k + bb) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨n', hn'N, hmN, hn'D, hcmp⟩ := hG
  set x := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₁ n') with hxdef
  refine ⟨x, inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad, ?_⟩
  have hyN : y ∈ W.N T₂ := NDl_N W T₂ hy
  have hyl : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c y := NDl_DL W T₂ hy

  have hml : (letE (c - 1) : LetA O n) • W.map F n' = W.map F n' := by
    rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hn'D.1]
  obtain ⟨hqN, hqc⟩ := cmp_qpphi W T₂ hs hR h3₂ hM₂ hmN hml
  have hFx : W.map F x = ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₂ (W.map F n')) := by
    rw [hxdef, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, W.map_φ]
  have hFxN : W.map F x ∈ W.N T₂ := by
    rw [hFx, ← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hqN
  have hxI := inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad
  have hFxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F x) := by
    refine ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hxI.1.1], fun δ hδ => ?_⟩
    rw [← W.map_γ, hxI.1.2 δ hδ]
  have hpyN : ((PD.p : O) ^ (e + s₁ + s₂)) • y ∈ W.N T₂ := by
    rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hyN
  have hzmem : ((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c :=
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).sub_mem ((Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).smul_mem _ hy) ⟨hFxN, hFxD⟩
  refine ker_NDl W T₂ c h3₂ hmod₂ hR hzmem ?_

  have hsub : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y) - Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (W.map F x) := by
    have := cmpD_add W T₂ ((W.N T₂).sub_mem hpyN hFxN) hFxN
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub, sub_eq_zero, cmpD_osmul W T₂ _ hyN, hFx, cmpD_osmul W T₂ _ hqN, hqc,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hmN, ← hcmp, map_pow, map_pow, map_natCast]

  have hsc : (PD.p : LL) ^ e * (PD.p : LL) ^ hh = (PD.p : LL) ^ bb * ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hp,
      ← zpow_add₀ hp, ← zpow_add₀ hp]
    congr 1
    omega
  have key : (PD.p : LL) ^ (e + s₂) • d1 = ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) •
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) := by
    apply smul_right_injective _ (pow_ne_zero bb hp)
    simp only
    rw [smul_comm, h2, pow_add, mul_smul, ← map_smul, h3, map_smul, smul_smul, smul_smul, hsc]
  rw [pow_add, pow_add, mul_smul, mul_smul, smul_comm ((PD.p : LL) ^ s₁), h1, ← mul_smul,
    ← pow_add, smul_comm, ← map_smul, key, map_smul, map_smul, smul_smul]
  simp only [smul_smul]
  congr 1
  ring

end Core

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem rhoLift_of [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hK : W.ClKNat) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Formalism.MainNotions.RamifiedCoefficientChains.S9.RhoLift W := by
  intro d T₁ T₂ F b S η m hS c hc w u κ k hu hR hcong
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  obtain ⟨hc1, hc2, -⟩ := hS.2.2.2.2.2.1
  have hcE : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 1 (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.sigC PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η) :=
    Or.inl ⟨rfl, Nat.le_add_left _ _, rfl⟩
  have T2 := hT2 hA hp11 1 _ η _ hTC

  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i →
      -((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  have hJ1 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₁.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (hS.2.2.2.2.2.2.1 i τ hτ a ha)
  have hJ1U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₁.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (hS.2.2.2.2.2.2.1 (c' + 1) τ hτ a ha)
  have hJ2 : ∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₂.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ))) :=
    fun i τ hτ a ha => hwin i a (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)
  have hJ2U : ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) :=
    fun c' τ hc' hτ a ha => hwinU c' hc' a (rk_jumps₂ W hE hC hQ hS (c' + 1) τ hτ a ha)
  have F1 := hF d T₁ T₂ F b S η m hS T₁ hc1 hJ1 hJ1U
  have F2 := hF d T₁ T₂ F b S η m hS T₂ hc2 hJ2 hJ2U
  dsimp only at F1 F2
  obtain ⟨-, -, F1c3, F1c4, F1c5⟩ := F1
  obtain ⟨-, -, F2c3, F2c4, -⟩ := F2

  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have hring := (((h9 T₁ hc1) hA.2.1 hA.2.2).2.2 hfin).1
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hring.1
  have hu0 : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1) := hring.2.2.1

  obtain ⟨hwI, hκ, z, x, htr, hx1, hx2, hcl⟩ := hR
  obtain ⟨zu, hzu⟩ := (T2.1 T₁ hc1 c).1 u hu
  obtain ⟨⟨xu, hxu1, hxu2⟩, -⟩ := F1c5 c u zu hcE hu hzu
  have hxuΔ := ((RL.mem_Z1DΔ_iff W T₁ _).1 xu.2).2
  have hxΔ := ((RL.mem_Z1DΔ_iff W T₂ _).1 x.2).2
  have hzuL : (letE (c + 1) : LetA O n) • zu = zu := RL.trunc_letter W T₁ c hu.1.1 hzu
  have hDLu : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ (c + 1) (xu : W.DD T₁ × W.DD T₁).1 := by
    refine ⟨by rw [hxu1]; exact hzuL, fun δ hδ => (hxuΔ δ hδ).1⟩
  have hPu : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₁ zu :=
    RL.trunc_polesFin W T₁ c η _ hu hzuL ((T2.1 T₁ hc1 c).2.1 u zu hu hzu).1
      (fun y hy hyl => F1c4 c y hcE hy hyl)
  have hH1f : W.clK T₁ xu ∈ latticeFiniteCohomology PD T₁.L := (F1c3 (c + 1) xu hDLu hxu2).2 (by rw [hxu1]; exact hPu)

  have hIu2 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (W.map F u) := RL.inI_map W F hc1 hc2 hu
  obtain ⟨z2, hz2⟩ := (T2.1 T₂ hc2 c).1 _ hIu2
  obtain ⟨p1, hp1, e1⟩ := T2.2 T₁ T₂ F hc1 hc2 c u zu z2 hu hzu hz2
  have hIw3 : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ c (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hwI)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T₂ _ hIu2)
  obtain ⟨z3, hz3⟩ := (T2.1 T₂ hc2 c).1 _ hIw3
  obtain ⟨p2, hp2, e2⟩ := (T2.1 T₂ hc2 c).2.2.2.1 ((PD.p : O) ^ k) (-1) w (W.map F u) z z2 z3
    hwI hIu2 htr hz2 hz3
  have hw3PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ k) • w + (-1 : O) • W.map F u) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact hcong
  obtain ⟨p3, hp3, e3⟩ := (T2.1 T₂ hc2 c).2.2.2.2.1 _ z3 hIw3 hw3PN hz3
  have hD1 : ((PD.p : O) ^ k) • z - W.map F zu =
      Formalism.MainNotions.CrystallineLiftingInputs.fMX W (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)) η • (p3 - p2 - p1) := by
    rw [smul_sub, smul_sub, ← e1, ← e2, ← e3, neg_one_smul]
    abel
  have hP : p3 - p2 - p1 ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ c 1 :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hp3 hp2) hp1
  have hY : Formalism.MainNotions.LiftingTheory.qp W ^ η • (p3 - p2 - p1) ∈ W.N T₂ :=
    F2c4 c _ hcE (RL.pullJ_le_φpull W T₂ c hP) (RL.pullJ_letter W T₂ c hP)
  have hD1Δ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((PD.p : O) ^ k) • z - W.map F zu) =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    intro δ hδ
    rw [map_sub, map_smul, ← W.map_γ, ← hx1, (hxΔ δ hδ).1, ← hxu1, (hxuΔ δ hδ).1]
  have hD1PN : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      (((PD.p : O) ^ k) • z - W.map F zu) :=
    RL.inPN_of_inv W T₂ hu0 hΔπ _ hY (by rw [hD1, Formalism.MainNotions.CrystallineLiftingInputs.fMX, mul_smul]) hD1Δ

  let yu : ↥(W.wachCocyclesDelta T₂) := ⟨_, RL.map_mem_Z1DΔ W F xu⟩
  have hnat : F.H1map (W.clK T₁ xu) = W.clK T₂ yu := hK F xu yu rfl
  have hdd1 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 =
      ((PD.p : O) ^ k) • z - W.map F zu := by
    simp [yu, hx1, hxu1]
  have hdd2 : ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 =
      ((PD.p : O) ^ k) • (x : W.DD T₂ × W.DD T₂).2 + (-1 : O) • W.map F (xu : W.DD T₁ × W.DD T₁).2 := by
    simp [yu, sub_eq_add_neg]
  have hDL2 : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (c + 1)
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).1 := by
    rw [hdd1]
    refine ⟨?_, hD1Δ⟩
    rw [smul_sub, smul_comm, RL.trunc_letter W T₂ c hwI.1.1 htr, ← RL.map_smulA, hzuL]
  have hPN2 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S))
      ((((PD.p : O) ^ k) • x - yu : ↥(W.wachCocyclesDelta T₂)) : W.DD T₂ × W.DD T₂).2 := by
    rw [hdd2]
    exact Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ hx2)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ (RL.inPN_map W F hc1 hc2 hxu2))
  have hz0 : W.clK T₂ (((PD.p : O) ^ k) • x - yu) = 0 :=
    (F2c3 (c + 1) _ hDL2 hPN2).1 (by rw [hdd1]; exact hD1PN)
  have hcls : ((PD.p : O) ^ k) • W.clK T₂ x = F.H1map (W.clK T₁ xu) := by
    have e : W.clK T₂ (((PD.p : O) ^ k) • x - yu) =
        ((PD.p : O) ^ k) • W.clK T₂ x - W.clK T₂ yu :=
      ((W.clK T₂).map_sub _ _).trans (congrArg (· - W.clK T₂ yu) ((W.clK T₂).map_smul _ _))
    rw [e] at hz0
    rw [hnat]
    exact sub_eq_zero.1 hz0
  have hmk : (Submodule.Quotient.mk (((PD.p : O) ^ k) • (⟨κ, hκ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ xu) := by
    rw [Submodule.Quotient.mk_smul, ← hcl, hcls]
  exact RL.mem_ImF_of_cls F _ ⟨_, hH1f, hmk.symm⟩

theorem rhoLift_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hT : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))],
      Formalism.MainNotions.CrystallineLiftingInputs.TTool2 ((HW l).W K 1 LL hg) ∧ Formalism.MainNotions.CrystallineLiftingInputs.FTool ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.rhoLift D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hS
  have h1 := hA.1 l K 1 LL hg
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have h17 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hp11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
  have hK : ((HW l).W K 1 LL hg).ClKNat := h17.2 fun h2 => absurd h2 (by omega)
  exact rhoLift_of _ (hT l K LL hg).1 (hT l K LL hg).2 hK h1.2.2.2.2.2.2.2.2.1 h11.1 h11.2.1
    h11.2.2 d T₁ T₂ F' b S η m hS

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Bs

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F] [Algebra ℤ_[p] O] [IsDomain O] [CharZero O]

theorem evR_bs (s : ℕ) {x : F} (hx : Polynomial.aeval x (Zp (O := O) p (s + 1)) = 0) (ζ : F)
    (hxζ : x = ζ - 1) (z : ℤ_[p]) :
    evR p (s + 1) hlm hx (PowerSeries.binomialSeries O z) =
      ζ ^ (PadicInt.toZModPow (s + 1) z).val := by
  set A := (PadicInt.toZModPow (s + 1) z).val with hA
  have hker : z - (A : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ (s + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hA,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hker
  have hz : z = (A : ℤ_[p]) + (((p ^ (s + 1) : ℕ)) : ℤ_[p]) * w := by
    push_cast; linear_combination -hw
  have hN : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [hz, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat,
    ← Formalism.MainNotions.UnusedSlot80.LG.subst_bs (p ^ (s + 1)) hN w, map_mul, evR_onePow,
    show 1 + x = ζ by rw [hxζ]; ring]
  have h0 : Polynomial.aeval (0 : F) (Zp (O := O) p (s + 1)) = 0 := root_Zp p (s + 1) (by simp)
  have hsub := evR_subst p (s + 1) hlm hx h0 ((1 + PowerSeries.X) ^ (p ^ (s + 1)) - 1)
    (by simp) (evR_Zs p (s + 1) hlm hx) (PowerSeries.binomialSeries O w)
  rw [hsub, evR_eq_cc p (s + 1) hlm h0 rfl, PowerSeries.binomialSeries_constantCoeff, map_one, mul_one]

end Bs

section Main

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
    (F : Type) [Field F] [Algebra O F]

theorem evAt_ps (a : ZMod n) (s t : ℕ) (ζ : Rs F PD.p s) :
    ∃ hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0,
      evAt hlm F a s ζ (ps W t) =
        evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  refine ⟨hy, ?_⟩
  have hφ := Formalism.MainNotions.UnusedSlot80.LG.phi_pow_X W.φ₀ PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) t
  have h0 : PowerSeries.constantCoeff ((W.φ₀ ^ t) PowerSeries.X) = 0 := by rw [hφ]; simp
  rw [evAt_apply, Formalism.MainNotions.UnusedSlot80.LG.ps_apply W t a, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst _ h0, hφ]
  refine evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hy _ (by simp) ?_ _
  rw [map_sub, evR_onePow, map_one, add_sub_cancel]

theorem evAt_ps_iff (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (a : ZMod n) (s t : ℕ)
    (ζ : Rs F PD.p s) : evAt hlm F a s ζ (ps W t) = 0 ↔ t = s := by
  obtain ⟨hy, he⟩ := evAt_ps W hlm F a s t ζ
  rw [he, ev_qp W hlm F hR s hy, add_sub_cancel]
  have hζ : IsPrimitiveRoot (ζ : F) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hp1 : 1 < PD.p := hpF.out.one_lt
  constructor
  · rintro ⟨hne, hpow⟩
    by_contra hts
    rcases Nat.lt_or_gt_of_ne hts with h | h
    ·
      have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
        (pow_dvd_pow PD.p (by omega : t ≤ s + 1))
      rw [Nat.pow_div (by omega) hpF.out.pos] at hprim
      have hd := hprim.dvd_of_pow_eq_one PD.p hpow
      have h1 := Nat.le_of_dvd hpF.out.pos hd
      have h2 : PD.p ^ 2 ≤ PD.p ^ (s + 1 - t) := Nat.pow_le_pow_right hpF.out.pos (by omega)
      have h3 : PD.p < PD.p ^ 2 := by nlinarith
      omega
    ·
      apply hne
      rw [sub_eq_zero]
      obtain ⟨k, hk⟩ : PD.p ^ (s + 1) ∣ PD.p ^ t := pow_dvd_pow PD.p (by omega)
      rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  · rintro rfl
    have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
      (pow_dvd_pow PD.p (by omega : t ≤ t + 1))
    rw [Nat.pow_div (by omega) hpF.out.pos, show t + 1 - t = 1 by omega, pow_one] at hprim
    exact ⟨sub_ne_zero.2 (hprim.ne_one hp1), hprim.pow_eq_one⟩

end Main

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
