module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle022
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

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

namespace A1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_add' {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    cmpD W T (x + y) = cmpD W T x + cmpD W T y := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).add_mem hx hy)]
  rw [← map_add (f := _)]
  rfl

theorem cmpD_sum' {ι : Type} (s : Finset ι) (y : ι → W.DD T) (hy : ∀ k ∈ s, y k ∈ W.N T) :
    cmpD W T (∑ k ∈ s, y k) = ∑ k ∈ s, cmpD W T (y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact map_zero (W.cmp T)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cmpD_add' W T (hy a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun k hk => hy k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hy k (Finset.mem_insert_of_mem hk)]

theorem cmpD_smul_letter' (i : ZMod n) (a : LetA O n) {w : W.DD T} (hw : w ∈ W.N T)
    (hwi : (letE i : LetA O n) • w = w) :
    cmpD W T (a • w) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem a hw)]
  exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i a w hw hwi

end A1

theorem arc_single_type_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hone : ∀ s < (arcOf b w S η up size).len c, up (c - (s : ZMod n)) = up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  have hbas := arcBasic W F hB
  dsimp only at hbas
  obtain ⟨hOK, -, -, -, hσ⟩ := hbas
  have hl : 5 ≤ PD.p := by have := hB.1; omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    by_cases h : up (c - (s : ZMod n)) = true <;> simp [arcOf, h, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
  refine ⟨rr + (arcOf b w S η up size).σ PD.p, by push_cast; linarith, ?_⟩
  cases hup : up c
  ·
    have hdn : ∀ s < (arcOf b w S η up size).len c,
        (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n))) := by
      intro s hs
      have h1 : up (c - (s : ZMod n)) = false := (hone s hs).trans hup
      simp [arcOf, h1]
    have hnn : nnDen W (arcOf b w S η up size) c = 1 := by
      unfold nnDen prodTy
      apply Finset.prod_eq_one
      intro s hs
      rw [hdn s (Finset.mem_range.1 hs)]
      simp
    have hcut' : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) ∈ (arcOf b w S η up size).cuts :=
      (hOK.2.2.1 c hc).2.2.1
    obtain ⟨d₁, b₁, sol₁, hb₁⟩ :=
      hHF hcase hl _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
    obtain ⟨x₁, hx₁, hx₁eq⟩ := hArcL hcase T₁ T₂ F hsur _ rr ((arcOf b w S η up size).len c)
      (hkill _ hcut') (bb k₀) (hbb.1.1 k₀)
    obtain ⟨a, ⟨-, hxa⟩, -⟩ := hb₁.1.2 x₁ hx₁
    have hb₁N : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hb₁.1.1 m).1.1
    have hb₁l : ∀ m, (letE (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
      fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T₁ _ (hb₁.1.1 m).2
    have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) • cmpD W T₁ (b₁ m) := by
      rw [hxa, A1.cmpD_sum' W T₁ _ _ (fun m _ => (W.N T₁).smul_mem _ (hb₁N m))]
      exact Finset.sum_congr rfl fun m _ =>
        A1.cmpD_smul_letter' W T₁ _ (a m) (hb₁N m) (hb₁l m)
    have e1 : dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m => PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) =
        ((φVB PD (LL := LL) (V := T₁.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₁ x₁) := by

      rw [hcmp, map_sum]
      simp only [map_smul]
      rfl
    have e2 : dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) =
        ((φVB PD (LL := LL) (V := T₂.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₂ (bb k₀)) := by
      unfold dv
      rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (by simp)]
      simp
    have hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m =>
        PowerSeries.constantCoeff (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))))) =
        ((PD.p : LL) ^ rr) • dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
      rw [e1, e2, hx₁eq]
    refine liftsAt_thin_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hW₁ hW₂ hbb ∅ (by simp) b₁ sol₁ hb₁ _ rr (by simp) hpr f ?_ ?_ ?_
    · have h := hf.1
      rw [hnn] at h
      rw [Finset.prod_empty]
      exact h
    · intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf.2 s hs bs hbs
      rw [hnn] at hx
      exact ⟨κ, x, by rw [Finset.prod_empty]; exact hx⟩
    · intro s hs _ bs hbs
      rw [hdn s hs] at hbs
      simp at hbs
  ·
    refine liftsAt_thick_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ f hf.1 ?_
    intro s hs bs hbs
    have h1 : up (c - (s : ZMod n)) = true := (hone s hs).trans hup
    simp [arcOf, h1] at hbs

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

theorem letter_window_bounded_below (ty : Formalism.MainNotions.LocalTheoryWindows.LT) (G₁ S₁ η₁ : ℕ) :
    ∃ U : ℤ, ∀ x ∈ ty.win G₁ S₁ η₁, U ≤ x := by
  cases ty with
  | thin => exact ⟨-(G₁ : ℤ), fun x hx => hx.1⟩
  | up b =>
    refine ⟨-(η₁ : ℤ), fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · exact hx.1
  | down b =>
    refine ⟨-(b : ℤ) - S₁ - η₁, fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · have := hx.1; omega

theorem arc_gamma_lift [IsDomain O] [FiniteDimensional Qp LL]
    (hinj : Function.Injective (algebraMap O LL)) (hArc : ArcCore W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W) : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W := by
  intro hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg hyp
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hCA W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have : NeZero n := ⟨by
    rw [W.n_eq]
    have := PD.finK₀
    exact Module.finrank_pos.ne'⟩
  have hS := Formalism.MainNotions.UnusedSlot80.KF.psStable_of W hR
  have hC := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR
  obtain ⟨t, htΔ, hγπ⟩ := Formalism.MainNotions.LiftingTheory.gamma_uniformizer_eq_mul_unit' W hR
  have hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u :=
    ⟨_, W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hR.1 htΔ), hγπ⟩
  obtain ⟨h, hγ, hhFr, hlev⟩ := hyp
  refine gamma_lift_along_arc W hinj hArc hR hS hP hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg
    ⟨h, ⟨hhFr, ?_⟩, hγ⟩
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    refine ⟨0, d, h, fun i => Pi.single i 1, fun _ _ => 0,
      fun i => ⟨?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, fun k => ?_⟩
    · have := hhFr i
      simpa [InId, abelian₂] using this
    · rw [Finset.sum_eq_single k (fun i _ hik => by simp [hik.symm]) (by simp)]
      simp [lE]
  · refine section_in_ideal_of_levels W hR hC T _ e hpos b h hlev fun t' ht' => ?_
    obtain ⟨U, hU⟩ := letter_window_bounded_below
      (A.ty ((c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) - (t' : ZMod n))) A.G₀ A.S A.η
    exact ⟨U, fun u hu c₀ =>
      (hFL hCA h5 A hA c hc e hje hel T hT d b sol hhor c₀ t' ht').1 u fun x hx => hu.trans (hU x hx)⟩

end Core

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arc_gamma_lift_at {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore ((HW l).W K 1 LL hG)) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore ((HW l).W K 1 LL hG) := by
  intro hCA h5
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have h5' : 5 ≤ l := hpl ▸ h5
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact arc_gamma_lift _ Subtype.val_injective (hU.a12 l K LL hG hK h5').1 (hU.p9 l K 1 LL hG) hFL
    hCA h5

end Record

end Formalism.MainNotions.N.Ln17
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

theorem arc_length_two_case_down [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false) (h2b : size (c - 1) ≤ Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨-, hSur, hηs, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega
  obtain ⟨hct, hcm⟩ := ArcLengthTwo.arc_len_two_thick_letters c hlen
  have hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) := by
    have h := hc
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hupm : up (c - 1) = true := by
    cases h : up (c - 1)
    · exact absurd (h.trans hup.symm) hdiff
    · rfl
  have hty0 : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    simp [arcOf, hupm]
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
    simp [hty0, hty1]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    simp only [arcOf]
    split <;> rfl
  obtain ⟨κ, x, hx⟩ := hf.2 0 (by rw [hlen]; norm_num) (size c) (by simpa using hty0)
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hW₁.1 hO hinj
  have hy1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  obtain ⟨de, x', hde, hde0, hg1, hg2⟩ := ArcLengthTwo.den_step W Br c (size (c - 1)) (size c + S) κ hy1
    (by have := hηs c; omega) f x (by rw [← hnn]; exact hf.1) (by rw [← hnn]; exact hx)
  set g := lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' with hgdef
  have hdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c) g := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp only [Nat.cast_zero, sub_zero, hty0, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hg2
    · simp [hty1] at hbs
  have hgl : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ g (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL
      hO hOv hinj hArc hArcL hNN hW₁ hW₂ hSur rr hkill hbb hk₀ g (by rw [hnn]; exact hg1) hdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  have hcst : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE x')
      (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x'
  have hcst' : LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') (rr + (arcOf b w S η up size).σ PD.p) :=
    LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hcst
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hcst' hgl
  have esum : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' + g = lE W de * f := by
    rw [hgdef]; ring
  rw [esum] at hsum
  have hfin := ArcLengthTwo.lifts_scale W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨rr + (arcOf b w S η up size).σ PD.p + de, ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hct⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg; rw [hhB]
  rw [hSgeq] at hrr hσ ⊢
  set Sg' := Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η with hSg'
  have hx11 : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hSg1 : 1 ≤ Sg' := by
    rw [hSg']; unfold Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    have hh1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      have := hηs c; have := hct.2; exact_mod_cast (by omega : 1 ≤ b + η + S)
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : 0 ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg (by linarith) (by linarith)
    linarith
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  have hηb0 : 0 ≤ (η : ℝ) * bandI PD.p b w S η size Cb := mul_nonneg hη0 hband0
  push_cast
  rcases lt_or_ge (PD.p * size (c - 1)) (size c + S) with hlt | hge
  · rw [hde0 hlt]; push_cast; linarith
  have hb1 : 1 ≤ b := by have := hηs c; have := hct.2; omega
  have hw' : size (c - 1) ≤ w := hnt (c - 1) hcm
  have hAI := ArcLengthTwo.aI_le W F hB' CR hWR c hct hc1
  have hwA : (size (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) + η := by exact_mod_cast h2b
  obtain ⟨k1, k2⟩ := case2b PD.p hp11 b w (size (c - 1)) S η (size c) hb1 hηb hSb hwb hw' hy1 hct.1 hct.2
    _ hAI hwA
  have hDle : (de : ℝ) ≤ η + 5 * Sg' := by
    have hm0 : 0 ≤ max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) := le_max_left _ _
    have hc' := Nat.ceil_lt_add_one hm0
    have hde' : (de : ℝ) ≤ (⌈max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ))⌉₊ : ℝ) := by exact_mod_cast hde
    have hmax : max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) ≤ η + 5 * Sg' - 1 := by
      apply max_le (by linarith)
      push_cast
      linarith
    linarith
  by_cases hband : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size
      (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb
  · have h1 : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hband]
    rw [h1]; linarith
  · have h0 : bandI PD.p b w S η size Cb = 0 := by unfold bandI; rw [if_neg hband]
    rw [hhB] at hband
    have hnb := fun hle => hband ⟨c - 1, hcm, Or.inl (by rw [sub_add_cancel]; exact hct), hle⟩
    have hη4 := k2 Cb hCb hge hnb
    rw [h0]; linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
