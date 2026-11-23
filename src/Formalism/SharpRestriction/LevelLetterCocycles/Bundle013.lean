module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Formalism.SharpRestriction.ParConsts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def HypB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ) : Prop :=
  11 ≤ PD.p ∧ TruncatedSeriesCountingBounds.HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi ∧ 20 * w ≤ b ∧ 20 * η ≤ b ∧
    20 * S ≤ b ∧ ∃ i, ¬ TruncatedSeriesCountingBounds.Thick b η size i

def Alt (b η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  ∀ i, up (i + 1) ≠ up i ∧
    ¬ (TruncatedSeriesCountingBounds.Thick b η size i ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 1) ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 2))

def One (b η R : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  (∀ i, up i = up 0) ∧ ∀ i, ¬ ∀ t : ℕ, t < R → TruncatedSeriesCountingBounds.Thick b η size (i + t)

def Sg (l b w S η : ℕ) (size : ZMod n → ℕ) : ℝ :=
  (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l +
    Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 1

def bandI (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) : ℝ :=
  if TruncatedSeriesCountingBounds.Band l b S η size (Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb then 1 else 0

def arcOf [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : ArcLiftingSetup.ArcP n where
  G₀ := w + S
  S := S
  η := η
  h := TruncatedSeriesCountingBounds.hB b w S η size
  j := 1
  ty := fun i => if up i then .up (size i) else .down (size i)
  cuts := Finset.univ.filter fun c => ¬ TruncatedSeriesCountingBounds.Thick b η size (c + 1)
  len := fun c => sInf {d : ℕ | 1 ≤ d ∧
    ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}

def kapC (l : ℕ) (A : ArcLiftingSetup.ArcP n) (c : ZMod n) : ℕ :=
  A.len c + ∑ i ∈ (A.JS c).erase 0, (A.len c + 1 + padicValInt l i)

def ExpIn (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Z : Finset (G → T₂.V)) (e : ℕ) : Prop :=
  ∀ c ∈ latticeFiniteCocycles PD T₂.L, ((PD.p : O) ^ e) • c ∈ F.ImF PD ⊔ Submodule.span O (Z : Set (G → T₂.V))

def ExtYCore (PD : PeriodData G Qp K₀ K B BdR) (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ cc ∈ latticeFiniteCocycles PD T.L,
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsCrys PD Y.ρ ∧ Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc

end Core

structure AdmBoundsB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) : Prop where
  p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F
  p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm
  p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm
  p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F
  p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F
  a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK
  a5 : ArcLiftingSetup.adm5 D HW F
  sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F
  kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F
  kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F
  a9 : ArcLiftingSetup.adm9 D
  a10 : ArcLiftingSetup.adm10 D
  a11 : ArcLiftingSetup.adm11 D HW F
  a12 : ArcLiftingSetup.adm12 D HW F Cm
  a13 : ArcLiftingSetup.adm13 D HW F Cm
  a14 : ArcLiftingSetup.adm14 D HW F Cm
  a15 : ArcLiftingSetup.adm15 D

theorem admBoundsB_of_adm {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {Cm : CmpOf D.loc D.locA HW F}
    {CR CA CB CK Ckap : ℝ} (h : ArcLiftingSetup.admitted D HW F Cm CR CA CB CK Ckap) : AdmBoundsB D HW F Cm CR CA CB CK :=
  ⟨fun l _ K s LL g => (h.1.1 l K s LL g).2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.2.2.1, h.2.2.2.2.1.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def FinLev (W : LocWach PD LL O v n) : Prop :=
  ∀ (a : ZMod n) (e : ℕ) (H : ℕ → ℕ), ∃ D : ℕ, ∀ u ∈ W.AΔ, ∃ (c : Fin D → O) (w : LetA O n),
    w ∈ W.AΔ ∧ (letE a : LetA O n) * u =
      letE a * ∑ j : Fin D, algebraMap O (LetA O n) (c j) * W.π₀ ^ (j : ℕ) +
        W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * (letE a * w)

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def LetterConditionLocal (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (y : ℕ), 1 ≤ y →
  ∀ (dop : W.DD T →ₗ[O] W.DD T), (∀ z, W.π₀ • dop z = W.γ T z - z) →
  ∀ (cc : ℤ → O), (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
  ∀ X : Finset ℤ,
    (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a → 1 ≤ j → j ≤ y →
      a + (j : ℤ) ∈ X) →
    ∀ z : W.DD T, Formalism.MainNotions.LiftingTheory.InNΔi W T i (qA W ^ y • z) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T i
        (Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z)

def LetterConditionGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    LetterConditionLocal ((HW l).W K s LL h)

end Formalism.MainNotions.N
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.KV

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem algebraMap_unit_zpow (u : Oˣ) (z : ℤ) :
    algebraMap O LL ((u ^ z : Oˣ) : O) = (algebraMap O LL (u : O)) ^ z := by
  change ((Units.map (algebraMap O LL).toMonoidHom (u ^ z) : LLˣ) : LL) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem v_prod {ι : Type*} (s : Finset ι) (f : ι → LL) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem padicValInt_mul_pow {p : ℕ} (hp : p.Prime) {i : ℤ} (hi : i ≠ 0) (ell : ℕ) :
    padicValInt p (i * (p : ℤ) ^ ell) = padicValInt p i + ell := by
  have := Fact.mk hp
  simp only [padicValInt, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rw [Nat.multiplicity_mul (Int.natAbs_ne_zero.2 hi) (pow_ne_zero _ hp.ne_zero),
    Nat.multiplicity_prime_pow]

theorem eval_PPO (W : LocWach PD LL O v n) (ell : ℕ) (JS : Finset ℤ) :
    algebraMap O LL ((PPO W ell JS).eval 1) =
      (∏ i ∈ JS.erase 0, (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell))) *
        (PD.p : LL) ^ ell := by
  simp only [PPO, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, map_mul, map_prod, map_sub, map_one, map_natCast,
    algebraMap_unit_zpow]
  push_cast
  ring

theorem val_PP_one (W : LocWach PD LL O v n) (hs : W.s = 1) (hp : PD.p ≠ 2) (ell : ℕ)
    (JS : Finset ℤ) :
    v (algebraMap O LL ((PPO W ell JS).eval 1)) =
      ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) : ℕ) : WithTop ℚ) := by
  have hy : 1 ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1) := by
    rw [W.gam_gen, hs, Nat.cast_one]
  have hfac : ∀ i ∈ JS.erase 0,
      v (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell)) =
        ((ell + 1 + padicValInt PD.p i : ℕ) : WithTop ℚ) := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
    have hm : i * (PD.p : ℤ) ^ ell ≠ 0 := mul_ne_zero hi0 (pow_ne_zero _ (by exact_mod_cast PD.hp.ne_zero))
    rw [AddValuation.map_sub_swap, LTE.val_zpow_sub_one v PD.hp hp W.v_l hy hm, W.gam_gen, hs,
      padicValInt_mul_pow PD.hp hi0]
    push_cast
    abel
  rw [eval_PPO, AddValuation.map_mul, v_prod, Finset.sum_congr rfl hfac, AddValuation.map_pow, W.v_l,
    nsmul_one, Nat.cast_add, Nat.cast_sum, add_comm]

end Formalism.MainNotions.UnusedSlot80.KV
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FiltrationPropertiesEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm

def AdmTools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def FiltrationPropertiesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmTools D HW F Cm → FiltrationPropertiesEtale D HW F Cm

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def Pi0LatticeCondition (W : LocWach PD LL O v n) : Prop := ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u

end Core

def GammaPreservesUniformiser (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Pi0LatticeCondition ((HW l).W K 1 LL h.2.2)

def AdmPi0 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def UniformiserGammaTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmPi0 D HW F → GammaPreservesUniformiser D HW F

def AdmSat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def SaturationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm5 D HW F
def SaturationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationArcLifting D HW F
def SaturationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm8 D HW F
def SaturationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationEtale D HW F

def FirstFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrNaturality D HW F

def FirstFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm6 D HW F
def FirstFiltrationTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationArcLifting D HW F
def FirstFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm9 D HW F
def FirstFiltrationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationEtale D HW F

def SecondFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P7 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2b D HW F

def SecondFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm7 D HW F
def SecondFiltrationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationArcLifting D HW F → SecondFiltrationArcLifting D HW F
def SecondFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm10 D HW F
def FamilyMassExplicitOfVolumeAgreement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationEtale D HW F → SecondFiltrationEtale D HW F

def KillerAtLevels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.KillerLevL D.loc D.locA HW F

def AdmKillLev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def KillerLevelsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmKillLev D HW F Cm → KillerAtLevels D HW F

def KillerBoundWithConstant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm8 D HW F C

def AdmKillA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F

def KillerWithConstantTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := AdmKillA D HW F → KillerBoundWithConstant D HW F C

def KillerAtLevelsSecondForm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm11 D HW F

def KillerWachCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := GammaPreservesUniformiser D HW F → KillerAtLevelsSecondForm D HW F

def RelayArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm11 D HW F

def AdmRelayA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧ Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧
    SaturationArcLifting D HW F ∧ FirstFiltrationArcLifting D HW F ∧ SecondFiltrationArcLifting D HW F

def RelayTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmRelayA D HW F → RelayArcLifting D HW F

def ArcLiftingCoordinates (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm12 D HW F Cm

def AdmArcA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧
    Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ SaturationArcLifting D HW F

def ArcCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmArcA D HW F Cm → ArcLiftingCoordinates D HW F Cm

def SplittingArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm13 D HW F Cm

def AdmSplitA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F ∧
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F ∧ FirstFiltrationArcLifting D HW F ∧ RelayArcLifting D HW F ∧ ArcLiftingCoordinates D HW F Cm

def SplittingTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmSplitA D HW F Cm → SplittingArcLifting D HW F Cm

def UniversalComponentCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm14 D HW F Cm

def AdmUnivA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := SaturationArcLifting D HW F ∧ KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F ∧ ArcLiftingCoordinates D HW F Cm

def H1fBaseChangeFree (D : D7) : Prop := Formalism.MainNotions.WachCoordinates.adm13 D

def H1fBaseChangeTheorem (D : D7) : Prop := H1fBaseChangeFree D

end Formalism.MainNotions.UnusedSlot80
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure RestPt {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop where

  ng0 : D.nd.l i ≠ D.host.g 0
  ng1 : D.nd.l i ≠ D.host.g 1

  good : GoodR D.nd i r

  chi1 : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)

  block : EmbeddingTypes.ambBlock i r ρ π

  chi : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ), 1 ≤ c → c ≤ D.R.t →
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)))

  g3 : AbsIrreducibleDistinct D i r

  cont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))

  rho : IsRhoOf D.nd i π (ρ π)

  ss : IsSSRep (rhoChiK D i (ρ π))

  eps : TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i

  shape : TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def tameList {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Option (Fin m × Bool) → (ZMod g)ˣ
  | none => 1
  | some (j, true) => χ j
  | some (j, false) => (χ j)⁻¹

def TameDistinct (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Prop :=
  Function.Injective (tameList χ) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB r g →
    Function.Injective (fun o => Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((tameList χ o : (ZMod g)ˣ) : ZMod g)))) ∧
  ∀ j, IsSquare (χ j)

def TameDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2) (v : (Fm.D x i).nd.PlG k),
    haveI : Fact ((Fm.D x i).host.g k).Prime := ⟨(Fm.D x i).host.g_prime k⟩
    TameDistinct (Fm.D x i).R.r ((Fm.D x i).host.g k) ((Fm.D x i).nd.chiT k v)

end Formalism.MainNotions
end
end
