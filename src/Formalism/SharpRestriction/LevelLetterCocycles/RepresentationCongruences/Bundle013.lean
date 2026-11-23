module

import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
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
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013

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

open scoped TensorProduct

namespace ArcLengthTwo

variable (W : LocWach PD LL O v n)

theorem φVB_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.φ.toLinearMap.restrictScalars Qp) := PD.φ_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem crisMap_φ {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V') (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by

  simp only [dv, map_sum, map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) :=
  dv_succ W T e b _

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun m' _ hm' => by simp [Pi.single_apply, hm']) (by simp)]
  simp

theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : Type} (s : Finset I)
    (a : I → O) (c₀ : I → Fin d → O) :
    dvO W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, algebraMap O LL (a i) • dvO W T e b (c₀ i) := by

  simp only [dvO, dv, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (x : O) (c₀ : Fin d → O) :
    dvO W T e b (fun m => x * c₀ m) = algebraMap O LL x • dvO W T e b c₀ := by
  simp only [dvO, dv, map_mul, Finset.smul_sum, smul_smul]

theorem filS_φ (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, ?_⟩
  · rw [hac]
    simpa using hy
  · simp

theorem filS_φ_inv (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u) : x ∈ FilS W T a 0 u := by
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := φVB_inj (by simpa using hyx)
  subst this
  refine ⟨y, ?_, by simp⟩
  rw [← hac]
  simpa using hy

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

theorem RepVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  apply Formalism.MainNotions.N.FrobeniusPowerSeries.repVV_smul_invariant <;> assumption

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, Pi.single_apply, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem avg_props {T : LocLat G Qp LL O} (a : ZMod n) {z : W.DD T} (hz : z ∈ W.N T)
    (hza : (letE a : LetA O n) • z = z) :
    (∑ δ ∈ W.DelF, W.γD T δ z) ∈ W.NΔ T ∧
      (letE a : LetA O n) • (∑ δ ∈ W.DelF, W.γD T δ z) = ∑ δ ∈ W.DelF, W.γD T δ z := by
  refine ⟨⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ' hδ' => ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
      (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp)
      (fun g _ => ?_)
    rw [W.γD_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← γA_letE W δ a, ← γD_smulA, hza]

end ArcLengthTwo

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup
open scoped TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem filV_sep {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hco : ∀ (a : ℤ) (w : V ⊗[Qp] BdR), w ∈ FilV PD (LL := LL) (V := V) a →
      ∀ j, E w j ∈ PD.Fil a := by
    intro a w hw
    obtain ⟨y, rfl⟩ := hw
    induction y using TensorProduct.induction_on with
    | zero => intro j; simp
    | tmul x f =>
      intro j
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul,
        Finsupp.mapRange_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
    | add x y hx hy =>
      intro j
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem (hx j) (hy j)
  have h0 : E z = 0 := by
    ext j
    exact PD.Fil_sep _ fun a => hco a z (hz a) j
  simpa using congrArg E.symm h0

theorem filS_top (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (A : ArcP n)
    (T : LocLat G Qp LL O) (hW : Win W A T) (a : ZMod n) (s : ℕ) (u : ℤ)
    (hu : ∀ x ∈ (A.ty (a - (s : ZMod n))).win A.G₀ A.S A.η, x < u) :
    FilS W T a s u = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨hxF, hxL⟩ := Submodule.mem_inf.mp hx
  suffices hx0 : x = 0 by simp [hx0]
  set i : ZMod n := a - (s : ZMod n) with hi
  obtain ⟨hbij, -, -⟩ := hcase
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
  have hez : ∀ z : K₀, e z = algebraMap K₀ K z := fun z => rfl
  have hover : ∀ z : K₀, τ (algebraMap K₀ K z) = W.emb i z := by
    intro z
    have : e.symm (algebraMap K₀ K z) = z := by
      rw [← hez, AlgEquiv.symm_apply_apply]
    show W.emb i (e.symm (algebraMap K₀ K z)) = W.emb i z
    rw [this]
  have hOver : Formalism.MainNotions.LiftingTheory.Over W τ i := by
    ext z
    exact hover z
  have hJ := hW.2 i τ hOver
  have hE : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T i τ hover hbij.2 ⟨x, hxL, rfl⟩
  have hV : ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) u :=
    (Submodule.mem_inf.mp hxF).2
  have hall : ∀ k : ℕ, ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ (u + k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, add_zero]
      exact Submodule.mem_inf.mpr ⟨hE, hV⟩
    | succ k ih =>
      have heq : FildR PD T.ρ τ (u + k + 1) = FildR PD T.ρ τ (u + k) := by
        by_contra h
        have := hu _ (hJ (u + k) h)
        omega
      rw [Nat.cast_succ, ← add_assoc, heq]
      exact ih
  have hallV : ∀ b : ℤ, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) b := by
    intro b
    by_cases h : b ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti h hV
    · have hk := (Submodule.mem_inf.mp (hall (b - u).toNat)).2
      have : u + ((b - u).toNat : ℤ) = b := by omega
      rwa [this] at hk
  have h0 := filV_sep _ hallV
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (h0.trans (map_zero _).symm)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem sum_split {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (π : R) (f : ℕ → M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ Finset.range N, π ^ r • f r = π • ∑ r ∈ Finset.range (N - 1), π ^ r • f (r + 1) + f 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.smul_sum, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ, mul_comm, mul_smul]

section Gen
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem g_step (L π g h a : R) (k k₂ r m : ℕ) (E γE x x' z : M)
    (hkx : L ^ k • (g • E) = π ^ r • x)
    (hzE : L ^ k₂ • (g • (γE - E)) = (π ^ r * π * π ^ m) • z)
    (h1x : L ^ k • ((g * (1 + π * h)) • γE) - π ^ r • x = a • (π ^ r • x) + π ^ (r + 1) • x') :
    π ^ r • (L ^ k₂ • (a • x) - π • (L ^ k₂ • (h • x) + L ^ k • ((1 + π * h) • (π ^ m • z)) -
      L ^ k₂ • x')) = 0 := by
  linear_combination (norm := module) (-(L ^ k₂)) • h1x + (L ^ k * (1 + π * h)) • hzE +
    (L ^ k₂ * (1 + π * h)) • hkx

theorem g_fin (L π g ε a : R) (k k₂ r : ℕ) (E x y : M) (hkx : L ^ k • (g • E) = π ^ r • x)
    (h4 : L ^ k₂ • (a • x) = π • y) :
    (L ^ (k + k₂) * (ε * a)) • (g • E) = π ^ (r + 1) • (ε • y) := by
  linear_combination (norm := module) (L ^ k₂ * ε * a) • hkx + (π ^ r * ε) • h4

theorem g_A (L π q P2 p1 aJ t : R) (κ' b1 κ κ₁ E σ e : ℕ) (FX FX' FD Fn Fz lam φHh y4 : M)
    (E1 : FX = π • FX' + L ^ κ₁ • FD) (E2 : Fn = FD + π • Fz)
    (E3 : q ^ b1 • Fn = L ^ E • (p1 ^ e • lam))
    (E4 : L ^ κ' • (L ^ κ • lam - L ^ σ • φHh) = (π * aJ) • y4)
    (ht : L ^ b1 * p1 ^ e - L ^ e * q ^ b1 = π * t) :
    L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz) +
        (L ^ (κ₁ + E + κ' + σ) * t) • (P2 • φHh)) := by
  have key : L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz)) +
      (L ^ (κ₁ + E + κ' + σ) * (L ^ b1 * p1 ^ e - L ^ e * q ^ b1)) • (P2 • φHh) := by
    linear_combination (norm := module) (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ)) • E1 -
    (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ + κ₁)) • E2 + (L ^ κ' * P2 * L ^ (b1 + κ + κ₁)) • E3 +
    (P2 * L ^ (b1 + κ₁ + E) * p1 ^ e) • E4
  rw [key, ht]
  module

theorem g_B (L π q P2 u3 Pk : R) (b1 κ c Rr R' M' : ℕ) (FX γFX Fx φHh γφHh φxH : M)
    (B1 : γFX - FX = (π ^ Rr * π ^ R') • Fx)
    (B2 : γφHh - φHh = (u3 * (π ^ Rr * π ^ M') * Pk) • φxH) :
    (q ^ b1 * P2) • (L ^ (b1 + κ) • γFX - L ^ c • γφHh - (L ^ (b1 + κ) • FX - L ^ c • φHh)) =
      π ^ Rr • ((L ^ (b1 + κ) * π ^ R' * (q ^ b1 * P2)) • Fx -
        (L ^ c * u3 * π ^ M' * Pk * q ^ b1) • (P2 • φxH)) := by
  linear_combination (norm := module) (q ^ b1 * P2 * L ^ (b1 + κ)) • B1 - (q ^ b1 * P2 * L ^ c) • B2

theorem g_K (L g π qB : R) (kU κ₁ b1 κ σ₁ E σ e₁ e₂ : ℕ) (Fy FZ φFX φφHh φV : M)
    (hrelF : L ^ κ₁ • Fy + (π * qB) • FZ = L ^ σ₁ • φFX)
    (hφV : φV = L ^ (b1 + κ) • φFX - L ^ (κ₁ + E + σ + (e₁ + e₂)) • φφHh) :
    L ^ (kU + κ₁) • g • (L ^ (b1 + κ) • Fy - L ^ (σ₁ + E + σ + e₁ + e₂) • φφHh) =
      L ^ σ₁ • (L ^ kU • (g • φV)) - (L ^ (kU + b1 + κ) * g * π) • (qB • FZ) := by
  rw [hφV]
  linear_combination (norm := module) (L ^ (kU + b1 + κ) * g) • hrelF

end Gen

variable (W : LocWach PD LL O v n)

theorem γ_mul_form {g g' h h' : LetA O n} (hg : W.γA W.gam g = g * (1 + W.π₀ * h))
    (hg' : W.γA W.gam g' = g' * (1 + W.π₀ * h')) :
    W.γA W.gam (g * g') = g * g' * (1 + W.π₀ * (h + h' + W.π₀ * h * h')) := by
  rw [map_mul, hg, hg']; ring

theorem γ_pow_form {g h : LetA O n} (hh : h ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hg : W.γA W.gam g = g * (1 + W.π₀ * h)) (k : ℕ) :
    ∃ h' ∈ W.AΔ, W.γA W.gam (g ^ k) = g ^ k * (1 + W.π₀ * h') := by
  induction k with
  | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨h', hh', e⟩ := ih
    refine ⟨h' + h + W.π₀ * h' * h, ?_, ?_⟩
    · exact W.AΔ.add_mem (W.AΔ.add_mem hh' hh) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh') hh)
    · rw [pow_succ, γ_mul_form W e hg]

theorem exists_pow_smul_eq_pi_pow_smul_of_twist_sub (T : LocLat G Qp LL O) (hC : Formalism.MainNotions.UnusedSlot80.Relay2.Ctx W T) (c : ZMod n)
    (g₀ h : LetA O n) (hh : h ∈ W.AΔ)
    (hγg : W.γA W.gam g₀ = g₀ * (1 + W.π₀ * h)) (R : ℕ) (E : W.DD T)
    (hE : ∃ (k : ℕ) (E' : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c E' ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ • E')
    (hγ : ∃ (k : ℕ) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c z ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • (W.γ T E - E)) = W.π₀ ^ R • z) :
    ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ R • x := by
  obtain ⟨k₂, z, hz, hzE⟩ := hγ
  have hπ : W.π₀ ∈ W.AΔ := hC.hπ
  have key : ∀ r, 1 ≤ r → r ≤ R → ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ r • x := by
    intro r hr1
    induction r with
    | zero => omega
    | succ r ih =>
      intro hrR
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        obtain ⟨k, E', hE', hk⟩ := hE
        exact ⟨k, E', hE', by rw [hk, zero_add, pow_one]⟩
      obtain ⟨k, x, hx, hkx⟩ := ih hpos (by omega)
      obtain ⟨x', hx', h1x⟩ := hC.H1 c r x hx
      obtain ⟨e, he⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.principal_unit_pow_sub_one_dvd W hC.inj hC.O2 r (hC.H2 r hpos)
      set a : LetA O n := algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) with ha
      rw [← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1), ← ha] at h1x
      have hγx : W.γ T (W.π₀ ^ r • x) =
          Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((g₀ * (1 + W.π₀ * h)) • W.γ T E) := by
        rw [← hkx, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, ← hγg]
        congr 1
        exact Formalism.MainNotions.LiftingTheory.frame_γD_smul W T W.gam g₀ E
      rw [hγx] at h1x
      have hR : W.π₀ ^ R = W.π₀ ^ r * W.π₀ * W.π₀ ^ (R - (r + 1)) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hR] at hzE
      obtain ⟨y, hy⟩ : ∃ y : W.DD T, y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (h • x) +
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((1 + W.π₀ * h) • (W.π₀ ^ (R - (r + 1)) • z)) -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • x' := ⟨_, rfl⟩
      have h3 : W.π₀ ^ r • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (a • x) - W.π₀ • y) = 0 := by
        rw [hy]; exact g_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkx hzE h1x
      have h4 := Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hC.hw r _ h3
      rw [sub_eq_zero] at h4
      have h1h : (1 + W.π₀ * h) ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hπ hh)
      have hyN : Formalism.MainNotions.LiftingTheory.InNΔi W T c y := by
        rw [hy]
        refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T c (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T c ?_ ?_)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ hx')
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hh hx)
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c h1h
            (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ _) hz))
      obtain ⟨ε, hε⟩ : ∃ ε : LetA O n, ε = algebraMap O (LetA O n) e := ⟨_, rfl⟩
      have he' : ε * a = Formalism.MainNotions.ArcLiftingSetup.lA W ^ (1 + padicValNat PD.p r) := by
        rw [hε, ha, ← map_mul, he, map_pow, map_natCast]; rfl
      refine ⟨k + k₂ + (1 + padicValNat PD.p r), ε • y,
        Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (by rw [hε]; exact W.AΔ.algebraMap_mem e) hyN, ?_⟩
      rw [pow_add, ← he']
      exact g_fin _ _ _ _ _ _ _ _ _ _ _ hkx h4
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    obtain ⟨k, E', hE', hk⟩ := hE
    exact ⟨k, W.π₀ • E', Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hπ hE', by rw [hk, pow_zero, one_smul]⟩
  · exact key R hpos le_rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA
end
end
