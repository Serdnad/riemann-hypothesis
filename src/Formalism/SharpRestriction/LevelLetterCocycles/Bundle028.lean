module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
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

@[expose] public section

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

theorem filV_sep (z : V ⊗[Qp] BdR) (h : ∀ a, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  have hfree : Module.Free Qp V := Module.Free.of_divisionRing Qp V
  let 𝔟 := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟
  have hcoord : ∀ a, ∀ w ∈ FilV PD (LL := LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by
    intro a w hw i
    obtain ⟨u, rfl⟩ := hw
    induction u using TensorProduct.induction_on with
    | zero => simp [(PD.Fil a).zero_mem]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
      simp only [Finsupp.mapRange_apply]
      have : (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR) := by
        rw [algebraMap_smul]
      rw [this]
      exact (PD.Fil a).smul_mem _ y.2
    | add u₁ u₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem h₁ h₂
  have hE : E z = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hcoord a z (h a) i
  exact E.injective (by rw [hE, map_zero])

end Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem fil_step (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
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

theorem fil_low (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) : x ∈ FilCris PD T.ρ (-(H : ℤ)) := by
  obtain ⟨u₀, hu₀⟩ := filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : -(H : ℤ) ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hx0
      | succ k ih =>
        intro hk
        have := fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega)
          hxD (ih (by push_cast at hk; omega))
        push_cast; rwa [← add_assoc]
    have := key (-(H : ℤ) - u₀).toNat (by omega)
    rwa [show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega] at this

theorem fil_high (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ)) (u : ℤ) (hu : (H : ℤ) < u) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) (hx : x ∈ FilCris PD T.ρ u) : x = 0 := by
  have key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have := fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih
      push_cast; rwa [← add_assoc]
  have hall : ∀ a, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by
    intro a
    by_cases ha : a ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2
    · have := (key (a - u).toNat).2
      rwa [show u + ((a - u).toNat : ℤ) = a by omega] at this
  have h0 := filV_sep (PD := PD) _ hall
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup in
theorem ps_zero : ps W 0 = W.π₀ + lA W := by
  simp [ps, qA]

open Formalism.MainNotions.ArcLiftingSetup in
theorem ps_succ (s : ℕ) : ps W (s + 1) = W.φA (ps W s) := by
  simp only [ps, pow_succ', AlgHom.mul_apply]

theorem hs_succ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (a : ZMod n) (e s : ℕ) :
    A.Hs a (e + 1) (s + 1) = A.Hs (a - 1) e s := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [show a - ((s + 1 : ℕ) : ZMod n) = a - 1 - (s : ZMod n) by push_cast; ring,
    show e + 1 - (s + 1) = e - s by omega]

def LamUp (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) : LetA O n :=
  W.φA (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e)

theorem lam_succ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) =
      Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 * LamUp W A c' e := by
  unfold LamUp
  conv_lhs => unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, ← ps_succ, hs_succ]
  congr 2
  push_cast; ring

def Cop (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = r * x + s * z

theorem lA_mem (m : ℕ) : Formalism.MainNotions.ArcLiftingSetup.lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

theorem cop_symm {x z : LetA O n} (h : Cop W x z) : Cop W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

theorem cop_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : Cop W x z) (h2 : Cop W y z) : Cop W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (lA_mem W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

theorem cop_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∀ N : ℕ, Cop W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact cop_mul W (W.AΔ.pow_mem hx N) hz ih h

theorem cop_prod {ι : Type} (s : Finset ι) (x : ι → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, Cop W (x i) z) :
    Cop W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact cop_mul W (W.AΔ.prod_mem fun i _ => hx i) hz (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      (h a (Finset.mem_insert_self a s))

theorem crt {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∃ m : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u₁ ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = u₀ + u₁ ∧
      (∃ r ∈ W.AΔ, u₀ = x * r) ∧ ∃ s ∈ W.AΔ, u₁ = z * s := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, r * x, W.AΔ.mul_mem hr hx, s * z, W.AΔ.mul_mem hs hz, e, ⟨r, hr, mul_comm _ _⟩,
    ⟨s, hs, mul_comm _ _⟩⟩

theorem coprime_uniformizer_first_factor : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
  ⟨1, -1, W.AΔ.neg_mem W.AΔ.one_mem, 1, W.AΔ.one_mem, by rw [ps_zero]; ring⟩

variable [IsDomain O]

theorem coprime_frobenius_uniformizer_powers (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP hR s hs
  have hq : Formalism.MainNotions.WachCoordinates.qP W = Formalism.MainNotions.ArcLiftingSetup.ps W 0 := by
    rw [ps_zero]; rfl
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
      (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, 1, W.AΔ.one_mem, -a, W.AΔ.neg_mem haΔ, ?_⟩
  rw [hq] at ha
  linear_combination (-1 : LetA O n) * e1 - ha

theorem cop_lamUp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e N : ℕ) :
    Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ N) := by
  have hp0Δ : Formalism.MainNotions.ArcLiftingSetup.ps W 0 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 0
  have hps : ∀ s, Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hU : Cop W (LamUp W A c' e) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
    unfold LamUp Formalism.MainNotions.ArcLiftingSetup.abelian₂
    rw [map_prod]
    refine cop_prod W _ _ (fun s => ?_) hp0Δ fun s _ => ?_
    · rw [map_pow, ← ps_succ]; exact W.AΔ.pow_mem (hps _) _
    · rw [map_pow, ← ps_succ]
      exact cop_pow W (hps _) hp0Δ (coprime_frobenius_uniformizer_powers W hR hp0 (s + 1) (by omega)) _
  have hUΔ : LamUp W A c' e ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A _ e)
  have h1 : Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
    cop_mul W hR.1 hp0Δ (coprime_uniformizer_first_factor W) (cop_pow W hUΔ hp0Δ hU 2)
  have hxΔ : W.π₀ * LamUp W A c' e ^ 2 ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hUΔ 2)
  exact cop_symm W (cop_pow W hp0Δ hxΔ (cop_symm W h1) N)

end Formalism.MainNotions.UnusedSlot80.LevC
end
end
