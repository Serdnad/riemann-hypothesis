module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Formalism.IncomingBounds.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle032
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GoodCorank

variable {C : Type} [Field C] {V : VF C}

theorem div_int {x y : C} (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  by_cases hy : y = 0
  · subst hy; simpa using VF.Ge.zero (V := V) 0
  · have e : V.v x = V.v y + V.v (x / y) := by
      rw [← V.v.map_mul, mul_div_cancel₀ _ hy]
    have hy' : V.v y ≠ ⊤ := by
      intro h0
      have h1 : V.v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, V.v.map_one]
      rw [V.v.map_mul, h0, top_add] at h1
      exact WithTop.top_ne_zero h1
    unfold VF.Ge
    rw [e] at h
    have h2 : V.v y + 0 ≤ V.v y + V.v (x / y) := by simpa using h
    simpa using (WithTop.add_le_add_iff_left hy').mp h2

theorem ge_ite (p : Prop) [Decidable p] : V.Ge 0 (if p then (1 : C) else 0) := by
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem exists_cut {N : ℕ} (φ : Fin (N + 1) → C) :
    ∃ A : Fin N → Fin (N + 1) → C, IsSat V A ∧ ∀ ν, ∑ k, A ν k * φ k = 0 := by
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k => V.v (φ k)) Finset.univ_nonempty
  refine ⟨fun ν k => (if k = k0.succAbove ν then 1 else 0) -
      (φ (k0.succAbove ν) / φ k0) * (if k = k0 then 1 else 0), ⟨fun ν k => ?_,
      fun k c => if k = k0.succAbove c then 1 else 0, fun k c => ge_ite _, fun c c' => ?_⟩, fun ν => ?_⟩
  · exact (ge_ite _).sub ((div_int (hk0 _ (Finset.mem_univ _))).mul_int (ge_ite _))
  · simp [Fin.succAbove_ne, eq_comm]
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : φ k0 = 0
    · have h1 := hk0 (k0.succAbove ν) (Finset.mem_univ _)
      rw [h0, V.v.map_zero, top_le_iff] at h1
      have h2 : φ (k0.succAbove ν) = 0 := by
        by_contra hy
        have h3 : V.v (φ (k0.succAbove ν) * (φ (k0.succAbove ν))⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hy, V.v.map_one]
        rw [V.v.map_mul, h1, top_add] at h3
        exact WithTop.top_ne_zero h3
      simp [h0, h2]
    · rw [div_mul_cancel₀ _ h0, sub_self]

theorem isSat_comp {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by
  obtain ⟨hA0, A', hA', hAA⟩ := hA
  obtain ⟨hw0, w', hw', hww⟩ := hw
  refine ⟨fun ν c => VF.Ge.sum fun k _ => (hA0 _ _).mul_int (hw0 _ _),
    fun x c => ∑ k, w' x k * A' k c, fun x c => VF.Ge.sum fun k _ => (hw' _ _).mul_int (hA' _ _),
    fun c c' => ?_⟩
  have e1 : Matrix.of A * Matrix.of A' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hAA i j
  have e2 : Matrix.of w * Matrix.of w' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hww i j
  have e3 : (Matrix.of A * Matrix.of w) * (Matrix.of w' * Matrix.of A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of w), e2, Matrix.one_mul, e1]
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun e3 c) c'

theorem exists_sat_ker {I κ : Type} [Fintype I] [DecidableEq I] (P : Finset I) (φ : κ → I → C) (S : Finset κ) :
    ∃ (N : ℕ) (w : Fin N → I → C), IsSat V w ∧ (∀ ν c, c ∉ P → w ν c = 0) ∧
      (∀ ν, ∀ b ∈ S, ∑ c, w ν c * φ b c = 0) ∧ P.card ≤ N + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨P.card, fun ν c => if c = (P.equivFin.symm ν : I) then 1 else 0, ⟨fun ν c => ge_ite _,
      fun c ν => if c = (P.equivFin.symm ν : I) then 1 else 0, fun c ν => ge_ite _, fun ν ν' => ?_⟩,
      fun ν c hc => ?_, by simp, by simp⟩
    · simp [Subtype.val_inj, eq_comm]
    · refine if_neg ?_
      rintro rfl
      exact hc (P.equivFin.symm ν).2
  | insert b S hb ih =>
    obtain ⟨N, w, hs, hP, hφ, hN⟩ := ih
    rw [Finset.card_insert_of_notMem hb]
    cases N with
    | zero => exact ⟨0, w, hs, hP, fun ν => ν.elim0, by omega⟩
    | succ N =>
      obtain ⟨A, hA, hA0⟩ := exists_cut (V := V) (fun k => ∑ c, w k c * φ b c)
      have key : ∀ ν b', ∑ c, (∑ k, A ν k * w k c) * φ b' c = ∑ k, A ν k * ∑ c, w k c * φ b' c := by
        intro ν b'
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      refine ⟨N, fun ν c => ∑ k, A ν k * w k c, isSat_comp hA hs, fun ν c hc => ?_, fun ν b' hb' => ?_, by omega⟩
      · simp [hP _ c hc]
      · rw [key]
        rcases Finset.mem_insert.mp hb' with rfl | hb'
        · exact hA0 ν
        · simp [hφ _ b' hb']

variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem good_of_int (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by
  obtain ⟨z, hz, hz0, hzp⟩ := G.t4 (a + 1) (fun b => y 1 (Sum.inl b)) h1
    (fun b hb => hy.2.2 1 _ (by simpa using hb))
  refine ⟨y - Vpow 1 z, ⟨G.Ty.sub_mem hy.1 (G.V_mem _ hz), ?_, fun i n hn => ?_⟩, fun c => ?_⟩
  · funext n
    simp [Vpow, hy.2.1]
  · cases i with
    | zero => simp [Vpow, hy.2.2 0 n hn]
    | succ i =>
      have : z i n = 0 := hzp i n (by
        intro hc; apply hn; rw [hc]; push_cast; ring)
      simp [Vpow, hy.2.2 _ n hn, this]
  · simp [Vpow, hz0]

theorem good_of_ker (G : Cart V d I J) {a : ZMod d} (r : I → I → C)
    (hr : ∀ b c, r b c ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b)) {u : I → C} (hu : ∀ c, V.Ge 0 (u c))
    (hp : ∀ c, G.ty (Sum.inl c) ≠ a → u c = 0)
    (hk : ∀ b, G.ty (Sum.inl b) = a + 1 → ∑ c, u c * r b c = 0) : ∃ x, G.Good a u x := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hy : G.IsCurve a u (∑ c, teich V.l (u c) (G.std c)) := by
    refine ⟨G.Ty.sum_mem fun c _ => G.teich_mem _ (hu c) _ (G.std_spec c).1, ?_, fun i n hn => ?_⟩
    · funext n
      have : ∀ b, G.std b 0 n = Sum.elim (Pi.single b 1) 0 n := fun b => by rw [(G.std_spec b).2.1]
      simp only [Finset.sum_apply, teich, this, pow_zero, pow_one]
      cases n with
      | inl c => simp [Pi.single_apply]
      | inr j => simp
    · simp only [Finset.sum_apply, teich]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : G.ty (Sum.inl c) = a
      · rw [(G.std_spec c).2.2 i n (by rwa [hc]), mul_zero]
      · rw [hp c hc, zero_pow (lpos i), zero_mul]
  refine good_of_int G hy fun b => ?_
  by_cases hb : G.ty (Sum.inl b) = a + 1
  · have hrint : ∀ c, V.Ge 0 (r b c) := fun c => by
      refine GlobalTheory.AdaptedChain.int_of_pow V.l_prime.ne_zero ?_
      rw [hr]
      simpa using (G.bound0 1 _ (G.std_spec c).1 (Sum.inl b)).l_mul
    have hf := (GlobalTheory.AdaptedChain.frob_sum Finset.univ (fun c => u c * r b c)
      (fun c => (hu c).mul_int (hrint c)) 1).neg
    rw [hk b hb, zero_pow (lpos 1), zero_sub, neg_neg] at hf
    have e : ∑ c, (u c * r b c) ^ V.l ^ 1 =
        (V.l : C) * (∑ c, teich V.l (u c) (G.std c)) 1 (Sum.inl b) := by
      simp only [Finset.sum_apply, teich, pow_one, mul_pow, hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at hf
    simpa using hf.of_l_mul
  · rw [hy.2.2 1 _ (by simpa using hb)]
    exact VF.Ge.zero 0

theorem exists_good_sat (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  have hex : ∀ b c : I, ∃ r : C, r ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b) := fun b c =>
    IsAlgClosed.exists_pow_nat_eq _ V.l_prime.pos
  choose r hr using hex
  obtain ⟨N, w, hs, hP, hφ, hN⟩ := exists_sat_ker (V := V)
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a) r
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1)
  have hp : ∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0 := fun ν c hc => hP ν c (by simpa using hc)
  have hx : ∀ ν, ∃ x, G.Good a (w ν) x := fun ν =>
    good_of_ker G r hr (hs.1 ν) (hp ν) fun b hb => hφ ν b (by simpa using hb)
  choose x hx using hx
  exact ⟨N, w, x, hx, hp, hs, hN⟩

end GlobalTheory.GoodCorank

end
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm.Axis

variable {C : Type} [Field C] {ι ι' : Type}

def VanishesOnFirstAxis (F : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ F = 0

theorem VanishesOnFirstAxis.mul_left {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (G : MvPowerSeries (ι ⊕ ι') C) : VanishesOnFirstAxis (G * F) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [h p.2, mul_zero]
  intro b
  have h1 := hμ b
  rw [← hp', Finsupp.add_apply] at h1
  omega

theorem VanishesOnFirstAxis.smul {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (c : C) : VanishesOnFirstAxis (c • F) := by
  intro μ hμ
  rw [map_smul, h μ hμ, smul_zero]

theorem VanishesOnFirstAxis.sum {α : Type} (s : Finset α) {F : α → MvPowerSeries (ι ⊕ ι') C}
    (h : ∀ x, VanishesOnFirstAxis (F x)) : VanishesOnFirstAxis (∑ x ∈ s, F x) := by
  intro μ hμ

  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => h x μ hμ

theorem vanishes_X_inr (b : ι') :
    VanishesOnFirstAxis (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have h1 := hμ b
  rw [h] at h1
  simp at h1

theorem VanishesOnFirstAxis.of_dvd {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by
  obtain ⟨K, rfl⟩ := hd
  rw [mul_comm]
  exact h.mul_left K

theorem vanishes_mainM [Fintype ι] [Fintype ι'] (V : VF C) (i : ℕ) (Φ : ι' → ι → C) :
    VanishesOnFirstAxis (mainM V i Φ) :=
  (VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ =>
    ((vanishes_X_inr b).mul_left _).smul _).smul _

theorem vanishes_hM {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) :
    VanishesOnFirstAxis (X.hM g a i e v') := by
  intro μ hμ
  unfold RowData.hM hPullW

  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
  intro w
  simp [map_sum]))]
  refine finsum_eq_zero_of_forall_eq_zero fun ν => ?_
  by_cases hν : ∀ w ∈ ν.support, w.1 = g
  · rw [X.hL_axes g _ _ ν (Or.inl hν), zero_smul]
  · push Not at hν
    obtain ⟨w, hw, hg⟩ := hν
    have h1 : VanishesOnFirstAxis
        ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
          ∑ b : ι', toW (1 - g) (v' b) w •
            (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) := by
      have h0 : ∀ c, toW g (e c) w = 0 := fun c => by simp [toW, hg]
      simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
      exact VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _
    rw [h1.of_dvd _ μ hμ, smul_zero]
    unfold Finsupp.prod
    exact (dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)

theorem coeff_hM_sub_mainM_eq_zero : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d]
    (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J)
    (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  intro C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ
  rw [map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]

end GlobalTheory.MainTerm.Axis
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.LowerSubst

open MvPowerSeries

variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)

def IntOn (g : MvPowerSeries σ C) : Prop := ∀ μ, P μ → V.Ge 0 (coeff μ g)

theorem intOn_one : IntOn V P (1 : MvPowerSeries σ C) := by
  intro α _
  rw [coeff_one]
  split_ifs with h
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intOn_mul (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine VF.Ge.sum fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact VF.Ge.mul_int (hf _ (hP α _ (hx ▸ le_self_add) hα)) (hg _ (hP α _ (hx ▸ le_add_self) hα))

theorem intOn_prod (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, IntOn V P (f i)) : IntOn V P (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOn V P) (fun _ _ => intOn_mul V P hP) (intOn_one V P) h

theorem intOn_pow (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f : MvPowerSeries σ C} (hf : IntOn V P f)
    (n : ℕ) : IntOn V P (f ^ n) := by
  induction n with
  | zero => simpa using intOn_one V P
  | succ n ih => rw [pow_succ]; exact intOn_mul V P hP ih hf

theorem subst_int_on_lower :
    ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  intro C _ V σ τ _ _ P hP γ T hγ hT0 hT α hα
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT0
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs γ α)]
  refine VF.Ge.sum fun β _ => ?_
  have hp : IntOn V P (β.prod fun s e => T s ^ e) :=
    intOn_prod V P hP _ _ fun s _ => intOn_pow V P hP (hT s) (β s)
  rw [smul_eq_mul]
  exact VF.Ge.mul_int (hγ β) (hp α hα)

end GlobalTheory.LowerSubst
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | exact GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | (intros; apply GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers <;> assumption)
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharGerm

section Series

variable {R₀ κ : Type} [CommRing R₀]

end Series

section Torsion

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)





end Torsion

section Value

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

lemma comp_χ_of_le {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  induction n, h using Nat.le_induction with
  | base => rw [torsion_hom_ext huv]
  | succ n hmn ih =>
    have h1 : (u ≫ torsion.ι G (p ^ m)) ^ (p ^ n) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, pow_mul, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, one_pow]
    rw [ih (torsionLift _ h1) (torsionLift_ι _ _).symm]
    exact χ.compat n _ _ _ (by rw [torsionLift_ι, huv])

lemma comp_χ_eq {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm


end Value

end CharGerm

end GlobalTheory
end
