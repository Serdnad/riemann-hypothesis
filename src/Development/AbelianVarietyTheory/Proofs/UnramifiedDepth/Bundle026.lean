module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle009
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle010
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

theorem toW_same {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by
  simp [toW]

theorem toW_other {C : Type} [Field C] {I : Fin 2 → Type} {g g' : Fin 2} (h : g' ≠ g) (u : I g → C)
    (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]

theorem hPullW_upG {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (g : Fin 2) (F : MvPowerSeries (I g) C) (a : ι → WV I → C)
    (b : ι' → WV I → C) :
    hPullW (upG g F) a b = MvPowerSeries.subst (fun x : I g =>
      (∑ c, a c ⟨g, x⟩ • MvPowerSeries.X (Sum.inl c) + ∑ c, b c ⟨g, x⟩ • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) F := by
  have hb : MvPowerSeries.HasSubst (fun w : WV I =>
      (∑ c, a c w • MvPowerSeries.X (Sum.inl c) + ∑ c, b c w • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have ha : MvPowerSeries.HasSubst (fun x : I g => (MvPowerSeries.X ⟨g, x⟩ : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold hPullW upG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hb]

theorem rename_linPull {C : Type} [Field C] {σ ι τ : Type} [Fintype σ] [Fintype ι] (f : ι → τ)
    (e : ι → σ → C) (F : MvPowerSeries σ C) :
    MvPowerSeries.rename f (linPull e F) = MvPowerSeries.subst (fun x : σ =>
      (∑ c, e c x • MvPowerSeries.X (f c) : MvPowerSeries τ C)) F := by
  have ha : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ c : ι, e c x • MvPowerSeries.X c : MvPowerSeries ι C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold linPull
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp f)]
  congr 1
  funext x
  rw [← MvPowerSeries.rename_eq_subst]
  simp

theorem hPullW_upG_toW : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  intro C _ I _ g ι ι' _ _ e v'
  have h : g ≠ 1 - g := by fin_cases g <;> decide
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h]
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h.symm]

end GlobalTheory.MainTerm
end
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.ChainStep

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) :
    V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right (by simpa using hb))

theorem int_mul_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

def intRing (V : VF C) : Subring C where
  carrier := {a | V.Ge 0 a}
  mul_mem' ha hb := VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' ha hb := VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' ha := VF.Ge.neg ha

theorem add_pow_congr {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM ((a + b) ^ (V.l ^ n) - (a ^ (V.l ^ n) + b ^ (V.l ^ n))) := by
  have h : ∃ r : intRing V, ((⟨a, ha⟩ : intRing V) + ⟨b, hb⟩) ^ (V.l ^ n) =
      (⟨a, ha⟩ : intRing V) ^ (V.l ^ n) + (⟨b, hb⟩ : intRing V) ^ (V.l ^ n) + (V.l : intRing V) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : intRing V) ⟨b, hb⟩ n
    first
      | exact ⟨r, hr⟩
      | exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (fun z : intRing V => (z : C)) hr
  push_cast at h2
  rw [h2, add_sub_cancel_left]
  exact mm_mul_int mm_l r.2

theorem sum_pow_congr {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) (n : ℕ) :
    V.MM ((∑ i ∈ s, f i) ^ (V.l ^ n) - ∑ i ∈ s, f i ^ (V.l ^ n)) := by
  induction s using Finset.induction_on with
  | empty => simpa [V.l_prime.ne_zero] using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h' := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := add_pow_congr (h a (Finset.mem_insert_self a s)) (VF.Ge.sum h') n
    have h2 := mm_add h1 (ih h')
    convert h2 using 1
    ring

theorem even_val_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d)).val ↔ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2,
    Nat.add_mod, Nat.mod_mod_of_dvd _ h2]
  simp

theorem big_add {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by
  fin_cases g
  · exact (hA.2 _).2 ((even_val_add hA.1 a s).2 ((hA.2 _).1 h))
  · have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
    refine (h1 _).2 fun h2 => (h1 _).1 h ?_
    exact (hA.2 _).2 ((even_val_add hA.1 a s).1 ((hA.2 _).1 h2))

theorem mm_of_tan {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : z c = ∑ k, (∑ b, z b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, z b * S.tan b k * S.U⁻¹ k c = z b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [h2]
  exact mm_sum fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem rank_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  intro C _ V d _ I J _ _ X hA g a hbig i S Z D hD s hs m y hy hyi N x hx hxi hker
  set F : Finset (I g) := Finset.univ.filter (fun c => D.lev c = s) with hF
  have hFm : ∀ c, c ∈ F ↔ D.lev c = s := fun c => by simp [hF]
  have hDi : D.i = i := hD.2.2.1
  have hDl : D.l = V.l := hD.2.1
  have hDv : D.v = V.v := hD.1
  have hgood : ∀ c ∈ F, D.good c := fun c hc =>
    D.pure_good c (by rw [(hFm c).1 hc, hDi]; omega)
  let w : Fin N → I g → C := fun ν c => ∑ δ, x ν δ * y δ c
  have hw : ∀ ν c, V.Ge 0 (w ν c) := fun ν c => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (hy δ c)
  have hG : ∀ c ∈ F, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 := hD.good (hgood c hc)
    rwa [hD.2.2.2.2 c (by rw [(hFm c).1 hc]; omega), (hFm c).1 hc] at h1
  have hal : ∀ c ∈ F, ∀ e, V.Ge 0 ((V.l : C) * D.al c 2 e) := fun c hc e =>
    hDl ▸ hD.l_mul_al_two_int (hgood c hc) e
  have key := X.R1 hA g _ (big_add X hA g a hbig s) N
    (fun ν => ∑ c ∈ F, w ν c • S.tan c) (fun ν => ∑ c ∈ F, teich V.l (w ν c) (S.cur c))
    (fun ν => Cart.Good.comb F (fun c _ => hw ν c) hG) ?_ ?_
  · omega
  · intro ν k
    rw [Cart.scaledSecond_sum]
    have e1 : ∑ c ∈ F, w ν c ^ (V.l ^ 2) * (X.G g).V2 (S.cur c) k =
        ∑ e, (∑ c ∈ F, w ν c ^ (V.l ^ 2) * ((V.l : C) * D.al c 2 e)) * S.tan e k := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := hD.2.2.2.1 c 2 k (by norm_num)
      simp only [Sys.al, Sys.cur_zero_inl] at h1
      simp only [Cart.V2, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e1]
    refine mm_sum fun e _ => mm_mul_int ?_ (tan_int S e k)
    by_cases he : D.lev e = s + 1
    · have h1 := hker ν e he
      have h2 : V.MM (∑ c ∈ F, (w ν c ^ (V.l ^ 2) - ∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) *
          ((V.l : C) * D.al c 2 e)) :=
        mm_sum fun c hc => mm_mul_int
          (sum_pow_congr (fun δ _ => (hx ν δ).mul_int (hy δ c)) 2) (hal c hc e)
      have e2 : ∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ F, (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2) =
          ∑ c ∈ F, (∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) * ((V.l : C) * D.al c 2 e) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun δ _ => by
          rw [mul_pow]; ring
      convert mm_add h1 h2 using 1
      rw [e2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    · refine mm_sum fun c hc => int_mul_mm ((hw ν c).pow _) ?_
      have hc' := (hFm c).1 hc
      rw [D.al_two c (by rw [hc', hDi]; omega) e,
        D.g_supp c (by rw [hc', hDi]; omega) e (by rw [hc']; exact he), hDl, zero_add,
        mul_inv_cancel_left₀ VF.l_ne_zero]
      refine mm_mul_int mm_l ?_
      have := D.lam_int c e
      rw [hDv] at this
      simpa [VF.Ge] using this
  · intro co hco hmm
    refine hxi co hco (hyi (fun δ => ∑ ν, co ν * x ν δ)
      (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) ?_)
    refine mm_of_tan S _ fun k => ?_
    convert hmm k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hF, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : D.lev c = s
    · simp only [hc, if_true, w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun δ _ => by ring
    · simp [hc]

end GlobalTheory.ChainStep
end
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot

namespace GlobalTheory.LastStep

theorem mm_mul_int {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)

theorem mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_of_tan {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
    {G : Cart V d I J} (S : Sys G) (w : I → C) (h : ∀ k, V.MM (∑ c, w c * S.tan c k)) (c : I) :
    V.MM (w c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [e]
  exact mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  have mm_pow : ∀ {a : C}, V.MM a → ∀ {n : ℕ}, n ≠ 0 → V.MM (a ^ n) := by
    intro a ha n hn
    unfold VF.MM at *
    rw [V.v.map_pow]
    exact nsmul_pos ha hn
  have ge_of_pow : ∀ {a : C} {n : ℕ}, n ≠ 0 → V.Ge 0 (a ^ n) → V.Ge 0 a := by
    intro a n hn ha
    unfold VF.Ge at *
    rw [V.v.map_pow] at ha
    rw [WithTop.coe_zero] at ha ⊢
    by_contra h
    exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))
  let R : Subring C := {
    carrier := {x | V.Ge 0 x}
    mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
    one_mem' := VF.Ge.one
    add_mem' := fun ha hb => VF.Ge.add ha hb
    zero_mem' := VF.Ge.zero 0
    neg_mem' := fun ha => VF.Ge.neg ha }
  have mm_add_pow : ∀ (e : ℕ) {a b : C}, V.Ge 0 a → V.Ge 0 b →
      V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
    intro e a b ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : R) (⟨b, hb⟩ : R) e
    have h := congrArg (Subtype.val) hr
    push_cast at h
    rw [h, add_sub_cancel_left]
    have hr0 : V.Ge 0 (r : C) := r.2
    have mm_of_ge_one : ∀ {x : C}, V.Ge 1 x → V.MM x := by
      intro x hx
      refine lt_of_lt_of_le ?_ hx
      exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
    apply mm_of_ge_one
    first
      | simpa using hr0.l_mul
      | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul
  have mm_sum_pow : ∀ (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C),
      (∀ i ∈ s, V.Ge 0 (x i)) →
      V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
    intro e ι s x hx
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
      unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
      convert h using 1 <;> ring
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]

end GlobalTheory.LastStep
end

section

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

theorem _root_.GlobalTheory.T.exists_finite_dvr_extension_embedding_residueField : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by
  first | exact @GlobalTheory.exists_finite_dvr_residueField_ringHom | exact GlobalTheory.exists_finite_dvr_residueField_ringHom | (intros; apply GlobalTheory.exists_finite_dvr_residueField_ringHom <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.padicInt_algebra_of_isAdicComplete_matrix_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O], Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ) (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]), f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  first | exact @GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | exact GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | (intros; apply GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique <;> assumption)
end
