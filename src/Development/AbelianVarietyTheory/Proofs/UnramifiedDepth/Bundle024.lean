module

public import Formalism.IncomingBounds.Bundle002
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle022
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle010
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.AddChar


open MvPowerSeries in
theorem subst_zero_eq {C : Type} [Field C] {κ τ : Type} [Fintype κ] (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun _ : κ => (0 : MvPowerSeries τ C)) F = MvPowerSeries.C (constantCoeff F) := by
  classical
  have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  ext m
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_one, coeff_C]
  · intro d hd
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hd
    have : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 := by
      refine Finset.prod_eq_zero (i := w) (by simpa using hw) ?_
      exact zero_pow (by simpa using hw)
    simp [this]


open MvPowerSeries in
theorem eq_mvExp_of_additive : ∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] (U : MvPowerSeries κ C), MvPowerSeries.constantCoeff U = 1 → MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) + MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U = MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U * MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U → U = mvExp (∑ i : κ, MvPowerSeries.coeff (Finsupp.single i 1) U • (MvPowerSeries.X i : MvPowerSeries κ C)) := by
  classical
  intro C _ _ κ _ U h0 h
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C)) := fun a =>
    hasSubst_of_constantCoeff_zero (by simp)
  let p : Fin 2 × κ → MvPowerSeries κ C := fun x => if x.1 = 0 then X x.2 else 0
  have hp : HasSubst p := hasSubst_of_constantCoeff_zero (by
    intro x; simp only [p]; split_ifs <;> simp)
  have hE : constantCoeff U = 1 ∧ ∀ w, pderiv w U = coeff (Finsupp.single w 1) U • U := by
    refine ⟨h0, fun w => ?_⟩
    have h1 := congrArg (pderiv (R := C) ((1 : Fin 2), w)) h
    rw [Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp),
      Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w,
      Finset.sum_eq_zero] at h1
    · simp [pderiv_X, Pi.single_apply] at h1
      have h2 := congrArg (subst p) h1
      rw [subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp,
        subst_comp_subst_apply (hB 1) hp] at h2
      simp only [subst_add hp, subst_X hp, p] at h2
      simp [subst_zero_eq] at h2
      have hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F :=
        fun F => congrFun subst_self F
      rw [hs, hs] at h2
      rw [h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]
      simp
    all_goals simp +contextual [pderiv_X, Pi.single_apply]
  have hcoeff : ∀ (F : MvPowerSeries κ C),
      (constantCoeff F = 1 ∧ ∀ w, pderiv w F = coeff (Finsupp.single w 1) U • F) →
      ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod (fun s k => coeff (Finsupp.single s 1) U ^ k) := by
    intro F h
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Finsupp.degree_eq_zero_iff] at hm
      subst hm
      simp [mfact, h.1]
    | succ n ih =>
      intro m hm
      have hne : m ≠ 0 := by rintro rfl; simp at hm
      obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        simp at hw; omega
      have hd : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm; omega
      have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
      rw [coeff_pderiv, coeff_smul] at h1
      have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
        unfold mfact
        have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
        have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
        rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
        simp [Nat.factorial_succ, mul_assoc]
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
        Finsupp.prod_single_index (by simp)]
      push_cast
      linear_combination (mfact m' : C) * h1
  have hF : constantCoeff (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) = 1 ∧
      ∀ w, pderiv w (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) =
        coeff (Finsupp.single w 1) U • mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C)) := by
    constructor
    · rw [← coeff_zero_eq_constantCoeff_apply, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl)]; simp
    · intro w
      ext m
      have hL : pderiv w (∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) = MvPowerSeries.C ((coeff (Finsupp.single w 1) U)) := by

        rw [map_sum, Finset.sum_eq_single w]
        · simp [smul_eq_C_mul]
        · intro b _ hb; simp [pderiv_X_of_ne hb]
        · simp
      rw [coeff_pderiv, coeff_smul, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), map_add (f := _), Finsupp.degree_single,
        Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
      have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
          ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ 0) = 0 := by
        rw [pow_zero, coeff_one, if_neg]
        intro h
        have := DFunLike.congr_fun h w
        simp at this
      rw [h0, zero_div, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := coeff_pderiv (i := w) ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ (k + 1)) m
      rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := κ) (R := C)),
        coeff_mul_C, coeff_C_mul] at h1
      have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
      rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
      push_cast at hk1 ⊢
      field_simp
  ext m
  have hm : (mfact m : C) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    unfold mfact
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hm ((hcoeff U hE _ m rfl).trans (hcoeff _ hF _ m rfl).symm)

end GlobalTheory.AddChar
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.SemilinearNullity

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  refine V.v.map_lt_add ha ?_
  rw [V.v.map_neg]; exact hb

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_inv {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by
  have h0 : a ≠ 0 := by rintro rfl; exact h mm_zero
  show (0 : WithTop ℝ) ≤ V.v a⁻¹
  have e : V.v a⁻¹ + V.v a = 0 := by rw [← V.v.map_mul, inv_mul_cancel₀ h0, V.v.map_one]
  have h1 : V.v a ≤ 0 := not_lt.mp h
  calc (0 : WithTop ℝ) = V.v a⁻¹ + V.v a := e.symm
    _ ≤ V.v a⁻¹ := add_le_of_nonpos_right h1

def IndepOn (V : VF C) {m : ℕ} {σ : Type} (Y : Fin m → σ → C) (T : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → C, (∀ δ, V.Ge 0 (c δ)) → (∀ δ, δ ∉ T → c δ = 0) →
    (∀ s, V.MM (∑ δ, c δ * Y δ s)) → ∀ δ, V.MM (c δ)

theorem IndepOn.indepMod {m : ℕ} {σ : Type} {Y : Fin m → σ → C} {T : Finset (Fin m)}
    (h : IndepOn V Y T) {N : ℕ} (f : Fin N ↪ Fin m) (hf : ∀ ν, f ν ∈ T) :
    IndepMod V (fun ν => Y (f ν)) := by
  intro c hc hs ν
  have key := h (fun δ => ∑ ν, if f ν = δ then c ν else 0) (fun δ => VF.Ge.sum fun ν _ => by
      split_ifs
      · exact hc ν
      · exact VF.Ge.zero 0)
    (fun δ hδ => Finset.sum_eq_zero fun ν _ => if_neg (by rintro rfl; exact hδ (hf ν)))
    (fun s => by
      convert hs s using 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp) (f ν)
  simpa using key

theorem exists_relation {m : ℕ} {σ : Type} {Y : Fin m → σ → C} (hY : ∀ δ x, V.Ge 0 (Y δ x))
    {T : Finset (Fin m)} (hT : IndepOn V Y T) {δ : Fin m}
    (hn : ¬ IndepOn V Y (insert δ T)) :
    ∃ r : Fin m → C, (∀ ε, V.Ge 0 (r ε)) ∧ r δ = 1 ∧ (∀ ε, ε ∉ T → ε ≠ δ → r ε = 0) ∧
      ∀ s, V.MM (∑ ε, r ε * Y ε s) := by
  unfold IndepOn at hn
  push Not at hn
  obtain ⟨c, hc, hc0, hs, ε₀, hε₀⟩ := hn
  have hcd : ¬ V.MM (c δ) := by
    intro hm
    have key := hT (fun ε => if ε = δ then 0 else c ε) (fun ε => by
        split_ifs
        · exact VF.Ge.zero 0
        · exact hc ε)
      (fun ε hε => by
        split_ifs with h
        · rfl
        · exact hc0 ε (by simp [h, hε]))
      (fun s => by
        have h1 : V.MM (Y δ s * c δ) := mm_int_mul (hY δ s) hm
        convert mm_sub (hs s) h1 using 1
        rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ δ),
          ← Finset.add_sum_erase _ (fun ε => c ε * Y ε s) (Finset.mem_univ δ)]
        rw [Finset.sum_congr rfl (g := fun ε => c ε * Y ε s)
          (fun ε hε => by rw [if_neg (Finset.ne_of_mem_erase hε)])]
        simp only [if_true]
        ring) ε₀
    by_cases h : ε₀ = δ
    · exact hε₀ (h ▸ hm)
    · exact hε₀ (by simpa [h] using key)
  have h0 : c δ ≠ 0 := by intro h; exact hcd (h ▸ mm_zero)
  refine ⟨fun ε => (c δ)⁻¹ * c ε, fun ε => (ge_inv hcd).mul_int (hc ε), inv_mul_cancel₀ h0,
    fun ε h1 h2 => ?_, fun s => ?_⟩
  · simp only [hc0 ε (by simp [h1, h2]), mul_zero]
  · convert mm_int_mul (ge_inv hcd) (hs s) using 1
    simp only [Finset.mul_sum, mul_assoc]

theorem rank_nullity : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  intro C _ _ V σ m k Q hQ Y hY hk
  have hQ0 : Q ≠ 0 := by omega
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Finset (Fin m) => IndepOn V Y T) Finset.card
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro c _ h0 _ δ
      rw [h0 δ (by simp)]
      exact mm_zero⟩
  have hT' : IndepOn V Y T := (Finset.mem_filter.1 hT).2
  have hn : ∀ δ, δ ∉ T → ¬ IndepOn V Y (insert δ T) := fun δ hδ h => by
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.card_insert_of_notMem hδ] at this
    omega
  have hrt : ∀ a : C, ∃ z : C, z ^ Q = a ∧ (a = 1 → z = 1) ∧ (a = 0 → z = 0) := by
    intro a
    by_cases h : a = 1
    · exact ⟨1, by simp [h], fun _ => rfl, fun h0 => absurd (h.symm.trans h0) one_ne_zero⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hQ0)
      exact ⟨z, hz, fun h1 => absurd h1 h, fun h0 => pow_eq_zero_iff hQ0 |>.mp (hz.trans h0)⟩
  choose rt hrt hrt1 hrt0 using hrt
  let e : Fin Tᶜ.card ↪ Fin m := (Tᶜ.orderEmbOfFin rfl).toEmbedding
  have he : ∀ ν, e ν ∉ T := fun ν => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl ν)
  choose r hr hr1 hr0 hrs using fun ν => exists_relation hY hT' (hn _ (he ν))
  have hle := hk Tᶜ.card (fun ν δ => rt (r ν δ))
    (fun ν δ => ge_of_pow hQ0 (by rw [hrt]; exact hr ν δ))
    (fun c _ hs ν => by
      have h1 : V.MM (∑ b, c b * rt (r b (e ν))) := hs (e ν)
      rw [Finset.sum_eq_single ν (fun b _ hb => by
        rw [hrt0 _ (hr0 b _ (he ν) (fun h => hb (e.injective h).symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), hrt1 _ (hr1 ν), mul_one] at h1
      exact h1)
    (fun ν s => by simp only [hrt]; exact hrs ν s)
  refine ⟨T.card, (T.orderEmbOfFin rfl).toEmbedding, ?_,
    hT'.indepMod _ fun ν => Finset.orderEmbOfFin_mem _ rfl ν⟩
  rw [Finset.card_compl, Fintype.card_fin] at hle
  omega

end GlobalTheory.SemilinearNullity
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_embedding_congr_integral_character : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  first | exact @GlobalTheory.ResidueChar.main | exact GlobalTheory.ResidueChar.main | (intros; apply GlobalTheory.ResidueChar.main <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory

theorem exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue {R : Type} [CommRing R]
    [IsLocalRing R] (n n0 : ℕ) (Φ : Fin n → Fin n0 → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue R (Φ b c))) :
    n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) R, IsUnit Y.det ∧
      ∀ (b : Fin n) (c : Fin n0), ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  have hle : n0 ≤ n := by simpa using h.fintype_card_le_finrank
  refine ⟨hle, ?_⟩
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨w, hw⟩ := exists_linearIndependent_sumElim_of_finrank_eq (n' := n') (by simp) _ h
  choose s hs using IsLocalRing.residue_surjective (R := R)
  let M : Matrix (Fin (n0 + n')) (Fin (n0 + n')) R := Matrix.of fun i j =>
    Sum.elim (Φ i) (fun j' => s (w j' i)) (finSumFinEquiv.symm j)
  have hcol : (M.map (IsLocalRing.residue R)).col =
      Sum.elim (fun (c : Fin n0) (b : Fin (n0 + n')) => IsLocalRing.residue R (Φ b c)) w ∘
        finSumFinEquiv.symm := by
    funext j i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j | j
    · simp [M, Matrix.col]
    · simp [M, Matrix.col, hs]
  have hu : IsUnit (M.map (IsLocalRing.residue R)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hw.comp _ finSumFinEquiv.symm.injective
  have hdet : IsUnit M.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have : (M.map (IsLocalRing.residue R)).det = IsLocalRing.residue R M.det :=
      (RingHom.map_det (IsLocalRing.residue R) M).symm
    rw [this] at hu
    exact (isUnit_map_iff (IsLocalRing.residue R) _).mp hu
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨-M⁻¹, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M hdet)).neg
  · intro b c
    have hij : ∑ b', M⁻¹ b b' * Φ b' c = (M⁻¹ * M) b (Fin.castAdd n' c) := by
      simp [M, Matrix.mul_apply]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hij, hinv, Matrix.one_apply]
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, if_pos (Fin.ext hbc)]
    · rw [if_neg hbc, if_neg (fun e => hbc (by rw [e]; rfl)), neg_zero]

theorem exists_unimodular_mul_eq_neg_of_indepMod : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  intro C _ V n n0 Φ hΦ hind
  let O : ValuationSubring C := (AddValuation.toValuation V.v).valuationSubring
  have hmem : ∀ x : C, x ∈ O ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hge : ∀ x : C, V.Ge 0 x ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hunit : ∀ x : O, IsUnit x ↔ V.v (x : C) = 0 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have h1 : V.v (x : C) + V.v (y : C) = 0 := by
        rw [← V.v.map_mul, ← V.v.map_one]
        exact congrArg (fun z : O => V.v (z : C)) hy
      have h2 := (hmem _).1 x.2
      have h3 := (hmem _).1 y.2
      exact le_antisymm (by
        calc V.v (x : C) = V.v (x : C) + 0 := (add_zero _).symm
          _ ≤ V.v (x : C) + V.v (y : C) := by gcongr
          _ = 0 := h1) h2
    · intro hx
      have hx0 : (x : C) ≠ 0 := by
        intro h0
        rw [h0, V.v.map_zero] at hx
        exact WithTop.top_ne_zero hx
      have h1 : V.v (x : C)⁻¹ = 0 := by
        have := V.v.map_mul (x : C) (x : C)⁻¹
        rw [mul_inv_cancel₀ hx0, V.v.map_one, hx, zero_add] at this
        exact this.symm
      exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, (hmem _).2 h1.ge⟩ : O)
        (Subtype.ext (mul_inv_cancel₀ hx0))
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ V.MM (x : C) := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne ((hmem _).1 x.2) (Ne.symm h), fun h => ne_of_gt h⟩
  let Ψ : Fin n → Fin n0 → O := fun b c => ⟨Φ b c, (hmem _).2 ((hge _).1 (hΦ b c))⟩
  have hli : LinearIndependent (IsLocalRing.ResidueField O)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue O (Ψ b c)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ν
    choose s hs using IsLocalRing.residue_surjective (R := O)
    rw [← hs (g ν), hres]
    refine hind (fun ν => (s (g ν) : C)) (fun ν => (hge _).2 ((hmem _).1 (s (g ν)).2)) (fun x => ?_) ν
    have h1 : IsLocalRing.residue O (∑ ν, s (g ν) * Ψ x ν) = 0 := by
      have := congrFun hg x
      simpa [hs, Finset.sum_apply] using this
    rw [hres] at h1
    simpa [Ψ] using h1
  obtain ⟨hle, Y, hY, hYΦ⟩ := exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue n n0 Ψ hli
  refine ⟨hle, Y.map O.subtype, fun b b' => (hge _).2 ((hmem _).1 (Y b b').2), ?_, fun b c _ => ?_⟩
  · have : (Y.map O.subtype).det = O.subtype Y.det := (RingHom.map_det O.subtype Y).symm
    rw [this]
    exact (hunit _).1 hY
  · have := congrArg O.subtype (hYΦ b c)

    rw [map_sum] at this
    simp only [map_mul, apply_ite O.subtype, map_neg, map_one, map_zero] at this
    exact this

end GlobalTheory
end

section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.rowData_adaptedChainData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.AdaptedChainData := by
  first | exact @GlobalTheory.AdaptedChain.adaptedChainData | exact GlobalTheory.AdaptedChain.adaptedChainData | (intros; apply GlobalTheory.AdaptedChain.adaptedChainData <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalDisc_points_valuationIntegers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  first | exact @GlobalTheory.ChF.formalDisc_points_integers | exact GlobalTheory.ChF.formalDisc_points_integers | (intros; apply GlobalTheory.ChF.formalDisc_points_integers <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  first | exact @GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | exact GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | (intros; apply GlobalTheory.LogSubst.coeff_subst_sum_pow_pow <;> assumption)
end
