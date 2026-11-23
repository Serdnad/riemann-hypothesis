module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

private theorem coeff_single_one_mul' (t : Fin 1 × Fin dd) (x y : PS C 1 dd) :
    MvPowerSeries.coeff (Finsupp.single t 1) (x * y) =
      MvPowerSeries.coeff (Finsupp.single t 1) x * MvPowerSeries.constantCoeff y +
        MvPowerSeries.constantCoeff x * MvPowerSeries.coeff (Finsupp.single t 1) y := by
  first
  | (have key : ∀ g : PS C 1 dd, MvPowerSeries.coeff (Finsupp.single t 1) g =
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) t g) := by
      intro g
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
      simp
     rw [key, key, key, Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul]
     ring)
  | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
     simp [Finset.Nat.antidiagonal_succ]
     ring)

private theorem coeff_single_one_pow_add_two_eq_zero (x : PS C 1 dd) (hx : MvPowerSeries.constantCoeff x = 0)
    (t : Fin 1 × Fin dd) (k : ℕ) : MvPowerSeries.coeff (Finsupp.single t 1) (x ^ (k + 1 + 1)) = 0 := by
  rw [pow_succ, coeff_single_one_mul']
  simp [hx]

private theorem constantCoeff_and_linear_coeff_finsupp_prod_pow (a : Fin 1 × Fin dd → PS C 1 dd) (hac : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (t : Fin 1 × Fin dd) (d : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.constantCoeff (d.prod fun s n => a s ^ n) = (if d = 0 then 1 else 0) ∧
      ((∀ s, d ≠ Finsupp.single s 1) →
        MvPowerSeries.coeff (Finsupp.single t 1) (d.prod fun s n => a s ^ n) = 0) := by
  induction d using Finsupp.induction
  next =>
    simp [MvPowerSeries.coeff_one]
  next s b f hs hb ih =>
    have hfs : f s = 0 := by
      by_contra h'
      exact hs (Finsupp.mem_support_iff.mpr h')
    have hne : Finsupp.single s b + f ≠ 0 := by
      intro h
      apply hb
      have h2 := congrArg (fun g : Fin 1 × Fin dd →₀ ℕ => g s) h
      simpa [hfs] using h2
    have hP : (Finsupp.single s b + f).prod (fun s n => a s ^ n) =
        a s ^ b * f.prod (fun s n => a s ^ n) := by
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero _)
    rw [hP]
    have hcs : MvPowerSeries.constantCoeff (a s ^ b) = 0 := by
      rw [map_pow, hac s, zero_pow hb]
    constructor
    · rw [map_mul, hcs, zero_mul, if_neg hne]
    · intro hnot
      rw [coeff_single_one_mul', hcs, zero_mul, add_zero]
      by_cases hf : f = 0
      · subst hf
        have hb1 : b ≠ 1 := by
          intro h1
          exact hnot s (by rw [h1, add_zero])
        obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 + 1 := ⟨b - 2, by omega⟩
        rw [coeff_single_one_pow_add_two_eq_zero (a s) (hac s) t k, zero_mul]
      · rw [ih.1, if_neg hf, mul_zero]

private theorem coeff_single_one_ev_eq_sum (f : PS C 1 dd) (ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (j : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] f) =
      ∑ k, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), k) 1) f *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ψ k) := by
  have hev : ev ![ψ] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => ψ p.2) f := by
    unfold ev
    congr 1
    funext ⟨i, k⟩
    rw [Fin.fin_one_eq_zero i]
    rfl
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => ψ p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun s => hψ s.2)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => hψ s.2)
    | exact ⟨fun s => by simp [hψ s.2], fun d => Set.toFinite _⟩
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by simp [hψ s.2])
  rw [hev, MvPowerSeries.coeff_subst hs]
  refine (finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun s => Finsupp.single s 1) ?_).trans ?_
  · intro d hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hne
    push_neg at hne
    apply hd
    try dsimp only
    rw [(constantCoeff_and_linear_coeff_finsupp_prod_pow _ (fun s => hψ s.2) _ d).2 (fun s h => hne s h.symm), smul_zero]
  · first
    | rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    | rw [Finset.sum_image ((Finsupp.single_left_injective one_ne_zero).injOn)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    simp [Finsupp.prod_single_index, smul_eq_mul]

theorem linAct_comp1 (φ ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) (x : Fin dd → C) :
    linAct (comp1 φ ψ) x = linAct φ (linAct ψ x) := by
  funext i
  simp only [linAct, comp1, coeff_single_one_ev_eq_sum _ ψ hψ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem linAct_smul (φ : Pt C 1 dd) (c : C) (x : Fin dd → C) : linAct φ (c • x) = c • linAct φ x := by
  funext i
  simp only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem linAct_sum {ι : Type} (φ : Pt C 1 dd) (s : Finset ι) (x : ι → Fin dd → C) :
    linAct φ (∑ c ∈ s, x c) = ∑ c ∈ s, linAct φ (x c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Rename

theorem prod_X_rename {σ τ : Type} (φ : σ → τ) (e : σ →₀ ℕ) :
    (e.prod fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) =
      MvPowerSeries.monomial (e.mapDomain φ) 1 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg,
      Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial, one_mul]
  · intro a b
    rw [Finsupp.prod_single_index (h := fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) (pow_zero _),
      Finsupp.mapDomain_single]
    simp only [MvPowerSeries.X_pow_eq]

theorem coeff_subst_rename_inj {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm

variable {dd : ℕ}

theorem snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h

theorem hasSubst_snd : MvPowerSeries.HasSubst
    (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp)

theorem uncurry_eq_subst (f : PS C 1 dd) :
    un1 f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) f := by
  ext μ
  have h := coeff_subst_rename_inj (C := C) (fun p : Fin 1 × Fin dd => p.2) snd_injective_fin_one f
    (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  have e1 : (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).mapDomain (fun p : Fin 1 × Fin dd => p.2) = μ := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  rw [e1] at h
  exact h.symm

theorem subst_singlePointUncurry {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]

theorem subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]

theorem uncurry_X (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]

theorem eval_single_eq_subst {n : ℕ} (a : Pt C n dd) (f : PS C 1 dd) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  simp only [ev]
  congr 1
  funext p
  rw [Subsingleton.elim p.1 0]
  rfl

theorem uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by
  have hu : ∀ j, MvPowerSeries.constantCoeff (un1 (a j)) = 0 := by
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (a j) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha j
  rw [subst_singlePointUncurry hu]
  show _ = un1 (ev ![a] (φ i))
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => a p.2) (fun s => ha s.2)]

end Rename

section Inst

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.lg_const (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h

end Inst

end Formalism.L2.FormalSeriesBounds
end
end
