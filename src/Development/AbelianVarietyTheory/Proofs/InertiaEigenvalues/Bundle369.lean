module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShuffle
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MackeyCellTermOfBlockSizes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfUniUp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem ModTh.abc_Nχ_of_range {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (e : ℤ) (h1 : -1 ≤ e) (h2 : e < Dt.t) :
    ABC (F.D (chr (M.ω ^ (-e)))) Dt.w Dt.wst (M.Nχ e) := by
  refine ⟨fun i => (M.χ_lat e h1 h2 i).1, fun i => ?_, fun i => (M.χ_lat e h1 h2 i).2.1⟩
  have ht : (1 : ℤ) ≤ Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have a := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
  have b := Dt.range i (Dt.w i + Dt.t - 1) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))
  rw [(M.χ_lat e h1 h2 i).2.2.1]
  exact ⟨sh_le_sh_of_le (by omega) _, sh_le_sh_of_le (by unfold TopData.wst; omega) _⟩

theorem ModTh.hom_chr_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  intro k G _ _ l n _ _ _ R F r Dt M T1 T2 T3 e h1 h2 A₁ j p hj hinj hp
  by_contra hne
  have hsurj : Function.Surjective p := by
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    have hx0 : p x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    intro y
    refine ⟨(y 0 / p x 0) • x, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hx0]
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hsub := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hinj M.std_model
  have hq := ModTh.model_push_of_surjective F M A₁ (chr (M.ω ^ (-e))) p _ hp hsurj hsub
  have hN := GlobalTheory.T.obj_and_abc_of_model F M _ _ hq
  have hχ := M.abc_Nχ_of_range e h1 h2
  have hs : sen ((F.D (chr (M.ω ^ (-e)))).γ 0) (M.Nχ e 0) (e : k) ≠ 0 := by
    rw [(M.χ_lat e h1 h2 0).2.2.2]
    classical
    unfold resCount
    rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro h
    exact h e (Multiset.mem_singleton_self e) (by simp)
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D (chr (M.ω ^ (-e)))) Dt _ _ hN.2 hχ 0 (e : k) hs
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ (chr (M.ω ^ (-e))) j p Dt.w Dt.wst M.Nstd hT.1 hj hinj hp hsurj hT.2 0
    ((e : k) + a)
  have hstd : resCount (Dt.U 0) (Dt.w 0) ((e : k) + a) ≠ 0 := by
    rw [← M.std_sen]
    omega
  classical
  unfold resCount at hstd
  rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hstd
  push Not at hstd
  obtain ⟨u, hu, hu'⟩ := hstd
  rw [abs_le] at ha
  refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3 0).2.1 u hu (Dt.w 0 + e + a) (by omega) (by omega) ?_
  push_cast at hu' ⊢
  linear_combination hu'

end GlobalTheory.Models
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.WhMul

variable {g : ℕ} [Fact g.Prime]

theorem entN_mul_succ {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) (k : ℕ) :
    entN (M * N) k (k + 1) = entN M k (k + 1) + entN N k (k + 1) := by
  unfold entN
  split_ifs with h
  · set i : Fin n := ⟨k, h.1⟩
    set j : Fin n := ⟨k + 1, h.2⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [(hM i i).2 rfl, (hN j j).2 rfl, one_mul, mul_one, add_comm]
    · rintro c ⟨hci, hcj⟩
      by_cases hc : c < i
      · rw [(hM i c).1 hc, zero_mul]
      · have : j < c := by
          rw [Fin.lt_def] at hc ⊢
          have h1 : (c : ℕ) ≠ k := fun e => hci (Fin.ext e)
          have h2 : (c : ℕ) ≠ k + 1 := fun e => hcj (Fin.ext e)
          simp only [i, j] at hc ⊢
          omega
        rw [(hN c j).1 this, mul_zero]
  · simp only [add_zero]

theorem supFrom_mul {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) :
    supFrom 0 (M * N) = supFrom 0 M + supFrom 0 N := by
  unfold supFrom
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => entN_mul_succ M N hM hN k

theorem supFrom_one (n : ℕ) : supFrom 0 (1 : Mt g n) = 0 := by
  unfold supFrom
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold entN
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    simp [Fin.ext_iff]
  · rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.tl_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.br_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem wh_hcT : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) →
      wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  intro g _ ψ hψ a b n hn Φ hΦ1 hΦ2
  obtain ⟨⟨P, hP⟩, ⟨U, hU⟩, -, -, -, -⟩ := ParBasic.par_basic g a b n hn
  subst hn

  have hl : ∀ h ∈ U, ∀ x ∈ U, (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (h * x * h⁻¹) =
      (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) x := by
    intro h hh x hx
    have hh' := (hU h).1 hh
    have hx' := (hU x).1 hx
    have hi' := (hU h⁻¹).1 (U.inv_mem hh)
    have e1 : supFrom 0 ((h : Mt g (a + b)) * ((h⁻¹ : Gn g (a + b)) : Mt g (a + b))) = 0 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, supFrom_one]
    rw [supFrom_mul _ _ hh' hi'] at e1
    have hxh := ParBasic.isUniUp_mul _ _ hh' hx'
    simp only [Units.val_mul]
    rw [supFrom_mul _ _ hxh hi', supFrom_mul _ _ hh' hx']
    congr 2
    linear_combination e1

  have hφ : ∀ k ∈ P, ∀ x ∈ P,
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) (k * x * k⁻¹) =
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) x := by
    intro k hk x hx
    have hk' := (hP k).1 hk
    have hx' := (hP x).1 hx
    have hi' := (hP k⁻¹).1 (P.inv_mem hk)
    have hkx := (hP (k * x)).1 (P.mul_mem hk hx)
    obtain ⟨uk, vk⟩ := ParBasic.isUnit_blocks k hk'
    obtain ⟨ux, vx⟩ := ParBasic.isUnit_blocks x hx'
    have m1 := ParBasic.blocks_mul _ _ hk' hi'
    have m2 := ParBasic.blocks_mul _ _ hk' hx'
    have m3 := ParBasic.blocks_mul _ _ hkx hi'
    have hkxk := (hP (k * x * k⁻¹)).1 (P.mul_mem (P.mul_mem hk hx) (P.inv_mem hk))
    obtain ⟨uc, vc⟩ := ParBasic.isUnit_blocks _ hkxk
    have e1 : ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = (k : Mt g (a + b)) * (x : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      simp only [Units.val_mul]
    have e0 : (k : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have iA : (((toG (tl a (k : Mt g (a + b))))⁻¹ : Gn g a) : Mt g a) = tl a ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG uk, ← m1.2.1, e0, tl_one]
    have iB : (((toG (br a b (k : Mt g (a + b))))⁻¹ : Gn g b) : Mt g b) = br a b ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG vk, ← m1.2.2, e0, br_one]
    have cA : toG (tl a ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (tl a (k : Mt g (a + b))) * toG (tl a (x : Mt g (a + b))) * (toG (tl a (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG uc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iA, OpenCell.coe_toG uk, OpenCell.coe_toG ux, m3.2.1, m2.2.1]
    have cB : toG (br a b ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG vc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iB, OpenCell.coe_toG vk, OpenCell.coe_toG vx, m3.2.2, m2.2.2]
    show Φ _ _ = Φ _ _
    rw [cA, cB]
    have h1 := hΦ1 (toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹)
      (toG (tl a (x : Mt g (a + b)))) (toG (tl a (k : Mt g (a + b))))
    have h2 := hΦ2 (toG (tl a (x : Mt g (a + b)))) (toG (br a b (x : Mt g (a + b)))) (toG (br a b (k : Mt g (a + b))))
    simp only at h1 h2
    rw [h1, h2]
  set R : Finset (Equiv.Perm (Fin (a + b))) := Finset.univ.filter fun σ =>
    ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j with hR
  have hRu : ∀ x : Gn g (a + b), ∃! σ, σ ∈ R ∧ ∃ h ∈ U, ∃ k ∈ P, x = h * pm g σ * k := by
    intro x
    obtain ⟨σ, ⟨hσ, u, p, hu, hp, hx⟩, huniq⟩ :=
      Shuffle.existsUnique_shuffle g a (a + b) (Nat.le_add_right a b) x
    refine ⟨σ, ⟨by simpa [hR] using hσ, u, (hU u).2 hu, p, (hP p).2 hp, hx⟩, ?_⟩
    rintro τ ⟨hτ, u', hu', p', hp', hx'⟩
    exact huniq τ ⟨by simpa [hR] using hτ, u', p', (hU u').1 hu', (hP p').1 hp', hx'⟩
  have M := mackey_doubleCoset_pairing (Gn g (a + b)) U P _ R (pm g) hRu
    (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹)
    (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) hl hφ
  have cU : (Nat.card U : ℂ) = ((Finset.univ.filter fun u : Gn g (a + b) => IsUniUp (u : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hU]
  have cP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hP]
  refine Eq.trans ?_ (M.trans ?_)
  · rw [OpenCell.wh_eq, cU, cP, ← Finset.sum_filter]
    simp only [hU, hP]
    rfl
  obtain ⟨σ₀, h0⟩ : ∃ σ₀ : Equiv.Perm (Fin (a + b)),
      ∀ j : Fin (a + b), (σ₀ j : ℕ) = if (j : ℕ) < a then b + j else j - a := by
    let f : Fin (a + b) → Fin (a + b) := fun j =>
      ⟨if (j : ℕ) < a then b + j else j - a, by have := j.2; split_ifs <;> omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have := i.2
      have := j.2
      simp only [f, Fin.mk.injEq] at h
      ext
      split_ifs at h <;> omega
    exact ⟨Equiv.ofBijective f hf.bijective_of_finite, fun j => rfl⟩
  have h0R : σ₀ ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i j hij hb
    rw [Fin.lt_def] at hij ⊢
    rw [h0, h0]
    split_ifs <;> omega
  rw [Finset.sum_eq_single_of_mem σ₀ h0R]
  · simp only [hU, hP]
    exact OpenCell.openCell g ψ a b (a + b) σ₀ Φ rfl h0
  · intro σ hσ hne
    have hσ' : ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j := by
      simpa [hR] using hσ
    have hnd : ¬ ∀ i j : Fin (a + b), (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1 := by
      intro h
      apply hne
      exact Equiv.ext fun j => Fin.ext (by rw [(shuffle_noDescent_iff_open a b (a + b) σ rfl hσ').1 h j, h0 j])
    push Not at hnd
    obtain ⟨i, j, hi, hj, hij⟩ := hnd
    simp only [hU, hP]
    rw [NonOpenCell.whittaker_term_eq_zero g ψ hψ a b (a + b) σ Φ i j rfl hi hj hij, mul_zero]

end GlobalTheory.GLq.WhMul
end

section

noncomputable section

namespace GlobalTheory.GLq.Mackey

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blocks_conj (a b n : ℕ) (hn : n = a + b) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) (Λ : Gn g a → Gn g b → ℂ)
    (h1 : ∀ y, IsClass fun x => Λ x y) (h2 : ∀ x, IsClass (Λ x)) :
    ∀ h ∈ P, ∀ x ∈ P, Λ (toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n))) (toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)))
      = Λ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) := by
  obtain ⟨-, -, hu, hmul, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  let f₁ : P →* Gn g a := MonoidHom.mk' (fun p => toG (tl a ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).1, Units.val_mul,
      Recip.coe_toG ((hu _ hp).1.mul (hu _ hq).1), Recip.coe_toG (hu _ hp).1, Recip.coe_toG (hu _ hq).1])
  let f₂ : P →* Gn g b := MonoidHom.mk' (fun p => toG (br a b ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).2, Units.val_mul,
      Recip.coe_toG ((hu _ hp).2.mul (hu _ hq).2), Recip.coe_toG (hu _ hp).2, Recip.coe_toG (hu _ hq).2])
  intro h hh x hx
  have E1 : toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₁ ⟨h, hh⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have E2 : toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₂ ⟨h, hh⟩ * f₂ ⟨x, hx⟩ * (f₂ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [E1, E2]
  exact (h2 _ _ _).trans (h1 _ _ _)

theorem mean_prod_right {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun b => mean (fun a => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type_right, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_prod_left {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun a => mean (fun b => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun b => mean (fun a => F a b)) = mean (fun a => mean (fun b => F a b)) := by
  rw [← mean_prod_right, mean_prod_left]

theorem mean_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (F : B → ℂ) :
    mean (fun x => F (e x)) = mean F := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp e F]

theorem mean_sum {A ι : Type} [Fintype A] (R : Finset ι) (Λ : A → ℂ) (T : ι → A → ℂ) :
    mean (fun p => Λ p * ∑ i ∈ R, T i p) = ∑ i ∈ R, mean (fun p => Λ p * T i p) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem res_comm {p q r s m k : ℕ} (Λ : Gn g m → Gn g k → ℂ) (y₁ : Gn g p) (y₃ : Gn g q) (y₂ : Gn g r)
    (y₄ : Gn g s) :
    res r s (fun h₂ => res p q (fun x => Λ x h₂) y₁ y₃) y₂ y₄ =
      res p q (fun z => res r s (Λ z) y₂ y₄) y₁ y₃ := by
  unfold res
  simp only [← Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem left_side (a b c d n : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (Φ : Gn g a → Gn g b → ℂ)
    (hΦ1 : ∀ y, IsClass fun x => Φ x y) (hΦ2 : ∀ x, IsClass (Φ x))
    (Λ : Gn g c → Gn g d → ℂ) (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d (hcT a b Φ n) p.1 p.2) =
      ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
          res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  obtain ⟨-, R2, -⟩ := Recip.reciprocity g
  obtain ⟨⟨Pc, hPc⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g c d n hn2
  obtain ⟨⟨Pa, hPa⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn1
  have hR : ∀ x : Gn g n, ∃! i, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧
      ∃ h ∈ Pc, ∃ k ∈ Pa, x = h * wI g a c i n * k := by
    intro x
    obtain ⟨i, ⟨hi, p, q, hp, hq, e⟩, hu⟩ := GlobalTheory.GLm.ParCoset.doubleCoset g a b c d n hn1 hn2 x
    refine ⟨i, ⟨hi, p, (hPc p).2 hp, q, (hPa q).2 hq, e⟩, ?_⟩
    rintro j ⟨hj, h, hh, k, hk, e'⟩
    exact hu j ⟨hj, h, k, (hPc h).1 hh, (hPa k).1 hk, e'⟩
  have hm := mackey_doubleCoset_pairing (Gn g n) Pc Pa ℕ
    ((Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b)) (fun i => wI g a c i n) hR
    (fun x => Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))))
    (fun z => Φ (toG (tl a (z : Mt g n))) (toG (br a b (z : Mt g n))))
    (blocks_conj c d n hn2 Pc hPc Λ hΛ1 hΛ2) (blocks_conj a b n hn1 Pa hPa Φ hΦ1 hΦ2)
  have cc : ∀ (P : Subgroup (Gn g n)) (Q : Gn g n → Prop), (∀ x, x ∈ P ↔ Q x) →
      Nat.card P = (Finset.univ.filter Q).card := by
    intro P Q hP
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [hP]
  rw [cc Pc _ hPc, cc Pa _ hPa] at hm
  simp only [hPc, hPa] at hm
  rw [R2 c d n hn2]
  unfold hcT
  rw [hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  exact mackey_cell_term g a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Λ Φ

theorem right_term (a b c d n i : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (hia : i ≤ a) (hic : i ≤ c)
    (hcb : c - i ≤ b) (Φ : Gn g a → Gn g b → ℂ) (Λ : Gn g c → Gn g d → ℂ)
    (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d p.2) c p.1) =
    mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
      res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
        res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  have hc : c = i + (c - i) := by omega
  have hd : d = (a - i) + (b - (c - i)) := by omega
  obtain ⟨R1, -, -⟩ := Recip.reciprocity g
  rw [mean_prod_right (fun (h₁ : Gn g c) (h₂ : Gn g d) => Λ h₁ h₂ * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁)]
  calc _ = mean (fun h₂ : Gn g d => mean (fun q : Gn g i × Gn g (c - i) =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) := by
        congr 1; funext h₂
        exact R1 i (c - i) c hc (fun x => Λ x h₂) _ (hΛ1 h₂)
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun h₂ : Gn g d =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) :=
        mean_swap _
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun r : Gn g (a - i) × Gn g (b - (c - i)) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)) := by
        congr 1; funext q
        refine R1 (a - i) (b - (c - i)) d hd _ _ ?_
        intro x y
        show res i (c - i) (fun z => Λ z (y * x * y⁻¹)) q.1 q.2 = res i (c - i) (fun z => Λ z x) q.1 q.2
        rw [show (fun z => Λ z (y * x * y⁻¹)) = (fun z => Λ z x) from funext fun z => hΛ2 z x y]
    _ = mean (fun w : (Gn g i × Gn g (c - i)) × (Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) w.1.1 w.1.2) w.2.1 w.2.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) w.1.2 w.2.2) w.1.1 w.2.1) :=
        (mean_prod_left (fun (q : Gn g i × Gn g (c - i)) (r : Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)).symm
    _ = _ := by
        rw [← mean_equiv (Equiv.prodProdProdComm (Gn g i) (Gn g (a - i)) (Gn g (c - i)) (Gn g (b - (c - i))))]
        congr 1; funext y
        simp only [Equiv.prodProdProdComm_apply]
        rw [res_comm]

theorem mackey_formula : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂,
      res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  intro g _ a b c d n hn1 hn2 Φ hΦ1 hΦ2 h₁ h₂
  obtain ⟨-, -, R3⟩ := Recip.reciprocity g
  have hcl : IsClass (hcT a b Φ n) := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g a b n hn1).1 Φ
  have hres := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g c d n hn2).2 _ hcl
  suffices H : (fun (h₁ : Gn g c) (h₂ : Gn g d) => res c d (hcT a b Φ n) h₁ h₂) =
      (fun (h₁ : Gn g c) (h₂ : Gn g d) => ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁) from
    congrFun (congrFun H h₁) h₂
  refine R3 (Gn g c) (Gn g d) _ _ hres.2 hres.1 ?_ ?_ ?_
  · intro y x z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g i (c - i) c (by omega)).1 _ x z
  · intro x y z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hd' : ∀ Ψ, hcT (a - i) (b - (c - i)) Ψ d (z * y * z⁻¹) = hcT (a - i) (b - (c - i)) Ψ d y :=
      fun Ψ => (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g (a - i) (b - (c - i)) d (by omega)).1 Ψ y z
    simp only [hd']
  · intro Λ hΛ1 hΛ2
    rw [left_side a b c d n hn1 hn2 Φ hΦ1 hΦ2 Λ hΛ1 hΛ2, mean_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (right_term a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Φ Λ hΛ1 hΛ2).symm

end GlobalTheory.GLq.Mackey
end
end
