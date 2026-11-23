module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Lattice
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem actT_fin {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (hfin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))) (y : TV n M P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y)) := by
  classical
  haveI hS : ∀ J : P → Fin n, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ (y J))) :=
    fun J => hfin (y J)
  set T : Submodule ℂ M := ⨆ J : P → Fin n, Submodule.span ℂ (Set.range fun γ => ρ γ (y J)) with hT
  haveI : FiniteDimensional ℂ T := by rw [hT]; infer_instance
  let L : ((P → Fin n) → T) →ₗ[ℂ] TV n M P := LinearMap.pi fun I => T.subtype ∘ₗ LinearMap.proj I
  have hle : Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    have hmem : ∀ I, actT lab κ ρ γ y I ∈ T := by
      intro I
      simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.proj_apply]
      refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
      exact Submodule.mem_iSup_of_mem J (Submodule.subset_span ⟨γ, rfl⟩)
    exact ⟨fun I => ⟨_, hmem I⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem actT_cont {ι Γ : Type} [TopologicalSpace Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ i j, Continuous fun γ => κ τ γ i j)
    (hc : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)) (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    Continuous fun γ => lam (actT lab κ ρ γ y) := by
  classical
  have h1 : ∀ x : TV n M P, lam x = ∑ I : P → Fin n, (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (x I) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]

    simp [map_sum]
  have key : (fun γ => lam (actT lab κ ρ γ y)) = fun γ => ∑ I : P → Fin n, ∑ J : P → Fin n,
      (∏ p : P, κ (lab p) γ (I p) (J p)) * (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (ρ γ (y J)) := by
    funext γ
    rw [h1]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
  rw [key]
  refine continuous_finsetSum _ fun I _ => continuous_finsetSum _ fun J _ => ?_
  exact (continuous_finsetProd _ fun p _ => hκ _ _ _).mul (hc (y J) _)

end PositivityTheory.Rg.Cz.TGK

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def omcGlue {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : Fin m → Fin n :=
  fun p => if h : p = j then b else R ⟨p, h⟩

def omcEquiv {m : ℕ} (j : Fin m) : (Fin m → Fin n) ≃ Fin n × ({p // p ≠ j} → Fin n) where
  toFun J := (J j, fun p => J p.1)
  invFun x := omcGlue j x.1 x.2
  left_inv J := by
    funext p
    by_cases h : p = j
    · subst h; simp [omcGlue]
    · simp [omcGlue, h]
  right_inv x := by
    rcases x with ⟨b, R⟩
    simp only [omcGlue, dite_true, Prod.mk.injEq, true_and]
    funext p
    simp [p.2]

theorem omc_sum {m : ℕ} {β : Type} [AddCommMonoid β] (j : Fin m) (h : (Fin m → Fin n) → β) :
    ∑ J, h J = ∑ b, ∑ R, h (omcGlue j b R) := by
  rw [← (omcEquiv (n := n) j).symm.sum_comp, Fintype.sum_prod_type]
  rfl

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_glue_j {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : omcGlue j b R j = b := by
  simp [omcGlue]

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_update {m : ℕ} (j : Fin m) (a b : Fin n) (R : {p // p ≠ j} → Fin n) :
    Function.update (omcGlue j b R) j a = omcGlue j a R := by
  funext p
  by_cases hp : p = j
  · subst hp
    simp [omc_glue_j]
  · rw [Function.update_of_ne hp]
    simp [omcGlue, hp]

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_prod {m : ℕ} (j : Fin m) (F : Fin m → Fin n → ℂ) (b : Fin n) (R : {p // p ≠ j} → Fin n) :
    ∏ p, F p (omcGlue j b R p) = F j b * ∏ p : {p // p ≠ j}, F p.1 (R p) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [omc_glue_j]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [omcGlue, p.2]

private theorem Om_apply_eq_sum_update {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    Om E j g I = ∑ a, E a (I j) (g (Function.update I j a)) := by
  simp only [Om, lift, eAt, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem actT_const_apply_eq_sum_prod_smul {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    actT (fun _ : Fin m => τ) κ ρ γ g I = ∑ J, (∏ p, κ τ γ (I p) (J p)) • ρ γ (g J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private theorem sum_smul_R0_sum_E_eq_of_unitary_of_adjoint (K : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (R0 : Module.End ℂ M) (hu : K * Kᴴ = 1)
    (had : ∀ a b, R0 * E a b = (∑ c, ∑ d, (K c a * star (K d b)) • E c d) * R0)
    (i : Fin n) (y : Fin n → M) :
    ∑ b, K i b • R0 (∑ a, E a b (y a)) = ∑ a, ∑ c, K c a • E c i (R0 (y a)) := by
  have h1 : ∀ a b, R0 (E a b (y a)) = ∑ c, ∑ d, (K c a * star (K d b)) • E c d (R0 (y a)) := by
    intro a b
    have h := congrArg (fun T : Module.End ℂ M => T (y a)) (had a b)
    simpa [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have h2 : ∀ d, ∑ b, K i b * star (K d b) = if i = d then 1 else 0 := by
    intro d
    have h := congrFun (congrFun hu i) d
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.conjTranspose_apply] using h

  simp_rw [map_sum, h1, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h3 : ∀ d (v : M), ∑ b, (K i b * (K c a * star (K d b))) • v
      = (K c a * if i = d then 1 else 0) • v := by
    intro d v
    rw [← Finset.sum_smul, ← h2 d, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [h3]
  simp [mul_ite]

theorem actT_Om {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (hu : κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ a b, ρ γ * E a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E c d) * ρ γ) (j : Fin m)
    (f : TV n M (Fin m)) :
    actT (fun _ : Fin m => τ) κ ρ γ (Om E j f) = Om E j (actT (fun _ : Fin m => τ) κ ρ γ f) := by
  funext I
  rw [actT_const_apply_eq_sum_prod_smul, Om_apply_eq_sum_update]
  simp_rw [Om_apply_eq_sum_update, actT_const_apply_eq_sum_prod_smul]
  set K := κ τ γ with hK
  have hP : ∀ b R, ∏ p, K (I p) (omcGlue j b R p)
      = K (I j) b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) :=
    fun b R => omc_prod j (fun p y => K (I p) y) b R
  have hQ : ∀ a b R, ∏ p, K (Function.update I j a p) (omcGlue j b R p)
      = K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) := by
    intro a b R
    rw [show ∏ p, K (Function.update I j a p) (omcGlue j b R p)
        = K (Function.update I j a j) b * ∏ p : {p // p ≠ j}, K (Function.update I j a p.1) (R p)
        from omc_prod j (fun p y => K (Function.update I j a p) y) b R]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro p _
      rw [Function.update_of_ne p.2]
  trans ∑ R : {p // p ≠ j} → Fin n, (∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
      ∑ a, ∑ c, K c a • E c (I j) (ρ γ (f (omcGlue j a R)))
  · conv_lhs => rw [omc_sum j]
    simp only [omc_glue_j, omc_update, hP]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← sum_smul_R0_sum_E_eq_of_unitary_of_adjoint K E (ρ γ) hu had (I j) (fun a => f (omcGlue j a R)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, mul_comm]
  · have hR : ∀ a, E a (I j) (∑ J, (∏ p, K (Function.update I j a p) (J p)) • ρ γ (f J))
        = ∑ b, ∑ R, (K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
          E a (I j) (ρ γ (f (omcGlue j b R))) := by
      intro a
      rw [omc_sum j]

      simp only [hQ, map_sum, map_smul]
    simp only [hR]
    symm
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext b
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, mul_comm]

end PositivityTheory.Rg.Cz.CtrX

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def npairs {m : ℕ} (col : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin m × Fin m => x.1 < x.2 ∧ col x.1 = col x.2).card

def ColInj {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) : Prop :=
  ∀ p q, col p = col q → I p = I q → p = q

def rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (p : Fin m) : ℕ :=
  (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card

theorem rk_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) (p : Fin m) : rk col I p ≤ (top : ℕ) - I p := by
  unfold rk
  have h1 : (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card ≤ (Finset.Ioi (I p)).card := by
    apply Finset.card_le_card_of_injOn I
    · intro q hq
      simp at hq ⊢
      exact hq.2
    · intro q hq q' hq' hqq
      simp at hq hq'
      exact hI q q' (hq.1.trans hq'.1.symm) hqq
  rw [Fin.card_Ioi] at h1
  omega

theorem sum_rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (hI : ColInj col I) :
    ∑ p, rk col I p = npairs col := by
  have e1 : ∑ p, rk col I p = (Finset.univ.filter fun x : Fin m × Fin m => col x.2 = col x.1 ∧ I x.1 < I x.2).card := by
    unfold rk
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [e1]
  unfold npairs
  apply Finset.card_bij' (fun x _ => if x.1 < x.2 then x else x.swap) (fun y _ => if I y.1 < I y.2 then y else y.swap)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases h : x.1 < x.2
    · simp [h, hx.2]
    · have h' : ¬ I x.2 < I x.1 := not_lt.mpr hx.2.le
      simp [h, h']
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases h : I y.1 < I y.2
    · simp [h, hy.1]
    · have h' : ¬ y.2 < y.1 := not_lt.mpr hy.1.le
      simp [h, h']
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hne : x.1 ≠ x.2 := fun h => by rw [h] at hx; exact lt_irrefl _ hx.2
    split_ifs with h
    · exact ⟨h, hx.1.symm⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      refine ⟨?_, hx.1⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd h' h
      · exact h'
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hne : I y.1 ≠ I y.2 := fun h => (ne_of_lt hy.1) (hI _ _ hy.2 h)
    split_ifs with h
    · exact ⟨hy.2.symm, h⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hy.2, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩

theorem npairs_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) : npairs col ≤ ∑ p, ((top : ℕ) - I p) := by
  rw [← sum_rk col I hI]
  exact Finset.sum_le_sum fun p _ => rk_le col top htop I hI p

theorem eq_of_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (b I : Fin m → Fin n)
    (hb : IsTab col b) (hI : ColInj col I) (h : ∑ p, ((top : ℕ) - I p) ≤ npairs col) :
    ∃ σ ∈ colG col, I = b ∘ σ := by
  classical
  have heq : ∀ p, rk col I p = (top : ℕ) - I p := by
    have hs : ∑ p, rk col I p = ∑ p, ((top : ℕ) - I p) :=
      le_antisymm (by rw [sum_rk col I hI]; exact npairs_le col top htop I hI) (by rw [sum_rk col I hI]; exact h)
    intro p
    exact (Finset.sum_eq_sum_iff_of_le (fun p _ => rk_le col top htop I hI p)).mp hs p (Finset.mem_univ p)
  have hex : ∀ p, ∃ q, col q = col p ∧ b q = I p := by
    intro p
    have hA : (top : ℕ) - I p + 1 ≤ (Finset.univ.filter fun q => col q = col p).card := by
      rw [← heq p]
      unfold rk
      rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun q => col q = col p ∧ I p < I q) (a := p) (by simp)]
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with rfl | hq
      · rfl
      · exact hq.1
    by_cases hb0 : ∃ q, col q = col p ∧ b q ≤ I p
    · obtain ⟨q0, hq0c, hq0b⟩ := hb0
      rcases lt_or_eq_of_le hq0b with hlt | heq'
      · obtain ⟨q, hqc, hqb⟩ := hb.2 q0 (I p) hlt
        exact ⟨q, hqc.trans hq0c, hqb⟩
      · exact ⟨q0, hq0c, heq'⟩
    · push_neg at hb0
      exfalso
      have hB : (Finset.univ.filter fun q => col q = col p).card ≤ (Finset.Ioi (I p)).card := by
        apply Finset.card_le_card_of_injOn b
        · intro q hq
          simp at hq ⊢
          exact hb0 q hq
        · intro q hq q' hq' hqq
          simp at hq hq'
          exact hb.1 q q' (hq.trans hq'.symm) hqq
      rw [Fin.card_Ioi] at hB
      have := (I p).isLt
      omega
  choose σf hσc hσb using hex
  have hinj : Function.Injective σf := by
    intro p p' hpp
    have hc : col p = col p' := by rw [← hσc p, ← hσc p', hpp]
    have hi : I p = I p' := by rw [← hσb p, ← hσb p', hpp]
    exact hI p p' hc hi
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_, ?_⟩
  · simp [colG, σ, hσc]
  · funext p
    simp [σ, hσb]

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end
