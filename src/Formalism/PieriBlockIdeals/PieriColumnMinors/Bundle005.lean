module

public import Formalism.PieriBlockIdeals.Bundle005
public import Formalism.PieriBlockIdeals.PieriColumnMinors.Symmetrization
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PieriBlockIdeals.ExponentBoundCounterexample
public import Formalism.PieriBlockIdeals.Bundle003
import Formalism.RankGapBounds.Bundle001

@[expose] public section

section

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lpa_nonneg {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (h : FormMod T B) (x : N) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (h.pos x hx).le

theorem highestWeightDominant_holds : HWDominant := by
  intro K N q _ _ _ _ _ T B hU v μ hv0 hv a b hab
  obtain ⟨hr, hd⟩ := hv
  have h2 := LinearMap.congr_fun (hU.gl a b b a) v
  rw [if_pos rfl, if_pos rfl] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hr a b hab, map_zero, sub_zero, hd a, hd b] at h2
  have hnn := lpa_nonneg hU (T b a v)
  rw [hU.adj b a v (T b a v), h2, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← sub_mul] at hnn
  have hpos := hU.pos v hv0
  by_contra hlt
  push Not at hlt
  have hneg : (μ a - μ b) * B v v < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  exact (not_le.mpr hneg) hnn

theorem lpa_joint {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : ι → Module.End K N) (hcomm : ∀ i j, Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, Module.End.eigenspace (f i) μ = ⊤) (s : Finset ι) (C : Submodule K N)
    (hC : ∀ i, ∀ x ∈ C, f i x ∈ C) (hne : C ≠ ⊥) :
    ∃ C' : Submodule K N, C' ≤ C ∧ C' ≠ ⊥ ∧ (∀ i, ∀ x ∈ C', f i x ∈ C') ∧ ∃ μ : ι → K, ∀ i ∈ s, ∀ x ∈ C', f i x = μ i • x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, hne, hC, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨C', hC'C, hC'ne, hC'st, μ, hμ⟩ := ih
    have key : C' ⊓ ⨆ c, (f i).genEigenspace c 1 = ⨆ c, C' ⊓ (f i).genEigenspace c 1 :=
      Submodule.inf_iSup_genEigenspace (p := C') (f := f i) (fun x hx => hC'st i x hx) 1
    have htop : (⨆ c, (f i).genEigenspace c 1) = ⊤ := hdiag i
    rw [htop, inf_top_eq] at key
    have hex : ∃ c, C' ⊓ (f i).genEigenspace c 1 ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hC'ne
      rw [key]
      exact iSup_eq_bot.mpr h
    obtain ⟨c, hc⟩ := hex
    refine ⟨C' ⊓ (f i).genEigenspace c 1, inf_le_left.trans hC'C, hc, ?_, Function.update μ i c, ?_⟩
    · intro j x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr
        ⟨hC'st j x hx1, Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) c 1 hx2⟩
    · intro j hj x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      rcases Finset.mem_insert.mp hj with hji | hjs
      · rw [hji, Function.update_self]
        exact Module.End.mem_genEigenspace_one.mp hx2
      · have hji : j ≠ i := fun h => hi (h ▸ hjs)
        rw [Function.update_of_ne hji]
        exact hμ j hjs x hx1

private theorem weighted_sum_add_single_sub_single {K : Type*} [Field K] {q : ℕ} (μ : Fin q → K) (a b : Fin q) :
    ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c =
      ∑ c : Fin q, -((c : ℕ) : K) * μ c + ((b : ℕ) : K) - ((a : ℕ) : K) := by
  have hs : ∀ d : Fin q, ∑ c : Fin q, -((c : ℕ) : K) * (Pi.single d (1 : K) : Fin q → K) c = -((d : ℕ) : K) := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hcd
      rw [Pi.single_eq_of_ne hcd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ d) h
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  ring

theorem existsHighestWeight_holds : ExistsHW := by
  intro K N q _ _ _ _ _ _ T hT hdiag C hC hne
  classical
  have hcomm : ∀ a b, Commute (T a a) (T b b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact Commute.refl _
    · have h := hT a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero] at h
      exact sub_eq_zero.mp h
  obtain ⟨C', hC'C, hC'ne, _, μ0, hμ0⟩ :=
    lpa_joint (fun a => T a a) (fun a b => hcomm a b) hdiag Finset.univ C
      (fun a x hx => hC a a x hx) hne
  obtain ⟨x0, hx0C', hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC'ne
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin q → K), ∀ ν, ν ∈ W ↔ ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v :=
    ⟨{ν | ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v}, fun ν => Iff.rfl⟩
  have hW0 : μ0 ∈ W := (hW μ0).mpr ⟨x0, hC'C hx0C', hx00, fun c => hμ0 c (Finset.mem_univ c) x0 hx0C'⟩
  have hfin : (Set.univ.pi fun c : Fin q => {z : K | (T c c).HasEigenvalue z}).Finite :=
    Set.Finite.pi fun c => Module.End.finite_hasEigenvalue (T c c)
  have hWfin : W.Finite := by
    refine hfin.subset ?_
    intro ν hν
    obtain ⟨v, -, hv0, hv⟩ := (hW ν).mp hν
    rw [Set.mem_univ_pi]
    intro c
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hv c), hv0⟩)
  obtain ⟨μ, hμW, hmax⟩ :=
    Set.exists_max_image W (fun ν => ∑ c : Fin q, -((c : ℕ) : K) * ν c) hWfin ⟨μ0, hW0⟩
  obtain ⟨v, hvC, hv0, hvw⟩ := (hW μ).mp hμW
  refine ⟨v, hvC, hv0, μ, And.intro ?_ hvw⟩
  intro a b hab
  by_contra hw
  have hba : b ≠ a := hab.ne'
  have hwt : ∀ c, T c c (T a b v) = (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c • T a b v := by
    intro c
    have h2 := LinearMap.congr_fun (hT c c a b) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hvw c, map_smul] at h2
    have h3 := sub_eq_iff_eq_add.mp h2
    by_cases hca : c = a
    · rw [hca] at h3 ⊢
      rw [if_pos rfl, if_neg hba, LinearMap.zero_apply, sub_zero] at h3
      rw [h3]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne, sub_zero]
      module
    · by_cases hcb : c = b
      · rw [hcb] at h3 ⊢
        rw [if_neg hba, if_pos rfl, LinearMap.zero_apply, zero_sub] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hba, add_zero]
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm), LinearMap.zero_apply, sub_zero, zero_add] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb,
          add_zero, sub_zero]
  have hνW : (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) ∈ W := (hW _).mpr ⟨T a b v, hC a b v hvC, hw, hwt⟩
  have hle : ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c ≤
      ∑ c : Fin q, -((c : ℕ) : K) * μ c := hmax _ hνW
  rw [weighted_sum_add_single_sub_single] at hle
  have hlt : ((a : ℕ) : K) < ((b : ℕ) : K) := by
    exact Nat.cast_lt.mpr hab
  linarith

theorem completeReducibility_holds : CompleteRed := by
  intro K N q _ _ _ _ _ _ T B hU S S' hS hS' hhw
  classical
  have hrefl : B.IsRefl := by
    intro x y h
    exact (hU.symm y x).trans h
  have hRst : Stab T (S ⊓ S') := fun a b x hx =>
    Submodule.mem_inf.mpr ⟨hS a b x (Submodule.mem_inf.mp hx).1, hS' a b x (Submodule.mem_inf.mp hx).2⟩
  have hUst : Stab T (S ⊓ B.orthogonal (S ⊓ S')) := by
    intro a b x hx
    obtain ⟨hxS, hxO⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hS a b x hxS, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hU.symm, hU.adj, hU.symm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) _ (hRst b a n hn)
  have hUbot : S ⊓ B.orthogonal (S ⊓ S') = ⊥ := by
    by_contra hne
    obtain ⟨v, hvU, hv0, μ, hμ⟩ := existsHighestWeight_holds K N q T hU.gl hU.diag _ hUst hne
    obtain ⟨hvS, hvO⟩ := Submodule.mem_inf.mp hvU
    have hvS' := hhw v hvS μ hμ
    have hvv := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvO) v (Submodule.mem_inf.mpr ⟨hvS, hvS'⟩)
    exact (hU.pos v hv0).ne' hvv
  have hcompl : IsCompl (S ⊓ S') (B.orthogonal (S ⊓ S')) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr
      (Submodule.disjoint_def.mpr fun x hxR hxO =>
        Classical.byContradiction fun h =>
          (hU.pos x h).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) x hxR))
  intro x hxS
  have hx : x ∈ (S ⊓ S') ⊔ B.orthogonal (S ⊓ S') := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hyR, z, hzO, hyz⟩ := Submodule.mem_sup.mp hx
  have hzS : z ∈ S := by
    have hz : z = x - y := by
      rw [← hyz]
      abel
    rw [hz]
    exact S.sub_mem hxS (Submodule.mem_inf.mp hyR).1
  have hz0 : z = 0 := by
    have hzU : z ∈ S ⊓ B.orthogonal (S ⊓ S') := Submodule.mem_inf.mpr ⟨hzS, hzO⟩
    rw [hUbot] at hzU
    exact (Submodule.mem_bot K).mp hzU
  rw [← hyz, hz0, add_zero]
  exact (Submodule.mem_inf.mp hyR).2

end Formalism.CohomologicalDescent.LP
end

section

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lcb_transp {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] {n : ℕ} (i p : ℕ) (u : Tens R P M n)
    (h : ∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + p →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) :
    ∀ (d : ℕ) (a b : Fin n), i ≤ a.val → b.val = a.val + d + 1 → b.val ≤ i + p →
      permY K (Equiv.swap a b) u = - u := by
  intro d
  induction d with
  | zero =>
    intro a b ha hb hbp
    have hj : a.val + 1 < n := by have := b.isLt; omega
    have hb' : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simpa using hb)
    rw [hb']; exact h a hj ha (by omega)
  | succ d ih =>
    intro a b ha hb hbp
    have hc : a.val + d + 1 < n := by have := b.isLt; omega
    have hcb : (⟨a.val + d + 1, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d + 1, hc⟩ : Fin n).val + 1, hcb⟩ := Fin.ext (by simp only; omega)
    have h1 : permY K (Equiv.swap a ⟨a.val + d + 1, hc⟩) u = - u := ih a ⟨a.val + d + 1, hc⟩ ha rfl (by simp only; omega)
    have h2 : permY K (Equiv.swap ⟨a.val + d + 1, hc⟩ b) u = - u := by
      rw [hb']; exact h ⟨a.val + d + 1, hc⟩ hcb (by simp only; omega) (by simp only; omega)
    have hac : a ≠ ⟨a.val + d + 1, hc⟩ := by
      intro e; have := congrArg Fin.val e; simp only at this; omega
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; omega
    have e : Equiv.swap a b = Equiv.swap ⟨a.val + d + 1, hc⟩ b * Equiv.swap a ⟨a.val + d + 1, hc⟩ *
        Equiv.swap ⟨a.val + d + 1, hc⟩ b := by
      rw [Equiv.swap_mul_swap_mul_swap hac hab, Equiv.swap_comm]
    rw [e, permOnTensor_mul, permOnTensor_mul]
    simp only [Module.End.mul_apply, h1, h2, map_neg, neg_neg]

theorem antitone_shapes : Anti := by
  intro K R P M _ _ _ _ _ _ _ _ n i hi u h
  classical
  have htr := lcb_transp (K := K) i (Fintype.card P) u h
  have hex : ∀ x : Fin n → P, ∃ ab : Fin n × Fin n, i ≤ ab.1.val ∧ ab.1.val < ab.2.val ∧
      ab.2.val ≤ i + Fintype.card P ∧ x ab.1 = x ab.2 := by
    intro x
    have hcard : Fintype.card P < Fintype.card (Fin (Fintype.card P + 1)) := by simp
    obtain ⟨s, t, hst, hx⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (Fintype.card P + 1) => x ⟨i + s.val, by have := s.isLt; omega⟩) hcard
    have hs := s.isLt
    have ht := t.isLt
    have hst' : s.val ≠ t.val := fun e => hst (Fin.ext e)
    rcases lt_or_gt_of_ne hst' with hlt | hlt
    · exact ⟨(⟨i + s.val, by omega⟩, ⟨i + t.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx⟩
    · exact ⟨(⟨i + t.val, by omega⟩, ⟨i + s.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx.symm⟩
  choose pr hpr using hex
  funext m
  rw [toSym_apply_sum_fiber]
  let xs : (Fin n → R × P) → Fin n → P := fun g s => (g s).2
  let inv : (Fin n → R × P) → (Fin n → R × P) := fun g => g ∘ Equiv.swap (pr (xs g)).1 (pr (xs g)).2
  have hxs : ∀ g, xs (inv g) = xs g := by
    intro g; funext s
    obtain ⟨_, _, _, h4⟩ := hpr (xs g)
    show (g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).2 = (g s).2
    by_cases hs1 : s = (pr (xs g)).1
    · rw [hs1, Equiv.swap_apply_left]; exact h4.symm
    · by_cases hs2 : s = (pr (xs g)).2
      · rw [hs2, Equiv.swap_apply_right]; exact h4
      · rw [Equiv.swap_apply_of_ne_of_ne hs1 hs2]
  have hu : ∀ g, u g + u (inv g) = 0 := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hpr (xs g)
    have key := congrFun (htr ((pr (xs g)).2.val - (pr (xs g)).1.val - 1) (pr (xs g)).1 (pr (xs g)).2 h1
      (by omega) h3) g
    rw [permSecond_apply] at key
    have e : (fun s => ((g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).1, (g s).2)) = inv g := by
      funext s
      have := congrFun (hxs g) s
      exact Prod.ext rfl this.symm
    rw [e] at key
    rw [key]; simp
  show _ = (0 : M)
  refine Finset.sum_involution (fun g _ => inv g) ?_ ?_ ?_ ?_
  · intro g _; exact hu g
  · intro g _ hne heq
    apply hne
    have h0 := hu g
    rw [heq] at h0
    have h2 : (2 : K) • u g = 0 := by rw [two_smul]; exact h0
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    show cont (g ∘ _) = m
    rw [content_comp_perm_eq]; exact hg
  · intro g _
    show (inv g) ∘ Equiv.swap (pr (xs (inv g))).1 (pr (xs (inv g))).2 = g
    rw [hxs g]
    funext s
    simp [inv]

theorem lcb_mono {n : ℕ} (col : Fin n → ℕ) (h : ∀ (j : Fin n) (hj : j.val + 1 < n), col j ≤ col ⟨j.val + 1, hj⟩) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d → col a ≤ col b := by
  intro d
  induction d with
  | zero => intro a b hb; have : a = b := Fin.ext (by omega); rw [this]
  | succ d ih =>
    intro a b hb
    have hc : a.val + d < n := by have := b.isLt; omega
    have hc' : (⟨a.val + d, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d, hc⟩ : Fin n).val + 1, hc'⟩ := Fin.ext (by simp only; omega)
    calc col a ≤ col ⟨a.val + d, hc⟩ := ih a _ rfl
      _ ≤ col b := by rw [hb']; exact h _ hc'

theorem lcb_ivt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (hp : IsPath n lam2 tau κ ρ) (a : Fin q) (j0 : ℕ) (h0 : lam2 a ≤ j0) :
    ∀ m ≤ n, j0 < κ m a → ∃ l : Fin n, ρ l = a ∧ κ l.val a = j0 := by
  intro m
  induction m with
  | zero => intro _ h; rw [hp.start] at h; omega
  | succ m ih =>
    intro hm h
    by_cases h' : j0 < κ m a
    · exact ih (by omega) h'
    · have hs := hp.step ⟨m, by omega⟩
      have hs' : κ (m + 1) a = κ m a + (Pi.single (ρ ⟨m, by omega⟩) 1 : Fin q → ℕ) a := by
        have := congrFun hs a; simpa using this
      by_cases hr : ρ ⟨m, by omega⟩ = a
      · refine ⟨⟨m, by omega⟩, hr, ?_⟩
        rw [hr, Pi.single_eq_same] at hs'
        simp only; omega
      · rw [Pi.single_eq_of_ne (Ne.symm hr)] at hs'
        omega

theorem monotone_run : MonoRun := by
  intro q n lam2 tau κ ρ hp hmono p j0 hlen
  classical
  unfold LD.colLen at hlen
  set S : Finset (Fin n) := Finset.univ.filter (fun l => colSeq κ ρ l = j0) with hS
  have hmem : ∀ l, l ∈ S ↔ colSeq κ ρ l = j0 := by
    intro l; simp [hS]
  have hsub : (Finset.univ.filter fun a : Fin q => lam2 a ≤ j0 ∧ j0 < tau a) ⊆ S.image ρ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, hl1, hl2⟩ := lcb_ivt hp a j0 ha.1 n le_rfl (by rw [hp.stop]; exact ha.2)
    refine Finset.mem_image.mpr ⟨l, ?_, hl1⟩
    rw [hmem]
    unfold colSeq
    rw [hl1]; exact hl2
  have hcard : p < S.card := by
    calc p < _ := hlen
      _ ≤ (S.image ρ).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hi : colSeq κ ρ (S.min' hne) = j0 := (hmem _).mp (Finset.min'_mem S hne)
  have hi' : colSeq κ ρ (S.max' hne) = j0 := (hmem _).mp (Finset.max'_mem S hne)
  have hIcc : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun l hl =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S l hl, Finset.le_max' S l hl⟩
  have hc2 : S.card ≤ (S.max' hne).val + 1 - (S.min' hne).val := by
    have := Finset.card_le_card hIcc
    rwa [Fin.card_Icc] at this
  refine ⟨(S.min' hne).val, by have := (S.max' hne).isLt; omega, fun l h1 h2 => ?_⟩
  have m1 := lcb_mono _ hmono (l.val - (S.min' hne).val) (S.min' hne) l (by omega)
  have m2 := lcb_mono _ hmono ((S.max' hne).val - l.val) l (S.max' hne) (by omega)
  omega

end Formalism.CohomologicalDescent.LC
end

section

open MvPolynomial TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla

open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices

theorem units_of_local_holds : UnitsOfLocal := by
  intro O _ _ l hl hlO m hm
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hb : ((l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m) = 1 := by
    have h := Nat.gcd_eq_gcd_ab l m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hO : ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) = 1 := by
    have h := congrArg (Int.cast : ℤ → O) hb
    push_cast at h
    exact h
  have hu : IsUnit ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) := by
    rw [hO]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact absurd (isUnit_of_mul_isUnit_left h) hlO
  · exact isUnit_of_mul_isUnit_left h

section core

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))

include hl hlO he

end core

theorem nabla_rep_tensor_product : NablaRepTprod := by
  intro O _ ι r n ν g a
  exact ⟨PiTensorProduct.map_tprod (fun i => dualWeylRep O (r i) (n i) (ν i) (g i)) a, fun i => rfl⟩

theorem delta_lattice_stable_holds : DeltaInStable := by
  intro O _ r n hn ν g x hx
  exact Formalism.UG.P.weyl_module_GL_stable O r n hn ν g _ hx

theorem nablaRep_mem_delta (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (x : Nabla O r n ν) (hx : x ∈ Delta O r n hn ν) : nablaRep O r n ν g x ∈ Delta O r n hn ν := by
  unfold Delta tensSub at hx ⊢
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, (nabla_rep_tensor_product O ι r n ν g _).1]
    refine Submodule.smul_mem _ c (LinearMap.mem_range.mpr ⟨PiTensorProduct.tprod O (fun i =>
      (⟨dualWeylRep O (r i) (n i) (ν i) (g i) (a i),
        delta_lattice_stable_holds O (r i) (n i) (hn i) (ν i) (g i) _ (a i).2⟩ :
          deltaIn O (r i) (n i) (hn i) (ν i))), ?_⟩)
    rw [PiTensorProduct.map_tprod]
    all_goals rfl
  | add x y ihx ihy =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ihx ihy

end Formalism.CohomologicalDescent.RealLocalDeltaNabla
end
end
