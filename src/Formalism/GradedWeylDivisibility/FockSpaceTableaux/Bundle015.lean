module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem weylEqNablaQ_of (h : ClosedEqNabla) : WeylEqNablaQ := by
  intro r n hn ν hν
  refine h r n hn ν hν (weyl ℚ r n hn ν) (weylLeDual ℚ r n hn ν hν)
    (fun a b k f hf => weylRowDivStable ℚ r n hn ν a b k f hf) ?_

  exact Submodule.subset_span ⟨[], rfl⟩

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem semistandard_module_assembly : SMSAssembly := by
  intro hCL hCS hSS hLI B _ _ r n ν
  apply le_antisymm
  · have key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl B r n ν,
        (colLex r n).toSyn ((colLex r n).degree f) = d →
        f ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
          (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        have hm := (colLex r n).degree_mem_support hf0
        obtain ⟨K, sz, hsz, I, hsh, hmono, hexp⟩ :=
          hSS r n ν _ (hCS B r n ν f hf _ hm) (hLI B r n ν f hf hf0)
        obtain ⟨hdeg, hlc⟩ := hCL B r n K sz hsz I hmono
        have hg : bideterminant B sz hsz I ∈ dualWeyl B r n ν := by
          rw [← hsh]; exact bidetMem B r n K sz hsz I
        have hgS : bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ)
            (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
            shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} :=
          Submodule.subset_span ⟨K, sz, hsz, I, hsh, rfl⟩
        have hf' : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ dualWeyl B r n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hg)
        have h1 : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ Submodule.span B
            {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
              shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
          by_cases hne : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I = 0
          · rw [hne]; exact Submodule.zero_mem _
          have hlt := lcassem_sub_lt (colLex r n) (hdeg.trans hexp) hlc hne
          exact ih _ (by rw [← hd]; exact hlt) _ hf' rfl
        have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ ((colLex r n).leadingCoeff f) hgS)
        rwa [sub_add_cancel] at h2
    exact fun f hf => key _ f hf rfl
  · rw [Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← hsh]
    exact bidetMem B r n K sz hsz I

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line_tall : HWLineTall := by
  intro K _ _ r n ν ⟨s, hs, hνs⟩ f hf hdiv
  obtain ⟨hhom, hcol⟩ := (dualWeylPoint K r n ν f).mp hf
  refine lhwline_vanish f (fun a b hab => lhwline_rowGen_eq a b f (hdiv a b hab)) hcol ?_
  intro D hD
  exact lhwline_diag_tall ν s hs hνs f hhom D hD

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_weight_sum {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) :
    ∑ s : Fin n, Finsupp.weight (colW r n) m s = Finsupp.weight (1 : Fin r × Fin n → ℕ) m := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [colW, Pi.single_apply]

theorem lclosedeq_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  classical
  have hS : Set.Finite {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin r × Fin n => ν v.2))).subset ?_
    intro d hd
    have hd' : Finsupp.weight (colW r n) d = ν := hd
    show d ≤ _
    rw [Finsupp.le_def]
    intro v
    have h1 : d v ≤ Finsupp.weight (colW r n) d v.2 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      by_cases hv : v ∈ d.support
      · refine le_trans ?_ (Finset.single_le_sum
          (f := fun u => (d u • colW r n u) v.2) (fun _ _ => Nat.zero_le _) hv)
        simp [colW]
      · have : d v = 0 := by
          by_contra h
          exact hv (Finsupp.mem_support_iff.mpr h)
        rw [this]
        exact Nat.zero_le _
    rw [hd'] at h1
    simpa using h1
  haveI := hS.to_subtype
  haveI hfd : FiniteDimensional ℚ (weightedHomogeneousSubmodule ℚ (colW r n) ν) := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp
      {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν}).symm
  exact Submodule.finiteDimensional_of_le (fun f hf => (Submodule.mem_inf.mp hf).1)

def lclosedeq_B {σ : Type} (h2 : FockQPos) (h3 : FockQBilin) :
    LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (h3 σ f f' g 1).1)
    (fun c f g => by rw [(h3 σ f f g c).2, smul_eq_mul])
    (fun f g g' => by rw [(h2 σ f _).1, (h3 σ g g' f 1).1, (h2 σ g f).1, (h2 σ g' f).1])
    (fun c f g => by rw [(h2 σ f _).1, (h3 σ g g f c).2, (h2 σ g f).1, smul_eq_mul])

theorem closedEqNabla_of (h1 : HWInClosed) (h2 : FockQPos) (h3 : FockQBilin) (h4 : FockQRowDivAdj) :
    ClosedEqNabla := by
  intro r n hn ν hν M hMV hMc hhw
  have hfdV : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := lclosedeq_fd r n ν
  have hfdM : FiniteDimensional ℚ M := Submodule.finiteDimensional_of_le hMV
  let B := lclosedeq_B (σ := Fin r × Fin n) h2 h3
  have hB : ∀ f g, B f g = fockQ f g := fun _ _ => rfl
  let N : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ) :=
    { carrier := {x | x ∈ dualWeyl ℚ r n ν ∧ ∀ g ∈ M, fockQ x g = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Submodule.add_mem _ hx hy, fun g hg => ?_⟩
        rw [← hB, map_add (f := _), LinearMap.add_apply, hB, hB, hx' g hg, hy' g hg, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by rw [← hB, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨Submodule.smul_mem _ c hx, fun g hg => ?_⟩
        rw [← hB, map_smul, LinearMap.smul_apply, hB, hx' g hg, smul_zero] }
  have hNV : N ≤ dualWeyl ℚ r n ν := fun x hx => hx.1
  have hNc : RowDivClosed N := by
    intro a b k f hf
    obtain ⟨hf1, hf2⟩ := hf
    refine ⟨rowDivStable ℚ r n ν a b k f hf1, fun g hg => ?_⟩
    rw [h4, hf2 _ (hMc b a k g hg)]
  have hN : N = ⊥ := by
    by_contra hne
    have hmem := h1 r n hn ν hν N hNV hNc hne
    have h0 := hmem.2 _ hhw
    have hpos := (h2 _ (hw ℚ hn ν) 0).2 (hwNe ℚ r n hn ν)
    linarith
  let BM := B.restrict M
  have hBM : ∀ x y : M, BM x y = fockQ (x : MvPolynomial (Fin r × Fin n) ℚ) y := fun _ _ => rfl
  have key : ∀ x : M, (∀ y : M, BM x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (h2 _ (x : MvPolynomial (Fin r × Fin n) ℚ) 0).2 hx0
    have h0 := hx x
    rw [hBM] at h0
    linarith
  have hnd : BM.Nondegenerate := by
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    rw [hBM, (h2 _ _ _).1, ← hBM]
    exact hy x
  apply le_antisymm hMV
  intro f hf
  let φ : Module.Dual ℚ M := (B f).domRestrict M
  let p : M := (BM.toDual hnd).symm φ
  have hp : ∀ g : M, fockQ (p : MvPolynomial (Fin r × Fin n) ℚ) g = fockQ f g := by
    intro g
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ g
    exact this
  have hd : f - p ∈ N := by
    refine ⟨Submodule.sub_mem _ hf (hMV p.2), fun g hg => ?_⟩
    rw [← hB, map_sub, LinearMap.sub_apply, hB, hB, ← hp ⟨g, hg⟩, sub_self]
  rw [hN] at hd
  have hfp : f = p := sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp hd)
  rw [hfp]
  exact p.2

end Formalism.GradedWeylDivisibility
end
end
