module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle031
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
public import GroundTheory.AutomorphicForms.WhittakerCells
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GLnLocal

@[expose] public section

section

namespace UpperTheory.Gal.LocD

theorem tracePow : TracePow := by
  intro J _ _ _ _ φ hφ k₀
  by_contra hne
  push_neg at hne
  set p := φ.charpoly with hp
  have hc : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff φ).1
      (by rw [Polynomial.constantCoeff_apply]; exact h0)
    exact hm (hφ (by rw [hm0, map_zero]))
  set t : Polynomial ℂ := -Polynomial.C (p.coeff 0)⁻¹ * Polynomial.divX p with ht
  have hinv : φ * Polynomial.aeval φ t = 1 := by
    have h := congrArg (Polynomial.aeval φ) (Polynomial.X_mul_divX_add p)
    rw [hp, LinearMap.aeval_self_charpoly, ← hp] at h
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    have h' : φ * Polynomial.aeval φ (Polynomial.divX p) = -(algebraMap ℂ _ (p.coeff 0)) :=
      eq_neg_of_add_eq_zero_left h
    rw [ht, map_mul, map_neg, Polynomial.aeval_C, neg_mul, mul_neg, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, h', mul_neg, neg_neg, ← map_mul, inv_mul_cancel₀ hc,
      map_one]
  set Q : Polynomial ℂ := (Polynomial.X * t) ^ k₀ with hQ
  have hQ1 : Polynomial.aeval φ Q = 1 := by
    rw [hQ, map_pow, map_mul, Polynomial.aeval_X, hinv, one_pow]
  have htr : LinearMap.trace ℂ J (Polynomial.aeval φ Q) = 0 := by

    rw [Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    by_cases hi : k₀ ≤ i
    · rw [hne i hi, mul_zero]
    · rw [hQ, mul_pow, Polynomial.coeff_X_pow_mul', if_neg hi, zero_mul]
  rw [hQ1, LinearMap.trace_one] at htr
  exact (Nat.cast_ne_zero.2 (Module.finrank_pos (R := ℂ) (M := J)).ne') htr

end UpperTheory.Gal.LocD
end

section

noncomputable section

namespace UpperTheory.Gal.LocD

private theorem common_eigenvector {T D : Type} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D]
    (φ : T → Module.End ℂ D) (hc : ∀ s t, Commute (φ s) (φ t)) :
    ∃ (l : D) (a : T → ℂ), l ≠ 0 ∧ ∀ t, φ t l = a t • l :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector φ hc

theorem eigZero : EigZero := by
  intro T J _ _ _ _ _ ρ
  have hcomm : ∀ s t, Commute (ρ s) (ρ t) := fun s t => by
    change ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  haveI : Nontrivial (Module.Dual ℂ J) := by
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    have hex : ∃ g : Module.Dual ℂ J, g y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, 0, fun h => hg (by simp [h])⟩
  obtain ⟨l, a, hl0, hl⟩ := common_eigenvector (fun t => (ρ t).dualMap) (fun s t => by
    change (ρ s).dualMap * (ρ t).dualMap = (ρ t).dualMap * (ρ s).dualMap
    ext g y
    have h := congrArg (fun F : Module.End ℂ J => F y) (hcomm s t).eq
    simp only [Module.End.mul_apply] at h
    simp [Module.End.mul_apply, LinearMap.dualMap_apply, h])
  have hact : ∀ t y, l (ρ t y) = a t * l y := fun t y => by
    have := congrArg (fun g : Module.Dual ℂ J => g y) (hl t)
    simpa [LinearMap.dualMap_apply] using this
  obtain ⟨y₀, hy₀⟩ : ∃ y, l y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl0 (LinearMap.ext h)
  let am : T →* ℂ :=
    { toFun := a
      map_one' := by
        have := hact 1 y₀
        simp only [map_one, Module.End.one_apply] at this
        exact (mul_right_cancel₀ hy₀ (by rw [one_mul]; exact this)).symm
      map_mul' := fun s t => by
        have := hact (s * t) y₀
        rw [map_mul, Module.End.mul_apply, hact s, hact t, ← mul_assoc] at this
        exact (mul_right_cancel₀ hy₀ this).symm }
  refine ⟨am.toHomUnits, l, ?_, ?_, ?_⟩
  · exact hl0
  · intro t y
    simpa [am] using hact t y
  · have hval : ∀ t, ((am.toHomUnits t : ℂˣ) : ℂ) = a t := fun t => by simp [am]
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun t => ρ t) (fun s t _ => hcomm s t)
      (fun t => Module.End.iSup_maxGenEigenspace_eq_top (ρ t))
    obtain ⟨χ, y, hy, hly⟩ : ∃ (χ : T → ℂ) (y : J),
        y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t) : Submodule ℂ J) ∧ l y ≠ 0 := by
      by_contra h
      push_neg at h
      have : (⊤ : Submodule ℂ J) ≤ LinearMap.ker l := by
        rw [← htop]
        exact iSup_le fun χ y hy => LinearMap.mem_ker.2 (h χ y hy)
      exact hl0 (LinearMap.ker_eq_top.1 (top_le_iff.1 this))
    have hpow : ∀ (t : T) (c : ℂ) (m : ℕ) (z : J), l (((ρ t - c • 1) ^ m) z) = (a t - c) ^ m * l z := by
      intro t c m
      induction m with
      | zero => intro z; simp
      | succ m ih =>
        intro z
        rw [pow_succ, Module.End.mul_apply, ih]
        simp [hact, pow_succ, sub_mul, mul_assoc]
    have hχ : ∀ t, χ t = a t := by
      intro t
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hy t)
      have h0 := hpow t (χ t) m y
      rw [hm, map_zero] at h0
      have : (a t - χ t) ^ m = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact h
        · exact absurd h hly
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at this
      exact (sub_eq_zero.1 ((pow_eq_zero_iff hm0).1 this)).symm
    intro hbot
    have hy' : y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) ((am.toHomUnits t : ℂˣ) : ℂ) : Submodule ℂ J) := by
      simp only [hval, ← hχ]
      exact hy
    rw [hbot, Submodule.mem_bot] at hy'
    exact hly (by rw [hy', map_zero])

end UpperTheory.Gal.LocD

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.distZero :
    CellStep → DistZero := by
  intro hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf
  obtain ⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j) := ⟨_, rfl⟩
  have hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l) := by
    intro l y
    rw [hC]
  have hcov : ∀ y, ∃ l, y ∈ C l := fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    exact hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))
  have hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l := by
    rw [hC]
    exact hcl
  have hsorb : ∀ l y, y ∈ C l → s y ∈ C l := by
    intro l y hy
    rw [hCl] at hy ⊢
    obtain ⟨g, rfl⟩ := hy
    exact ⟨τ g, by rw [hcomm, hfix]⟩
  have key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero] at hg
      have hg0 : g = 0 := by
        funext y
        by_contra hy
        exact hg.2 hy
      rw [hg0, map_zero]
    | succ j ih =>
      intro hjk g hg
      have hj : j < k := by omega
      have hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩ :=
        GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩
      refine hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum
        (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩)
        (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg
      · rw [Set.inter_comm]
        have h1 := GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩
        rw [h1, hC]
      · intro h y hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hy ⊢
        obtain ⟨l, hl, hyl⟩ := hy
        refine ⟨l, hl, ?_⟩
        rw [hCl] at hyl ⊢
        obtain ⟨g', rfl⟩ := hyl
        exact ⟨h * g', mul_smul _ _ _⟩
      · intro y
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]
        constructor
        · rintro ⟨l, hl, hsy⟩
          obtain ⟨m, hm⟩ := hcov y
          have hlm : l = m := (huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))
          subst hlm
          exact ⟨l, hl, hm⟩
        · rintro ⟨l, hl, hy⟩
          exact ⟨l, hl, hsorb l y hy⟩
      · intro g' hg'
        rw [Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn] at hg'
        obtain ⟨hg1, hg2⟩ := hg'
        apply ih (by omega)
        rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn]
        refine ⟨hg1.1, ?_⟩
        intro y hy
        have hyU := hg1.2 hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hyU ⊢
        obtain ⟨l, hl, hyl⟩ := hyU
        refine ⟨l, ?_, hyl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact hlt
        · exfalso
          apply hy
          apply hg2
          have hleq : l = ⟨j, hj⟩ := Fin.ext heq
          rw [hleq] at hyl
          exact subset_closure hyl
  apply key k le_rfl f
  rw [GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]
  exact ⟨hf, Set.subset_univ _⟩
end

section

noncomputable section

open UpperTheory.ConvolutionTheory.Loc Matrix
open GroundTheory.Automorphic (permGL permGL_apply)
open DoubleCoset (doubleCoset mem_doubleCoset)

namespace UpperTheory.Gal.LocD

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {n : ℕ}

private theorem mem_blockUpper_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_borel]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

private theorem mem_autBorel_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.borel n E ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.mem_borel_iff, GlobalTheory.SmGL.mem_borel E]

private theorem mem_unipotent_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.unipotent E n ↔ g ∈ GlobalTheory.SmGL.unipB E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_unipotent, GlobalTheory.SmGL.mem_unipB E]
  exact Iff.rfl

private theorem unipB_le_borel {g : GL (Fin n) E} (hg : g ∈ GlobalTheory.SmGL.unipB E (Fin n)) :
    g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GlobalTheory.SmGL.mem_unipB] at hg
  rw [GlobalTheory.SmGL.mem_borel]
  exact hg.1

private theorem doubleCoset_eq_cell (w : Equiv.Perm (Fin n)) :
    doubleCoset (permGL E w) (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) : Set (GL (Fin n) E))
        (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) =
      cell (GlobalTheory.SmGL.borel E (Fin n)) (GlobalTheory.SmGL.unipB E (Fin n)) (permGL E w) := by
  have hset : ((GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) : Set (GL (Fin n) E)) =
      ((GroundTheory.Automorphic.Iwasawa.borel E n) : Set (GL (Fin n) E)) := by
    ext g
    simp only [SetLike.mem_coe]
    rw [mem_blockUpper_iff, ← mem_autBorel_iff]
    rfl
  ext g
  constructor
  · intro hg
    rw [hset, GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm] at hg
    obtain ⟨u, hu, t, v, hv, rfl⟩ := hg
    refine ⟨u * GroundTheory.Automorphic.Iwasawa.diagGL E n t, ?_, v, ?_, rfl⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact unipB_le_borel (mem_unipotent_iff.mp hu)
      · exact mem_autBorel_iff.mp (GroundTheory.Automorphic.Whittaker.diagGL_mem_borel t)
    · exact mem_unipotent_iff.mp hv
  · rintro ⟨b, hb, u, hu, rfl⟩
    rw [mem_doubleCoset]
    exact ⟨b, mem_blockUpper_iff.mpr hb, u, mem_blockUpper_iff.mpr (unipB_le_borel hu), rfl⟩

private theorem sg_permGL (σ : E ≃+* E) (w : Equiv.Perm (Fin n)) : sg σ (permGL E w) = permGL E w := by
  ext i j
  rw [sg_val, permGL_apply]
  split_ifs <;> simp

end SlopeTestRemainingChoices

theorem gLCells : GLCells := by
  intro E _ _ _ _ n σ
  haveI : T2Space E := GroundTheory.Automorphic.GLnLocal.t2Space E
  obtain ⟨k, w, hcov, hanti⟩ :=
    GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := E) (Fin.val : Fin n → ℕ) Fin.val
  have hcl := GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, fun j => permGL E (w j), fun j => sg_permGL σ _, fun g => ?_, fun j => ?_⟩
  · simpa only [doubleCoset_eq_cell] using hcov g
  · simpa only [doubleCoset_eq_cell] using hcl j

end UpperTheory.Gal.LocD

end
end
