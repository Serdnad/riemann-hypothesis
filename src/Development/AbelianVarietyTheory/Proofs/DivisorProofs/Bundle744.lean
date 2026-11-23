module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalRingCardinality.DataTheta
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705

@[expose] public section

section

set_option autoImplicit false

open Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.WeylBasis

theorem map_mem_span {σ ι : Type} (R : Type) [CommRing R] (g : ι → MvPolynomial σ ℤ) {f : MvPolynomial σ ℤ}
    (hf : f ∈ Submodule.span ℤ (Set.range g)) :
    MvPolynomial.map (Int.castRingHom R) f ∈
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (g i)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a

theorem weyl_finite (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) : Module.Finite ℤ (weyl ℤ n n le_rfl ν) := by
  obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
  have : Finite (ssIdx n n ν) := (sSIdxFinite n n ν).to_subtype
  have : Module.Finite ℤ (dualWeyl ℤ n n ν) := by
    rw [← hc.2.1]
    exact Module.Finite.span_of_finite ℤ (Set.finite_range c)
  exact Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ n n le_rfl ν hν))
    (Submodule.inclusion_injective _)

theorem exists_weyl_basis : ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∃ (P : Type) (_ : Fintype P) (b : P → MvPolynomial (Fin n × Fin n) ℤ), LinearIndependent ℤ b ∧ (∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (b i))) ∧ ∀ (K : Type) [Field K] [CharZero K], dualWeyl K n n ν = Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (b i)) := by
  intro n ν hν
  have := weyl_finite n ν hν
  have : Module.Free ℤ (weyl ℤ n n le_rfl ν) := inferInstance
  let B := Module.Free.chooseBasis ℤ (weyl ℤ n n le_rfl ν)
  have hspan : Submodule.span ℤ (Set.range fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ)) = weyl ℤ n n le_rfl ν := by
    have h := congrArg (Submodule.map (weyl ℤ n n le_rfl ν).subtype) B.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h
    exact h
  have hR : ∀ (R : Type) [CommRing R], weyl R n n le_rfl ν =
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (B i : MvPolynomial (Fin n × Fin n) ℤ)) := by
    intro R _
    apply le_antisymm
    · unfold weyl
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      have hw' : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ n n le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
      rw [← hspan] at hw'
      have h := map_mem_span R _ hw'
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h := map_mem_span R (fun w : List (Fin n × Fin n × ℕ) => applyWord ℤ w (hw ℤ le_rfl ν)) (B i).2
      simp only [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
  refine ⟨_, inferInstance, fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ), ?_, hR, ?_⟩
  · exact B.linearIndependent.map' (weyl ℤ n n le_rfl ν).subtype (Submodule.ker_subtype _)
  · intro K _ _
    apply le_antisymm
    · obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
      rw [← span_map_weightBasis_eq_dualWeyl (K := K) hc, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : c j ∈ dualWeyl ℤ n n ν := hc.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨m, hm, hmj⟩ := weylRational n n le_rfl ν hν _ hj
      rw [← hspan] at hmj
      have h := map_mem_span K _ hmj
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul K] at h
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hm)).1 h
    · rw [← hR K]
      exact weylLeDual K n n le_rfl ν hν

end GlobalTheory.WeylBasis
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockCasimir

theorem sum_mul_normal_order {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x d : ι → κ → A)
    (h : ∀ b c e, d b c * x b e = x b e * d b c + if c = e then 1 else 0) :
    ∑ a, ∑ b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      (∑ a, ∑ b, ∑ c, ∑ e, x a c * x b e * (d b c * d a e)) +
        ((Fintype.card ι : ℂ) + (Fintype.card κ : ℂ)) • (∑ a, ∑ c, x a c * d a c) +
        ((Fintype.card ι : ℂ) * (Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) := by
  have h0 : ∀ a b, (∑ c, x a c * d b c) * (∑ e, x b e * d a e) =
      (∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c := by
    intro a b
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∀ e, x a c * d b c * (x b e * d a e) =
        x a c * x b e * (d b c * d a e) + if c = e then x a c * d a e else 0 := by
      intro e
      have : x a c * d b c * (x b e * d a e) = x a c * (d b c * x b e) * d a e := by
        simp only [mul_assoc]
      rw [this, h, mul_add, add_mul]
      split_ifs <;> simp [mul_assoc]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ a b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      ((∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c) +
        if a = b then (Fintype.card κ : ℂ) • (∑ c, x a c * d a c) +
          ((Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) else 0 := by
    intro a b
    rw [← h0]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hab, Ne.symm hab]
  simp only [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.smul_sum]
  module

variable {p q r s : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (l m : σ) (P : MvPolynomial σ ℂ) :
    pderiv l (pderiv m P) = pderiv m (pderiv l P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), hP, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem lowB_comm (l m : Ln p q r s) : lowB l * lowB m = lowB m * lowB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun P => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [lowB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
      mul_left_comm]

theorem lowB_mul_raiB (l m : Ln p q r s) :
    lowB l * raiB m = raiB m * lowB l + if l = m then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases hlm : l = m
  · subst hlm
    cases hl : linePos l <;> simp [lowB, raiB, hl, add_comm]
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp [lowB, raiB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
        mul_left_comm]

theorem casimir_fockAct1_sub_casimir_fockAct2 : ∀ (p q r s : ℕ),
    casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) =
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) •
        (1 : Module.End ℂ (Pol p q r s)) := by
  intro p q r s
  have h1 := sum_mul_normal_order (fun (a : Ix p q) (c : Ix r s) => raiB (a, c))
    (fun (a : Ix p q) (c : Ix r s) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have h2 := sum_mul_normal_order (fun (c : Ix r s) (a : Ix p q) => raiB (a, c))
    (fun (c : Ix r s) (a : Ix p q) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have hQ : (∑ c : Ix r s, ∑ e : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q,
        raiB (a, c) * raiB (b, e) * (lowB (a, e) * lowB (b, c))) =
      ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ e : Ix r s,
        raiB (a, c) * raiB (b, e) * (lowB (b, c) * lowB (a, e)) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q)]
    simp only [← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q),
      ← Fintype.sum_prod_type' (α₁ := Ix r s) (α₂ := Ix r s)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [lowB_comm]
  have hE : (∑ c : Ix r s, ∑ a : Ix p q, raiB (a, c) * lowB (a, c)) =
      ∑ a : Ix p q, ∑ c : Ix r s, raiB (a, c) * lowB (a, c) := Finset.sum_comm
  rw [hQ, hE] at h2
  simp only [Formalism.BasicNotions.TH.casimir, fockAct1_Eab, fockAct2_Eab, Formalism.BasicNotions.TH.omE, Prod.mk.injEq, and_true, true_and]
  rw [h1, h2]
  simp only [Fintype.card_sum, Fintype.card_fin]
  module

end GlobalTheory.FockCasimir
end
end

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]

  simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
  map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

end GlobalTheory.FockSplit
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockPolGK

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (i j : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) :
    X i * pderiv j P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [mem_restrictTotalDegree] at hP

  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : (α.sum fun _ e => e) ≤ d := (le_totalDegree hα).trans hP
  rw [pderiv_monomial]
  by_cases h : α j = 0
  · simp [h]
  · rw [mem_restrictTotalDegree, X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [hk]
    conv_rhs => rw [hα]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
    rfl

theorem omE_mem {p q r s : ℕ} (d : ℕ) (l l' : Ln p q r s) (h : linePos l = linePos l')
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omE l l' P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      change -(pderiv l ((X l' : Pol p q r s) * P)) ∈ _
      refine Submodule.neg_mem _ ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_
      by_cases e : l' = l
      · subst e; rw [pderiv_X_self, mul_one]; exact hP
      · rw [pderiv_X_of_ne e, mul_zero]; exact Submodule.zero_mem _
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      exact X_mul_pderiv_mem d _ _ P hP
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem omAct_mem {p q r s : ℕ} (d : ℕ) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (hZ : ∀ l l', linePos l ≠ linePos l' → Z l l' = 0)
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omAct p q r s Z P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem d l l' h P hP)
  · rw [hZ l l' h, zero_smul]; exact Submodule.zero_mem _

theorem kStable1 (p q r s d : ℕ) :
    KStable (fockAct1 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change Z a b * (1 : Mat r s) c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hZ a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, mul_zero]

theorem kStable2 (p q r s d : ℕ) :
    KStable (fockAct2 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change (1 : Mat p q) a b * Z c e = 0
  by_cases hc : a = b
  · subst hc
    rw [hZ c e, mul_zero]
    rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, zero_mul]

def signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) : ℚ := if linePos (a, c) then 1 else -1

theorem cast_signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) :
    ((signQ a c : ℚ) : ℂ) = lineSign a c := by
  rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]

theorem mem_of_monomials {σ : Type} (N : Submodule ℂ (MvPolynomial σ ℂ))
    (h : ∀ α, monomial α (1 : ℂ) ∈ N) (P : MvPolynomial σ ℂ) : P ∈ N := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have := N.smul_mem (AddMonoidAlgebra.coeff P α) (h α)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

theorem monomial_mem_weightSpace_fockAction_first {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct1 p q r s)
      (fun a => ∑ c, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem monomial_mem_weightSpace_fockAction_second {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct2 p q r s)
      (fun c => ∑ a, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem pol_locFin_weights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  intro p q r s
  refine ⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩,
    fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P

end GlobalTheory.FockPolGK
end
end
