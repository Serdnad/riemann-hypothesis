module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartMul

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem isEval_algHom_comp {A A' σ : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A']
    {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E) (g : A →ₐ[O] A') :
    IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    rw [e]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem ev₂_inL (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev₂_inR (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev_nmul (c : QLog.Chart G d) (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  induction k generalizing i with
  | zero =>
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero]
    simp [mulBy, c.aug n i]
  | succ k ih =>
    let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    let L : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift M (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    have e : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    have hE := isEval_algHom_comp (c.isEval₂ n) L
    have hx : (fun j => L (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
        fun j => c.ev n (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) := by
      funext j
      rcases j with j | j
      · simp [L, M, ih j]
      · simp [L, (c.isEval n).1 j]
    rw [hx] at hE
    rw [e, H _ _ _ hs hE, AlgHom.comp_apply, c.comul n i]
    have h1 : mulBy O (G.A n) (k + 1) (c.x n i) =
        (WithConv.toConv (AlgHom.id O (G.A n)) ^ (k + 1)).ofConv (c.x n i) :=
      DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O (G.A n)) (k + 1)) (c.x n i)
    have h2 : (M : G.A n →ₐ[O] G.A n) = (WithConv.toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
      comp_mulBy_pts (AlgHom.id O (G.A n)) k
    rw [h1, pow_succ, AlgHom.convMul_apply]
    simp only [L, h2]

theorem ev_subst_nmul (c : QLog.Chart G d) (n k : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  have hE := isEval_algHom_comp (c.isEval n) M
  have hx : (fun j => M (c.x n j)) = fun j => c.ev n (nmul c.μ k j) :=
    funext fun j => (ev_nmul c n k j).symm
  rw [hx] at hE
  exact H (Fin d) _ _ (constantCoeff_nmul c.isLaw.const k) hE f

theorem ev₂_pull2_nmul (c : QLog.Chart G d) (n k : ℕ) (s : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  let T : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] G.A n := Algebra.TensorProduct.map M M
  have hs : ∀ j, constantCoeff (Sum.elim (fun j => inL (nmul c.μ k j))
      (fun j => inR (nmul c.μ k j)) j) = 0 := by
    have hX : ∀ j : Fin d, constantCoeff (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    have hY : ∀ j : Fin d, constantCoeff (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hX) hX
        (constantCoeff_nmul c.isLaw.const k j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hY) hY
        (constantCoeff_nmul c.isLaw.const k j)
  have hE := isEval_algHom_comp (c.isEval₂ n) T
  have hx : (fun j => T (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n))
      (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
      fun j => c.ev₂ n (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j)) j) := by
    funext j
    rcases j with j | j
    · simp [T, M, ev₂_inL, ev_nmul]
    · simp [T, M, ev₂_inR, ev_nmul]
  rw [hx] at hE
  have e : pull2 (nmul c.μ k) s =
      subst (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j))) s := rfl
  rw [e, H _ _ _ hs hE, AlgHom.comp_apply]
  generalize c.ev₂ n s = t
  induction t with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a b => simp [T, M]

theorem nmul_ev : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n k,
    (∀ i, c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i)) ∧
    (∀ f, c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f)) ∧
    ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) :=
  fun _ _ _ _ _ _ c n k => ⟨ev_nmul c n k, ev_subst_nmul c n k, ev₂_pull2_nmul c n k⟩

end GlobalTheory.QLog.ChartMul
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalChart_natMultiple_eval_properties :
    ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d), ∀ n k,
      (∀ i, c.ev n (nmul c.μ k i) = GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k (c.x n i)) ∧
      (∀ f, c.ev n (subst (nmul c.μ k) f) =
        GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k (c.ev n f)) ∧
      ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) =
        pullbackTwo (GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k) (c.ev₂ n s) := by
  intro p O _ _ G d c n k
  have isEval_algHom_comp {A A' σ : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A']
      {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E) (g : A →ₐ[O] A') :
      IsEval p (fun i => g (x i)) (g.comp E) := by
    refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
    obtain ⟨N, hN⟩ := hE.2 m
    refine ⟨N, fun f hf => ?_⟩
    have := map_dvd g (hN f hf)
    rwa [map_pow, map_natCast] at this

  have constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
      (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
    induction k generalizing i with
    | zero => simp [nmul]
    | succ k ih =>
      have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X _
      have e : nmul μ (k + 1) i = subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (μ i) := by
        simp only [nmul]
        rw [Function.iterate_succ_apply']
        rfl
      rw [e]
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

  have ev₂_inL (c : GlobalTheory.QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      GlobalTheory.T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_algHom_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

  have ev₂_inR (c : GlobalTheory.QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      GlobalTheory.T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_algHom_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

  have ev_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (i : Fin d) :
      c.ev n (nmul c.μ k i) = GlobalTheory.PDiv.mulBy O (G.A n) k (c.x n i) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := GlobalTheory.T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
    induction k generalizing i with
    | zero =>
      have h0 : nmul c.μ 0 i = 0 := rfl
      rw [h0, map_zero]
      simp [GlobalTheory.PDiv.mulBy, c.aug n i]
    | succ k ih =>
      let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
      let L : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
        Algebra.TensorProduct.lift M (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
      have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact constantCoeff_nmul c.isLaw.const k j
        · exact constantCoeff_X _
      have e : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ i) := by
        simp only [nmul]
        rw [Function.iterate_succ_apply']
        rfl
      have hE := isEval_algHom_comp (c.isEval₂ n) L
      have hx : (fun j => L (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
          fun j => c.ev n (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) := by
        funext j
        rcases j with j | j
        · simp [L, M, ih j]
        · simp [L, (c.isEval n).1 j]
      rw [hx] at hE
      rw [e, H _ _ _ hs hE, AlgHom.comp_apply, c.comul n i]
      have h1 : GlobalTheory.PDiv.mulBy O (G.A n) (k + 1) (c.x n i) =
          (WithConv.toConv (AlgHom.id O (G.A n)) ^ (k + 1)).ofConv (c.x n i) :=
        DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O (G.A n)) (k + 1)) (c.x n i)
      have h2 : (M : G.A n →ₐ[O] G.A n) = (WithConv.toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
        comp_mulBy_pts (AlgHom.id O (G.A n)) k
      rw [h1, pow_succ, AlgHom.convMul_apply]
      simp only [L, h2]

  have ev_subst_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev n (subst (nmul c.μ k) f) = GlobalTheory.PDiv.mulBy O (G.A n) k (c.ev n f) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := GlobalTheory.T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
    let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    have hE := isEval_algHom_comp (c.isEval n) M
    have hx : (fun j => M (c.x n j)) = fun j => c.ev n (nmul c.μ k j) :=
      funext fun j => (ev_nmul c n k j).symm
    rw [hx] at hE
    exact H (Fin d) _ _ (constantCoeff_nmul c.isLaw.const k) hE f

  have ev₂_pull2_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (s : MvPowerSeries (Fin d ⊕ Fin d) O) :
      c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (GlobalTheory.PDiv.mulBy O (G.A n) k) (c.ev₂ n s) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      GlobalTheory.T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    let T : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] G.A n := Algebra.TensorProduct.map M M
    have hs : ∀ j, constantCoeff (Sum.elim (fun j => inL (nmul c.μ k j))
        (fun j => inR (nmul c.μ k j)) j) = 0 := by
      have hX : ∀ j : Fin d, constantCoeff (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
        fun _ => constantCoeff_X _
      have hY : ∀ j : Fin d, constantCoeff (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
        fun _ => constantCoeff_X _
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hX) hX
          (constantCoeff_nmul c.isLaw.const k j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hY) hY
          (constantCoeff_nmul c.isLaw.const k j)
    have hE := isEval_algHom_comp (c.isEval₂ n) T
    have hx : (fun j => T (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n))
        (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
        fun j => c.ev₂ n (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j)) j) := by
      funext j
      rcases j with j | j
      · simp [T, M, ev₂_inL, ev_nmul]
      · simp [T, M, ev₂_inR, ev_nmul]
    rw [hx] at hE
    have e : pull2 (nmul c.μ k) s =
        subst (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j))) s := rfl
    rw [e, H _ _ _ hs hE, AlgHom.comp_apply]
    generalize c.ev₂ n s = t
    induction t with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul a b => simp [T, M]
  exact ⟨ev_nmul c n k, ev_subst_nmul c n k, ev₂_pull2_nmul c n k⟩
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem cob2_cob1_lift_mem_intBy_and_swap_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ →
    ∀ f ∈ quasiInt p k (Fin d),
      cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧
      swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈
        intBy p k _ p := by
  intro p _ k _ _ _ d μ hμ f hf
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  obtain ⟨hcc1, hcc2, -⟩ := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL f
  have hred := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have hr := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)

  have hX3 : ∀ (j : Fin d ⊕ (Fin d ⊕ Fin d)),
      constantCoeff (X j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)) = 0 :=
    fun j => constantCoeff_X j
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff (op (fun i => Katz.lift p (μ i)) a b i) = 0 := by
    intro a b ha hb i
    exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty a b ha hb).2.2.2.1 _).trans (hL i)
  refine ⟨?_, ?_⟩
  · rw [hcc1]
    have hA := hop x1 _ hx1 (hop x2 x3 hx2 hx3)
    have hB := hop _ x3 (hop x1 x2 hx1 hx2) hx3
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) _ _ (op μ x1 (op μ x2 x3)) f
      hA hB (fun i => (hred.2.2.1 i).1) (fun i => ?_) hf
    rw [← hμ.assoc]
    exact (hred.2.2.1 i).2
  · rw [hcc2]
    have hXs : ∀ (j : Fin d ⊕ Fin d),
        constantCoeff (X j : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
      fun j => constantCoeff_X j
    have hS : ∀ i, constantCoeff (swap (Katz.lift p (μ i))) = 0 := by
      intro i
      exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty _ _ (fun j => hXs _) (fun j => hXs _)).2.2.2.1 _).trans
        (hL i)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ Fin d) _ _ μ f hS hL (fun i => ?_)
      (fun i => (hr.2.2.1 (μ i))) hf
    have := (hred.1 _ _ (hr.2.2.1 (μ i))).2
    rwa [hμ.comm i] at this

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.degree_part_integralDifferential_of_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  first | exact @GlobalTheory.Katz.WDer.main | exact GlobalTheory.Katz.WDer.main | (intros; apply GlobalTheory.Katz.WDer.main <;> assumption)
end
