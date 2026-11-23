module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_relabel_injective {Ψ : Type} {N : ℕ} (σ : Equiv.Perm Ψ) :
    Function.Injective (fun x : Ψ × Fin N => (σ x.1, x.2)) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (σ.injective hxy.1) hxy.2

theorem pa_degFl_relabel {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (σ : Equiv.Perm Ψ) (F : RP Ψ N) :
    degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F := by
  have hinj := pa_relabel_injective (N := N) σ
  have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
      Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (permExp (fun t => ρ (σ t))) := by
    intro ρ
    ext ⟨t, i⟩
    have ht : ((t, i) : Ψ × Fin N) = (fun x : Ψ × Fin N => (σ x.1, x.2)) (σ.symm t, i) := by simp
    rw [ht, Finsupp.mapDomain_apply_of_injective hinj]
    simp [permExp]
  unfold degFl
  congr 1
  have hterm : ∀ ρ : Ψ → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) *
          (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F).coeff (permExp ρ) =
        (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
          (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ')) (fun t => ρ (σ t)) := by
    intro ρ
    rw [hexp ρ, coeff_rename_mapDomain _ hinj]
    congr 1
    exact (Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ))).symm
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)]
  exact Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N))))
    (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
      (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ'))

theorem degFl_symmetry_invariance : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  intro Ψ _ _ N
  refine ⟨?_, ?_⟩
  · intro τ a b F hab
    have hinv : ∀ x : Ψ × Fin N,
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          ((fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) x) = x := by
      rintro ⟨t, i⟩
      by_cases ht : t = τ <;> simp [ht]
    have hinj : Function.Injective
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) := by
      intro x y hxy
      exact (hinv x).symm.trans ((congrArg
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) hxy).trans (hinv y))
    have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
        Finsupp.mapDomain (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          (permExp (ρ * Pi.mulSingle τ (Equiv.swap a b))) := by
      intro ρ
      ext y
      conv_rhs => rw [← hinv y]
      rw [Finsupp.mapDomain_apply_of_injective hinj]
      rcases y with ⟨t, i⟩
      by_cases ht : t = τ
      · subst ht
        simp [permExp]
      · simp [permExp, ht, Pi.mulSingle_apply]
    have hsgn : ∀ ρ : Ψ → Equiv.Perm (Fin N),
        (∏ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ)) =
          -∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) := by
      intro ρ
      have hfac : ∀ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
          ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * (if t = τ then -1 else 1) := by
        intro t
        by_cases ht : t = τ
        · subst ht
          simp [Equiv.Perm.sign_swap hab]
        · simp [ht]
      rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib]
      simp
    unfold degFl
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulRight (Pi.mulSingle τ (Equiv.swap a b)))
      (fun ρ => -((∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)) * F.coeff (permExp ρ)))]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Equiv.coe_mulRight]
    rw [hexp ρ, coeff_rename_mapDomain _ hinj, hsgn ρ]
    ring
  · intro σ F
    have hinj := pa_relabel_injective (N := N) σ
    refine ⟨pa_degFl_relabel σ F, fun j τ => ⟨?_, ?_⟩⟩
    · unfold Sh
      conv_rhs => rw [← pa_degFl_relabel σ]

      rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F
    · unfold Tot
      conv_rhs => rw [← pa_degFl_relabel σ]

      rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F

end RootFieldNumerics
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem coeff_X_pow_mul_flag_immersions {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) (x : σ) (k : ℕ)
    (p : MvPolynomial σ ℝ) :
    (X x ^ k * p).coeff m = if k ≤ m x then p.coeff (m - Finsupp.single x k) else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
  simp only [Finsupp.single_le_iff]

theorem degFl_power_sum_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 := by
  intro Ψ _ _ N τ k G hk
  have hval : ∀ (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N),
      permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := fun σ x => rfl
  have key : ∀ j : Fin N, ∑ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
        (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ) = 0 := by
    intro j
    have hjN := j.isLt
    by_cases hj : (j : ℕ) + k < N
    · let j' : Fin N := ⟨j + k, hj⟩
      have hj'v : (j' : ℕ) = j + k := rfl
      have hne : j ≠ j' := fun h => by
        have := congrArg Fin.val h
        rw [hj'v] at this
        omega
      let ρ : Ψ → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap j j')
      have hρτ : ρ τ = Equiv.swap j j' := Pi.mulSingle_eq_same _ _
      have hρt : ∀ t, t ≠ τ → ρ t = 1 := fun t ht => Pi.mulSingle_eq_of_ne ht _
      let F : (Ψ → Equiv.Perm (Fin N)) → ℝ := fun σ =>
        (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ)
      have hanti : ∀ σ, F (ρ * σ) = -F σ := by
        intro σ
        have hsign : (∏ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ)) =
            -∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
          have h1 : ∀ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ) =
              ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
            intro t
            rw [Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
          rw [Finset.prod_congr rfl fun t _ => h1 t, Finset.prod_mul_distrib,
            Finset.prod_eq_single τ (fun t _ ht => by rw [hρt t ht, Equiv.Perm.sign_one]; simp)
              (fun h => absurd (Finset.mem_univ τ) h), hρτ, Equiv.Perm.sign_swap hne]
          simp
        have hsymm : ((ρ * σ) τ).symm j = (σ τ).symm j' := by
          rw [Equiv.symm_apply_eq, Pi.mul_apply, hρτ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
            Equiv.swap_apply_right]
        have hat : (σ τ) ((σ τ).symm j) = j := Equiv.apply_symm_apply _ _
        have hbt : (σ τ) ((σ τ).symm j') = j' := Equiv.apply_symm_apply _ _
        have hab : (σ τ).symm j ≠ (σ τ).symm j' := fun h => hne ((σ τ).symm.injective h)
        have hexp : permExp (ρ * σ) - Finsupp.single (τ, (σ τ).symm j') k =
            permExp σ - Finsupp.single (τ, (σ τ).symm j) k := by
          ext ⟨t, i⟩
          simp only [Finsupp.coe_tsub, Pi.sub_apply, hval, Finsupp.single_apply, Prod.mk.injEq]
          by_cases ht : t = τ
          · rw [ht, Pi.mul_apply, hρτ, Equiv.Perm.mul_apply]
            by_cases hia : (σ τ).symm j = i
            · rw [← hia, hat, Equiv.swap_apply_left]
              simp only [hab.symm, true_and, and_false, if_true, if_false]
              omega
            · by_cases hib : (σ τ).symm j' = i
              · rw [← hib, hbt, Equiv.swap_apply_right]
                simp only [hab, true_and, and_false, if_true, if_false]
                omega
              · have h1 : (σ τ) i ≠ j := fun h => hia (by rw [← h, Equiv.symm_apply_apply])
                have h2 : (σ τ) i ≠ j' := fun h => hib (by rw [← h, Equiv.symm_apply_apply])
                rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
                simp only [hia, hib, and_false, if_false]
          · rw [Pi.mul_apply, hρt t ht, one_mul]
            simp only [Ne.symm ht, false_and, if_false]
        have hcond : ∀ σ' : Ψ → Equiv.Perm (Fin N), ∀ a : Fin N, σ' τ a = j →
            (k ≤ permExp σ' (τ, a)) := by
          intro σ' a ha
          rw [hval]
          simp only [ha]
          omega
        have hL : (ρ * σ) τ ((σ τ).symm j') = j := by
          rw [Pi.mul_apply, hρτ, Equiv.Perm.mul_apply, hbt, Equiv.swap_apply_right]
        show (∏ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ)) *
            (X (τ, ((ρ * σ) τ).symm j) ^ k * G).coeff (permExp (ρ * σ)) =
          -((∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
            (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ))
        rw [hsign, hsymm, coeff_X_pow_mul_flag_immersions, coeff_X_pow_mul_flag_immersions, if_pos (hcond _ _ hL),
          if_pos (hcond _ _ hat), hexp, neg_mul]
      have h2 : ∑ σ, F (ρ * σ) = ∑ σ, F σ := Equiv.sum_comp (Equiv.mulLeft ρ) F
      rw [Finset.sum_congr rfl fun σ _ => hanti σ, Finset.sum_neg_distrib] at h2
      change ∑ σ, F σ = 0
      linarith
    · refine Finset.sum_eq_zero fun σ _ => ?_
      have hlt : ¬ k ≤ permExp σ (τ, (σ τ).symm j) := by
        rw [hval]
        simp only [Equiv.apply_symm_apply]
        omega
      rw [coeff_X_pow_mul_flag_immersions, if_neg hlt, mul_zero]
  have hsplit : degFl (pk τ k * G) = (-1) ^ dimFl Ψ N * ∑ j : Fin N, ∑ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
        (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ) := by
    unfold degFl
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [pk, Finset.sum_mul, coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm fun i =>
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (X (τ, i) ^ k * G).coeff (permExp σ)).symm
  rw [hsplit, Finset.sum_eq_zero fun j _ => key j, mul_zero]

end RootFieldNumerics
end

section

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def expo (a : Ψ → Fin N → ℕ) (σ : Ψ → Equiv.Perm (Fin N)) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => a x.1 (σ x.1 x.2))

def alt (a : Ψ → Fin N → ℕ) (G : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * G.coeff (expo a σ)

def rho : Ψ → Fin N → ℕ := fun _ c => N - 1 - (c : ℕ)

def bump (τ : Ψ) (c : Fin N) (k : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c' => N - 1 - (c' : ℕ) + if τ' = τ ∧ c' = c then k else 0

def lam (τ : Ψ) (k : ℕ) (G : RP Ψ N) : ℝ := ∑ c, alt (bump τ c k) G

def Maj (f : Polynomial ℝ) (c A : ℝ) : Prop := ∀ s : ℕ, |f.coeff s| ≤ c * A ^ s / (s.factorial : ℝ)

def gdet (e : Fin N → ℕ) (v : Fin N → Polynomial ℝ) : Polynomial ℝ :=
  Matrix.det (Matrix.of fun c b => Polynomial.C (((e c).factorial : ℝ)⁻¹) * v b ^ e c)

theorem degFl_eq (G : RP Ψ N) : degFl G = (-1) ^ dimFl Ψ N * alt rho G := rfl

theorem alt_add (a : Ψ → Fin N → ℕ) (F G : RP Ψ N) : alt a (F + G) = alt a F + alt a G := by
  simp [alt, mul_add, Finset.sum_add_distrib]

theorem alt_C_mul (a : Ψ → Fin N → ℕ) (r : ℝ) (G : RP Ψ N) : alt a (C r * G) = r * alt a G := by
  simp only [alt, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem alt_sum {ι : Type*} (a : Ψ → Fin N → ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    alt a (∑ i ∈ s, F i) = ∑ i ∈ s, alt a (F i) := by
  simp only [alt, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem lam_add (τ : Ψ) (k : ℕ) (F G : RP Ψ N) : lam τ k (F + G) = lam τ k F + lam τ k G := by
  simp [lam, alt_add, Finset.sum_add_distrib]

theorem lam_sum {ι : Type*} (τ : Ψ) (k : ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    lam τ k (∑ i ∈ s, F i) = ∑ i ∈ s, lam τ k (F i) := by
  simp only [lam, alt_sum]
  exact Finset.sum_comm

end RootFieldNumerics.M5
end
end

section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.L3

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem permExp_apply (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]

theorem permExp_injective :
    Function.Injective (permExp : (Ψ → Equiv.Perm (Fin N)) → (Ψ × Fin N) →₀ ℕ) := by
  intro σ σ' h
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, i)
  rw [permExp_apply, permExp_apply] at h1
  have h2 := (σ τ i).2
  have h3 := (σ' τ i).2
  dsimp only at h1
  omega

theorem degree_permExp_one :
    (permExp (1 : Ψ → Equiv.Perm (Fin N))).degree = dimFl Ψ N := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [permExp_apply, Pi.one_apply, Equiv.Perm.one_apply]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl,
    Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

theorem degFl_monomial_one [DecidableEq Ψ] :
    degFl (monomial (permExp (1 : Ψ → Equiv.Perm (Fin N))) ((-1 : ℝ) ^ dimFl Ψ N)) = 1 := by
  unfold degFl
  rw [Finset.sum_eq_single (1 : Ψ → Equiv.Perm (Fin N))]
  · simp [← mul_pow]
  · intro σ _ hσ
    rw [coeff_monomial, if_neg (fun h => hσ (permExp_injective h).symm), mul_zero]
  · simp

end RootFieldNumerics.L3

theorem RootFieldNumerics.exists_degree_one_class : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  intro Ψ _ _ N j τ h1 hj
  refine ⟨⟨_, isHomogeneous_monomial _ RootFieldNumerics.L3.degree_permExp_one, RootFieldNumerics.L3.degFl_monomial_one⟩, ?_⟩
  let i0 : Fin N := ⟨j - 1, by omega⟩
  let i1 : Fin N := ⟨j, hj⟩
  let m : (Ψ × Fin N) →₀ ℕ := permExp (1 : Ψ → Equiv.Perm (Fin N)) - Finsupp.single (τ, i0) 1
  have hm : Finsupp.single (τ, i0) 1 + m = permExp (1 : Ψ → Equiv.Perm (Fin N)) := by
    apply add_tsub_cancel_of_le
    rw [Finsupp.single_le_iff, RootFieldNumerics.L3.permExp_apply]
    simp only [Pi.one_apply, Equiv.Perm.one_apply, i0]
    omega
  have hdeg : m.degree = dimFl Ψ N - 1 := by
    rw [← RootFieldNumerics.L3.degree_permExp_one, ← hm, map_add (f := _), Finsupp.degree_single]
    omega
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, i1] at this
    omega
  have hm0 : m (τ, i0) = N - 1 - j := by
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, Finsupp.single_eq_same, Pi.one_apply,
      Equiv.Perm.one_apply, i0]
    omega
  have hm1 : m (τ, i1) = N - 1 - j := by
    have : (Finsupp.single (τ, i0) 1 : (Ψ × Fin N) →₀ ℕ) (τ, i1) = 0 :=
      Finsupp.single_eq_of_ne' (by simpa using h01)
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, this, Pi.one_apply,
      Equiv.Perm.one_apply, i1]
    omega
  refine ⟨monomial m ((-1 : ℝ) ^ dimFl Ψ N), isHomogeneous_monomial _ hdeg, ?_⟩
  refine Eq.trans ?_ (RootFieldNumerics.L3.degFl_monomial_one (Ψ := Ψ) (N := N))
  unfold degFl
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [pkLow, Finset.sum_mul, coeff_sum, Finset.sum_eq_single i0]
  · rw [X_pow_eq_monomial, monomial_mul, one_mul, hm]
  · intro i hi hi0
    rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, if_neg]
    intro h
    have hi1 : i ≠ i1 := by
      intro h'
      rw [Finset.mem_filter, h'] at hi
      simp [i1] at hi
    have e0 := DFunLike.congr_fun h (τ, i0)
    have e1 := DFunLike.congr_fun h (τ, i1)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi0), hm0,
      RootFieldNumerics.L3.permExp_apply] at e0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi1), hm1,
      RootFieldNumerics.L3.permExp_apply] at e1
    dsimp only at e0 e1
    have h2 := (σ τ i0).2
    have h3 := (σ τ i1).2
    exact h01 ((σ τ).injective (Fin.ext (by omega)))
  · intro h
    exact absurd (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]; omega) h
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.Lin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def degL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ dimFl Ψ N) •
    ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (permExp σ)

theorem degL_apply (F : RP Ψ N) : degL Ψ N F = degFl F := by
  simp only [degL, degFl, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]

def shL (j : ℕ) (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
    (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem shL_apply (j : ℕ) (τ : Ψ) (F : RP Ψ N) : shL j τ F = Sh j τ F := by
  rw [shL, LinearMap.comp_apply, degL_apply, Sh]
  congr 1
  simp

def totL (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i : Fin N, (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem totL_apply (τ : Ψ) (F : RP Ψ N) : totL τ F = Tot τ F := by
  rw [totL, LinearMap.comp_apply, degL_apply, Tot]
  congr 1
  simp

end RootFieldNumerics.Lin
end
end
