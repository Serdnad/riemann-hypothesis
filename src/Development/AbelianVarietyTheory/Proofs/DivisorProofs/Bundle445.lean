module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLAssoc
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle250
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.RowsSummed

theorem norm_ch (N : ℕ) (j : ZMod N) : ‖ch N j‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp]
  simp [Complex.div_re]

theorem norm_q_lt (N : ℕ) [NeZero N] (τ : ℍ) :
    ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N)‖ < 1 := by
  rw [Complex.norm_exp, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hτ := τ.im_pos
  have : ((2 * (Real.pi : ℂ) * Complex.I) * τ / N).re = -(2 * Real.pi * τ.im) / N := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [this]
  apply div_neg_of_neg_of_pos _ hN
  have := Real.pi_pos
  nlinarith

theorem main : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) (S : ℂ), 1 ≤ e → HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) S → ∃ T : ℂ, HasSum (fun k : ℕ => cSum N e ((-1) ^ (e + 1)) x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T ∧ S = (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) else 0) + (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * T := by
  intro N _ e τ x S he hS
  set q : ℂ := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set K : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ)
  set R : ℤ → ℂ := fun k => ∑' m : ℤ, 1 / (((k : ℂ) * τ + ((x 1).val : ℂ)) / N + m) ^ (e + 1) with hR
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hfR : (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) =
      fun n : ℤ => R (((x 0).val : ℤ) + n * N) := by
    funext n
    simp only [hR]
    congr 1
    funext m
    congr 3
    unfold tors
    push_cast
    field_simp
    ring
  rw [hfR] at hS
  have hsplit := GlobalTheory.T.tsum_residueClass_split_by_sign N (x 0) R hS.summable
  let c₁ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0
  let c₂ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0
  have hq1 : ‖q‖ < 1 := norm_q_lt N τ
  have hc₁ : ∀ d m, ‖c₁ d m‖ ≤ 1 := by
    intro d m
    simp only [c₁]
    split_ifs
    · rw [norm_ch]
    · simp
  have hc₂ : ∀ d m, ‖c₂ d m‖ ≤ 1 := by
    intro d m
    simp only [c₂]
    split_ifs
    · rw [norm_ch]
    · simp
  have h₁ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₁ hq1 hc₁
  have h₂ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₂ hq1 hc₂
  set T₁ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ))
  set T₂ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))
  refine ⟨T₁ + (-1) ^ (e + 1) * T₂, ?_, ?_⟩
  · have h := h₁.add (h₂.mul_left ((-1) ^ (e + 1)))
    convert h using 1
    funext k
    rw [show ∀ A B C D : ℂ, A * D + C * (B * D) = (A + C * B) * D from fun A B C D => by ring]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · rw [← hS.tsum_eq, hsplit]
    have hpos : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = x 0 then R ((d : ℕ) : ℤ) else 0) =
        K * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ)) := by
      intro d
      simp only [c₁]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).1
        simp only [hR]
        push_cast
        rw [this]
      · simp
    have hneg : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = -x 0 then R (-((d : ℕ) : ℤ)) else 0) =
        K * ((-1) ^ (e + 1) * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))) := by
      intro d
      simp only [c₂]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).2
        simp only [hR]
        push_cast
        rw [this]
      · simp
    rw [tsum_congr hpos, tsum_congr hneg, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    have h0 : R 0 = ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) := by
      simp [hR]
    rw [h0]
    ring

end GlobalTheory.WpFam.RowsSummed
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  first | (exact @GlobalTheory.Shin.Mass.mass) | (exact GlobalTheory.Shin.Mass.mass) | (intros; apply GlobalTheory.Shin.Mass.mass <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem liftAll_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) →
    deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftAll, deg]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun x hx => hL x (by simp [hx]))
    have hcons : liftAll q l (p :: L) = (if l ∣ p.1 then liftL q l [p]
        else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++ liftAll q l L := by
      simp [liftAll, List.flatMap_cons]
    have hdegapp : ∀ A B : List (ℕ × ℕ), deg (A ++ B) = deg A + deg B := by intro A B; simp [deg]
    have hdegcons : deg (p :: L) = p.1 + deg L := by simp [deg]
    rw [hcons, hdegapp, hdegcons]
    by_cases h : l ∣ p.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [p] hq hl.pos (by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, h, hp.2⟩)
      rw [if_pos h]
      have hs : deg [p] = p.1 := by simp [deg]
      refine ⟨by rw [h1, hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact ih'.2 x hx
    · rw [if_neg h]
      have hr := (GlobalTheory.T.regular_pair_lift_to_prime_power_field q l p.1 p.2 hq hl hp.1 h hp.2).1
      have hs : deg [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] = p.1 := by simp [deg]
      refine ⟨by rw [hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, hr⟩
      · exact ih'.2 x hx

end GlobalTheory
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionGL_assoc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b c n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (γ : GL (Fin c) F → ℂ), IsCl α → IsCl β → IsCl γ → n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n := by
  first | (exact @GlobalTheory.Shin.HcAssoc.hc_assoc) | (exact GlobalTheory.Shin.HcAssoc.hc_assoc) | (intros; apply GlobalTheory.Shin.HcAssoc.hc_assoc <;> assumption)
end

section

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Intertwine

variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}

end GlobalTheory.DetInv.Intertwine

namespace GlobalTheory.DetInv

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_right_cancel_lemma {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B X : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hX : X * B = 0) : X = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : X * B * B.adjugate = B.det • X := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [hX, Matrix.zero_mul] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hB

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_left_cancel_lemma_2 {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B Y : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hY : A * Y = 0) : Y = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : A.adjugate * (A * Y) = A.det • Y := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hY, Matrix.mul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hA


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.datum_scalar_intertwine : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))) ∧ D.F * D.G = _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧ (∀ l, D.G * D.ρM l = _root_.GlobalTheory.DetInv.rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) * D.Ψ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  set F := D.F with hF
  set G := D.G with hG
  set Ψ := D.Ψ with hΨ
  set Ψ' := D.Ψ' with hΨ'
  set M := D.ρM with hM
  set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ
  have hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 :=
    (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1
  have hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0 := by
    rw [hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]
    exact (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2
  have hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    have h1 := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])
    exact one_ne_zero h1
  have hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1 := D.G_mul_F
  have hFΨ : F = Ψ * F.map φ := D.F_eq
  have hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1 := D.Ψ_mul
  have hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F := fun l =>
    D.F_act l

  have hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1 := by
    have h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)

  have hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l := by
    intro l
    unfold _root_.GlobalTheory.DetInv.rhoTA
    rw [Matrix.map_map]
    congr 1
    funext x
    exact _root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x

  have hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ := by
    intro l
    have := congrArg (fun X => X.map φ) (hFT l)
    simp only [Matrix.map_mul] at this
    rwa [hTφ] at this
  have hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ := by
    intro l
    have h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT,
        Matrix.mul_assoc, ← hFΨ, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)
  refine ⟨?_, hFG, ?_, hΨM, ?_⟩
  · intro c
    have hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) =
        _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) := by
      unfold _root_.GlobalTheory.DetInv.rhoTA
      rw [AlgHom.commutes]
      ext i j
      simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 := hFT (algebraMap ℤ_[p] Λ c)
    rw [hT] at h1
    have h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0 := by
      rw [Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc,
        hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc,
        hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)

end GlobalTheory.DetInv
end
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.FibreRanks

theorem fibre_ranks : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  intro O _ M _ _ N _ _ K _ _ _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ q
    have hinj : Function.Injective (f.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : ρ ∘ₗ f = LinearMap.id := LinearMap.ext hρ
      rw [this]
      simp
    exact LinearMap.finrank_range_of_inj hinj
  · intro g q hg
    have hker := LinearMap.finrank_range_add_finrank_ker (g.baseChange q.asIdeal.ResidueField)
    have h0 : Module.finrank q.asIdeal.ResidueField
        (LinearMap.ker (g.baseChange q.asIdeal.ResidueField)) = 0 := by
      unfold fibreRank fibreDim at hg
      omega
    have hinj : Function.Injective (g.baseChange q.asIdeal.ResidueField) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.finrank_eq_zero.mp h0
    unfold fibreRank
    rw [LinearMap.baseChange_comp, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  · intro h
    exact surjective_of_fibre_rank O M N f h
  · intro _ q
    haveI : Nontrivial O := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact q.isPrime.ne_top (Subsingleton.elim _ _)
    exact Module.finrank_baseChange

end GlobalTheory.FibreRanks
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCofan

theorem comm_el {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) : φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  have := ConcreteCategory.congr_hom (φ.comm i j) x
  simp only [ConcreteCategory.comp_apply] at this
  exact this.symm

theorem cochains_bij (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E)
    (hc : ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k)))))
    (n : ℤ) : Function.Bijective (fun (x : ((HC R F).obj (op E)).X n) (i : ι) => ((HC R F).map (a i).op).f n x) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  have nat : ∀ (k : ℕ) (i : ι) (x : ((HC R F).obj (op E)).X n),
      (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) =
        (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x := by
    intro k i x
    have := ConcreteCategory.congr_hom ((π k).naturality (a i).op) x
    exact this
  let hk := fun k : ℕ => (hc (op (SimplexCategory.mk k))).some
  constructor
  · intro x y hxy
    apply (hπ (op E)).1
    funext k
    apply Cofan.IsColimit.hom_ext (hk k)
    intro i
    have h : ((HC R F).map (a i).op).f n x = ((HC R F).map (a i).op).f n y := congrFun hxy i
    change (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x =
      (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) y
    rw [← nat, ← nat, h]
  · intro y
    obtain ⟨x, hx⟩ := (hπ (op E)).2 (fun k => Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)))
    refine ⟨x, funext fun i => ?_⟩
    apply (hπ (op (Q i))).1
    funext k
    have e : (π k).app (op E) x = Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)) := congrFun hx k
    show (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) = (π k).app (op (Q i)) (y i)
    rw [nat, e]
    exact Cofan.IsColimit.fac (hk k) _ i

end GlobalTheory.EtC.HCofan

theorem GlobalTheory.EtC.HCofan.main : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  intro R _ F E ι Q a hc n
  obtain ⟨-, cl, hsurj, heq, -, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  have hb := fun m => GlobalTheory.EtC.HCofan.cochains_bij R F E ι Q a hc m
  constructor
  · intro x x' hxx
    obtain ⟨z, hz, rfl⟩ := hsurj E n x
    obtain ⟨z', hz', rfl⟩ := hsurj E n x'
    rw [heq]
    have hi : ∀ i, ∃ y, ((HC R F).map (a i).op).f n z =
        ((HC R F).map (a i).op).f n z' + ((HC R F).obj (op (Q i))).d (n - 1) n y := by
      intro i
      have h : pull R (a i) F n (cl E n z hz) = pull R (a i) F n (cl E n z' hz') := congrFun hxx i
      obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n z hz
      obtain ⟨h2, e2⟩ := hpull (Q i) E (a i) n z' hz'
      rw [e1, e2] at h
      exact (heq _ _ _ h1 _ h2).1 h
    choose y hy using hi
    obtain ⟨w, hw⟩ := (hb (n - 1)).2 y
    have hw' : ∀ i, ((HC R F).map (a i).op).f (n - 1) w = y i := fun i => congrFun hw i
    refine ⟨w, (hb n).1 (funext fun i => ?_)⟩
    show ((HC R F).map (a i).op).f n z = ((HC R F).map (a i).op).f n (z' + ((HC R F).obj (op E)).d (n - 1) n w)
    rw [map_add (f := _), GlobalTheory.EtC.HCofan.comm_el, hw' i]
    exact hy i
  · intro x
    choose z hz hzx using fun i => hsurj (Q i) n (x i)
    obtain ⟨w, hw⟩ := (hb n).2 z
    have hw' : ∀ i, ((HC R F).map (a i).op).f n w = z i := fun i => congrFun hw i
    have hdw : ((HC R F).obj (op E)).d n (n + 1) w = 0 := by
      apply (hb (n + 1)).1
      funext i
      show ((HC R F).map (a i).op).f (n + 1) (((HC R F).obj (op E)).d n (n + 1) w) = ((HC R F).map (a i).op).f (n + 1) 0
      rw [GlobalTheory.EtC.HCofan.comm_el, hw' i, hz i, map_zero]
    refine ⟨cl E n w hdw, funext fun i => ?_⟩
    obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n w hdw
    show pull R (a i) F n (cl E n w hdw) = x i
    rw [e1, ← hzx i]
    exact (heq _ _ _ h1 _ (hz i)).2 ⟨0, by rw [hw' i, map_zero, add_zero]⟩
end
