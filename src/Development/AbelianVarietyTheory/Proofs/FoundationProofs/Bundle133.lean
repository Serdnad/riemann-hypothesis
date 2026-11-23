module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizes
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.CjLaws

end GlobalTheory.KZ.CjLaws

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_of_exists {m : Matrix (Fin 2) (Fin 2) ℤ} {δ : SL(2, ℤ)}
    (h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  unfold _root_.GlobalTheory.KZ.H3.cj
  rw [dite_eq_left h]
  exact h.choose_spec

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma eq_of_mul_eq_mul_of_det_ne_zero {m δ₁ δ₂ : Matrix (Fin 2) (Fin 2) ℤ} (hm : m.det ≠ 0)
    (h : δ₁ * m = δ₂ * m) : δ₁ = δ₂ := by
  have h2 : δ₁ * m * adjugate m = δ₂ * m * adjugate m := by rw [h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  exact smul_right_injective _ hm h2

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_and_cj_mem_gamma (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ) (hm : 0 < m.det)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs)) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
      _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M := by
  set d := m.det with hd
  have hd0 : d ≠ 0 := hm.ne'
  have hN : ((M * d.natAbs : ℕ) : ℤ) = (M : ℤ) * d := by
    push_cast
    rw [abs_of_pos hm]
  have hdvd : ∀ i j, ((M : ℤ) * d) ∣
      (δ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [CongruenceSubgroup.Gamma_mem] at hδ
    obtain ⟨h00, h01, h10, h11⟩ := hδ
    intro i j
    rw [← hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp_all
  choose X hX using hdvd
  set D : Matrix (Fin 2) (Fin 2) ℤ := 1 + (M : ℤ) • (m * Matrix.of X * adjugate m) with hD
  have hδX : (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + ((M : ℤ) * d) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]
    ring
  have hDm : D * m = m * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hD, hδX, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, smul_smul]
  have hdetD : D.det = 1 := by
    have h := congrArg Matrix.det hDm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact mul_right_cancel₀ hd0 (by rw [h, one_mul])
  have hex : ∃ δ' : SL(2, ℤ),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    ⟨⟨D, hdetD⟩, hDm.symm⟩
  have h1 := mul_eq_cj_mul_of_exists hex
  refine ⟨h1, ?_⟩
  have h2 : (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) = D :=
    eq_of_mul_eq_mul_of_det_ne_zero hd0 (by rw [← h1, hDm])
  rw [CongruenceSubgroup.Gamma_mem, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> simp

open Matrix in
open scoped MatrixGroups TensorProduct in
theorem _root_.GlobalTheory.KZ.cj_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det →
    ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
        _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M) ∧
    (∀ γ δ : SL(2, ℤ), _root_.GlobalTheory.KZ.H3.cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det →
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m →
        ∀ z ∈ _root_.GlobalTheory.KZ.Hs,
          _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ) z) =
            _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ')
              (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) z)) := by
  refine ⟨mul_eq_cj_mul_and_cj_mem_gamma, fun γ δ => ?_, fun m δ δ' hm h => ?_⟩
  · have hex : ∃ δ' : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ' : Matrix (Fin 2) (Fin 2) ℤ) * γ :=
      ⟨γ * δ * γ⁻¹, by simp [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h1 := mul_eq_cj_mul_of_exists hex
    apply Subtype.ext
    refine eq_of_mul_eq_mul_of_det_ne_zero (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by simp) ?_
    rw [← h1]
    simp [Matrix.mul_assoc, Matrix.adjugate_mul]
  · intro z hz
    obtain ⟨-, hmul, -, -, hcoe, hhom⟩ := _root_.GlobalTheory.KZ.mob_laws
    have hδ : (0 : ℤ) < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    have hδ' : (0 : ℤ) < (δ' : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    rw [← hmul _ _ z hz, ← hmul _ _ z hz, ← hcoe, ← hcoe, ← hhom _ _ hm hδ, ← hhom _ _ hδ' hm, h]
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.binaryMonomialDegree_subst_expansion : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  first | exact @GlobalTheory.KZ.H3.mon_expand | exact GlobalTheory.KZ.H3.mon_expand | (intros; apply GlobalTheory.KZ.H3.mon_expand <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E], (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) → ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_mem_VB | exact GlobalTheory.KZ.H3.exists_pot_of_mem_VB | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_mem_VB <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ → Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_succ_reduce | exact GlobalTheory.KZ.H3.kum_succ_reduce | (intros; apply GlobalTheory.KZ.H3.kum_succ_reduce <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T → (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E))) (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  first | exact @GlobalTheory.KZ.ssPot_transport | exact GlobalTheory.KZ.ssPot_transport | (intros; apply GlobalTheory.KZ.ssPot_transport <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  first | exact @GlobalTheory.KZ.H3.kum_near_zero_eval | exact GlobalTheory.KZ.H3.kum_near_zero_eval | (intros; apply GlobalTheory.KZ.H3.kum_near_zero_eval <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs, ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  first | exact @GlobalTheory.KZ.H3.exists_place_at_point | exact GlobalTheory.KZ.H3.exists_place_at_point | (intros; apply GlobalTheory.KZ.H3.exists_place_at_point <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LamEq

theorem pow_prime_step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (t : ℤ) :
    (p : ℤ) ^ (2 * n + 1) ∣ (1 + (p : ℤ) ^ n * t) ^ p - 1 - (p : ℤ) ^ (n + 1) * t := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  set P : ℤ := ((q + 2 : ℕ) : ℤ) with hP
  have hexp : (1 + P ^ n * t) ^ (q + 2) =
      ∑ i ∈ Finset.range (q + 1), (P ^ n * t) ^ (i + 2) * ((q + 2).choose (i + 2) : ℤ) + (q + 2 : ℕ) * (P ^ n * t) + 1 := by
    rw [add_comm (1 : ℤ), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_one]
    push_cast; ring
  rw [hexp]
  have hPP : (q + 2 : ℕ) * (P ^ n * t) = P ^ (n + 1) * t := by rw [hP]; ring
  rw [hPP, show ∀ a b : ℤ, a + b + 1 - 1 - b = a from fun a b => by ring]
  apply Finset.dvd_sum
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hc : ((q + 2 : ℕ) : ℤ) ∣ ((q + 2).choose 2 : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by norm_num) (by omega)
    rw [← hP] at hc
    obtain ⟨c, hc⟩ := hc
    exact ⟨t ^ 2 * c, by rw [hc]; ring⟩
  · have h3 : 2 * n + 1 ≤ n * (i + 2) := by nlinarith
    refine Dvd.dvd.mul_right ?_ _
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ h3) _

theorem pow_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (j n : ℕ), 1 ≤ n → ∀ t : ℤ,
      (p : ℤ) ^ (2 * n + j) ∣ (1 + (p : ℤ) ^ n * t) ^ (p ^ j) - 1 - (p : ℤ) ^ (n + j) * t := by
  intro j
  induction j with
  | zero => intro n _ t; simp
  | succ j ih =>
    intro n hn t
    obtain ⟨w, hw⟩ := pow_prime_step p hp hp2 n hn t
    have h1 : (1 + (p : ℤ) ^ n * t) ^ p = 1 + (p : ℤ) ^ (n + 1) * (t + (p : ℤ) ^ n * w) := by
      linear_combination hw + (0 : ℤ) * w
    obtain ⟨w', hw'⟩ := ih (n + 1) (by omega) (t + (p : ℤ) ^ n * w)
    rw [pow_succ', pow_mul, h1]
    refine ⟨(p : ℤ) * w' + w, ?_⟩
    linear_combination hw'
end GlobalTheory.LamEq

namespace GlobalTheory.LamEq

theorem aut_pow_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (c : ℕ) (hc : s z = z ^ c) :
    ∀ k : ℕ, (s ^ k) z = z ^ (c ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hc, map_pow, ih, ← pow_mul, pow_succ]

theorem lam_eq : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' := by
  intro Ω _ _ _ ε p hpf hp2 L n m hm1 hmn hnL s _ tt tt' hlam hL
  have hp : p.Prime := hpf.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨e, rfl⟩ : ∃ e, L = n + e := ⟨L - n, by omega⟩
  set z := zt ε p (n + e + n) with hzdef
  have hz : IsPrimitiveRoot z (p ^ (n + e + n)) := IsNTr.isPrimitiveRoot_zt ε p _
  obtain ⟨c, -, hc⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have hs := aut_pow_apply s z c hc.symm
  have h2n : zt ε p (2 * n) = z ^ (p ^ e) := by
    rw [hzdef, ← IsNTr.zt_pow ε p (2 * n) e]; congr 2; omega
  have hn : zt ε p n = z ^ (p ^ (n + e)) := by
    rw [hzdef, ← IsNTr.zt_pow ε p n (n + e)]; congr 2; omega

  have E1 : z ^ (c ^ (p ^ (n - m)) * p ^ e) = z ^ (p ^ (n + e) * tt.val + p ^ e) := by
    have := hlam
    unfold IsLamG at this
    change (s ^ (p ^ (n - m))) (zt ε p (2 * n)) = zt ε p n ^ tt.val * zt ε p (2 * n) at this
    rw [h2n, hn, map_pow, hs, ← pow_mul, ← pow_mul, ← pow_add] at this
    exact this
  have E2 : z ^ (c ^ (p ^ (n + e - m))) = z ^ (p ^ (n + e) * tt'.val + 1) := by
    rw [← hs, hL, hn, ← pow_mul, pow_succ]
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, hz.pow_eq_one⟩
  have hmod : ∀ a b : ℕ, z ^ a = z ^ b ↔ a ≡ b [MOD p ^ (n + e + n)] := by
    intro a b; rw [hz.eq_orderOf]; exact hfin.pow_eq_pow_iff_modEq
  rw [hmod, Nat.modEq_iff_dvd] at E1 E2
  obtain ⟨w1, hw1⟩ := E1
  obtain ⟨w3, hw3⟩ := E2
  push_cast at hw1 hw3
  set P : ℤ := (p : ℤ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.ne_zero
  set a : ℤ := (c : ℤ) ^ (p ^ (n - m)) with ha
  set v : ℤ := ((tt.val : ℕ) : ℤ)
  set v' : ℤ := ((tt'.val : ℕ) : ℤ)
  have h1 : a = 1 + P ^ n * (v - P ^ n * w1) := by
    apply mul_left_cancel₀ (pow_ne_zero e hP0)
    linear_combination (-1 : ℤ) * hw1
  obtain ⟨w2, hw2⟩ := pow_prime_pow p hp hp2 e n (by omega) (v - P ^ n * w1)
  rw [← h1, ← hP] at hw2
  have hce : (c : ℤ) ^ (p ^ (n + e - m)) = a ^ (p ^ e) := by
    rw [ha, ← pow_mul, ← pow_add]; congr 2; omega
  rw [hce] at hw3
  have hd : v' - v = P ^ n * (w3 - w1 + w2) := by
    apply mul_left_cancel₀ (pow_ne_zero (n + e) hP0)
    linear_combination hw3 + hw2
  have hv : ((v : ℤ) : ZMod (p ^ n)) = ((v' : ℤ) : ZMod (p ^ n)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨w3 - w1 + w2, by push_cast; rw [hd]⟩
  simpa [v, v', ZMod.natCast_zmod_val] using hv

end GlobalTheory.LamEq
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_algClosure_automorphism_restricting_local : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.CuspDown.exists_restrict | exact GlobalTheory.CuspDown.exists_restrict | (intros; apply GlobalTheory.CuspDown.exists_restrict <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  first | exact @GlobalTheory.Glue.KTExp.mem_KT_iff | exact GlobalTheory.Glue.KTExp.mem_KT_iff | (intros; apply GlobalTheory.Glue.KTExp.mem_KT_iff <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ GlobalTheory.K5.IsInt (p := p) (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | exact GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | (intros; apply GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem normOp_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r →
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  intro R _ p hp σ hF h₁ h₂ r k hk hu he
  obtain ⟨b, hb⟩ := exists_basis_one_add_X_pow R p hF.complete
  exact normOp_congr_of_basis R p b hb h₁ h₂ r k hk hu he

end GlobalTheory.Col
end
