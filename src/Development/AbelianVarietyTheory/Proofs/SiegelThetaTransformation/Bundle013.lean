module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticOfUnitaryCmField
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMul
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  first | exact @GlobalTheory.SW.haar_ofQ_proportional | exact GlobalTheory.SW.haar_ofQ_proportional | (intros; apply GlobalTheory.SW.haar_ofQ_proportional <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.gaussian_quadForm_rationalCoords_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.gauss_form_dictionary | exact GlobalTheory.SW.gauss_form_dictionary | (intros; apply GlobalTheory.SW.gauss_form_dictionary <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.hermitianTheta_summable_and_determines_testFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * expo Ψ x Z z z')‖) ∧ ∀ ψ, IsSB ψ → (∀ z z', thH Ψ φ Z z z' = thH Ψ ψ Z z z') → φ = ψ := by
  first | exact @GlobalTheory.SW.thH_summable_and_inj | exact GlobalTheory.SW.thH_summable_and_inj | (intros; apply GlobalTheory.SW.thH_summable_and_inj <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.exists_symplectic_of_unitary | exact GlobalTheory.SW.exists_symplectic_of_unitary | (intros; apply GlobalTheory.SW.exists_symplectic_of_unitary <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by
  obtain ⟨R, hR, hs, hp⟩ := h
  obtain ⟨D, hD, ha⟩ := heisS_exists_den a
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))
  refine ⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩
  · intro x hx k i
    have h1 := hs x (left_ne_zero_of_mul hx) k i
    have : (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [this]; exact (hn D).mul h1
  · intro x y hy
    have e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul]
    have hy' : IntM ((D : ℚ) • y) := fun k i => by
      simpa using (hn D).mul (hy k i)
    have hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))) :=
      IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ)
        = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n := by
      have : (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by simpa using hn'
      rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k
          = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
      rw [this]; ring
    simp only []
    rw [e2, e1, hp x _ hy']
    congr 1
    rw [Rat.cast_add, mul_add, Complex.exp_add]
    have : (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem heisS_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  intro κ ι _ _ _ a b φ hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSB_mul_char a b _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1
  · intro τ hτ ζ
    unfold thS
    rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, heisS, add_sub_cancel_right]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v := fun u v => by
      simp [dotProduct, qv]
    have hadd : qv ((y + b) k) = qv (y k) + qv (b k) := by
      ext i; simp [qv]
    have hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
    rw [Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]
    push_cast; ring
  · intro a' b'
    funext x
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]
    congr 2
    rw [← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  · funext x
    simp [heisS, dotProduct]
  · intro ψ hψ
    have h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1
    have h2 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ _ hφ h1).2.2.1
    have h3 := ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2
    unfold ip
    refine Eq.trans ?_ h3
    congr 1
    funext x
    simp only [heisS, Pi.mul_apply, map_mul]
    rw [← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    simp

end GlobalTheory.SW
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.siegelThetaTransformationLaw_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  first | exact @GlobalTheory.SW.transS_comp | exact GlobalTheory.SW.transS_comp | (intros; apply GlobalTheory.SW.transS_comp <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.siegelTheta_transformation_siegelParabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  first | exact @GlobalTheory.SW.Parab.trans_parabolic | exact GlobalTheory.SW.Parab.trans_parabolic | (intros; apply GlobalTheory.SW.Parab.trans_parabolic <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

private theorem quotient_out_sub_mem' {G : Type} [AddCommGroup G] (N : AddSubgroup G) (x : G) :
    (x : G ⧸ N).out - x ∈ N := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm
  rwa [neg_add_eq_sub] at h


open scoped Classical in
open Classical in
theorem ph_finsum_quotient {A : Type} [AddCommGroup A] (P S : AddSubgroup A) (φ f : A → ℂ) (c : ℂ) (a : A)
    (hper : ∀ x, ∀ y ∈ P, φ (x + y) = φ x)
    (hfin : (Function.support fun q : A ⧸ P => φ q.out).Finite)
    (hc : Ph c) (hf : Quad S f) (hφ : ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0) :
    Ph (∑ᶠ q : A ⧸ P, φ q.out) := by
  by_cases hc0 : c = 0
  · have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]
    simp only [h0, finsum_zero]
    exact ph_zero

  have hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s := by
    intro s hs t htS htP
    have h1 := hφ (a + (s + t))
    have h2 := hφ (a + s)
    rw [add_sub_cancel_left, if_pos (S.add_mem hs htS)] at h1
    rw [add_sub_cancel_left, if_pos hs] at h2
    have h3 : φ (a + (s + t)) = φ (a + s) := by rw [← add_assoc]; exact hper _ t htP
    exact mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))

  let ψ : S →+ A ⧸ P := (QuotientAddGroup.mk' P).comp S.subtype
  have hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P := fun u => by
    simp [ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  let ι' : S ⧸ ψ.ker →+ A ⧸ P := QuotientAddGroup.kerLift ψ
  have hι : Function.Injective ι' := QuotientAddGroup.kerLift_injective ψ
  let j : S ⧸ ψ.ker → A ⧸ P := fun m => (a : A ⧸ P) + ι' m
  have hj : Function.Injective j := fun m m' h => hι (add_left_cancel h)
  have hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P) := fun u => by
    simp [j, ι', ψ]
  let fb : S ⧸ ψ.ker → ℂ := fun m => f (m.out : A)
  have hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u := by
    intro u
    have hk := (hker _).mp (quotient_out_sub_mem' ψ.ker u)
    have e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A) := by simp
    show f (((u : S ⧸ ψ.ker).out : S) : A) = f u
    rw [e]
    exact hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk
  have hval : ∀ m, φ (j m).out = c * fb m := by
    intro m
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective m
    rw [hjmk, hfb]
    have hk := quotient_out_sub_mem' P (a + (u : A))
    have e : ((a + (u : A) : A) : A ⧸ P).out =
        (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u)) := by abel
    rw [e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]
  have hfbne : ∀ m, fb m ≠ 0 := fun m h => by
    have h1 := (hf.1 _ (m.out).2).norm_eq_one
    simp [fb] at h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out) := by
    rintro _ ⟨m, rfl⟩
    rw [Function.mem_support, hval]
    exact mul_ne_zero hc0 (hfbne m)
  have : Finite (S ⧸ ψ.ker) := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out)))
      (fun m m' h => hj (congrArg Subtype.val h))
  haveI := Fintype.ofFinite (S ⧸ ψ.ker)

  have hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j := by
    intro q hq
    rw [Function.mem_support, hφ] at hq
    split_ifs at hq with hmem
    · refine ⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩
      rw [hjmk]
      simp
    · exact absurd rfl hq
  have hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j)
        (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hval m
  rw [hsum]
  refine Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h0 : fb 0 = f 0 := by simpa using hfb 0
  have e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker) := fun x y => rfl
  rw [e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]
  simp only [hfb]
  simpa using hf.2 _ u.2 _ v.2 _ w.2

theorem ph_haar_of_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  intro κ ι _ _ _ φ hφ
  obtain ⟨hsb, c, a, S, f, hc, hf, hφx⟩ := hφ
  have hR := hsb.choose_spec
  unfold haar
  rw [dite_eq_left hsb]
  unfold haarAt
  refine Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a
    (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)

  have h := GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1
    (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)
  convert h using 1
  push_cast
  rfl

end GlobalTheory.Phase
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) := by
  first | exact @GlobalTheory.Phase.shape_conj_chr_mul | exact GlobalTheory.Phase.shape_conj_chr_mul | (intros; apply GlobalTheory.Phase.shape_conj_chr_mul <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ParabValues

open GlobalTheory.SW.Parab

theorem ph_rat_mul_exp (r q : ℚ) : Ph ((r : ℂ) * cexp (-(Real.pi * I * (q : ℂ)))) := by
  refine ⟨2 * q.den, by have := q.den_pos; omega, ?_⟩
  have hn : ‖cexp (-(Real.pi * I * (q : ℂ)))‖ = 1 := by
    have : -(Real.pi * I * (q : ℂ)) = ((-(Real.pi * q) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he : cexp (-(Real.pi * I * (q : ℂ))) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    have h : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
    push_cast
    rw [← h]
    ring
  rw [mul_pow, he, mul_one, norm_mul, hn, mul_one, Complex.norm_ratCast]
  have : (|(r : ℝ)|) ^ (2 * q.den) = (r : ℝ) ^ (2 * q.den) := Even.pow_abs ⟨q.den, by ring⟩ _
  rw [← Complex.ofReal_pow, this]
  push_cast
  rfl

theorem trans_explicit (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by
  classical
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hDA : D * Aᵀ = 1 := by
    have h := SymplecticGroup.mem_iff.mp hσ
    rw [← Matrix.fromBlocks_toBlocks σ, hC, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have := congrArg Matrix.toBlocks₂₁ h
    simpa using this
  have hdet : D.det * A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  refine ⟨?_, ?_⟩
  · have h1 := isSB_parChar_mul (B * Aᵀ) _
      ((GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hA0).1
    exact (GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h1 h1).2.1 _
  · intro τ _ ζ
    have hden : spDen σ τ = qm D := by
      unfold spDen
      rw [hC]
      have : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
      rw [this, Matrix.zero_mul, zero_add]
    have hinv : (qm D)⁻¹ = (qm A)ᵀ := by
      apply Matrix.inv_eq_right_inv
      have e : (qm A)ᵀ = qm Aᵀ := rfl
      rw [e, ← qm_mul', hDA]
      ext i j; by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]
    have hdetD : (qm D).det = (D.det : ℂ) := ((Rat.castHom ℂ).map_det D).symm
    have hC' : qm σ.toBlocks₂₁ = 0 := by rw [hC]; ext i j; simp [qm]
    unfold spAct
    rw [hden, hinv, hC', hdetD]
    simp only [Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one]
    let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
      { toFun := fun x => x * A
        invFun := fun x => x * A⁻¹
        left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right A x hAu
        right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right A x hAu }
    unfold thS
    rw [← tsum_mul_left, ← e.tsum_eq (fun x => _ * (φ x * _))]
    refine tsum_congr fun x => ?_
    show ((D.det : ℂ) ^ (Fintype.card κ / 2)) * (parChar (B * Aᵀ) x * φ (x * A)) * _ =
      _ * (φ (x * A) * cexp (Real.pi * I * ∑ k, (qv ((x * A) k) ⬝ᵥ τ *ᵥ qv ((x * A) k) +
        2 * (qv ((x * A) k) ⬝ᵥ ζ k))))
    rw [mul_assoc, mul_comm (parChar _ _), mul_assoc]
    congr 2
    unfold parChar
    rw [← Complex.exp_add]
    congr 1
    rw [← mul_neg, ← mul_add, Rat.cast_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qv_bilin, qv_row_mul, qm_mul']
    have e1 : qm Aᵀ = (qm A)ᵀ := rfl
    beta_reduce
    rw [e1, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec (qv (x k)) (qm A),
      Matrix.dotProduct_mulVec (qv (x k)) (qm A)]
    ring

theorem trans_unique (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e : ζ = fun k => (ζ k ᵥ* spDen σ (I • (1 : Matrix ι ι ℂ))) ᵥ*
      (spDen σ (I • (1 : Matrix ι ι ℂ)))⁻¹ := by
    funext k
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.vecMul_one]
  rw [e, h _ I_mem_siegel, h' _ I_mem_siegel]

theorem values_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  intro κ ι _ _ _ _ σ hσ hC φ ψ hφ hψ h y
  obtain ⟨h1, h2⟩ := trans_explicit κ ι σ hσ hC φ hφ
  have e := trans_unique κ ι σ hσ φ _ _ hψ h1 h h2
  refine ⟨((σ.toBlocks₂₂.det ^ (Fintype.card κ / 2) : ℚ) : ℂ) *
    parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) y, y * σ.toBlocks₁₁, ph_rat_mul_exp _ _, ?_⟩
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.Phase.ParabValues
end
