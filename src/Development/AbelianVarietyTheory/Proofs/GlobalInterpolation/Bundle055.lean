module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.primeMeanValue_characters_twist_integral_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T → (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T, ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤ C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  first | exact @GlobalTheory.PrimeMeanValue.prime_mean_value | exact GlobalTheory.PrimeMeanValue.prime_mean_value | (intros; apply GlobalTheory.PrimeMeanValue.prime_mean_value <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomFin

theorem pairing_scaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  intro D cc δ δ₀ B N N' g S e p _ lam Ω r b y a hq _ _ hb
  have hphi : ∀ z : D.host.E, D.host.φ₀ z ∈ Qbar := fun z => by
    have hx : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
    exact (mem_algebraicClosure_iff).2 (hx.algHom D.host.φ₀.toRatAlgHom)

  have hlin : ∀ (c : ℂ) (z w : Fin g → ℂ), JMB.beta S.d S.Hm (c • z) w = c * JMB.beta S.d S.Hm z w := by
    intro c z w
    simp only [JMB.beta, JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set n := Ideal.absNorm cc
  have key : ∀ i, JMB.lamA lam (JMB.beta S.d S.Hm ((δ₀ / δ) • e (δ • embV D B.tor y)) (e (δ • embV D B.tor (b i))))
      = (lamC lam (δ / δ₀))⁻¹ * ((n : ℂ_[p]))⁻¹ * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
    intro i
    rw [hlin, hb]
    set z := D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)
    have hz := hphi ((hYY D y (b i) : D.host.K) : D.host.E)
    have heq : δ₀ / δ * (z / (n : ℂ)) = (((⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ : Qbar) : ℂ) := by
      have hc : (((n : Qbar)) : ℂ) = (n : ℂ) := by norm_cast
      simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, hc]
      rw [inv_div]; ring
    have hmem : δ₀ / δ * (z / (n : ℂ)) ∈ Qbar := by rw [heq]; exact SetLike.coe_mem _
    unfold JMB.lamA lamC
    rw [dite_eq_left hmem, dite_eq_left hq, dite_eq_left hz]
    have : (⟨δ₀ / δ * (z / (n : ℂ)), hmem⟩ : Qbar) = (⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ := Subtype.ext heq
    rw [this, map_mul, map_mul, map_inv₀, map_inv₀, map_natCast]
  unfold JMB.pairD pairN
  simp only [key]
  have hzc : ∀ i, JMB.zc (a i) = zc (a i) := fun i => rfl
  simp only [hzc, mul_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.MomFin
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgDirMom

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz0, hz⟩ := hc.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  rw [zsmul_eq_mul] at hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz; simpa using hz
  · rw [h] at hz
    have := hz.neg
    simpa using this

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • v ∈ L' := by
  have hv : v ∈ Submodule.span E (L' : Set (Fin n → E)) := hL' ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]
      push_cast
      rw [mul_comm (b : E) (a : E)]
    rw [e]
    exact L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
    have h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L' := L'.smul_mem _ hax
    rw [← algebraMap_smul E] at h2
    convert h2 using 1
    change _ = ((m : E) * c) • ((a : E) • x)
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf

theorem exists_nat_smul_maps {E : Type} [Field E] [NumberField E] {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin N' → E)) = ⊤) (y : Matrix (Fin N') (Fin N) E) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ L, ((k : E) • y).mulVec x ∈ L' := by
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L' := fun g _ => exists_nat_smul_mem L' hL' _
  choose! kf hkpos hkmem using hk
  refine ⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rw [Matrix.smul_mulVec]
    rw [← Finset.mul_prod_erase s kf hg]
    push_cast
    rw [mul_comm, ← smul_smul]
    rw [← Nat.cast_prod, Nat.cast_smul_eq_nsmul]
    exact L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L'.add_mem hx hy
  | smul r x _ hx =>
    rw [Matrix.mulVec_smul]
    exact L'.smul_mem r hx

end GlobalTheory.AlgDirMom

namespace GlobalTheory.AlgDirMom

theorem embV_natCast_smul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {N N' : ℕ} (n : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D B.tor ((n : D.host.E) • y) = (n : ℂ) • embV D B.tor y := by
  funext τ i j
  simp [embV, Base.tor, tor0]

theorem algDir_smul_embV : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  intro D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y
  have hδ : δ ≠ 0 := fun h => hq0 (by simp [h])
  have hδ₀ : δ₀ ≠ 0 := fun h => hq0 (by simp [h])
  obtain ⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩ := hadm
  obtain ⟨n, hn, hnmap⟩ := exists_nat_smul_maps L L' hLfg hL'sp y
  have hNc : Ideal.absNorm cc ≠ 0 := fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : (n : D.host.E) • y ∈ YYl D L L' :=
    Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx),
      (one_smul _ _).symm⟩
  have hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂ := by
    change _ ∈ lamOf D cc δ
    exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩
  have hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L' :=
    AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩
  have hu := (he _).2 hx
  have hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar := by
    have h1 : δ₀ / δ = (δ / δ₀)⁻¹ := (inv_div δ δ₀).symm
    rw [h1]
    exact div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))
  refine ⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)),
    fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩
  rw [Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hN0 : (Ideal.absNorm cc : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNc
  field_simp

end GlobalTheory.AlgDirMom
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDensityMult

theorem re_lt_one_of_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra hc
  push Not at hc
  by_cases h1 : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    rw [LFunction_modOne_eq] at h
    exact riemannZeta_ne_zero_of_one_le_re hc h
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hc h

theorem log_le {Q N t : ℝ} (hQ : 3 ≤ Q) (hN0 : 0 < N) (hN : N ≤ Q) (ht : |t| ≤ Q + 1) :
    Real.log (N * (|t| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
  have h0 := abs_nonneg t
  have h1 : N * (|t| + 2) ≤ Q ^ 3 := by
    have : N * (|t| + 2) ≤ Q * (Q + 3) := mul_le_mul hN (by linarith) (by linarith) (by linarith)
    have h4 : Q + 3 ≤ Q ^ 2 := by nlinarith
    have h5 : Q * (Q + 3) ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
    have h6 : Q * Q ^ 2 = Q ^ 3 := by ring
    linarith
  have h2 : Real.log (N * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log (by positivity) h1
  have h3 := Real.log_le_rpow_div (x := Q) (ε := (1 : ℝ) / 8) (by linarith) (by norm_num)
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem zero_density_mult : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le
  refine ⟨C₂ * (C₁ * 24), by positivity, ?_⟩
  intro Q hQ T hT
  have hQ0 : 0 < Q := by linarith
  have hcard := H₂ Q hQ T hT
  set g : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hg
  rw [← Finset.coe_image, Set.ncard_coe_finset] at hcard
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  have hcell : ∀ c ∈ T.image g, ∑ p ∈ T with g p = c,
      ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C₁ * (24 * Q ^ ((1 : ℝ) / 8)) := by
    intro c hc
    obtain ⟨⟨n, χ, z⟩, hz, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a1, a2, -, -, a5⟩ := hT _ hz
    simp only at a1 a2 a5
    obtain ⟨hfin, hsum⟩ := H₁ (n + 1) χ a2 (⌊z.im⌋ : ℤ)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hl : Real.log (((n + 1 : ℕ) : ℝ) * (|((⌊z.im⌋ : ℤ) : ℝ)| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
      refine log_le hQ (by positivity) a1 ?_
      have b1 := Int.floor_le z.im
      have b2 := Int.lt_floor_add_one z.im
      rw [abs_le] at a5 ⊢
      constructor <;> linarith [a5.1, a5.2]
    refine le_trans ?_ (hsum.trans (mul_le_mul_of_nonneg_left hl hC₁.le))
    have hinj : Function.Injective
        (fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) := by
      intro x y h
      simpa using h
    have e := Finset.sum_image (s := hfin.toFinset)
      (g := fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))
      (f := fun p => ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ)) hinj.injOn
    refine le_trans ?_ e.le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
    rintro ⟨m, ψ, ρ⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hgp⟩ := hp
    obtain ⟨-, b2, b3, b4, -⟩ := hT _ hp
    simp only [hg] at hgp b2 b3 b4
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hgp
    have h3 := eq_of_heq h2
    obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
    refine Finset.mem_image.2 ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨by linarith, re_lt_one_of_zero _ b2 b3, ?_, b3⟩
    have c1 := Int.floor_le ρ.im
    have c2 := Int.lt_floor_add_one ρ.im
    rw [← h4, abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_card_nsmul _ _ _ hcell).trans ?_
  rw [nsmul_eq_mul]
  have hp : Q ^ ((1 : ℝ) / 4) = Q ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hQ0]; norm_num
  rw [hp]
  calc _ ≤ (C₂ * Q ^ ((1 : ℝ) / 8)) * (C₁ * (24 * Q ^ ((1 : ℝ) / 8))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GlobalTheory.ZeroDensityMult
end
