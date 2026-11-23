module

public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqLawOfZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TwoDvdMultiplierOfThetaZActEqUnitMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix ComplexConjugate

namespace GlobalTheory.CuspExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_congr_diagonal (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by
  classical
  set s : Fin r → E := fun a => if (a : ℕ) < X.p0 then (1 : E) else -1 with hs
  have hs0 : ∀ a, s a ≠ 0 := fun a => by
    simp only [hs]; split_ifs <;> simp
  have hscc : ∀ a, cc (s a) = s a := fun a => by
    simp only [hs]; split_ifs <;> simp [cc]
  have hsτ : ∀ (τ : E →+* ℂ) a, τ (s a) = ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ a => by
    simp only [hs, sgn]; split_ifs <;> simp
  have hS0 : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hs0 a
  have hSh : ∀ a b, cc (Matrix.diagonal s a b) = Matrix.diagonal s b a := by
    intro a b
    by_cases h : a = b
    · subst h; simpa using hscc a
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  set d : E := X.Gm.det / (Matrix.diagonal s).det with hd
  have hd0 : d ≠ 0 := div_ne_zero X.Gm_det hS0
  have hdcc : cc d = d := by
    have h1 := GlobalTheory.Published.cc_det_of_herm X.Gm_herm
    have h2 := GlobalTheory.Published.cc_det_of_herm hSh
    unfold cc at h1 h2 ⊢
    rw [hd, map_div₀, h1, h2]
  have hdet : (Matrix.diagonal fun a : Fin r => s a * (if a = k then d else 1)).det = X.Gm.det := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
      ← Matrix.det_diagonal, hd]
    field_simp
  refine ⟨d, GlobalTheory.Published.Landherr.of_signature H X.Gm_herm ?_ X.Gm_det (hdet ▸ X.Gm_det)
    (X.Ψ : Set (E →+* ℂ)) (fun τ => ?_) (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, ?_⟩) ⟨1, ?_⟩⟩
  · intro a b
    by_cases h : a = b
    · subst h
      have h1 := hscc a
      unfold cc at h1 hdcc ⊢
      rw [Matrix.diagonal_apply_eq, map_mul, h1]
      congr 1
      split_ifs
      · exact hdcc
      · exact map_one _
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  · by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact Or.inr h
    · exact Or.inl ((X.cmType τ).mpr h)
  · obtain ⟨Q, hQ, hg⟩ := X.signature ⟨τ, hτ⟩
    have hpos : 0 < (τ d).re := by
      refine GlobalTheory.Published.Landherr.re_det_div_pos X.Gm_det τ ⟨Q, hQ, ?_⟩
      rw [← GlobalTheory.Published.gram_eq, hg, Matrix.diagonal_map (map_zero τ)]
      simp only [hsτ]
    have hre : ((τ d).re : ℂ) = τ d := by
      rw [← Complex.conj_eq_iff_re, ← GlobalTheory.Published.embedding_cc, hdcc]
    set t : ℝ := (Real.sqrt (τ d).re)⁻¹ with ht
    have ht0 : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
    have htt : (t : ℂ) * τ d * t = 1 := by
      rw [← hre, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ht, ← mul_inv,
        Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    refine ⟨Matrix.diagonal fun a => if a = k then (t : ℂ) else 1, ?_, ?_⟩
    · rw [Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
      exact_mod_cast ht0
    · rw [GlobalTheory.Published.gram_eq, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero τ),
        Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [map_mul, hsτ]
      split_ifs
      · rw [Complex.conj_ofReal]
        linear_combination ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * htt
      · simp
  · rw [hdet, div_self X.Gm_det]; simp [cc]


omit [NumberField E] [IsCMField E] in
theorem linearIndependent_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hij : ∀ a b, i a ≠ j b) :
    LinearIndependent E fun a => (Pi.single (i a) 1 + Pi.single (j a) 1 : Fin r → E) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have := congrFun hg (i a)
  simpa [Finset.sum_apply, Pi.single_apply, hij, hi.eq_iff] using this

theorem herm_diagonal_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hj : Function.Injective j) (hij : ∀ a b, i a ≠ j b) (g : Fin r → E)
    (hg : ∀ a, g (i a) + g (j a) = 0) (a b : Fin ρ) :
    herm (Matrix.diagonal g) (Pi.single (i a) 1 + Pi.single (j a) 1)
      (Pi.single (i b) 1 + Pi.single (j b) 1) = 0 := by
  classical
  have hji : ∀ a b, j a ≠ i b := fun a b => (hij b a).symm
  rw [GlobalTheory.Published.LandherrSt.herm_eq, add_dotProduct, single_dotProduct, single_dotProduct,
    Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases h : a = b
  · subst h
    simpa [cc, Pi.single_apply, hij, hji] using hg a
  · simp [cc, hij, hji, hi.eq_iff, hj.eq_iff, h]

theorem nonempty_cuspFD : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), ρ ≤ X.p0 → ρ + X.p0 ≤ r → 2 * ρ < r → Nonempty (FJ.CuspFD X ρ) := by
  intro HN E _ _ _ r ρ X h1 h2 h3
  classical
  have H := GlobalTheory.Published.landherr_of_landherrSt (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt HN)
  obtain ⟨k, hk⟩ : ∃ k : Fin r, (k : ℕ) + ρ < X.p0 ∨ X.p0 + ρ ≤ k := by
    by_cases h : ρ < X.p0
    · exact ⟨⟨0, by omega⟩, Or.inl (by simpa using h)⟩
    · exact ⟨⟨r - 1, by omega⟩, Or.inr (by simp only; omega)⟩
  obtain ⟨d, P, hP, hG⟩ := exists_congr_diagonal H X k
  let i : Fin ρ → Fin r := fun a => ⟨X.p0 - 1 - a, by have := a.2; omega⟩
  let j : Fin ρ → Fin r := fun a => ⟨X.p0 + a, by have := a.2; omega⟩
  have hi : Function.Injective i := fun a b h => by
    have := a.2; have := b.2
    simp only [i, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hj : Function.Injective j := fun a b h => by
    simp only [j, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hij : ∀ a b, i a ≠ j b := fun a b h => by
    have := a.2
    simp only [i, j, Fin.mk.injEq] at h
    omega
  refine ⟨⟨fun a => P *ᵥ (Pi.single (i a) 1 + Pi.single (j a) 1), ?_, fun a b => ?_⟩⟩
  · refine (linearIndependent_single_add (E := E) hi hij).map' (Matrix.toLin' P) ?_
    rw [LinearMap.ker_eq_bot]
    exact Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP))
  · rw [GlobalTheory.Published.LandherrSt.herm_mulVec, ← hG]
    refine herm_diagonal_single_add hi hj hij _ (fun c => ?_) a b
    have := c.2
    have e1 : i c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [i] at this
      omega
    have e2 : j c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [j] at this
      omega
    have e3 : (i c : ℕ) < X.p0 := by simp only [i]; omega
    have e4 : ¬ (j c : ℕ) < X.p0 := by simp only [j]; omega
    simp only [if_pos e3, if_neg e4, if_neg e1, if_neg e2]
    ring

end GlobalTheory.CuspExist
end

section

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaRatio

theorem thetaChar_ofRealVec {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin g → ℂ) : thetaChar τ (ofRealVec a) (ofRealVec b) z = theta a b z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + ofRealVec a) = shiftVec a l := rfl
  rw [e, thetaTerm, eC]
  congr 1
  ring

theorem exists_eq_halfVec {g : ℕ} {c : Fin g → ℂ} (h : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ n : Fin g → ℤ, c = ofRealVec (halfVec n) := by
  have : ∀ k, ∃ m : ℤ, c k = (((m : ℝ) / 2 : ℝ) : ℂ) := fun k => by
    rcases h k with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem ratio_sq_eq_det_jAut : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = 1 * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → ∀ (c₁ c₂ : Fin g → ℂ), (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → ∀ τ ∈ SiegelH (Fin g), ∀ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → ρ 0 = 1 → κ ≠ 0 → (∀ z, thetaChar (spAct γ τ) c₁ c₂ (zAct γ τ z) * ρ z = κ * thetaChar τ c₁ c₂ z) → κ ^ 2 = (jAut γ τ).det := by
  intro g γ hγ h8 h0 c₁ c₂ h₁ h₂ τ hτ ρ κ hρ hρ0 hρ1 hκ h
  obtain ⟨n, rfl⟩ := exists_eq_halfVec h₁
  obtain ⟨n', rfl⟩ := exists_eq_halfVec h₂
  simp only [thetaChar_ofRealVec] at h
  have hfix := halfChar_fixed_of_theta_transform_unit g γ hγ h8 1 n n' one_ne_zero h0 τ hτ
    (fun z => κ / ρ z) (by simpa only [div_eq_mul_inv] using (hρ.fun_inv hρ0).const_mul κ) (fun z => div_ne_zero hκ (hρ0 z))
    (fun z => by rw [div_mul_eq_mul_div, ← h z, mul_div_cancel_right₀ _ (hρ0 z)])
  have hlaw := ThetaCharMult.theta_sq_law_of_zero g γ hγ h8 1 n n' h0 hfix τ hτ
  have hE : Differentiable ℂ fun z => eC (expArg γ τ z) := by
    simp only [eC, expArg, dotProduct, mulVec]
    fun_prop
  have hθ : (fun z => theta (halfVec n) (halfVec n') z τ ^ 2) ≠ 0 := fun hz =>
    theta_ne_zero hτ (halfVec n) (halfVec n')
      (funext fun z => pow_eq_zero_iff (two_ne_zero) |>.1 (congrFun hz z))
  have key := entire_eq_zero_of_mul_continuous_eq_zero
    (f := fun z => (jAut γ τ).det * eC (expArg γ τ z) * ρ z ^ 2 - κ ^ 2)
    (((hE.const_mul _).mul (hρ.pow 2)).sub_const _)
    ((differentiable_theta hτ (halfVec n) (halfVec n')).continuous.pow 2) hθ
    (fun z => by
      have h1 := hlaw z
      have h2 : (theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) * ρ z) ^ 2 =
          (κ * theta (halfVec n) (halfVec n') z τ) ^ 2 := by rw [h z]
      show _ * theta (halfVec n) (halfVec n') z τ ^ 2 = 0
      linear_combination h2 - ρ z ^ 2 * h1) 0
  have e0 : eC (expArg γ τ 0) = 1 := by simp [expArg, eC]
  simp only [e0, hρ1] at key
  linear_combination -key

end GlobalTheory.ThetaRatio
end
end

section

noncomputable section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelExist

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem_adjoin (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    H.bar a ∈ Algebra.adjoin ℤ {H.w0} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (Algebra.self_mem_adjoin_singleton ℤ _)
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem map_bar_span_bar (H : Host E) (al : 𝓞 E) :
    (Ideal.span {H.bar al}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {al} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact bar_bar H al

def levelOfSplit (H : Host E) (al : 𝓞 E) (M A : ℕ) (hal : al ∈ Algebra.adjoin ℤ {H.w0})
    (hM : al * H.bar al = (M : 𝓞 E)) (hc : IsCoprime al (H.bar al)) (h3 : 3 ≤ M) (ho : Odd M)
    (hA : 0 < A) : Level H where
  M := M
  three_le := h3
  odd := ho
  Mb := Ideal.span {H.bar al}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, bar_mem_adjoin H hal⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [map_bar_span_bar, Ideal.span_singleton_mul_span_singleton, mul_comm, hM]
  coprime := by
    rw [map_bar_span_bar, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hc.symm
  A := A
  A_pos := hA

theorem M'_pos {H : Host E} (l : Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem zeta_eq_pow_of_dvd {a n : ℕ} (hn : 0 < n) (h : a ∣ n) : ∃ k : ℕ, zeta a = zeta n ^ k := by
  obtain ⟨k, rfl⟩ := h
  have ha : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  have hk : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  refine ⟨k, ?_⟩
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem isIntegral_zeta {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top

theorem hostRootValue_eq_or_neg_embedding (H : Host E) (τ : E →+* ℂ) : H.rt0 = τ (H.rt : E) ∨ H.rt0 = -τ (H.rt : E) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [H.sqrt_neg_disc_sq, ← map_pow, coe_rt_sq]
  simp

def minCoeff {H : Host E} (l : Level H) : Coeff l :=
  have hconj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} := fun τ a =>
    (le_sup_left : IntermediateField.normalClosure ℚ E ℂ ≤ _)
      (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)
  have hz : zeta l.M' ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} :=
    (le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  { F := IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
    fin := by
      have := IntermediateField.adjoin.finiteDimensional (isIntegral_zeta (M'_pos l))
      infer_instance
    conj := hconj
    zeta_mem := hz
    le := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        rcases hostRootValue_eq_or_neg_embedding H τ with h | h <;> rw [h]
        · exact hconj τ _
        · exact neg_mem (hconj τ _)
      · obtain ⟨k, hk⟩ := zeta_eq_pow_of_dvd (M'_pos l) (Nat.dvd_lcm_right l.M l.A)
        rw [hk]
        exact pow_mem hz k }

instance instNonemptyCoeff {H : Host E} (l : Level H) : Nonempty (Coeff l) := ⟨minCoeff l⟩

end GlobalTheory.LevelExist

namespace GlobalTheory

theorem level_of_split_and_level_coeff_exist :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (al : 𝓞 E) (M A : ℕ),
      al ∈ Algebra.adjoin ℤ {H.w0} → al * H.bar al = (M : 𝓞 E) → IsCoprime al (H.bar al) → 3 ≤ M →
      Odd M → 0 < A → ∃ l : Level H, l.M = M ∧ l.A = A ∧ l.Mb = Ideal.span {H.bar al}) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Nonempty (Level H)) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H),
      Nonempty (Coeff l) :=
  ⟨fun _ _ _ _ H al M A h1 h2 h3 h4 h5 h6 =>
      ⟨LevelExist.levelOfSplit H al M A h1 h2 h3 h4 h5 h6, rfl, rfl, rfl⟩,
    fun _ _ _ _ H => HostModel.instNonemptyLevel H,
    fun _ _ _ _ _ l => ⟨LevelExist.minCoeff l⟩⟩

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ObjRebase

def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)

theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _

theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm

def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}

end GlobalTheory.ObjRebase
end
end
