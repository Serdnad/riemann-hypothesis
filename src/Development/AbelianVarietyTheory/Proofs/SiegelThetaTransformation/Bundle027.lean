module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Mathlib.NumberTheory.NumberField.House
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle004
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Dual
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PosSum

theorem norm_entry_le_trace {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (i j : Fin N) : ‖A i j‖ ≤ A.trace.re := by
  have hd : ∀ k, 0 ≤ (A k k).re := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).1
  have hi : ∀ k, (A k k).im = 0 := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).2.symm
  have ht : ∀ k, (A k k).re ≤ A.trace.re := fun k => by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.single_le_sum (f := fun k => (A k k).re) (fun k _ => hd k) (Finset.mem_univ k)
  have h2 := (Complex.nonneg_iff.1 (hA.submatrix ![i, j]).det_nonneg).1
  have hji : A j i = conj (A i j) := by
    have := hA.1.apply j i
    simpa using this.symm
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hji,
    Complex.mul_conj, Complex.sub_re, Complex.mul_re, hi, Complex.ofReal_re, mul_zero, sub_zero,
    Matrix.cons_val_fin_one] at h2
  have h0 : 0 ≤ A.trace.re := (hd i).trans (ht i)
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [Complex.sq_norm, sq]
  have := mul_le_mul (ht i) (ht j) (hd j) h0
  linarith

theorem exists_repr_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  apply _root_.GlobalTheory.IntCount.exists_abs_repr_le_mul_house <;> assumption

theorem house_le_of_isType {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ τ ∈ Ψ, ‖τ x‖ ≤ B) : house x ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun τ => ?_
  change ‖τ x‖ ≤ B
  by_cases hτ : τ ∈ Ψ
  · exact h τ hτ
  · have := h _ (not_not.1 fun h' => hτ ((hΨ τ).2 h'))
    simpa using this

end GlobalTheory.SW.PosSum


open GlobalTheory.SW.PosSum in
theorem GlobalTheory.SW.summable_exp_neg_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  intro E _ _ _ Ψ hΨ N c δ hc hδ
  obtain ⟨C, hC, hb⟩ := exists_repr_le E
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let K : ℝ := Fintype.card ι * (C * c) + 1
  have hK : 0 < K := by positivity
  let m : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
      ∀ τ : Ψ, (T.map τ.1).PosSemidef} → ι → ℤ := fun T q =>
    (RingOfIntegers.basis E).repr ⟨_, T.2.2.1 q.1 q.2.1⟩ q.2.2
  have hm : Function.Injective m := by
    intro T T' h
    ext a b
    have : (⟨_, T.2.2.1 a b⟩ : 𝓞 E) = ⟨_, T'.2.2.1 a b⟩ :=
      (RingOfIntegers.basis E).ext_elem fun j => congrFun h (a, b, j)
    have h2 : (c : E) * T.1 a b = c * T'.1 a b := congrArg Subtype.val this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hc.ne') h2
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun T => ?_)
    ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (div_pos hδ hK)).comp_injective hm)
  set S := ∑ τ : Ψ, (T.1.map τ.1).trace.re with hS
  have h0 : ∀ τ : Ψ, 0 ≤ (T.1.map τ.1).trace.re := fun τ =>
    (Complex.nonneg_iff.1 (T.2.2.2 τ).trace_nonneg).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => h0 τ
  have hq : ∀ q, |(m T q : ℝ)| ≤ C * c * S := fun q => by
    refine (hb _ _).trans ?_
    change C * house ((c : E) * T.1 q.1 q.2.1) ≤ _
    rw [house_nat_mul, mul_assoc]
    gcongr
    refine house_le_of_isType hΨ hS0 fun τ hτ => ?_
    exact (norm_entry_le_trace (T.2.2.2 ⟨τ, hτ⟩) q.1 q.2.1).trans
      (Finset.single_le_sum (fun τ _ => h0 τ) (Finset.mem_univ (⟨τ, hτ⟩ : Ψ)))
  have hs : ∑ q, |(m T q : ℝ)| ≤ K * S := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun q _ => hq q).trans ?_
    simp only [Finset.card_univ, nsmul_eq_mul, K]
    nlinarith
  simp only [Function.comp_apply]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  calc δ / K * ∑ q, |(m T q : ℝ)| ≤ δ / K * (K * S) := by gcongr
    _ = δ * S := by field_simp
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem sum_mul_conj_orthonormalBasis {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Fintype ι] (b b' : OrthonormalBasis ι ℂ V) (l l' : V →ₗ[ℂ] ℂ) :
    ∑ j, l (b j) * conj (l' (b j)) = ∑ j, l (b' j) * conj (l' (b' j)) := by
  have := FiniteDimensional.complete ℂ V
  have h (l : V →ₗ[ℂ] ℂ) : ∃ a : V, ∀ v, l v = inner ℂ a v :=
    ⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap l), fun v => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨a, ha⟩ := h l
  obtain ⟨a', ha'⟩ := h l'
  simp only [ha, ha', inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner]

theorem exists_family_invariant_of_fockInner {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (hW : W ≠ ⊥) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial σ ℂ), (∀ j, P j ∈ W) ∧ (∃ j, P j ≠ 0) ∧
      ∀ f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ Q ∈ W, f Q ∈ W) →
        (∀ Q Q', MvPoly.fockInner (f Q) (f Q') = MvPoly.fockInner Q Q') →
        ∀ l l' : MvPolynomial σ ℂ →ₗ[ℂ] ℂ,
          ∑ j, l (f (P j)) * conj (l' (f (P j))) = ∑ j, l (P j) * conj (l' (P j)) := by
  let cr : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => MvPoly.fockInner (y : MvPolynomial σ ℂ) x
      conj_inner_symm := fun x y => MvPoly.fockInner_conj_symm _ _
      re_inner_nonneg := fun x => by
        rw [MvPoly.fockInner_self, RCLike.ofReal_re]; exact MvPoly.fockNormSq_nonneg _
      add_left := fun x y z => MvPoly.fockInner_add_right _ _ _
      smul_left := fun x y r => MvPoly.fockInner_smul_right _ _ _
      definite := fun x hx => by
        rw [MvPoly.fockInner_self] at hx
        exact Subtype.ext (MvPoly.fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp hx)) }
  letI : NormedAddCommGroup W := cr.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore cr.toCore
  let b := stdOrthonormalBasis ℂ W
  have hpos : 0 < Module.finrank ℂ W := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hW
  refine ⟨_, fun j => b j, fun j => (b j).2, ⟨⟨0, hpos⟩, fun e => ?_⟩, fun f hf hi l l' => ?_⟩
  · exact b.orthonormal.ne_zero _ (Subtype.ext e)
  · let U : W →ₗᵢ[ℂ] W := (f.restrict hf).isometryOfInner fun x y => hi _ _
    exact sum_mul_conj_orthonormalBasis (b.map (U.toLinearIsometryEquiv rfl)) b
      (l ∘ₗ W.subtype) (l' ∘ₗ W.subtype)

theorem exists_invFam_rowHighest : ∀ (T : Type) [Fintype T] [DecidableEq T] (p q n : ℕ)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), p + q ≤ n →
    ∃ (m : ℕ) (P : Fin m → Harm.Poly ℂ T p q (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') ∧
      (∃ j, P j ≠ 0) ∧ InvFam P := by
  intro T _ _ p q n c c' h
  obtain ⟨m, P, h₁, h₂, h₃⟩ := exists_family_invariant_of_fockInner
    (Harm.rowHighest (κ := Fin n) ℂ c c') (Harm.rowHighest_ne_bot h c c')
  refine ⟨m, P, h₁, h₂, fun u hu z w => ?_⟩
  have hs : star u * u = 1 := funext fun t => Units.ext (Matrix.mem_unitaryGroup_iff'.mp (hu t))
  refine h₃ (Harm.colActHom u).toLinearMap (fun Q hQ => Harm.colAct_mem_rowHighest u hQ)
    (fun Q Q' => ?_) (MvPolynomial.aeval z).toLinearMap (MvPolynomial.aeval w).toLinearMap
  change MvPoly.fockInner (Harm.colAct ℂ T p q (Fin n) u Q) (Harm.colAct ℂ T p q (Fin n) u Q') = _
  rw [Harm.fockInner_colAct, ← AlgEquiv.mul_apply, ← map_mul, hs, map_one, AlgEquiv.one_apply]

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem one_mem_rowHighest_and_thP_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), (1 : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) ∈ Harm.rowHighest ℂ (fun _ _ => 0) (fun _ _ => 0) ∧ ∀ (c : ℂ) (φ : TF n g) (x : Frame X.Ψ r), thP X hr bas idx (c • φ) 1 x = c * (hMat X bas idx x).det ^ (n / 2) * thS φ (tauMat X bas idx x) 0 := by
  intro E _ _ _ r X g q0 hr bas idx n
  refine ⟨?_, fun c φ x => ?_⟩
  · simp only [Harm.rowHighest, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine ⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_, ?_⟩
    · show Harm.IsHarmonic _
      unfold Harm.IsHarmonic
      intro t a b
      simp [Harm.laplacian]
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · intro t a b _ s
      simp
    · intro t a b _ s
      simp
  · simp only [thP, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_one, Finset.sum_singleton,
      MvPolynomial.coeff_zero_one, one_mul]
    have h0 : ∀ (k : ℕ) (hk : k = 0) (v : Fin k → (Fin n → Fin g → ℂ)),
        iteratedFDeriv ℂ k (thA X bas idx (c • φ) x) 0 v = thA X bas idx (c • φ) x 0 := by
      rintro _ rfl v
      exact iteratedFDeriv_zero_apply v
    rw [h0 _ (by simp)]
    unfold thA thS
    simp only [Pi.zero_apply, Matrix.mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left, add_zero]
    ring

end GlobalTheory.SW
end

section

open Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.SW.KernSym

variable {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable abbrev lst (m : σ →₀ ℕ) : List σ := (Finsupp.toMultiset m).toList

theorem polyDeriv_eq_sum_list (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support, P.coeff m * lineDerivList ℂ ((lst m).map u) F x := by
  rw [dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]

theorem polyDeriv_polyDeriv (P Q : MvPolynomial σ ℂ) (u : σ → W) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0) 0 =
      ∑ m ∈ P.support, ∑ m' ∈ Q.support, P.coeff m * Q.coeff m' *
        lineDerivList ℂ ((lst m).map (fun s => (u s, 0)) ++ (lst m').map (fun s => (0, u s)))
          F 0 := by
  have h1 (z : W) : _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0 = ∑ m' ∈ Q.support, Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z) := by
    have ha : AnalyticAt ℂ (fun w => F (z, w)) 0 := (hF _).comp₂ analyticAt_const analyticAt_id
    rw [polyDeriv_eq_sum_list _ _ ha]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have h2 := congrFun (lineDerivList_comp_linearMap (LinearMap.inr ℂ W W) ((lst m').map u)
      (fun p => F (p + (z, 0)))) 0
    rw [lineDerivList_comp_add_const] at h2
    simp only [LinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, List.map_map] at h2
    rw [h2]
    rfl
  have h3 (m' : σ →₀ ℕ) : AnalyticAt ℂ (fun z => Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z)) 0 :=
    analyticAt_const.fun_smul
      ((analyticAt_lineDerivList (hF _) _).comp ((ContinuousLinearMap.inl ℂ W W).analyticAt 0))
  simp only [h1]
  rw [polyDeriv_eq_sum_list _ _ (Finset.analyticAt_fun_sum _ fun m' _ => h3 m')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lineDerivList_sum _ fun m' _ => h3 m', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [lineDerivList_const_smul, lineDerivList_comp_linearMap, lineDerivList_append, List.map_map,
    mul_assoc]
  simp only [map_zero]
  rfl

theorem lineDerivList_conj {V : Type} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] (l : List V) (hl : ∀ v ∈ l, star v = v) (F : V → ℂ) :
    lineDerivList ℂ l (fun z => conj (F (star z))) =
      fun z => conj (lineDerivList ℂ l F (star z)) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    rw [lineDerivList_cons, ih fun w hw => hl w (List.mem_cons_of_mem _ hw), lineDerivList_cons]
    simp only [lineDeriv, star_add, star_smul, hl v List.mem_cons_self]
    have h := congrFun (deriv_conj_conj (f := fun t : ℂ => lineDerivList ℂ l F (star z + t • v))) 0
    simpa [Function.comp_def] using h

theorem polyDeriv_barP_symm [StarAddMonoid W] [StarModule ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    (hu : ∀ s, star (u s) = u s) {F G : W → W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ (fun p : W × W => F p.1 p.2) p)
    (hG : ∀ p, AnalyticAt ℂ (fun p : W × W => G p.1 p.2) p)
    (h : ∀ z w, G z w = conj (F (star w) (star z))) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (G z) 0) 0 =
      conj (_root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (F z) 0) 0) := by
  have hs : (barP P).support = P.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  have hc (m : σ →₀ ℕ) : (barP P).coeff m = conj (P.coeff m) := MvPolynomial.coeff_map _ _ _
  have e1 := polyDeriv_polyDeriv P (barP P) u hF
  have e2 := polyDeriv_polyDeriv P (barP P) u hG
  dsimp only at e1 e2
  rw [e1, e2, hs, Finset.sum_comm]

  simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  have h1 : (fun p : W × W => G p.1 p.2) =
      fun p => conj ((fun q : W × W => F q.2 q.1) (star p)) := funext fun p => h p.1 p.2
  have h2 (l : List (W × W)) := congrFun (lineDerivList_comp_linearMap
    (LinearEquiv.prodComm ℂ W W).toLinearMap l (fun p : W × W => F p.1 p.2)) 0
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_zero] at h2
  rw [h1, lineDerivList_conj _ (by
    simp only [List.mem_append, List.mem_map]
    rintro v (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> simp [Prod.ext_iff, hu]) fun q : W × W => F q.2 q.1]
  simp only [star_zero]
  rw [h2, List.map_append, List.map_map, List.map_map,
    lineDerivList_perm (hF 0) List.perm_append_comm, mul_comm (P.coeff m')]
  rfl

theorem lineDerivList_exp (ℓ : W →L[ℂ] ℂ) (C : ℂ) (l : List W) :
    lineDerivList ℂ l (fun w => C * Complex.exp (ℓ w)) =
      fun w => (l.map ℓ).prod * (C * Complex.exp (ℓ w)) := by
  induction l with
  | nil => simp [lineDerivList]
  | cons v l ih =>
    funext w
    rw [lineDerivList_cons, ih]
    have h := (((ℓ.hasFDerivAt (x := w)).cexp.const_mul C).const_mul
      (l.map ℓ).prod).hasLineDerivAt v
    simp only [h.lineDeriv, List.map_cons, List.prod_cons, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring

theorem polyDeriv_exp (Q : MvPolynomial σ ℂ) (u : σ → W) (ℓ : W →L[ℂ] ℂ) (C : ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => C * Complex.exp (ℓ w)) 0 =
      C * MvPolynomial.eval (fun s => ℓ (u s)) Q := by
  have ha : AnalyticAt ℂ (fun w => C * Complex.exp (ℓ w)) 0 :=
    analyticAt_const.mul (ℓ.analyticAt 0).cexp
  rw [polyDeriv_eq_sum_list _ _ ha, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : ((List.map u (lst m)).map ℓ).prod = ∏ i ∈ m.support, ℓ (u i) ^ m i := by
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp)
        (by simp [pow_add])]
    rfl
  rw [lineDerivList_exp, h]
  simp only [map_zero, Complex.exp_zero]
  ring

theorem coeff_aeval_smul_X [Fintype σ] (t : σ → ℂ) (Q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m
      (MvPolynomial.aeval (fun s => t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) Q) =
      (∏ s, t s ^ m s) * Q.coeff m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    have h : n.prod (fun s k => (t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) ^ k) =
        (∏ s, t s ^ n s) • MvPowerSeries.monomial n 1 := by
      rw [← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq,
        ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp only [map_one, one_mul, smul_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_pow]
      rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_smul]
      simp
    rw [MvPolynomial.aeval_monomial, h, ← Algebra.smul_def, map_smul, map_smul,
      MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases e : m = n
    · subst e; simp [mul_comm]
    · simp [e, Ne.symm e]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ, MvPolynomial.coeff_add, mul_add]

theorem polyDeriv_barP_exp [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ) (u : σ → W)
    (π : σ → W →L[ℂ] ℂ) (hπ : ∀ s s', π s (u s') = if s = s' then 1 else 0) (t : σ → ℝ) (C : ℝ) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0) 0 =
      ((C * ∑ m ∈ P.support, (∏ s, (m s).factorial : ℕ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) : ℝ) : ℂ) := by
  have h1 (z : W) : _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0 =
      C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P) := by
    have h := polyDeriv_exp (barP P) u (∑ s, (t s * π s z) • π s) C
    simpa [hπ] using h
  have h2 (s : σ) : taylorDir u ((t s : ℂ) • π s : W →L[ℂ] ℂ) = (t s : ℂ) • MvPowerSeries.X s := by
    rw [taylorDir_clm]
    simp [hπ]
  have ha (s : σ) : AnalyticAt ℂ ((t s : ℂ) • π s : W →L[ℂ] ℂ) 0 := ContinuousLinearMap.analyticAt _ _
  have h3 : taylorDir u (fun z => C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P)) =
      (C : ℂ) • MvPolynomial.aeval (fun s => (t s : ℂ) • (MvPowerSeries.X s : MvPowerSeries σ ℂ))
        (barP P) := by
    simp only [← h2]
    rw [← taylorDir_eval u ha, ← taylorDir_smul]
    · rfl
    · exact AnalyticAt.aeval_mvPolynomial ha _
  simp only [h1]
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, h3]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, coeff_aeval_smul_X, barP, MvPolynomial.coeff_map, ← Complex.mul_conj, smul_eq_mul]
  ring

theorem apolar_norm_pos [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) {t : σ → ℝ}
    (ht : ∀ s, 0 < t s) :
    0 < ∑ m ∈ P.support, ((∏ s, (m s).factorial : ℕ) : ℝ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) := by
  refine Finset.sum_pos (fun m hm => ?_) (MvPolynomial.support_nonempty.2 hP)
  refine mul_pos (mul_pos ?_ (Finset.prod_pos fun s _ => pow_pos (ht s) _))
    (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hm))
  exact_mod_cast Finset.prod_pos fun s _ => Nat.factorial_pos _

end GlobalTheory.SW.KernSym
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isOpen_stabilizer_completedLattice_adelicUnitary : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  first | exact @GlobalTheory.StabOpen.isOpen_stab_latHat | exact GlobalTheory.StabOpen.isOpen_stab_latHat | (intros; apply GlobalTheory.StabOpen.isOpen_stab_latHat <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.integrableOn_inv_norm_det_pow_near_indefinite_gram : ∀ (p q n : ℕ), 2 * (p + q) ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn (fun y : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) * (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)) a b‖ < δ₀} volume := by
  first | exact @GlobalTheory.MinorInt.integrableOn_minor_fin | exact GlobalTheory.MinorInt.integrableOn_minor_fin | (intros; apply GlobalTheory.MinorInt.integrableOn_minor_fin <;> assumption)
end
