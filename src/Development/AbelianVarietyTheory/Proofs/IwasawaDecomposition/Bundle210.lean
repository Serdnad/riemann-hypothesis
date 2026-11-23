module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEqMulProdMinors
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Aesop.Main
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfPartialSumsNonneg
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.DefLift.Joint

theorem X_mul_pderiv_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : X u * pderiv v Q ∈ restrictTotalDegree σ ℂ N := by
  classical

  rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_restrictTotalDegree] at hQ ⊢
  have hd : (m.sum fun _ e => e) ≤ N := (le_totalDegree hm).trans hQ
  rw [pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have h1 : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have h2 : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := (add_tsub_cancel_of_le h1).symm
    conv_rhs => rw [h2]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp
    rfl

theorem antitone_rowOp {σ J : Type} [Fintype σ] [Fintype J] {p : ℕ} (z : Fin p × J → σ)
    (hz : Function.Injective z) {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (μ : Fin p → ℤ)
    (hup : ∀ a b, a < b → ∑ k, X (z (a, k)) * pderiv (z (b, k)) P = 0)
    (hwt : ∀ a, ∑ k, X (z (a, k)) * pderiv (z (a, k)) P = (μ a : ℂ) • P) : Antitone μ :=
  highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (restrictTotalDegree σ ℂ P.totalDegree)
    (fun i j w hw => by
      rw [rowOp_apply]
      exact Submodule.sum_mem _ fun _ _ => X_mul_pderiv_mem _ _ _ _ hw)
    P ((mem_restrictTotalDegree _ _ _).2 le_rfl) hP μ
    (fun a b h => (rowOp_apply _ _ _ _).trans (hup a b h))
    (fun a => (rowOp_apply _ _ _ _).trans (hwt a))

theorem degree_of_mem_support {σ J : Type} [Fintype J] (z : J → σ) {P : MvPolynomial σ ℂ} {w : ℤ}
    (h : ∑ k, X (z k) * pderiv (z k) P = (w : ℂ) • P) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ((∑ k, m (z k) : ℕ) : ℤ) = w := by
  have := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [coeff_sum, MvPolynomial.coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2

theorem exists_eq_smul_base {T : Type} [Fintype T] {p n : ℕ} (h : p + 0 ≤ n)
    {P : Poly ℂ T p 0 (Fin n)} (hP : P ≠ 0) (κ : T → Fin n → ℤ) (μ : T → Fin p → ℤ)
    (hup : ∀ t k l, k < l → ∑ a, X (xVar t a k) * pderiv (xVar t a l) P = 0)
    (hwt : ∀ t k, ∑ a, X (xVar t a k) * pderiv (xVar t a k) P = (κ t k : ℂ) • P)
    (hup' : ∀ t a b, a < b → ∑ k, X (xVar t a k) * pderiv (xVar t b k) P = 0)
    (hwt' : ∀ t a, ∑ k, X (xVar t a k) * pderiv (xVar t a k) P = (μ t a : ℂ) • P) :
    ∃ r : ℂ, P = r • basePoly ℂ h (fun t => diffOf fun a : Fin p => (κ t (Fin.castLE (n := p) h a)).toNat)
      (fun _ _ => 0) := by
  classical
  let z : T → Fin p × Fin n → Var T p 0 (Fin n) := fun t w => xVar t w.1 w.2
  let y : T → Fin 0 × Fin n → Var T p 0 (Fin n) := fun t w => yVar t w.1 w.2
  have hz : ∀ t, Function.Injective (z t) := fun t u w e => by simpa [z, Prod.ext_iff] using e
  have hy : ∀ t, Function.Injective (y t) := fun t u w e => u.1.elim0
  have hzy : ∀ t u w, z t u ≠ y t w := fun t u w => w.1.elim0
  have hμ : ∀ t, Antitone (μ t) := fun t => antitone_rowOp (z t) (hz t) hP _ (hup' t) (hwt' t)
  have hκ : ∀ t, Antitone (κ t) := fun t =>
    antitone_rowOp (fun w : Fin n × Fin p => z t w.swap) ((hz t).comp Prod.swap_injective) hP _
      (hup t) (hwt t)
  let a : T → Fin p → ℕ := fun t i => (μ t i).toNat
  have ha : ∀ t, Antitone (a t) := fun t i j hij => Int.toNat_le_toNat (hμ t hij)
  have hdeg : ∀ t i, ∀ m ∈ P.support, ∑ k, m (xVar t i k) = a t i := fun t i m hm => by
    have := degree_of_mem_support (fun k => xVar t i k) (hwt' t i) hm
    simp only [a]
    omega
  have hinv : ∀ t (i j : Fin p), i < j → ∀ s : ℂ,
      bind₁ (fun v => X v + ∑ k, if v = z t (j, k) then C s * X (z t (i, k)) else 0) P = P :=
    fun t i j hij => ((rowAdd_invariant_iff (fun k => z t (i, k)) (fun k => z t (j, k))
      (fun k l e => by simpa using hz t e)
      (fun k l e => hij.ne (congrArg Prod.fst (hz t e))) P).out 3 2).1 (hup' t i j hij)
  have hw : ∀ t, κ t = mixedWeight n (a t) (fun _ : Fin 0 => 0) := fun t =>
    weight_eq_mixedWeight h (z t) (hz t) (y t) (hy t) (hzy t) (a t) _ (ha t) (fun i => i.elim0)
      (hdeg t) (fun i => i.elim0) (hinv t) (fun i => i.elim0) (fun _ i => i.elim0) (κ t) (hκ t)
      (fun k l hkl => by rw [mixedOp_apply]; simpa using hup t k l hkl)
      (fun k => by rw [mixedOp_apply]; simpa using hwt t k) hP
  have e : (fun t => diffOf fun i : Fin p => (κ t (Fin.castLE (n := p) h i)).toNat) = fun t => diffOf (a t) := by
    funext t
    congr 1
    funext i
    rw [hw t, mixedWeight_apply]
    simp
  rw [e]
  refine exists_eq_smul_basePoly h _ _ ?_ κ hκ (fun t k l hkl => by simpa using hup t k l hkl)
    fun t k => by simpa using hwt t k
  refine mem_rowHighest_iff_of_charZero.2 ⟨fun _ _ b => b.elim0, fun t i m hm => ?_,
    fun _ b => b.elim0, fun t i j hij s => ?_, fun _ b => b.elim0⟩
  · rw [partOf_diffOf (ha t)]; exact hdeg t i m hm
  · rw [rowAddX_eq_bind₁]; exact hinv t i j hij s

end GlobalTheory.DefLift.Joint

namespace GlobalTheory.DefLift

theorem joint_highest_proportional (ι : Type) [Fintype ι] (m n : ℕ) (hnm : n ≤ m) (P Q : Pol ι m n)
    (κ : ι → Fin m → ℤ) (μ μ' : ι → Fin n → ℤ) (hP : P ≠ 0)
    (h1 : ∀ τ k l, k < l → rowLie n τ k l P = 0 ∧ rowLie n τ k l Q = 0)
    (h2 : ∀ τ k, rowLie n τ k k P = (κ τ k : ℂ) • P ∧ rowLie n τ k k Q = (κ τ k : ℂ) • Q)
    (h3 : ∀ τ k l, k < l → colLie m τ k l P = 0 ∧ colLie m τ k l Q = 0)
    (h4 : ∀ τ k, colLie m τ k k P = (μ τ k : ℂ) • P ∧ colLie m τ k k Q = (μ' τ k : ℂ) • Q) :
    ∃ r : ℂ, Q = r • P := by
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [hQ]⟩
  let f : ι × Fin m × Fin n → Var ι n 0 (Fin m) := fun v => xVar v.1 v.2.2 v.2.1
  have hf : Function.Injective f := fun u w e => by
    simp only [f, Prod.ext_iff, Sum.inl.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)
  have hr : ∀ τ k l (R : Pol ι m n), rename f (rowLie n τ k l R) =
      ∑ a, X (xVar τ a k) * pderiv (xVar τ a l) (rename f R) := fun τ k l R => by

    rw [rowLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hc : ∀ τ k l (R : Pol ι m n), rename f (colLie m τ k l R) =
      ∑ a, X (xVar τ k a) * pderiv (xVar τ l a) (rename f R) := fun τ k l R => by

    rw [colLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hi := rename_injective (R := ℂ) f hf
  obtain ⟨r, er⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hP) κ μ
    (fun t k l h => by rw [← hr, (h1 t k l h).1, map_zero])
    (fun t k => by rw [← hr, (h2 t k).1, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).1, map_zero])
    (fun t k => by rw [← hc, (h4 t k).1, map_smul])
  obtain ⟨s, es⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hQ) κ μ'
    (fun t k l h => by rw [← hr, (h1 t k l h).2, map_zero])
    (fun t k => by rw [← hr, (h2 t k).2, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).2, map_zero])
    (fun t k => by rw [← hc, (h4 t k).2, map_smul])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hP (hi (by rw [er, zero_smul, map_zero]))
  refine ⟨s / r, hi ?_⟩
  rw [map_smul, er, es, smul_smul, div_mul_cancel₀ _ hr0]

end GlobalTheory.DefLift

end
end

section

noncomputable section

open MvPolynomial GlobalTheory.MvPoly GlobalTheory.Harm Matrix

namespace GlobalTheory.DefLift

namespace Compl

theorem exists_sub_perp {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x, B x x = 0 → x = 0) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (P : E) :
    ∃ Q ∈ W, ∀ w ∈ W, B (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : E →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun i => B.flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : B P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)

    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this

    rw [← this, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ]
    exact smul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hB _ (hL x hx x x.2))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

theorem totalDegree_aeval_le {σ : Type*} (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeBound.main
  | exact _root_.GlobalTheory.AevalTotalDegreeBound.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeBound.main ..)

variable {ι : Type} {m n : ℕ}

theorem totalDegree_subst_le (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    (subst a b P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) P
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun c _ => ?_
  exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le

theorem totalDegree_colSub_le (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P : Pol ι m n) :
    (colSub m τ g P).totalDegree ≤ P.totalDegree := by
  unfold colSub
  rw [AlgHom.toLinearMap_apply]
  exact totalDegree_subst_le _ _ _

theorem fockInner_subst [Fintype ι] (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ)
    (P Q : Pol ι m n) :
    fockInner (subst a b P) Q = fockInner P (subst (fun τ => star (a τ)) (fun τ => star (b τ)) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _
    (fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0) ?_ ?_ P Q
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type]
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type, apply_ite star, mul_comm]

theorem fockInner_colSub [Fintype ι] (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P Q : Pol ι m n) :
    fockInner (colSub m τ g P) Q = fockInner P (colSub m τ g⁻¹ Q) := by
  unfold colSub
  simp only [AlgHom.toLinearMap_apply]
  rw [fockInner_subst]
  congr 3
  · funext ρ
    split_ifs
    · rfl
    · simp
  · funext ρ
    simp

end Compl


open Compl in
theorem exists_colStable_disjoint (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n))
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) (hW : ∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) (hlt : U < W) :
    ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧
      ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  classical
  let b := Module.finBasis ℂ X
  let B : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ Ψ => ∑ i, fockInner (Φ (b i)) (Ψ (b i)))
      (fun _ _ _ => by simp [fockInner_add_left, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_left, Finset.mul_sum])
      (fun _ _ _ => by simp [fockInner_add_right, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_right, Finset.mul_sum])
  have hBa (Φ Ψ) : B Φ Ψ = ∑ i, fockInner (Φ (b i)) (Ψ (b i)) := rfl
  have hB (Φ) (h : B Φ Φ = 0) : Φ = 0 := by
    rw [hBa] at h
    simp only [fockInner_self] at h
    have h' : ∑ i, fockNormSq (Φ (b i)) = 0 := by
      rw [← RCLike.ofReal_sum] at h
      exact RCLike.ofReal_eq_zero.mp h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => fockNormSq_nonneg _] at h'
    exact b.ext fun i => fockNormSq_eq_zero.mp (h' i (Finset.mem_univ i))
  have hadj (Φ Ψ τ g) : B (colSub m τ g ∘ₗ Φ) Ψ = B Φ (colSub m τ g⁻¹ ∘ₗ Ψ) := by
    simp only [hBa, LinearMap.comp_apply, fockInner_colSub]
  clear hBa
  clear_value B
  obtain ⟨β, hβW, hβU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i, (β (b i)).totalDegree ≤ d :=
    ⟨_, fun i => Finset.le_sup (f := fun i => (β (b i)).totalDegree) (Finset.mem_univ i)⟩
  obtain ⟨R, hRf, hR⟩ : ∃ R : Submodule ℂ (Pol ι m n), FiniteDimensional ℂ R ∧ ∀ P, P ∈ R ↔ P.totalDegree ≤ d :=
    ⟨restrictTotalDegree (ι × Fin m × Fin n) ℂ d, inferInstance, fun P => mem_restrictTotalDegree _ _ _⟩
  let ψ : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) :=
    { toFun := fun Ψ => R.subtype ∘ₗ Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let D : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range ψ
  have hD (Φ) : Φ ∈ D ↔ ∀ x, Φ x ∈ R := by
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  haveI : FiniteDimensional ℂ D := inferInstance
  clear_value D
  have hDs (Φ) (h : Φ ∈ D) (τ g) : colSub m τ g ∘ₗ Φ ∈ D := by
    rw [hD] at h ⊢
    intro x
    have := h x
    rw [hR] at this ⊢
    rw [LinearMap.comp_apply]
    exact (totalDegree_colSub_le τ g _).trans this
  have hβD : β ∈ D := by
    rw [hD]
    intro x

    rw [← b.sum_repr x, map_sum]
    refine R.sum_mem fun i _ => ?_
    rw [map_smul]
    exact R.smul_mem _ ((hR _).2 (hd i))
  haveI : FiniteDimensional ℂ (U ⊓ D : Submodule ℂ _) := Submodule.finiteDimensional_inf_right _ _
  let T : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := ⨅ w ∈ U ⊓ D, LinearMap.ker (B.flip w)
  have hT (Φ) : Φ ∈ T ↔ ∀ w ∈ U ⊓ D, B Φ w = 0 := by simp [T, Submodule.mem_iInf]
  obtain ⟨Q, hQ, hperp⟩ := exists_sub_perp B hB (U ⊓ D) β
  refine ⟨W ⊓ D ⊓ T, ?_, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · intro h
    have hm : β - Q ∈ W ⊓ D ⊓ T :=
      ⟨⟨W.sub_mem hβW (hlt.le hQ.1), D.sub_mem hβD hQ.2⟩, (hT _).2 hperp⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hm
    exact hβU (hm ▸ hQ.1)
  · rw [Submodule.eq_bot_iff]
    rintro Φ ⟨h1, ⟨-, h2⟩, h3⟩
    exact hB Φ ((hT Φ).1 h3 Φ ⟨h1, h2⟩)
  · rintro Φ ⟨⟨h1, h2⟩, h3⟩ τ g
    refine ⟨⟨hW Φ h1 τ g, hDs Φ h2 τ g⟩, (hT _).2 fun w hw => ?_⟩
    rw [hadj]
    exact (hT Φ).1 h3 _ ⟨hU w hw.1 τ _, hDs w hw.2 τ _⟩

end GlobalTheory.DefLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVec

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def fieldDeriv (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ) where
  toFun X g := fderiv ℝ φ g (-(P * X * P⁻¹) * g)
  map_add' X Y := by
    funext g
    simp only [Pi.add_apply, ← map_add (f := _), Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, ← map_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]

theorem isTest_fderiv {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest fun g => fderiv ℝ φ g (Y * g) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (le_of_eq rfl)).clm_apply (contDiff_const.mul contDiff_id), ?_⟩
  refine HasCompactSupport.intro hφ.2 fun g hg => ?_
  rw [fderiv_of_notMem_tsupport ℝ hg]; rfl

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem hasDerivAt_integral_translate (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}
    (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    HasDerivAt (fun t : ℝ => ∫ g : Formalism.REAL.UJ ε, φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
      ∂(Formalism.REAL.muG ε)) (gard ε σ (fun g => fderiv ℝ φ g (Y * g)) w) 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := continuous_umat
  have hb := continuous_orbit hσ w
  have he : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (Z * NormedSpace.exp (t • Z)) t :=
    fun Z t => hasDerivAt_exp_smul_const' Z t
  have hc : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
    fun Z => continuous_iff_continuousAt.2 fun t => (he Z t).continuousAt
  have hxy : ∀ t : ℝ, NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_left.smul_left t).smul_right t), ← smul_add]
    simp
  have hC : IsCompact (Set.image2 (· * ·) ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1)
      (tsupport φ)) := ((isCompact_closedBall (0 : ℝ) 1).image (hc _)).mul hφ.2
  have hK := hemb.isCompact_preimage hC
  set K := (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹' (Set.image2 (· * ·)
    ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1) (tsupport φ)) with hKdef
  replace hK : IsCompact K := hK
  have hout : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g ∉ K, NormedSpace.exp (t • Y) * umat g ∉ tsupport φ :=
    fun t ht g hg hm => hg ⟨_, ⟨t, ht, rfl⟩, _, hm, by
      show _ * (_ * _) = umat g
      rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]⟩
  set μ := Formalism.REAL.muG ε
  let F' : ℝ → Formalism.REAL.UJ ε → H := fun t g =>
    fderiv ℝ φ (NormedSpace.exp (t • Y) * umat g) (Y * NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
  have hF'c : Continuous fun p : ℝ × Formalism.REAL.UJ ε => F' p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => NormedSpace.exp (p.1 • Y) := (hc Y).comp continuous_fst
    have h2 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => umat p.2 := hu.comp continuous_snd
    exact (((hφ.1.continuous_fderiv (by simp)).comp (h1.mul h2)).clm_apply
      ((continuous_const.mul h1).mul h2)).smul (hb.comp continuous_snd)
  obtain ⟨C, hCb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  have hint : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, Integrable
      (fun g : Formalism.REAL.UJ ε => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) μ := fun t ht =>
    Continuous.integrable_of_hasCompactSupport ((hφ.continuous.comp (continuous_const.mul hu)).smul hb)
      (HasCompactSupport.intro hK fun g hg => by
        rw [image_eq_zero_of_notMem_tsupport (hout t ht g hg), zero_smul])
  have e0 : F' 0 = fun g : Formalism.REAL.UJ ε => fderiv ℝ φ (umat g) (Y * umat g) • σ (umat g) w := by
    funext g; simp [F']
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t g => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) (F' := F')
    (bound := K.indicator fun _ => C) (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    (by filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
        exact (hint t ht).aestronglyMeasurable)
    (hint 0 (Metric.mem_closedBall_self zero_le_one))
    (by rw [e0]; exact ((isTest_fderiv hφ Y).integrable hb).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g t ht => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg]; exact hCb (t, g) ⟨ht, hg⟩
      · rw [Set.indicator_of_notMem hg]
        simp [F', fderiv_of_notMem_tsupport ℝ (hout t ht g hg)])
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun g t _ =>
      (((hφ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ((he Y t).mul_const (umat g))).smul_const _)
  rw [e0] at key
  exact key.2

theorem dRep_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  intro n ε H _ _ _ σ P G hP h hσ φ hφ
  refine ⟨fieldDeriv φ P, fun X => ⟨isTest_fderiv hφ _, fun hX w => ?_⟩⟩
  refine Eq.trans ?_ (hasDerivAt_integral_translate hσ hφ (-(P * X * P⁻¹)) w).deriv
  unfold dRep
  congr 1
  funext t
  rw [gard_eq hσ hφ]
  refine GlobalTheory.LowTypeRestriction.garding_translate hσ hφ.continuous hφ.2 w
    (conj_mem_UJ hP h (exp_mem_UH (gram_unit hP h) hX t)) ?_
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl (P * X * P⁻¹)).neg_left.smul_left t).smul_right t), ← smul_add]
  simp

end GlobalTheory.SmVec

end
end
