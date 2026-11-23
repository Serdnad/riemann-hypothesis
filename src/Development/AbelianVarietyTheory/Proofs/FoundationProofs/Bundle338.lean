module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.CoordConj

theorem cj_coe (ρ : Qbar →ₐ[ℚ] ℂ) (w : Qbar) : cj Qbar ρ (w : ℂ) = ρ w := by
  simp [cj, TaylorLogMetric.liftM]

theorem differentiable_U {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N')) {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U _ hG).const_mul _).const_mul _

theorem applyAt0_comb {D : D7} {a d : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (G : ι → VC D a d → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i)) (p : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D p (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * GL3Theta.applyAt0 D p (G i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) 0 (differentiable_const 0)).2.2.1 0 p
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ ((hG i).const_smul (c i))).2.2.2 _ p
        (Differentiable.sum fun j _ => (hG j).const_smul (c j)), ih,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ (hG i)).2.2.1]

theorem comb_bound {ι : Type} [Fintype ι] (ρ : Qbar →ₐ[ℚ] ℂ) (r : ι → Qbar) (t : ι → ℂ) (S M : ℝ) (hM : 0 ≤ M)
    (hr : (∑ i, ‖ρ (r i)‖) ^ 2 ≤ S) (ht : ∀ i, t i ∈ Qbar ∧ ‖cj Qbar ρ (t i)‖ ^ 2 ≤ M) :
    ∑ i, (r i : ℂ) * t i ∈ Qbar ∧ ‖cj Qbar ρ (∑ i, (r i : ℂ) * t i)‖ ^ 2 ≤ S * M := by
  have e : ∑ i, (r i : ℂ) * t i = ((∑ i, r i * ⟨t i, (ht i).1⟩ : Qbar) : ℂ) := by
    push_cast
    rfl
  refine ⟨e ▸ SetLike.coe_mem _, ?_⟩

  rw [e, cj_coe, map_sum]
  have h1 : ∀ i, ‖ρ ⟨t i, (ht i).1⟩‖ ≤ Real.sqrt M := fun i => by
    rw [← cj_coe]
    exact Real.le_sqrt_of_sq_le (ht i).2
  have h2 : ‖∑ i, ρ (r i * ⟨t i, (ht i).1⟩)‖ ≤ (∑ i, ‖ρ (r i)‖) * Real.sqrt M := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg _)
  calc _ ≤ ((∑ i, ‖ρ (r i)‖) * Real.sqrt M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = (∑ i, ‖ρ (r i)‖) ^ 2 * M := by rw [mul_pow, Real.sq_sqrt hM]
    _ ≤ S * M := mul_le_mul_of_nonneg_right hr hM

theorem coord_conj_le : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D hI cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact GlobalTheory.T.vacuumTranslate_conjugate_jet_bound D hI cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := GlobalTheory.T.definiteThetaPair_testVector_expansion D hI cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := GlobalTheory.T.intertwiner_selfDual_vacuum_isVacuum D hI cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, applyAt0_comb _ _ _ fun i => differentiable_U _ hGd]
    refine comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.NormSum.CoordConj
end

section

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem alg_apply {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem entN_par {a b : ℕ} (x : Gn g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (y : Gn g b) (i j : ℕ) :
    (i < a → j < a → entN (par finSumFinEquiv x B y).val i j = entN x.val i j) ∧
    (a ≤ i → j < a → entN (par finSumFinEquiv x B y).val i j = 0) ∧
    (entN (par finSumFinEquiv x B y).val (a + i) (a + j) = entN y.val i j) ∧
    (B = 0 → i < a → a ≤ j → entN (par finSumFinEquiv x B y).val i j = 0) := by
  refine ⟨fun hi hj => ?_, fun hi hj => ?_, ?_, fun hB hi hj => ?_⟩
  · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inl ⟨j, hj⟩)
    rw [entN, entN, dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨hi, hj⟩]
    exact this
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inr ⟨i - a, by omega⟩) (.inl ⟨j, hj⟩)
      rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp; omega)) (Fin.ext (by simp))
    · rfl
  · unfold entN
    by_cases h : i < b ∧ j < b
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left h]
      exact par_apply finSumFinEquiv x B y (.inr ⟨i, h.1⟩) (.inr ⟨j, h.2⟩)
    · rw [dite_eq_right (by omega), dite_eq_right h]
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inr ⟨j - a, by omega⟩)
      subst hB
      rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp)) (Fin.ext (by simp; omega))
    · rfl

theorem ext_entN {n : ℕ} {x y : Gn g n} (h : ∀ i j : ℕ, i < n → j < n → entN x.val i j = entN y.val i j) :
    x = y := by
  ext i j
  rw [← ParInd.entN_self x.val, ← ParInd.entN_self y.val, h _ _ i.2 j.2]

section Local

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def repK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Representation ℂ (Gn g n) (fixK1 π) where
  toFun x := (π (lift g n x)).restrict fun _ hv => padicIntGL_smul_mem_principalCongruenceFixed π hv _
  map_one' := LinearMap.ext fun v => Subtype.ext (lift_one_apply π v.2)
  map_mul' x y := LinearMap.ext fun v => Subtype.ext (lift_mul_apply π v.2 x y)

theorem repK_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : fixK1 π) :
    (repK π (red g n k) v : V) = π (inc g n k) v :=
  inc_eq_of_red_eq π v.2 (red_invFun _)

theorem repK_alg (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) (v : fixK1 π) :
    ((repK π).asAlgebraHom a v : V) = actK π a v := by
  rw [alg_apply, actK, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

end Local

section Ind

variable {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) : GL (Fin (a + b)) ℤ_[g] where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val B 0 y.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x⁻¹).val
    (-((x⁻¹).val * B * (y⁻¹).val)) 0 (y⁻¹).val)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem parZ_apply (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (i j : Fin a ⊕ Fin b) : (parZ x B y).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks x.val B 0 y.val i j := by
  simp [parZ]

theorem red_parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) :
    red g _ (parZ x B y) =
      par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply, ParInd.red_val, Matrix.map_apply, parZ_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [ParInd.red_val]

theorem exists_dual_right (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W, P z ≠ 0 ∧
    ∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y) := by
  let β := Module.Basis.ofVectorSpace ℂ W'
  have h1 : TensorProduct.equivFinsuppOfBasisRight β z ≠ 0 := by simpa using hz
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  refine ⟨Finsupp.lapply i ∘ₗ (TensorProduct.equivFinsuppOfBasisRight β).toLinearMap, hi, fun A y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem exists_dual_left (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W', P z ≠ 0 ∧
    ∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y) := by
  obtain ⟨P, h1, h2⟩ := exists_dual_right (TensorProduct.comm ℂ W W' z) (by simpa using hz)
  refine ⟨P ∘ₗ (TensorProduct.comm ℂ W W').toLinearMap, h1, fun A y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h2]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

end Ind

end GlobalTheory.GLp.Supp
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WeilInter

variable {D : D7} {N N' : ℕ}

theorem sd_of_moves {g : GA D N} {L : Lat D N} (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L : Lat D N} {L' : Lat D N'}
    (h : Moves D (g : GL (Fin N) (AE D)) L) (h' : Moves D (g' : GL (Fin N') (AE D)) L') :
    KLat D T (La D T L L') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem quot_bijective {V : Type} [AddCommGroup V] (A₁ A₂ B₁ B₂ : AddSubgroup V) (f : B₁ → B₂)
    (h1 : ∀ x y : B₁, (x : V) - (y : V) ∈ A₁ ↔ (f x : V) - (f y : V) ∈ A₂)
    (h2 : ∀ y : B₂, ∃ x : B₁, (f x : V) - (y : V) ∈ A₂) :
    Function.Bijective (fun q : B₁ ⧸ A₁.addSubgroupOf B₁ =>
      (QuotientAddGroup.mk (f (Quotient.out q)) : B₂ ⧸ A₂.addSubgroupOf B₂)) := by
  have e1 : ∀ x y : B₁, (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₁ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have e2 : ∀ x y : B₂, (QuotientAddGroup.mk x : B₂ ⧸ A₂.addSubgroupOf B₂) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₂ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  constructor
  · intro q q' hq
    have := (e1 _ _).2 ((h1 _ _).2 ((e2 _ _).1 hq))
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  · intro r
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
    obtain ⟨x, hx⟩ := h2 y
    refine ⟨QuotientAddGroup.mk x, ?_⟩
    have h3 := (h1 _ _).1 ((e1 (Quotient.out (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁)) x).1
      (QuotientAddGroup.out_eq' _))
    refine (e2 _ _).2 ?_
    have := A₂.add_mem h3 hx
    rwa [sub_add_sub_cancel] at this

theorem wd_congr {T : Tor D} {A B : AddSubgroup (VC D N N')} (hA : Nice D T A) (hB : Nice D T B)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {u v : VC D N N'} (hu : u ∈ B) (hv : v ∈ B) (h : u - v ∈ A) :
    Wd D T u G = Wd D T v G := by
  have h1 := Wd_Wd D T v (u - v) G
  rw [((hA.mem_ThSp G).1 hG).2 _ h, hB.2.1 v hv _ (B.sub_mem hu hv), one_smul, add_sub_cancel] at h1
  exact h1.symm

theorem iop_sum {T : Tor D} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')} (hB : Nice D T B)
    [Fintype (B ⧸ A.addSubgroupOf B)] (F : VC D N N' → ℂ) :
    Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
      ∑ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F := by
  rw [hB.Iop_eq]
  funext z
  rw [finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

theorem zero_mem_TT (T : Tor D) : (0 : VC D N N' → ℂ) ∈ TT D T N N' := by
  refine ⟨differentiable_const _, 1, Nat.one_pos, fun x _ => ?_⟩
  have := Wd_smul D T (1 • x) 0 (0 : VC D N N' → ℂ)
  rwa [zero_smul, zero_smul] at this

theorem om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (hadd : ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N')
    (g : GA D N) (g' : GA D N') {ι : Type} (s : Finset ι) (φ : ι → VC D N N' → ℂ)
    (hφ : ∀ i, φ i ∈ TT D (tor0 D cc δ) N N') :
    ∑ i ∈ s, φ i ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, φ i) = ∑ i ∈ s, W.Om g g' (φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨zero_mem_TT _, ?_⟩
    have := W.smul g g' 0 0 (zero_mem_TT _)
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hadd _ (hφ a) _ ih.1, by rw [W.add g g' _ (hφ a) _ ih.1, ih.2]⟩

theorem om_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) M₁ M₁') F) = Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) M₂ M₂') (W.Om g g' F) := by
  intro D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hc N N'
  have hFT := t1 _ _ (sd_of_moves a1) (sd_of_moves a1') F hF
  have hG := GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W g h g' h' L₁ L₂ L₁' L₂' a1 a1' a2 a2' F hF
  obtain ⟨f, f1, f2, f3⟩ := GlobalTheory.T.exists_thetaLattice_correspondence_weilOperator D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂'
    a1 a1' a2 a2' b1 b1' b2 b2' F hFT
  have kA1 := klat (tor0 D cc δ) a1 a1'
  have kA2 := klat (tor0 D cc δ) a2 a2'
  have kB1 := klat (tor0 D cc δ) b1 b1'
  have kB2 := klat (tor0 D cc δ) b2 b2'
  have nA2 := GlobalTheory.ThetaTriple.nice_of_klat hc kA2
  have nB1 := GlobalTheory.ThetaTriple.nice_of_klat hc kB1
  have nB2 := GlobalTheory.ThetaTriple.nice_of_klat hc kB2
  haveI i1 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA1 kB1)
  haveI i2 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA2 kB2)
  have hb := quot_bijective _ _ _ _ f f2 f3
  have hi : ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁')).index =
      ((La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂')).index :=
    Nat.card_congr (Equiv.ofBijective _ hb)
  have hW : ∀ x : La D (tor0 D cc δ) M₁ M₁', Wd D (tor0 D cc δ) (x : VC D N N') F ∈ TT D (tor0 D cc δ) N N' := by
    intro x
    obtain ⟨z, hz, -⟩ := exists_pt_of_mem_La_moved D (GlobalTheory.InducedType.induced_type D).1 cc δ hc.1.1 N N' k k'
      M₁ M₁' b1 b1' x x.2
    rw [hz]
    exact t2 z F hFT
  obtain ⟨s1, s2⟩ := om_sum W t3 g g' Finset.univ
    (fun q : La D (tor0 D cc δ) M₁ M₁' ⧸ (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁') =>
      Wd D (tor0 D cc δ) ((Quotient.out q : La D (tor0 D cc δ) M₁ M₁') : VC D N N') F) (fun q => hW _)
  rw [iop_sum _ nB1, iop_sum _ nB2, W.smul g g' _ _ s1, s2, hi]
  congr 1
  refine Fintype.sum_bijective _ hb _ _ fun q => ?_
  rw [f1]
  refine wd_congr nA2 nB2 hG (f _).2 (Subtype.property _) ?_
  have := (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (f (Quotient.out q)) : La D (tor0 D cc δ) M₂ M₂' ⧸
    (La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂'))).symm
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at this
  exact this

end GlobalTheory.WeilInter
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints : ∀ D : D7, gal D := by
  first | exact @GlobalTheory.GalTheta.gal_all | exact GlobalTheory.GalTheta.gal_all | (intros; apply GlobalTheory.GalTheta.gal_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaVacua_conjugates_cmPoints : ∀ D : D7, useConj D := by
  first | exact @GlobalTheory.ThetaConj.useConj_all | exact GlobalTheory.ThetaConj.useConj_all | (intros; apply GlobalTheory.ThetaConj.useConj_all <;> assumption)
end
