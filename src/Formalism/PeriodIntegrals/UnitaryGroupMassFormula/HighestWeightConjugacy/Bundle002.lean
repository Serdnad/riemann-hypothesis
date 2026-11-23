module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix MvPolynomial
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

def coords (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace L × Fin n × Fin n → ℂ :=
  fun q => Y q.1 q.2.1 q.2.2

def Mx (w : InfinitePlace L) : Matrix (Fin n) (Fin n) (MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (w, i, j)

theorem eval_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    (eval (coords Y)).mapMatrix (Mx w) = Y w := by
  ext i j
  simp [Mx, coords]

theorem eval_det_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (Mx w).det = (Y w).det := by
  rw [RingHom.map_det, eval_Mx]

theorem eval_det_one_add_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (1 + Mx w).det = (1 + Y w).det := by
  rw [RingHom.map_det, map_add (f := _), map_one, eval_Mx]

theorem eval_adj_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) (i j : Fin n) :
    eval (coords Y) ((Mx w).adjugate i j) = (Y w).adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (eval (coords Y)) (Mx w)) i) j
  rw [eval_Mx] at h
  simpa using h

def Dl (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : ℂ := ∏ w, (Y w).det

def DlP : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ := ∏ w, (Mx w).det

theorem eval_DlP (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : eval (coords Y) (DlP (L := L) (n := n)) = Dl Y := by
  simp [DlP, Dl, map_prod, eval_det_Mx]

theorem var_hom (v : (L →+* ℂ) × Fin n × Fin n) :
    ∃ N : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ, ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y * repPt Y v = eval (coords Y) N := by
  obtain ⟨σ, i, j⟩ := v
  by_cases h : σ = (InfinitePlace.mk σ).embedding
  · refine ⟨X (InfinitePlace.mk σ, i, j) * DlP, fun Y _ => ?_⟩
    simp only [repPt, if_pos h, map_mul, eval_X, eval_DlP, coords]
    ring
  · refine ⟨(Mx (InfinitePlace.mk σ)).adjugate j i *
      ∏ w ∈ Finset.univ.erase (InfinitePlace.mk σ), (Mx w).det, fun Y hY => ?_⟩
    simp only [repPt, if_neg h, map_mul, map_prod, eval_adj_Mx, eval_det_Mx]
    rw [Matrix.inv_def, Matrix.smul_apply, Dl,
      ← Finset.mul_prod_erase Finset.univ (fun w => (Y w).det) (Finset.mem_univ (InfinitePlace.mk σ)),
      Ring.inverse_eq_inv', smul_eq_mul]
    have := hY (InfinitePlace.mk σ)
    field_simp

theorem hom_exists (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    ∃ (K : ℕ) (P : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ), ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y ^ K * eval (repPt Y) F = eval (coords Y) P := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, fun Y _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K1, P1, h1⟩ := hp
    obtain ⟨K2, P2, h2⟩ := hq
    refine ⟨K1 + K2, P1 * DlP ^ K2 + P2 * DlP ^ K1, fun Y hY => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_DlP, ← h1 Y hY, ← h2 Y hY]
    ring
  | mul_X p v hp =>
    obtain ⟨K, P, h⟩ := hp
    obtain ⟨N, hN⟩ := var_hom (L := L) v
    refine ⟨K + 1, P * N, fun Y hY => ?_⟩
    rw [map_mul, map_mul, ← h Y hY, ← hN Y hY, eval_X]
    ring

theorem repPt_of_InV [IsCMField L] (y : (L →+* ℂ) × Fin n × Fin n → ℂ) (hy : InV y) :
    repPt (fun w => Matrix.of fun i j => y (w.embedding, i, j)) = y ∧
      ∀ w : InfinitePlace L, (Matrix.of fun i j => y (w.embedding, i, j)).det ≠ 0 := by
  refine ⟨?_, fun w => ?_⟩
  · funext p
    obtain ⟨σ, i, j⟩ := p
    simp only [repPt]
    split_ifs with h
    · exact congrArg (fun s => y (s, i, j)) h.symm
    · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
        rcases InfinitePlace.embedding_mk_eq σ with h' | h'
        · exact absurd h'.symm h
        · rw [h']; exact (star_star σ).symm
      obtain ⟨B, hB⟩ := hy (InfinitePlace.mk σ).embedding
      have hYB : (Matrix.of fun i j => y ((InfinitePlace.mk σ).embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
        ext a b; exact (hB a b).1
      rw [hYB, ← Matrix.coe_units_inv]
      conv_rhs => rw [hc]
      exact ((hB i j).2).symm
  · obtain ⟨B, hB⟩ := hy w.embedding
    have hYB : (Matrix.of fun i j => y (w.embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
      ext a b; exact (hB a b).1
    rw [hYB]
    exact (Matrix.isUnits_det_units B).ne_zero

theorem density_second_bound : DensB := by
  intro L _ _ _ n F hF y hy
  obtain ⟨K, P, hP⟩ := hom_exists (L := L) F
  have hG : (∏ w, (1 + Mx (L := L) (n := n) w).det) * P = 0 := by
    apply productFramesDense_holds (InfinitePlace L) n (fun _ => 1) (fun _ => Matrix.PosDef.one)
    intro Y hY
    have hY' : ∀ w, (Y w)ᴴ * Y w = 1 := fun w => by simpa using hY w
    have hdet : ∀ w, (Y w).det ≠ 0 := fun w h0 => by
      have := congrArg Matrix.det (hY' w)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    change eval (coords Y) _ = 0
    rw [map_mul, map_prod]
    simp only [eval_det_one_add_Mx]
    by_cases h1 : ∀ w, (1 + Y w).det ≠ 0
    · rw [← hP Y hdet, hF Y hY' h1]
      simp
    · push Not at h1
      obtain ⟨w, hw⟩ := h1
      rw [Finset.prod_eq_zero (Finset.mem_univ w) hw, zero_mul]
  have hne : (∏ w, (1 + Mx (L := L) (n := n) w).det) ≠ 0 := by
    intro h0
    have := congrArg (eval (coords (fun _ : InfinitePlace L => (0 : Matrix (Fin n) (Fin n) ℂ)))) h0
    rw [map_prod] at this
    simp only [eval_det_one_add_Mx, add_zero, Matrix.det_one, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hP0 : P = 0 := (mul_eq_zero.mp hG).resolve_left hne
  obtain ⟨hYy, hYdet⟩ := repPt_of_InV y hy
  have := hP _ hYdet
  rw [hP0, map_zero, hYy] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun w _ => hYdet w))

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def evM {ι : Type} (P : ι → ι → MvPolynomial (Vars L n) ℂ) (y : Vars L n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval y (P i j)

theorem mult_right (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (z : Vars L n → ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z) =
      evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z)
    (y : Vars L n → ℂ) (hy : InV y) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (z (p.1, k, p.2.2)) * MvPolynomial.X (p.1, p.2.1, k) with hg
  have hv : ∀ y' : Vars L n → ℂ, (fun p => MvPolynomial.eval y' (g p)) = vmul y' z := by
    intro y'
    funext p
    simp [hg, vmul, mul_comm]
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (MvPolynomial.aeval g (P i j) -
      ∑ k, P i k * MvPolynomial.C (MvPolynomial.eval z (P k j))) =
      evM P (vmul y' z) i j - (evM P y' * evM P z) i j := by
    intro y'

    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem mult_left (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (y : Vars L n → ℂ)
    (hrat : ∀ δ₀ ∈ GQ0 L n, evM P (vmul y (ratPt (δ₀ : Matrix (Fin n) (Fin n) L))) =
      evM P y * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (z : Vars L n → ℂ) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (y (p.1, p.2.1, k)) * MvPolynomial.X (p.1, k, p.2.2) with hg
  have hv : ∀ z' : Vars L n → ℂ, (fun p => MvPolynomial.eval z' (g p)) = vmul y z' := by
    intro z'
    funext p
    simp [hg, vmul]
  have hF : ∀ z' : Vars L n → ℂ, MvPolynomial.eval z' (MvPolynomial.aeval g (P i j) -
      ∑ k, MvPolynomial.C (MvPolynomial.eval y (P i k)) * P k j) =
      evM P (vmul y z') i j - (evM P y * evM P z') i j := by
    intro z'

    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun δ₀ hδ => by rw [hF, hrat δ₀ hδ, sub_self]) z hz
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem mult_of_dens (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, ∀ δ₀ ∈ GQ0 L n,
      evM P (ratPt ((γ₀ * δ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (y z : Vars L n → ℂ) (hy : InV y) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  have hl : ∀ γ₀ ∈ GQ0 L n, ∀ z' : Vars L n → ℂ, InV z' →
      evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z') =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z' := by
    intro γ₀ hγ z' hz'
    apply mult_left hd P _ _ z' hz'
    intro δ₀ hδ
    rw [← hrat γ₀ hγ δ₀ hδ]
    congr 1
    funext p

    simp [vmul, ratPt, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  exact mult_right hd P z (fun γ₀ hγ => hl γ₀ hγ z hz) y hy

theorem change_of_dens (hd : DensStep) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (P : ι → ι → MvPolynomial (Vars L n) ℂ) (P' : ι' → ι' → MvPolynomial (Vars L n) ℂ)
    (C : Matrix ι ι' ℂ) (C' : Matrix ι' ι ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) =
      C * evM P' (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * C')
    (y : Vars L n → ℂ) (hy : InV y) : evM P y = C * evM P' y * C' := by
  ext i j
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (P i j -
      ∑ l, ∑ k, MvPolynomial.C (C i k * C' l j) * P' k l) = evM P y' i j - (C * evM P' y' * C') i j := by
    intro y'

    rw [map_sub, map_sum]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, evM, Matrix.of_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

theorem toGQ_mul (γ₀ δ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (hδ : δ₀ ∈ GQ0 L n) :
    toGQ (γ₀ * δ₀) (Subgroup.mul_mem _ hγ hδ) = toGQ γ₀ hγ * toGQ δ₀ hδ := by
  apply Subtype.ext
  apply Subtype.ext
  simp [toGQ, map_mul]

theorem toGQ_surj (γ : GQ L n) : ∃ γ₀ : GL (Fin n) L, ∃ hγ : γ₀ ∈ GQ0 L n, γ = toGQ γ₀ hγ := by
  obtain ⟨g, hg, h⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨g, hg, Subtype.ext (Subtype.ext h.symm)⟩

theorem span_orbit (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (x : a.W)
    (hx : x ≠ 0) :
    Submodule.span ℂ {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} = ⊤ := by
  classical
  set R : Set a.W := Set.range fun γ : GQ L n => a.ρ γ x with hR
  have hT : {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} =
      b.equivFun '' R := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image, hR, Set.mem_range, exists_exists_eq_and]
    have key : ∀ γ : GQ L n, b.equivFun (a.ρ γ x) = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x) := by
      intro γ
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
  have hS : Submodule.span ℂ R = ⊤ := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ (GQ L n)) a.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule a.ρ).1 a.irr
    set m := a.ρ.asModuleEquiv.symm x with hm
    have hm0 : m ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hx
    have htop : Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ((Submodule.span_singleton_eq_bot).not.2 hm0)
    have halg : ∀ r : MonoidAlgebra ℂ (GQ L n), a.ρ.asAlgebraHom r x ∈ Submodule.span ℂ R := by
      intro r
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact add_mem hf hg
      | single g c =>
        rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)
    rw [eq_top_iff]
    intro w _
    have hw : a.ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} := by
      rw [htop]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hw
    have e : w = a.ρ.asAlgebraHom r x := by
      have h2 := congrArg a.ρ.asModuleEquiv hr
      rw [Representation.asModuleEquiv_map_smul, hm, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [e]
    exact halg r
  rw [hT]
  have e2 : (b.equivFun : a.W → (ι → ℂ)) '' R = (b.equivFun.toLinearMap : a.W →ₗ[ℂ] (ι → ℂ)) '' R := rfl
  rw [e2, Submodule.span_image, hS, Submodule.map_top, LinearMap.range_eq_top]
  exact b.equivFun.surjective

end

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
