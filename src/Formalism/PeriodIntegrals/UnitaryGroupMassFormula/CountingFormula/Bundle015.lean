module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle010
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hermP (D : Formalism.BasicNotions.D7) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  (alM D x).conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * alM D x

private theorem fr_sub_eq_sum_hypE_of_good_of_pWf_eq (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) (b : Fin (D.R.rS + 1)) :
    fr D x b - fr D y b = ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) • D.sp.hypE c := by
  have hE : ∀ c, (VS D).hT (D.sp.hypE c) (fr D x b - fr D y b) = 0 := by
    intro c
    have h1 := hx.2.1 (Fin.castSucc c) b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZ : (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
    obtain ⟨c0, hc0, hz⟩ := hF.2.2.2.2
    have h1 := hx.2.1 (Fin.last _) b
    have h2 := hy.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    have h3 : (starRingEnd D.host.E) c0 * (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
      rw [map_sub, mul_sub, h1, h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd ((map_eq_zero _).1 h) hc0
    · exact h
  have hP : pW D (fr D x b - fr D y b) = 0 := by
    have h := congrFun hw b
    simp only [pWf] at h
    rw [pW_eq, map_sub, ← pW_eq, ← pW_eq, h, sub_self]
  have h := hP
  simp only [pW, hE, hZ, zero_smul, Finset.sum_const_zero, sub_zero, zero_div, add_zero] at h
  exact sub_eq_zero.1 h

theorem hermitianDivisible_eq_smul (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) : hermP D Z x = hermP D Z y := by
  have hd := fun b => fr_sub_eq_sum_hypE_of_good_of_pWf_eq D T' F0 Λ hF Z hx hy hw b
  have hβ : ∀ c b, (VS D).hT (D.sp.hypE c) (fr D y b) = betaZ D Z c b := by
    intro c b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h2
    simp only [betaZ, Matrix.submatrix_apply, id, h2]
  have hβ' : ∀ c a, (VS D).hT (fr D y a) (D.sp.hypE c) = star (betaZ D Z c a) := by
    intro c a
    rw [← hβ, hT_star]
  have hα : ∀ c b, alM D x c b = alM D y c b + (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) := by
    intro c b
    simp only [alM, map_sub]
    ring
  have hee : ∀ i j, (VS D).hT (D.sp.hypE i) (D.sp.hypE j) = 0 := fun i j => D.sp.hyp_ee i j
  have key : ∀ a b, ∑ c, star ((VS D).hT (D.sp.hypF c) (fr D x a - fr D y a)) * betaZ D Z c b +
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) = 0 := by
    intro a b
    have hxx := hx.2.2 a b
    rw [← hy.2.2 a b] at hxx
    have ex : ∀ a, fr D x a = fr D y a + ∑ c, (VS D).hT (D.sp.hypF c) (fr D x a - fr D y a) • D.sp.hypE c := by
      intro a
      rw [← hd a]
      abel
    rw [ex a, ex b] at hxx

    simp only [map_add (f := _), map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, hee, mul_zero,
    Finset.sum_const_zero, add_zero, hβ, hβ', starRingEnd_apply] at hxx
    linear_combination hxx
  ext a b
  simp only [hermP, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hα, star_add,
    add_mul, mul_add, Finset.sum_add_distrib]
  have k2 : ∑ c, star (betaZ D Z c a) * (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) =
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linear_combination key a b + k2

private theorem exists_nat_mul_alM_mul_isIntegral_of_fr_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : (Fin D.R.rS → (VS D).V) × (VS D).V, (∀ b, fr D x b ∈ Λ) →
      ∀ i j, IsIntegral ℤ ((N : D.host.E) * (alM D x * R) i j) := by
  obtain ⟨g, hg⟩ := hF.1.fg
  obtain ⟨N1, hN1, h1⟩ := commonDen (K := D.host.E)
    (Finset.image (fun p : Fin D.R.rS × (VS D).V => (VS D).hT (D.sp.hypF p.1) p.2)
      (Finset.univ ×ˢ g) ∪
     Finset.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) Finset.univ)
  have hv : ∀ v ∈ Λ, ∀ c, IsIntegral ℤ ((N1 : D.host.E) * (VS D).hT (D.sp.hypF c) v) := by
    intro v hv c
    rw [← hg] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      exact h1 _ (Finset.mem_union_left _ (Finset.mem_image.2
        ⟨(c, y), Finset.mem_product.2 ⟨Finset.mem_univ _, by exact_mod_cast hy⟩, rfl⟩))
    | zero =>
      rw [map_zero, mul_zero]
      exact isIntegral_zero
    | add y z _ _ hy hz =>
      rw [map_add (f := _), mul_add]
      exact hy.add hz
    | smul o y _ hy =>
      rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, mul_left_comm]
      exact (isInt_O o).mul hy
  refine ⟨N1 * N1, Nat.mul_pos hN1 hN1, fun x hx i j => ?_⟩
  rw [Matrix.mul_apply, Nat.cast_mul, Finset.mul_sum]
  refine IsIntegral.sum _ (fun b _ => ?_)
  have e : (N1 : D.host.E) * N1 * (alM D x i b * R b j) =
      ((N1 : D.host.E) * alM D x i b) * ((N1 : D.host.E) * R b j) := by ring
  rw [e]
  exact (hv _ (hx b) i).mul (h1 _ (Finset.mem_union_right _ (Finset.mem_image.2
    ⟨(b, j), Finset.mem_univ _, rfl⟩)))

theorem orbit_count_second_stage : Stage2 := by
  intro D T T' F0 Λ hF Z R hR Wf hWf
  obtain ⟨N, hN, hden⟩ := exists_nat_mul_alM_mul_isIntegral_of_fr_mem D F0 Λ hF R
  obtain ⟨Rep, hRepF, hRepI, hrep⟩ := reduceRep (K := D.host.E) (4 * N) (by omega)
  let hfun : (Fin (D.R.rS + 1) → (VS D).V) → Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun w =>
    if h : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = w then R.conjTranspose * hermP D Z h.choose * R else 0
  refine ⟨(fun q : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E × (Fin D.R.rS → Fin D.R.rS → D.host.E) =>
      Matrix.of fun i j => q.1 i j / 2 + (q.2 i j - star (q.2 j i)) / 4) ''
      ((hfun '' Wf) ×ˢ Set.pi Set.univ
        (fun _ => Set.pi Set.univ (fun _ => (fun ρ => ρ / (N : D.host.E)) '' Rep))), ?_, ?_⟩
  · exact ((hWf.image _).prod (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hRepF.image _)).image _
  intro x hx hxw
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ i j, IsIntegral ℤ ((N : D.host.E) *
      ((alM D x * R) i j - star ((alM D x * R) j i))) := by
    intro i j
    rw [mul_sub]
    refine (hden x hx.1 i j).sub ?_
    have h := isInt_star (hden x hx.1 j i)
    rw [star_mul', star_natCast] at h
    exact h
  choose t ρ ht hρ heq using fun i j => hrep _ (hint i j)
  have hrel : ∀ i j, (alM D x * R) i j - star ((alM D x * R) j i) = 4 * t i j + ρ i j / N := by
    intro i j
    have h := heq i j
    push_cast at h
    have h' : (alM D x * R) i j - star ((alM D x * R) j i) - 4 * t i j = ρ i j / N := by
      rw [eq_div_iff hN0]
      linear_combination h
    linear_combination h'
  let S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := Matrix.of fun i j => star (t j i) - t i j
  have hSskew : ∀ i j, star (S j i) = -S i j := by
    intro i j
    simp only [S, Matrix.of_apply, star_sub, star_star, neg_sub]
  have hSint : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j :=
    fun i j => O_of_isInt ((isInt_star (ht j i)).sub (ht i j))
  refine ⟨skE D S, skE_mem D F0 Λ hF S hSskew hSint, pWf_skE D S x, ?_⟩
  rw [alM_skE D T' F0 Λ hF Z S hx, Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one]
  have e1 : R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = (alM D x * R).conjTranspose := by
    calc R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = R.conjTranspose * (alM D x).conjTranspose * (betaZ D Z * R) := by
          simp only [Matrix.mul_assoc]
      _ = (alM D x * R).conjTranspose := by rw [hR, Matrix.mul_one, Matrix.conjTranspose_mul]
  have e2 : R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = alM D x * R := by
    calc R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = (R.conjTranspose * (betaZ D Z).conjTranspose) * (alM D x * R) := by
          simp only [Matrix.mul_assoc]
      _ = alM D x * R := by
          rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one, Matrix.one_mul]
  have hH : R.conjTranspose * hermP D Z x * R = alM D x * R + (alM D x * R).conjTranspose := by
    rw [hermP, Matrix.mul_add, Matrix.add_mul, e1, e2, add_comm]
  have hfx : hfun (pWf D x) = alM D x * R + (alM D x * R).conjTranspose := by
    have hex : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = pWf D x := ⟨x, hx, rfl⟩
    simp only [hfun, dif_pos hex]
    rw [hermitianDivisible_eq_smul D T' F0 Λ hF Z hex.choose_spec.1 hx hex.choose_spec.2, hH]
  refine ⟨(alM D x * R + (alM D x * R).conjTranspose, fun i j => ρ i j / N),
    ⟨⟨pWf D x, hxw, hfx⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    exact ⟨ρ i j, hρ i j, rfl⟩
  · ext i j
    have h1 := hrel i j
    have h2 := congrArg star (hrel j i)
    simp only [star_sub, star_add, star_mul', star_star, star_div₀, star_natCast, star_ofNat] at h2
    simp only [S, Matrix.of_apply, Matrix.add_apply, Matrix.conjTranspose_apply, star_div₀,
      star_natCast]
    linear_combination (-1 / 4 : D.host.E) * h1 + (1 / 4 : D.host.E) * h2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

open Matrix Polynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Generic

variable {K : Type*} [Field K]

theorem adjugate_last (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem det_sub_single (r : ℕ) (W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (W - single (Fin.last r) (Fin.last r) c).det =
      W.det - c * W.adjugate (Fin.last r) (Fin.last r) := by
  have hrow : W - single (Fin.last r) (Fin.last r) c =
      W.updateRow (Fin.last r) (W (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.updateRow_apply, Matrix.single_apply, Pi.add_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [sub_eq_add_neg]
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← Matrix.adjugate_apply]
  ring

theorem det_blocks_of_ne (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) (hZ : Z.det ≠ 0) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det = Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  haveI := Z.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hZ)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.single_mul_mul_single,
    det_sub_single, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  field_simp

theorem single_map {L M : Type*} [Ring L] [Ring M] (f : L →+* M) (r : ℕ) (c : L) :
    (single (Fin.last r) (Fin.last r) c).map f = single (Fin.last r) (Fin.last r) (f c) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

private theorem blocks_map_lemma {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (a b : R) :
    f ((fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det -
      (Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r))) =
    (fromBlocks (Z.map f) (single (Fin.last r) (Fin.last r) (f a))
        (single (Fin.last r) (Fin.last r) (f b)) (W.map f)).det -
      ((Z.map f).det * (W.map f).det - f a * f b * (Z.map f).adjugate (Fin.last r) (Fin.last r) *
        (W.map f).adjugate (Fin.last r) (Fin.last r)) := by
  have hdet : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R, f M.det = (M.map f).det := fun M =>
    RingHom.map_det f M
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R,
      f (M.adjugate (Fin.last r) (Fin.last r)) = (M.map f).adjugate (Fin.last r) (Fin.last r) := by
    intro M
    rw [show M.map f = f.mapMatrix M from rfl, ← RingHom.map_adjugate]
    rfl
  simp only [map_sub, map_mul, hdet, hadj]
  rw [RingHom.map_det f, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, single_map, single_map]

theorem det_blocks (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det =
      Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] (FractionRing K[X])
  have hdet : ((charmatrix (-Z)).map φ).det ≠ 0 := by
    have h1 : φ (charmatrix (-Z)).det ≠ 0 := fun h =>
      (Matrix.charpoly_monic (-Z)).ne_zero (hφ (h.trans (map_zero φ).symm))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  have key := det_blocks_of_ne r ((charmatrix (-Z)).map φ) ((W.map Polynomial.C).map φ)
    (φ (Polynomial.C a)) (φ (Polynomial.C b)) hdet
  have hX : (fromBlocks (charmatrix (-Z)) (single (Fin.last r) (Fin.last r) (Polynomial.C a))
      (single (Fin.last r) (Fin.last r) (Polynomial.C b)) (W.map Polynomial.C)).det -
      ((charmatrix (-Z)).det * (W.map Polynomial.C).det - Polynomial.C a * Polynomial.C b *
        (charmatrix (-Z)).adjugate (Fin.last r) (Fin.last r) *
        (W.map Polynomial.C).adjugate (Fin.last r) (Fin.last r)) = 0 := by
    apply hφ
    rw [blocks_map_lemma, map_zero, key, sub_self]
  have h0 := congrArg (Polynomial.evalRingHom (0 : K)) hX
  rw [blocks_map_lemma, map_zero] at h0
  have hZ0 : (charmatrix (-Z)).map (Polynomial.evalRingHom (0 : K)) = Z := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.charmatrix_apply_eq]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h]
  have hW0 : (W.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = W := by
    ext i j; simp
  rw [hZ0, hW0] at h0
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h0
  exact sub_eq_zero.mp h0

end Generic

theorem det_swap {K : Type*} [Field K] (n : ℕ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (0 : Matrix (Fin n) (Fin n) K)).det = (-1) ^ n := by
  have hN : (fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    simp [Matrix.det_fromBlocks_zero₁₂]
  have hMN : fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) * fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) := by
    simp [Matrix.fromBlocks_multiply]
  have h := congrArg Matrix.det hMN
  rw [Matrix.det_mul, hN, mul_one, Matrix.det_fromBlocks_one₁₁] at h
  rw [h]
  simp [Matrix.det_neg]

open Formalism.L2.SG.CntLocal Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem leadMinorE_r (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) := by
  rw [adjugate_last]
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ _)]
  rfl

theorem gram_determinant_formula_alt : DetGa := by
  intro D T T' _ _ Z
  have hA : ∀ c : D.host.E, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0) =
      single (Fin.last D.R.rS) (Fin.last D.R.rS) c := by
    intro c
    ext a b
    by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;>
      simp_all [Matrix.single_apply, eq_comm]
  have hprod : Ga T T' Z * fromBlocks (0 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) 1 1 0 =
      fromBlocks Z (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T))
        (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T')) Zᴴ := by
    unfold Ga
    rw [hA, hA, Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_mul, det_swap, det_blocks, Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose,
    Matrix.conjTranspose_apply] at h
  unfold GZ
  rw [leadMinorE_full, leadMinorE_r]
  have hsq : ((-1 : D.host.E) ^ (D.R.rS + 1)) * (-1) ^ (D.R.rS + 1) = 1 := by
    rw [← mul_pow]; simp
  calc (Ga T T' Z).det = (Ga T T' Z).det * ((-1) ^ (D.R.rS + 1) * (-1) ^ (D.R.rS + 1)) := by
        rw [hsq, mul_one]
    _ = (-1) ^ (D.R.rS + 1) * ((Ga T T' Z).det * (-1) ^ (D.R.rS + 1)) := by ring
    _ = _ := by rw [h]; ring

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section

open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

def JordanExists : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a

def DetLocal : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K), IsFixF K F →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    ∀ (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F), 𝔭.IsMaximal →
      IsJordanIn h X (pbLat x 𝔞) 𝔭 b a →
      ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          FractionalIdeal.count K P
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((a j : 𝓞 F) : F))))

def CountExt : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K] (n : ℕ)
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : Fin n → 𝓞 F), 𝔭.IsMaximal →
    P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 → (∀ j, α j ≠ 0) →
    FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((α j : 𝓞 F) : F)))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * ∑ j, vF 𝔭 (α j) : ℕ) : ℤ)

def NormAssembly : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (w : Ideal (𝓞 F) → ℕ), J ≠ 0 →
    (∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P J = ((P.asIdeal.ramificationIdx (𝓞 F) * w 𝔭 : ℕ) : ℤ)) →
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) ^ 2 =
      (FractionalIdeal.absNorm J : ℝ)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
