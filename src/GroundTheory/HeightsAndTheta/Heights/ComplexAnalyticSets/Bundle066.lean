module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import Mathlib.RingTheory.Localization.Away.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
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
import Mathlib.RingTheory.LocalProperties.Reduced
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SliceBundleRadicalAway

variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk J (X k - C (q k)))

def toBase : MvPolynomial (Fin n) ℂ →+* Base J q k :=
  (algebraMap _ (Base J q k)).comp (Ideal.Quotient.mk J)

def rowForm (i : Fin d) : MvPolynomial (Fin d × Fin n) (Base J q k) :=
  ∑ j, X (i, j) * C (toBase J q k (X j - C (q j)))

def coeffMap : MvPolynomial (Fin d × Fin n) ℂ →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (C.comp ((toBase J q k).comp C)) fun ij =>
    X ij - if ij.2 = k then
      C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k ij.1
    else 0

def solveMap :
    MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (coeffMap J d q k) fun j => C (toBase J q k (X j))

abbrev Quo := MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) ⧸ universalSliceIdeal J d q

instance instCommRingQuo : CommRing (Quo J d q) := Ideal.Quotient.commRing _

def uQuo : Quo J d q :=
  algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) (X k - C (C (q k)))

abbrev Tot := Localization.Away (uQuo J d q k)

def toTot : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* Tot J d q k :=
  algebraMap _ _

theorem toTot_apply (x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :
    toTot J d q k x = algebraMap (Quo J d q) (Tot J d q k)
      (algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) x) :=
  IsScalarTower.algebraMap_apply _ _ _ x

theorem toTot_eq_zero {x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)}
    (hx : x ∈ universalSliceIdeal J d q) : toTot J d q k x = 0 := by
  rw [toTot_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

def quotToTot : (MvPolynomial (Fin n) ℂ ⧸ J) →+* Tot J d q k :=
  Ideal.Quotient.lift J ((toTot J d q k).comp (MvPolynomial.map C)) fun a ha =>
    toTot_eq_zero J d q k (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

theorem quotToTot_isUnit : IsUnit (quotToTot J d q k (Ideal.Quotient.mk J (X k - C (q k)))) := by
  have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X k - C (q k)) =
      X k - C (C (q k)) := by simp
  rw [quotToTot, Ideal.Quotient.lift_mk, RingHom.comp_apply, e, toTot_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := Tot J d q k) (uQuo J d q k)

def baseToTot : Base J q k →+* Tot J d q k :=
  IsLocalization.Away.lift (R := MvPolynomial (Fin n) ℂ ⧸ J) (S := Base J q k) (P := Tot J d q k)
    (Ideal.Quotient.mk J (X k - C (q k))) (g := quotToTot J d q k) (quotToTot_isUnit J d q k)

theorem baseToTot_toBase (a : MvPolynomial (Fin n) ℂ) :
    baseToTot J d q k (toBase J q k a) = toTot J d q k (MvPolynomial.map C a) := by
  simp [baseToTot, toBase, quotToTot]

def backMap : MvPolynomial (Fin d × Fin n) (Base J q k) →+* Tot J d q k :=
  eval₂Hom (baseToTot J d q k) fun ij => toTot J d q k (C (X ij))

theorem backMap_rowForm (i : Fin d) : backMap J d q k (rowForm J d q k i) = 0 := by

  simp only [rowForm, map_sum, map_mul, backMap, eval₂Hom_X', eval₂Hom_C, baseToTot_toBase]
  rw [← toTot_eq_zero J d q k (x := ∑ j, C (X (i, j)) * (X j - C (C (q j))))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))]

  simp [map_sum, map_mul, map_sub]

theorem backMap_comp_solveMap : (backMap J d q k).comp (solveMap J d q k) = toTot J d q k := by
  have hc : (backMap J d q k).comp (coeffMap J d q k) = (toTot J d q k).comp C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coeffMap, backMap, baseToTot_toBase]
    · intro ij
      simp only [RingHom.comp_apply, coeffMap, eval₂Hom_X', map_sub]
      split_ifs
      · rw [map_mul, backMap_rowForm, mul_zero, sub_zero]
        simp [backMap]
      · simp [backMap]
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [solveMap] using RingHom.congr_fun hc a
  · intro j
    simp [solveMap, backMap, baseToTot_toBase]

theorem coeffMap_comp_mapC :
    (solveMap J d q k).comp (MvPolynomial.map C) = C.comp (toBase J q k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [solveMap, coeffMap]
  · intro j
    simp [solveMap]

theorem solveMap_gen (i : Fin d) :
    solveMap J d q k (∑ j, C (X (i, j)) * (X j - C (C (q j)))) = 0 := by
  have h : ∀ j, solveMap J d q k (C (X (i, j)) * (X j - C (C (q j)))) =
      (X (i, j) - if j = k then
        C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k i
      else 0) * C (toBase J q k (X j - C (q j))) := by
    intro j
    have := RingHom.congr_fun (coeffMap_comp_mapC J d q k) (X j - C (q j))
    have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X j - C (q j)) =
        X j - C (C (q j)) := by simp
    rw [RingHom.comp_apply, RingHom.comp_apply, e] at this
    rw [map_mul, this]
    congr 1
    rw [solveMap, eval₂Hom_C, coeffMap, eval₂Hom_X']

  rw [map_sum, Finset.sum_congr rfl fun j _ => h j]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← rowForm, mul_assoc, mul_comm (rowForm J d q k i), ← mul_assoc, ← map_mul]
  have hu : IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k))) *
      toBase J q k (X k - C (q k)) = (1 : Base J q k) := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (S := Base J q k) (Ideal.Quotient.mk J (X k - C (q k)))
  rw [hu, map_one, one_mul, sub_self]

theorem le_ker_solveMap : universalSliceIdeal J d q ≤ RingHom.ker (solveMap J d q k) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, coeffMap_comp_mapC]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact solveMap_gen J d q k i

end SliceBundleRadicalAway

theorem SliceBundleRadicalAway.proof : SliceBundleRadicalAway.Statement := by
  intro n d J q hJ k f hf
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  obtain ⟨m, hm⟩ := hf
  have h0 : SliceBundleRadicalAway.solveMap J d q k f = 0 := by
    apply IsNilpotent.eq_zero
    exact ⟨m, by rw [← map_pow]; exact SliceBundleRadicalAway.le_ker_solveMap J d q k hm⟩
  have h1 : SliceBundleRadicalAway.toTot J d q k f = 0 := by
    rw [← SliceBundleRadicalAway.backMap_comp_solveMap J d q k, RingHom.comp_apply, h0, map_zero]
  rw [SliceBundleRadicalAway.toTot_apply] at h1
  obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (SliceBundleRadicalAway.uQuo J d q k)) (SliceBundleRadicalAway.Tot J d q k) _).1 h1
  refine ⟨e, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
  exact he

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n d : ℕ}

theorem isHomogeneous_leadIdeal_sup_linIdeal (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
  · rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩

theorem monomial_mem_originIdeal_pow {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by
  have hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i :=
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]
  rw [← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow
    (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _

theorem originIdeal_pow_le_span (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by
  induction N with
  | zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
            exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [originIdeal, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩

theorem originIdeal_pow_le {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by
  refine (originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm

theorem isZariskiOpen_of_local {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by
  refine ⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ,
    eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩
  ext A
  constructor
  · intro hA
    obtain ⟨p, hp, hpU⟩ := H A hA
    exact ⟨p, hpU, hp⟩
  · rintro ⟨p, hpU, hp⟩
    exact hpU A hp

theorem ConeAvoidsOpen.proof : ConeAvoidsOpen.Statement := by
  intro n d N J
  classical
  refine isZariskiOpen_of_local fun A₀ hA₀ => ?_
  set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N
  have hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N := fun m => by
    simp [V, Finsupp.degree_eq_sum]
  have hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ,
      a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))
    obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    exact ⟨a, ha, h, hab⟩
  choose a ha h hah using hrep
  let T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ :=
    fun A m => a m + ∑ j, h m j * linPoly A j
  let P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ) := fun m' m =>
    C (AddMonoidAlgebra.coeff (a m) (m' : Fin n →₀ ℕ)) +
      ∑ j, ∑ k, C (AddMonoidAlgebra.coeff (h m j * X k) (m' : Fin n →₀ ℕ)) * X (j, k)
  have hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V),
      (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m =
        AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := by
    intro A m' m
    show eval _ (P m' m) = _

    simp only [P, T, linPoly, map_add (f := _), map_sum, map_mul, eval_C, eval_X, MvPolynomial.coeff_add, coeff_sum,
    Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, coeff_C_mul, mul_comm]
  refine ⟨P.det, ?_, fun A hA => ?_⟩
  · rw [RingHom.map_det]
    have h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1 := by
      ext m' m
      rw [hP, Matrix.one_apply]
      simp only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · rw [RingHom.map_det] at hA
    set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P
    have hMT : ∀ m' m : V, M m' m = AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := hP A
    have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)
    have hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A := fun m =>
      Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)
    have hhom := isHomogeneous_leadIdeal_sup_linIdeal J A
    refine originIdeal_pow_le fun m hm => ?_
    have key : monomial m (1 : ℂ) =
        ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'') := by
      ext s
      simp only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]
      by_cases hs : s.degree = N
      · have e := congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩
        simp only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e
        simp only [hs, if_true]
        simp_rw [mul_comm (M⁻¹ _ _)]
        rw [e]
        by_cases hsm : s = m
        · simp [hsm]
        · simp [hsm, Ne.symm hsm]
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl
        exact hs hm
    rw [key]
    exact Ideal.sum_mem _ fun m'' _ =>
      Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by
  have hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) =
        homogeneousComponent i p := fun p i => decomposition.decompose'_apply p i
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a)
    ((mem_homogeneousSubmodule e g).2 hg)
  simpa only [hd] using h

theorem isHomogeneous_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (linPoly A j).IsHomogeneous 1 := by
  have : linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))
  exact (mem_homogeneousSubmodule 1 _).1 this

theorem ConeAvoidsFinite.proof : ConeAvoidsFinite.Statement := by
  intro n d N J A hcone
  letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule
  show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
  classical
  let gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J) := Finset.univ.image fun f : Fin n → Fin N =>
    Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)
  let M := Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))
  set_option synthInstance.maxHeartbeats 100000 in
  have hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ),
      Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M := by
    intro s p hp
    have : Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]; rfl
    rw [this]; exact M.smul_mem s hp
  have hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ),
      (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M :=
    fun s q h => by rw [map_sum]; exact M.sum_mem h
  have hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>

    have key : ∀ (b x : MvPolynomial (Fin n) ℂ),
        x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) →
        Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M := by
      rintro b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree)
          (homogeneousComponent_isHomogeneous f.totalDegree f)]
        split_ifs with hek
        · have hs := sum_homogeneousComponent f
          rw [Finset.sum_range_succ] at hs
          have hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f := by
            rw [leadForm]; linear_combination hs
          rw [hf', mul_sub, map_sub, Finset.mul_sum,
            Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]
          refine M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _
            ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))
          have := Finset.mem_range.1 hi; omega
        · simp
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)]
        split_ifs with hk
        · have hl : linPoly A j = pullback A (X j) := by simp [pullback]
          rw [mul_comm, hl]
          exact hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))
        · simp

    intro q hq
    rw [q.as_sum]
    refine hsum _ _ fun s hs => ?_
    have hdeg : s.degree = k := by
      have := hq (mem_support_iff.mp hs)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have hCs : monomial s (AddMonoidAlgebra.coeff q s) = pullback A (C (AddMonoidAlgebra.coeff q s)) * monomial s 1 := by
      simp [pullback, C_mul_monomial]
    rw [hCs]
    refine hsmul _ _ ?_
    by_cases hlow : ∀ i, s i < N
    · refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))
      congr 2; ext i; simp
    simp only [not_forall, not_lt] at hlow
    obtain ⟨i, hi⟩ := hlow

    have hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A := by
      apply hcone
      have hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1 := by
        rw [← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
      rw [hsplit]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)
    rw [leadIdeal, linIdeal, ← Ideal.span_union] at hmem
    obtain ⟨r, a, g, hag⟩ := Submodule.mem_span_set'.1 hmem
    have hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ)) := by
      rw [hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    exact hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sum_homogeneousComponent p]
    exact hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)
  exact ⟨⟨gen, htop⟩⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end
