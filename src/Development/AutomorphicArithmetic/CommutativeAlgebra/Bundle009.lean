module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle195
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorOfRootSubsetProductEquation
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootSubsetProductEquationOfHenselianReduct
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001

@[expose] public section

section

noncomputable section
open IsLocalRing UpperTheory.Et

private lemma UpperTheory.eval_zero_pderiv {R : Type} [CommRing R] {n : ℕ} (j : Fin n)
    (P : MvPolynomial (Fin n) R) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv j P) = AddMonoidAlgebra.coeff P (Finsupp.single j 1) := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = Finsupp.single j 1
    · subst hs
      simp
    · rw [if_neg hs]
      split_ifs with h
      · by_cases hsj : s j = 0
        · simp [hsj]
        · exfalso
          apply hs
          ext k
          have hk := DFunLike.congr_fun h k
          by_cases hkj : k = j
          · subst hkj
            simp at hk ⊢
            omega
          · simp [Finsupp.single_apply, hkj, Ne.symm hkj] at hk ⊢
            exact hk
      · rfl
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

theorem UpperTheory.exists_zero_of_linear_form_jacobian_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] (n : ℕ) (Φ : MvPolynomial (Fin n) E) (L : E →ₗ[A] (Fin n → A)),
      (∀ i, L (MvPolynomial.eval 0 Φ) i ∈ maximalIdeal A) →
      (∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ maximalIdeal A) →
      ∃ x : Fin n → A, (∀ j, x j ∈ maximalIdeal A) ∧ L (MvPolynomial.eval (fun j => algebraMap A E (x j)) Φ) = 0 := by
  intro A E _ _ _ _ n Φ L h0 h1
  let G : Fin n → MvPolynomial (Fin n) E → MvPolynomial (Fin n) A := fun i P =>
    ∑ d ∈ P.support, MvPolynomial.monomial d (L (AddMonoidAlgebra.coeff P d) i)
  have hG : ∀ i d P, AddMonoidAlgebra.coeff (G i P) d = L (AddMonoidAlgebra.coeff P d) i := by
    intro i d P
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [MvPolynomial.mem_support_iff, not_not] at h
      simp [h]
  have hGadd : ∀ i p q, G i (p + q) = G i p + G i q := by
    intro i p q
    ext d
    rw [MvPolynomial.coeff_add, hG, hG, hG, MvPolynomial.coeff_add, map_add (f := _), Pi.add_apply]
  have key : ∀ i (x : Fin n → A) (P : MvPolynomial (Fin n) E),
      MvPolynomial.eval x (G i P) = L (MvPolynomial.eval (fun j => algebraMap A E (x j)) P) i := by
    intro i x P
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      have hm : G i (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c i) := by
        ext d'
        rw [hG, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
        split_ifs <;> simp
      rw [hm, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      have hp : (d.prod fun k e => (algebraMap A E (x k)) ^ e) = algebraMap A E (d.prod fun k e => x k ^ e) := by
        simp [Finsupp.prod, map_prod, map_pow]
      rw [hp, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
      simp [mul_comm]
    | add p q hp hq =>
      rw [hGadd, map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  let F : Fin n → MvPolynomial (Fin n) A := fun i => G i Φ
  have hF0 : ∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A := by
    intro i
    have h := key i 0 Φ
    have e : (fun j => algebraMap A E ((0 : Fin n → A) j)) = 0 := by
      ext
      simp
    rw [e] at h
    show MvPolynomial.eval 0 (G i Φ) ∈ maximalIdeal A
    rw [h]
    exact h0 i
  have hF1 : ∀ i j, MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)) =
      L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i := by
    intro i j
    rw [UpperTheory.eval_zero_pderiv, UpperTheory.eval_zero_pderiv]
    exact hG i _ Φ
  have hdet : IsUnit (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
    have hM : (residue A).mapMatrix (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))) = 1 := by
      ext i j
      have h := (residue_eq_zero_iff _).mpr (h1 i j)
      rw [map_sub, sub_eq_zero] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hF1, h, Matrix.one_apply]
      split_ifs <;> simp
    by_contra hu
    have hm := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    have h := (residue_eq_zero_iff _).mpr hm
    rw [RingHom.map_det, hM, Matrix.det_one] at h
    exact one_ne_zero h
  obtain ⟨x, hx, hxm⟩ := UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian A n F hF0 hdet
  refine ⟨x, hxm, ?_⟩
  funext i
  rw [← key i x Φ]
  exact hx i

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.ProductProjectionSubgroup

variable {S : Scheme.{0}}

private noncomputable def pr1 (Y G : Over S) : (Y ⊗ G).left ⟶ Y.left := pullback.fst Y.hom G.hom

private noncomputable def pr2 (Y G : Over S) : (Y ⊗ G).left ⟶ G.left := pullback.snd Y.hom G.hom

private theorem pr_cond (Y G : Over S) : pr1 Y G ≫ Y.hom = pr2 Y G ≫ G.hom := pullback.condition

private theorem pr_ext {Y G : Over S} {Z : Scheme.{0}} {f f' : Z ⟶ (Y ⊗ G).left}
    (h₁ : f ≫ pr1 Y G = f' ≫ pr1 Y G) (h₂ : f ≫ pr2 Y G = f' ≫ pr2 Y G) : f = f' :=
  pullback.hom_ext h₁ h₂

private theorem lift_comp_pr1 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr1 Y G = t.left :=
  pullback.lift_fst t.left a.left (by rw [Over.w t, Over.w a])

private theorem lift_comp_pr2 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr2 Y G = a.left :=
  pullback.lift_snd t.left a.left (by rw [Over.w t, Over.w a])

private noncomputable abbrev subH {Y G : Over S} (U : (Y ⊗ G).left.Opens) : Over Y.left :=
  Over.mk (U.ι ≫ pr1 Y G)

private theorem sub_sq {Y A G : Over S} (inc : G ⟶ A) (U : (Y ⊗ G).left.Opens) :
    (U.ι ≫ pr2 Y G ≫ inc.left) ≫ A.hom = (U.ι ≫ pr1 Y G) ≫ Y.hom := by
  simp only [Category.assoc, Over.w inc, pr_cond]

variable {Y A G : Over S} [GrpObj A] [GrpObj G] {A₀ : Over Y.left} [GrpObj A₀]
  {φ₀ : A₀.left ⟶ A.left}

private noncomputable def subJ (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : subH U ⟶ A₀ :=
  Over.homMk (hP.1.lift (U.ι ≫ pr2 Y G ≫ inc.left) (U.ι ≫ pr1 Y G) (sub_sq inc U))
    (hP.1.lift_snd _ _ _)

private theorem subJ_fst (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ φ₀ = U.ι ≫ pr2 Y G ≫ inc.left :=
  hP.1.lift_fst _ _ _

private theorem subJ_snd (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ A₀.hom = U.ι ≫ pr1 Y G :=
  hP.1.lift_snd _ _ _

private theorem subJ_mono (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [Mono inc.left]
    (U : (Y ⊗ G).left.Opens) : Mono (subJ hP inc U) := by
  have : Mono (subJ hP inc U).left := by
    constructor
    intro Z x y e
    rw [← cancel_mono U.ι]
    apply pr_ext
    · have := congrArg (· ≫ A₀.hom) e
      simpa only [Category.assoc, subJ_snd] using this
    · rw [← cancel_mono inc.left]
      have := congrArg (· ≫ φ₀) e
      simpa only [Category.assoc, subJ_fst] using this
  exact Over.mono_of_mono_left _

private theorem subJ_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀) :
    (∃ h : Over.mk t.left ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  constructor
  · rintro ⟨h, rfl⟩
    have hh : h.left ≫ U.ι ≫ pr1 Y G = t.left := Over.w h
    have e : (h.left ≫ U.ι ≫ pr2 Y G) ≫ G.hom = T'.hom := by
      have e' : (h.left ≫ U.ι ≫ pr1 Y G) ≫ Y.hom = T'.hom := by rw [hh, Over.w t]
      simpa only [Category.assoc, pr_cond] using e'
    refine ⟨Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e, ?_, ?_⟩
    · show (h.left ≫ U.ι ≫ pr2 Y G) ≫ inc.left = (h ≫ subJ hP inc U).left ≫ φ₀
      simp only [Over.comp_left, Category.assoc, subJ_fst]
    · have : (lift t (Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e)).left = h.left ≫ U.ι := by
        apply pr_ext
        · rw [lift_comp_pr1, Category.assoc, hh]
        · rw [lift_comp_pr2]
          simp only [Category.assoc, Over.homMk_left]
      rw [this]
      rintro _ ⟨x, rfl⟩
      show _ ∈ (U : Set (Y ⊗ G).left)
      rw [← U.range_ι]
      exact ⟨h.left x, by simp⟩
  · rintro ⟨a, ha, hr⟩
    have hr' : Set.range (lift t a).left ⊆ Set.range U.ι := by
      rw [U.range_ι]; exact hr
    let s := IsOpenImmersion.lift U.ι (lift t a).left hr'
    have hs : s ≫ U.ι = (lift t a).left := IsOpenImmersion.lift_fac _ _ _
    have h1 : s ≫ U.ι ≫ pr1 Y G = t.left := by
      rw [← Category.assoc, hs, lift_comp_pr1]
    refine ⟨Over.homMk s h1, ?_⟩
    apply SubRep.pull_ext hP
    show (s ≫ (subJ hP inc U).left) ≫ φ₀ = _
    rw [Category.assoc, subJ_fst, ← ha, ← Category.assoc, ← Category.assoc, hs, lift_comp_pr2]

private theorem fac_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (K : Over Y.left) (g : K ⟶ A₀) :
    (∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : Over.mk (K.hom ≫ Y.hom) ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧
        Set.range (lift (Over.homMk K.hom : Over.mk (K.hom ≫ Y.hom) ⟶ Y) a).left ⊆ U :=
  subJ_iff hP inc U (Over.mk (K.hom ≫ Y.hom)) (Over.homMk K.hom) g

private theorem fac_one (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = 1 := by
  refine (fac_iff hP inc U K 1).2 ⟨1, ?_, (hc _ _).1⟩
  have e := SubRep.pull_one hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl
  refine Eq.trans ?_ e.symm
  show ((1 : Over.mk (K.hom ≫ Y.hom) ⟶ G) ≫ inc).left = _
  rw [one_comp]

private theorem fac_sub (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g'⁻¹ := by
  obtain ⟨a, ea, ra⟩ := (fac_iff hP inc U K g).1 h
  obtain ⟨b, eb, rb⟩ := (fac_iff hP inc U K g').1 h'
  refine (fac_iff hP inc U K _).2 ⟨a * b⁻¹, ?_, (hc _ _).2 a b ra rb⟩
  have i2 := SubRep.pull_inv hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g') (a := b ≫ inc) eb.symm
  have m := SubRep.pull_mul hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g) (a := a ≫ inc)
    (a' := (b ≫ inc)⁻¹) ea.symm i2
  refine Eq.trans ?_ m.symm
  show ((a * b⁻¹) ≫ inc).left = _
  have hi : b⁻¹ ≫ inc = (b ≫ inc)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_comp, inv_mul_cancel, one_comp])
  rw [mul_comp, hi]

private theorem fac_inv (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g⁻¹ := by
  have := fac_sub hP inc U hc K 1 g (fac_one hP inc U hc K) h
  rwa [_root_.one_mul] at this

private theorem fac_mul (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g' := by
  have := fac_sub hP inc U hc K g g'⁻¹ h (fac_inv hP inc U hc K g' h')
  rwa [inv_inv] at this

end UpperTheory.ProductProjectionSubgroup

open UpperTheory.ProductProjectionSubgroup in
theorem UpperTheory.exists_lift_of_closed_subgroup_locus :
    ∀ {S : Scheme.{0}} (Y A G : Over S) [GrpObj A] [GrpObj G] (inc : G ⟶ A) [IsFinite G.hom] [Etale G.hom] (U : (Y ⊗ G).left.Opens), Mono inc → IsMonHom inc → IsClosed (U : Set (Y ⊗ G).left) → (∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U → Set.range (lift t (a * b⁻¹)).left ⊆ U) → ∀ (A₀ : Over Y.left) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (j : H ⟶ A₀), IsMonHom j ∧ Mono j ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀), (∃ h : Over.mk t.left ⟶ H, h ≫ j = g) ↔ ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  intro S Y A G _ _ inc _ _ U hm hmon hU hc A₀ _ φ₀ hP
  have hmL : Mono inc.left := Over.mono_left_of_mono inc
  have hmj := subJ_mono hP inc U
  have hcl : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  have hf1 : IsFinite (pr1 Y G) := inferInstanceAs (IsFinite (pullback.fst Y.hom G.hom))
  have he1 : Etale (pr1 Y G) := inferInstanceAs (Etale (pullback.fst Y.hom G.hom))
  have hf : IsFinite (subH U).hom := inferInstanceAs (IsFinite (U.ι ≫ pr1 Y G))
  have he : Etale (subH U).hom := inferInstanceAs (Etale (U.ι ≫ pr1 Y G))
  obtain ⟨m, hm'⟩ := fac_mul hP inc U hc (subH U ⊗ subH U) (fst _ _ ≫ subJ hP inc U)
    (snd _ _ ≫ subJ hP inc U) ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨e, he'⟩ := fac_one hP inc U hc (𝟙_ (Over Y.left))
  obtain ⟨v, hv⟩ := fac_inv hP inc U hc (subH U) (subJ hP inc U) ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨gH, hj⟩ := GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor Y.left A₀ (subH U) (subJ hP inc U) hmj
    ⟨m, by rw [hm', Hom.mul_def, lift_fst_comp_snd_comp]⟩
    ⟨e, by rw [he', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]⟩
    ⟨v, by rw [hv, Hom.inv_def]⟩
  exact ⟨subH U, gH, subJ hP inc U, hj, hmj, hf, he, subJ_iff hP inc U⟩
end

section

noncomputable section
open Polynomial

theorem UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m := by
  intro A _ I _ g hg n m hgm
  by_cases hR : Nontrivial (A ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI := hR
  haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1 := by simp
  have hdeg : g.natDegree = n + m := by
    have h := congrArg natDegree hgm
    rw [hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m),
      natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one] at h
    exact h
  obtain ⟨α, c, hα, hc⟩ := UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm
  obtain ⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩ := UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)
  have hPdeg : P.natDegree = n := by
    have h := hP.natDegree_mul hQ
    rw [← hPQ, hdeg, hQdeg] at h
    omega
  set φ := Ideal.Quotient.mk I
  have hPb : (P.map φ).Monic := hP.map φ
  have hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m := by
    rw [← Polynomial.map_mul, ← hPQ, hgm]
  have hQ0b : (Q.map φ).eval 0 = (-1) ^ m := by
    rw [eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]
  have hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ) := by
    have hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0) := X_dvd_sub_C
    obtain ⟨r, hr⟩ := hd
    rw [coeff_zero_eq_eval_zero, hQ0b] at hr
    refine ⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩
    have hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc -(C ((-1) ^ m) * r) * X + C ((-1) ^ m) * Q.map φ
        = C ((-1) ^ m) * (Q.map φ - X * r) := by ring
      _ = 1 := by rw [← hr, sub_sub_cancel, ← C_mul, hu, C_1]
  obtain ⟨s, hs⟩ := hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩
  have hsm : s.Monic := (monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)
  have hsdeg : s.natDegree = 0 := by
    have h := congrArg natDegree hs
    rw [hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg] at h
    omega
  have hs1 : s = 1 := eq_one_of_monic_natDegree_zero hsm hsdeg
  have hPmap : P.map φ = X ^ n := by rw [hs, hs1, mul_one]
  have hQmap : Q.map φ = (X - 1) ^ m := by
    rw [hPmap] at hprod
    have h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0 := by rw [mul_sub, hprod, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)
  exact ⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩

end
end
