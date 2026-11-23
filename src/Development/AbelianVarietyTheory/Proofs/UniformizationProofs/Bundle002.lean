module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm

theorem exists_ringHom_lift (F : Type) [Field F] [IsAlgClosed F] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsIntegrallyClosed O] [Algebra O F] [IsFractionRing O F] {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (φ : A →+* ResidueField O)
    (hφ : φ.comp (algebraMap O A) = residue O) :
    ∃ ψ : A →+* O, ψ.comp (algebraMap O A) = RingHom.id O ∧ (residue O).comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker φ).LiesOver (maximalIdeal O) := ⟨by
    show maximalIdeal O = Ideal.comap (algebraMap O A) (RingHom.ker φ)
    rw [RingHom.comap_ker, hφ, ker_residue]⟩
  obtain ⟨P, hPQ, hP, hPlo⟩ := (RingHom.ker φ).exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal O)) (q := maximalIdeal O) bot_le
  have hjinj : Function.Injective (algebraMap O P.ResidueField) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : algebraMap O A y ∈ P := by
      rw [← Ideal.algebraMap_residueField_eq_zero, ← IsScalarTower.algebraMap_apply]
      exact hy
    have h2 : y ∈ P.under O := h1
    rw [← hPlo.over] at h2
    simpa using h2
  let : Algebra F P.ResidueField := (IsFractionRing.lift (K := F) hjinj).toAlgebra
  have : IsScalarTower O F P.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun y => (IsFractionRing.lift_algebraMap hjinj y).symm
  have hrange : ∀ a : A, ∃ y : O, algebraMap O P.ResidueField y = algebraMap A P.ResidueField a := by
    intro a
    have hO : IsIntegral O (algebraMap A P.ResidueField a) :=
      (Algebra.IsIntegral.isIntegral a).algebraMap
    have hF : IsIntegral F (algebraMap A P.ResidueField a) := hO.tower_top
    obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := integralClosure F P.ResidueField)).2 ⟨_, hF⟩
    have hr' : algebraMap F P.ResidueField r = algebraMap A P.ResidueField a := congrArg Subtype.val hr
    have hrO : IsIntegral O r := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom O F P.ResidueField)
        (algebraMap F P.ResidueField).injective]
      simpa [hr'] using hO
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrO
    exact ⟨y, by rw [IsScalarTower.algebraMap_apply O F P.ResidueField, hy, hr']⟩
  let e : O ≃+* (algebraMap O P.ResidueField).range :=
    RingEquiv.ofBijective (algebraMap O P.ResidueField).rangeRestrict
      ⟨fun a b h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let π' : A →+* (algebraMap O P.ResidueField).range :=
    (algebraMap A P.ResidueField).codRestrict _ fun a => by
      obtain ⟨y, hy⟩ := hrange a
      exact ⟨y, hy⟩
  have key : ∀ a, algebraMap O P.ResidueField (e.symm (π' a)) = algebraMap A P.ResidueField a :=
    fun a => congrArg Subtype.val (e.apply_symm_apply (π' a))
  refine ⟨e.symm.toRingHom.comp π', ?_, ?_⟩
  · ext y
    apply hjinj
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply]
    rw [key]
    exact (IsScalarTower.algebraMap_apply O A P.ResidueField y).symm
  · ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hmem : algebraMap O A (e.symm (π' a)) - a ∈ RingHom.ker φ := by
      apply hPQ
      rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, ← IsScalarTower.algebraMap_apply, key,
        sub_self]
    have h1 : φ (algebraMap O A (e.symm (π' a))) = φ a := by
      rw [← sub_eq_zero, ← map_sub]
      exact (RingHom.mem_ker).mp hmem
    rw [← h1, ← RingHom.comp_apply φ (algebraMap O A), hφ]

theorem exists_section_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f := ⟨_, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    exact MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  let _ := φ.hom.toAlgebra
  have : Module.Finite O Γ(H, ⊤) := hfin
  have : Module.Flat O Γ(H, ⊤) := hflat
  have hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O := by
    have h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O)) := by
      rw [Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_ringHom_lift F χ.hom hcomp
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩
  · have h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      exact CommRingCat.hom_ext hψ1
    rw [Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]
  · have h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ := by
      exact CommRingCat.hom_ext hψ2
    rw [← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem exists_torsion_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (n : ℕ) [IsFinite ((𝟙 G) ^ n : G ⟶ G).left] [Flat ((𝟙 G) ^ n : G ⟶ G).left]
    (t : Spec (CommRingCat.of O) ⟶ S)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G) (hx : x ^ n = 1) :
    ∃ y : Over.mk t ⟶ G, y ^ n = 1 ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ y.left = x.left := by
  have hpow : ∀ {Y : Over S} (z : Y ⟶ G), z ^ n = z ≫ (𝟙 G) ^ n := fun z => by
    rw [MonObj.comp_pow, Category.comp_id]
  have hxm : x.left ≫ ((𝟙 G) ^ n : G ⟶ G).left =
      Spec.map (CommRingCat.ofHom (residue O)) ≫ t ≫ η[G].left := by
    have h1 : (x ≫ (𝟙 G) ^ n).left = (1 : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G).left := by
      rw [← hpow, hx]
    rw [Over.comp_left, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left] at h1
    rw [h1]
    exact Category.assoc _ _ _
  obtain ⟨q, hq1, hq2⟩ := exists_section_lift O
    (pullback.snd ((𝟙 G) ^ n : G ⟶ G).left (t ≫ η[G].left))
    (pullback.lift x.left (Spec.map (CommRingCat.ofHom (residue O))) hxm) (pullback.lift_snd _ _ _)
  have hw : ((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have he : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨Over.homMk (q ≫ pullback.fst _ _) ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hw, pullback.condition_assoc, Category.assoc, he, Category.comp_id,
      ← Category.assoc, hq1]
    exact Category.id_comp t
  · rw [hpow, CategoryTheory.Hom.one_def]
    ext
    change (q ≫ pullback.fst _ _) ≫ ((𝟙 G) ^ n : G ⟶ G).left = t ≫ η[G].left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq1]
    exact Category.id_comp _
  · change Spec.map (CommRingCat.ofHom (residue O)) ≫ (q ≫ pullback.fst _ _) = x.left
    rw [← Category.assoc, hq2, pullback.lift_fst]

end GlobalTheory.UT.ExactTerm
end
end

section

open Polynomial

namespace GlobalTheory

def reesShiftIdeal {R : Type} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    rw [Subalgebra.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' := fun p q hq n => by
    rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    have e' : j + k = n := by simpa using e
    rw [← e', add_assoc, pow_add]
    exact Ideal.mul_mem_mul (p.2 j) (hq k)

theorem mem_reesShiftIdeal {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := Iff.rfl

theorem coeff_sum_algebraMap_mul_rees {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by
  simp [Polynomial.algebraMap_eq]

theorem exists_graded_ring_kernel_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∃ (S : Type) (_ : CommRing S) (g : R →+* S), IsNoetherianRing S ∧ (∀ x ∈ I, g x = 0) ∧ ∀ (e : ℕ) (g' : R ⧸ I ^ (e + 1 + 1) →+* S), g'.comp (Ideal.Quotient.mk _) = g → ∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) (R ⧸ I ^ (e + 1 + 1))) (D₁ : Matrix (Fin c) (Fin b) (R ⧸ I ^ (e + 1 + 1))), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g').mulVec w = 0 → ∃ v, (D₀.map g').mulVec v = w) → ∀ v' : Fin a → R ⧸ I ^ (e + 1), (D₀.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))).mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) (v k) = v' k := by
  intro R _ _ I
  refine ⟨reesAlgebra I ⧸ reesShiftIdeal I, inferInstance,
    (Ideal.Quotient.mk _).comp (algebraMap R (reesAlgebra I)), inferInstance, ?_, ?_⟩
  ·
    intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    split_ifs with hn
    · subst hn
      simpa using hx
    · exact Ideal.zero_mem _
  · intro e g' hg' a b c D₀ D₁ hD hex v' hv'
    have hg'x : ∀ x : R, g' (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk (reesShiftIdeal I) (algebraMap R (reesAlgebra I) x) := fun x => by
      have := RingHom.congr_fun hg' x
      simpa only [RingHom.comp_apply] using this

    obtain ⟨d₀, rfl⟩ : ∃ d : Matrix (Fin b) (Fin a) R, D₀ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun j k => (Ideal.Quotient.mk_surjective (D₀ j k)).choose, by
        ext j k
        simp [(Ideal.Quotient.mk_surjective (D₀ j k)).choose_spec]⟩
    obtain ⟨d₁, rfl⟩ : ∃ d : Matrix (Fin c) (Fin b) R, D₁ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (D₁ i j)).choose, by
        ext i j
        simp [(Ideal.Quotient.mk_surjective (D₁ i j)).choose_spec]⟩
    obtain ⟨r, rfl⟩ : ∃ r : Fin a → R, v' = fun k => Ideal.Quotient.mk _ (r k) :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (v' k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (v' k)).choose_spec.symm⟩

    have hs : ∀ j, ∑ k, d₀ j k * r k ∈ I ^ (e + 1) := fun j => by
      have h := congrFun hv' j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Ideal.Quotient.factor_mk,
        Pi.zero_apply] at h

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_mul] using h

    have hs2 : ∀ i, ∑ j, d₁ i j * ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1) := fun i => by
      have hrow : ∀ k, ∑ j, d₁ i j * d₀ j k ∈ I ^ (e + 1 + 1) := fun k => by
        have h := congrFun (congrFun hD i) k
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h

        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simpa only [map_mul] using h
      have heq : ∑ j, d₁ i j * ∑ k, d₀ j k * r k = ∑ k, (∑ j, d₁ i j * d₀ j k) * r k := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [heq]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hrow k)

    obtain ⟨m, hm⟩ : ∃ m : Fin b → reesAlgebra I,
        ∀ j, (m j : R[X]) = Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k) :=
      ⟨fun j => ⟨Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k),
        reesAlgebra.monomial_mem.mpr (hs j)⟩, fun _ => rfl⟩

    have hW : ((d₁.map (Ideal.Quotient.mk _)).map g').mulVec
        (fun j => Ideal.Quotient.mk (reesShiftIdeal I) (m j)) = 0 := by
      funext i
      have hmem : (∑ j, algebraMap R (reesAlgebra I) (d₁ i j) * m j) ∈ reesShiftIdeal I := by
        rw [mem_reesShiftIdeal]
        intro n
        rw [coeff_sum_algebraMap_mul_rees]
        simp only [hm, Polynomial.coeff_monomial]
        by_cases hn : e + 1 = n
        · subst hn
          simpa using hs2 i
        · simp [hn]
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem

      rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, Pi.zero_apply,
        map_mul] using this

    obtain ⟨V, hV⟩ := hex _ hW
    choose P hP using fun k => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (V k)
    have hdiff : ∀ j, ∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k ∈
        I ^ (e + 1 + 1) := fun j => by
      have h := congrFun hV j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, ← hP] at h
      have h' : Ideal.Quotient.mk (reesShiftIdeal I)
          (∑ k, algebraMap R (reesAlgebra I) (d₀ j k) * P k) =
          Ideal.Quotient.mk (reesShiftIdeal I) (m j) := by

        rw [map_sum]
        simpa only [map_mul] using h
      rw [Ideal.Quotient.eq, mem_reesShiftIdeal] at h'
      have h'' := h' (e + 1)
      rw [Subalgebra.coe_sub, Polynomial.coeff_sub, coeff_sum_algebraMap_mul_rees, hm,
        Polynomial.coeff_monomial, Finsupp.single_eq_same] at h''
      exact h''
    refine ⟨fun k => Ideal.Quotient.mk _ (r k - (P k : R[X]).coeff (e + 1)), ?_, ?_⟩
    · funext j
      have hmem : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) ∈ I ^ (e + 1 + 1) := by
        have heq : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) =
            -(∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        rw [heq]
        exact neg_mem (hdiff j)
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem

      rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_mul] using this
    · intro k
      simp only [Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, sub_sub_cancel_left]
      exact neg_mem ((P k).2 (e + 1))

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]

theorem support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by
  intro X _ _ S S₂ ⟨a, ha⟩ h hd
  have h02 : (0 : X) ∈ S₂ := by simpa using ((h a a).mp ⟨ha, ha⟩).2
  have h0 : (0 : X) ∈ S := ((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1
  have heq : S₂ = S := by
    ext x
    have := h x 0
    simp only [add_zero, sub_zero, and_self, h0, and_true] at this
    exact this.symm
  subst heq
  refine ⟨rfl, ?_⟩
  let Λ : AddSubgroup X :=
    { carrier := S₂
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1
      neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }
  refine ⟨Λ, rfl, ?_⟩
  by_cases ht : Λ = ⊤
  · exact Or.inl ht
  · right
    obtain ⟨l, hl, f, hf, hΛ⟩ := exists_prime_hom_zmod_of_ne_top X Λ ht
    refine ⟨l, hl, ?_, f, hf, hΛ⟩
    refine hl.odd_of_ne_two ?_
    rintro rfl
    apply hf
    ext x
    obtain ⟨z, hz⟩ := hd x
    have h1 := hΛ _ hz
    have h2 : f z + f z = 0 := CharTwo.add_self_eq_zero _
    rw [map_add (f := _), map_add (f := _), h2, add_zero] at h1
    simpa using h1

end GlobalTheory
end

section

namespace GlobalTheory.Unif

theorem exists_limit_of_successive_corrections (R : Type) [CommRing R] (a : R) (M : Type)
    [AddCommGroup M] [Module R M] [IsPrecomplete (Ideal.span {a}) M] (K : ℕ → Submodule R M)
    (hK : ∀ e, K (e + 1) ≤ K e) (ha : ∀ (e : ℕ) (x : M), a ^ (e + 1) • x ∈ K e)
    (hs : ∀ e, ∀ x ∈ K e, ∃ y : M, x - a ^ (e + 1) • y ∈ K (e + 1)) :
    ∀ e, ∀ x ∈ K e, ∃ x' y : M, (∀ e', x' ∈ K e') ∧ x - x' = a ^ (e + 1) • y := by
  intro e x hx
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R M) ↔
      ∃ y : M, z = a ^ n • y := by
    intro n z
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, h⟩
      exact ⟨y, h.symm⟩
    · rintro ⟨y, h⟩
      exact ⟨y, trivial, h.symm⟩
  choose y hy using hs
  let s : (n : ℕ) → K (e + n) := fun n =>
    Nat.rec (motive := fun n => K (e + n)) ⟨x, hx⟩
      (fun n z => ⟨z.1 - a ^ (e + n + 1) • y (e + n) z.1 z.2, hy _ _ _⟩) n
  have hs0 : (s 0 : M) = x := rfl
  have hsn : ∀ n, (s (n + 1) : M) = s n - a ^ (e + n + 1) • y (e + n) (s n).1 (s n).2 :=
    fun n => rfl
  have hd : ∀ m n, m ≤ n → ∃ z : M, (s m : M) - s n = a ^ (e + m + 1) • z := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨z + a ^ k • y (e + (m + k)) (s (m + k)).1 (s (m + k)).2, ?_⟩
      rw [hsn, smul_add, ← hz, smul_smul, ← pow_add,
        show e + m + 1 + k = e + (m + k) + 1 by ring]
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) (M := M) inferInstance
    (f := fun n => (s n : M)) (by
      intro m n hmn
      obtain ⟨z, hz⟩ := hd m n hmn
      rw [SModEq.sub_mem, hmem]
      refine ⟨a ^ (e + 1) • z, ?_⟩
      rw [hz, smul_smul, ← pow_add, show m + (e + 1) = e + m + 1 by ring])
  have hl : ∀ m, ∃ z : M, (s m : M) - L = a ^ (e + m + 1) • z := by
    intro m
    obtain ⟨z, hz⟩ := hd m (e + m + 1) (by omega)
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    obtain ⟨w, hw⟩ := h
    refine ⟨z + w, ?_⟩
    rw [smul_add, ← hz, ← hw]
    abel
  obtain ⟨z, hz⟩ := hl 0
  refine ⟨L, z, fun m => ?_, hz⟩
  obtain ⟨w, hw⟩ := hl m
  have hLe : L = (s m : M) - a ^ (e + m + 1) • w := by rw [← hw]; abel
  apply hanti (show m ≤ e + m by omega)
  rw [hLe]
  exact Submodule.sub_mem _ (s m).2 (ha _ _)

end GlobalTheory.Unif
end
