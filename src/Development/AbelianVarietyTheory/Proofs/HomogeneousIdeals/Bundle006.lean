module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Exponential
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

section

open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

def Proportional (T U : Fin 3 → R) : Prop :=
  ∀ i j, T i * U j = T j * U i

lemma Proportional.symm {T U : Fin 3 → R} (h : Proportional T U) : Proportional U T :=
  fun i j => by linear_combination h j i

lemma proportional_negY (W : Projective R) {X N Z X' N' Z' : R} (hxz : X * Z' = Z * X')
    (hnz : N * Z' = Z * N') (hxn : X * N' = N * X') :
    Proportional ![X, W.negY ![X, N, Z], Z] ![X', W.negY ![X', N', Z'], Z'] := by
  have hxy : X * W.negY ![X', N', Z'] = W.negY ![X, N, Z] * X' := by
    simp only [negY_eq]; linear_combination -hxn - W.a₃ * hxz
  have hyz : W.negY ![X, N, Z] * Z' = Z * W.negY ![X', N', Z'] := by
    simp only [negY_eq]; linear_combination -hnz - W.a₁ * hxz
  intro i j
  fin_cases i <;> fin_cases j
  exacts [rfl, hxy, hxz, hxy.symm, rfl, hyz, hxz.symm, hyz.symm, rfl]

variable {W : Projective R}

lemma diagXYZ_X (P Q : Fin 3 → R) : diagXYZ W P Q 0 = diagX W P Q := rfl

lemma diagXYZ_Y (P Q : Fin 3 → R) : diagXYZ W P Q 1 = diagY W P Q := rfl

lemma diagXYZ_Z (P Q : Fin 3 → R) : diagXYZ W P Q 2 = diagZ W P Q := rfl

lemma diagXYZ_self {P : Fin 3 → R} (hP : W.Equation P) : diagXYZ W P P = W.dblXYZ P := by
  rw [diagXYZ, diagY, diagX_self hP, negDiagY_self hP, diagZ_self hP, dblXYZ, dblY]

lemma diagY_smul (P Q : Fin 3 → R) (u v : R) :
    diagY W (u • P) (v • Q) = (u * v) ^ 2 * diagY W P Q := by
  simp only [diagY, negY_eq, diagX_smul, negDiagY_smul, diagZ_smul]
  ring1

lemma diagXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    diagXYZ W (u • P) (v • Q) = (u * v) ^ 2 • diagXYZ W P Q := by
  rw [diagXYZ, diagX_smul, diagY_smul, diagZ_smul, smul_fin3, diagXYZ_X, diagXYZ_Y, diagXYZ_Z]

lemma map_diagY (f : R →+* S) (P Q : Fin 3 → R) :
    diagY (W.map f) (f ∘ P) (f ∘ Q) = f (diagY W P Q) := by
  simp only [diagY, negY_eq, map_diagX, map_negDiagY, map_diagZ]
  simp only [map_neg, map_sub, map_mul, WeierstrassCurve.map]

lemma map_diagXYZ (f : R →+* S) (P Q : Fin 3 → R) :
    diagXYZ (W.map f) (f ∘ P) (f ∘ Q) = f ∘ diagXYZ W P Q := by
  simp only [diagXYZ, map_diagX, map_diagY, map_diagZ, comp_fin3]

lemma proportional_diagXYZ_addXYZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    Proportional (diagXYZ W P Q) (W.addXYZ P Q) :=
  proportional_negY W (diagX_mul_addZ hP hQ) (negDiagY_mul_addZ hP hQ) (diagX_mul_negAddY hP hQ)







end Ring

section Field

variable {F : Type*} [Field F] {W : Projective F}

lemma ne_zero_of_nonsingular {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  exact Y_ne_zero_of_Z_eq_zero hP rfl rfl

lemma nonsingular_iff_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) (P : Fin 3 → F) :
    W.Nonsingular P ↔ W.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.left, ne_zero_of_nonsingular h⟩, fun ⟨h, h0⟩ => ?_⟩
  by_cases hz : P 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => h0 <| by
      ext i; fin_cases i
      exacts [hx, hy, hz]
    refine (nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (nonsingular_of_Z_ne_zero hz).mpr <|
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <| (equation_of_Z_ne_zero hz).mp h

lemma equiv_of_proportional {T U : Fin 3 → F} (h : Proportional T U) (hT : T ≠ 0) (hU : U ≠ 0) :
    T ≈ U := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hU
  replace hj : U j ≠ 0 := hj
  have e : (T j / U j) • U = T := by
    ext i
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hj, h i j]
  have hu : T j / U j ≠ 0 := fun h0 => hT <| by rw [← e, h0, zero_smul]
  exact ⟨Units.mk0 _ hu, e⟩


lemma addXYZ_ne_zero_iff {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ↔ ¬P ≈ Q := by
  refine ⟨fun h ⟨u, e⟩ => h ?_, fun h => ?_⟩
  · have := addXYZ_smul (W' := W) Q Q u 1
    rw [one_smul, addXYZ_self] at this
    rw [← show (u : F) • Q = P from e, this]
    ext i
    fin_cases i <;> simp
  · rw [← add_of_not_equiv h]
    exact ne_zero_of_nonsingular <| nonsingular_add hP hQ

lemma diagXYZ_equiv_add_of_equiv {P Q : Fin 3 → F} (hP : W.Equation P) (h : P ≈ Q) :
    diagXYZ W P Q ≈ W.add P Q := by
  rw [add_of_equiv h, ← diagXYZ_self hP]
  obtain ⟨u, e⟩ := Setoid.symm h
  have := diagXYZ_smul (W := W) P P 1 u
  rw [one_smul, one_mul] at this
  rw [← show (u : F) • P = Q from e, this]
  exact smul_equiv _ (u.isUnit.pow 2)

lemma diagXYZ_ne_zero_of_equiv {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : P ≈ Q) : diagXYZ W P Q ≠ 0 :=
  ne_zero_of_nonsingular <| (nonsingular_of_equiv <| diagXYZ_equiv_add_of_equiv hP.left h).mpr <|
    nonsingular_add hP hQ

theorem addXYZ_ne_zero_or_diagXYZ_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ diagXYZ W P Q ≠ 0 := by
  by_cases h : P ≈ Q
  · exact Or.inr <| diagXYZ_ne_zero_of_equiv hP hQ h
  · exact Or.inl <| (addXYZ_ne_zero_iff hP hQ).mpr h

lemma addXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : W.addXYZ P Q ≠ 0) : W.addXYZ P Q ≈ W.add P Q := by
  rw [add_of_not_equiv <| (addXYZ_ne_zero_iff hP hQ).mp h]

lemma diagXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : diagXYZ W P Q ≠ 0) : diagXYZ W P Q ≈ W.add P Q := by
  by_cases e : P ≈ Q
  · exact diagXYZ_equiv_add_of_equiv hP.left e
  · rw [add_of_not_equiv e]
    exact equiv_of_proportional (proportional_diagXYZ_addXYZ hP.left hQ.left) h <|
      (addXYZ_ne_zero_iff hP hQ).mpr e

lemma equiv_add_of_proportional {P Q T : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h₁ : Proportional T (W.addXYZ P Q)) (h₂ : Proportional T (diagXYZ W P Q)) (hT : T ≠ 0) :
    T ≈ W.add P Q := by
  rcases addXYZ_ne_zero_or_diagXYZ_ne_zero hP hQ with h | h
  · exact Setoid.trans (equiv_of_proportional h₁ hT h) (addXYZ_equiv_add hP hQ h)
  · exact Setoid.trans (equiv_of_proportional h₂ hT h) (diagXYZ_equiv_add hP hQ h)

variable [DecidableEq F]

end Field

end GlobalTheory.AddLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupRingConst

noncomputable def pt {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) : AddMonoidAlgebra R X →+* F :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom F).comp c) (fun _ _ ↦ Commute.all _ _)

@[simp] lemma pt_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (a : X) (x : R) :
    pt r c (AddMonoidAlgebra.single a x) = r x * (c (Multiplicative.ofAdd a) : F) := by
  simp [pt, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma pt_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) :
    (pt r c).comp (algebraMap R (AddMonoidAlgebra R X)) = r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, pt_single]

def powChar {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G) :
    Multiplicative X →* G :=
  (zpowersHom G u).comp (AddMonoidHom.toMultiplicative l)

@[simp] lemma powChar_apply {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G)
    (a : X) : powChar l u (Multiplicative.ofAdd a) = u ^ l a := by
  simp [powChar]

lemma eq_prod_powChar {G X I : Type} [CommGroup G] [AddCommGroup X] [Fintype I]
    (b : Module.Basis I ℤ X) (c : Multiplicative X →* G) :
    c = ∏ i, powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i))) := by
  refine MonoidHom.ext fun m => ?_
  obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = m := ⟨Multiplicative.toAdd m, rfl⟩
  rw [MonoidHom.finsetProd_apply]
  simp only [powChar_apply]
  conv_lhs => rw [← b.sum_repr a]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  simp [Module.Basis.coord_apply]

noncomputable def family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) : AddMonoidAlgebra R X →+* AddMonoidAlgebra F ℤ :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap F (AddMonoidAlgebra F ℤ)).comp r)
    (((algebraMap F (AddMonoidAlgebra F ℤ)).toMonoidHom.comp ((Units.coeHom F).comp c)) *
      ((AddMonoidAlgebra.of F ℤ).comp (AddMonoidHom.toMultiplicative l)))
    (fun _ _ ↦ Commute.all _ _)

lemma family_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (a : X) (x : R) :
    family r c l (AddMonoidAlgebra.single a x) =
      AddMonoidAlgebra.single (l a) (r x * (c (Multiplicative.ofAdd a) : F)) := by
  simp [family, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single,
    AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.of_apply, _root_.mul_assoc]

lemma family_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) :
    (family r c l).comp (algebraMap R (AddMonoidAlgebra R X)) =
      (algebraMap F (AddMonoidAlgebra F ℤ)).comp r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, family_single]

lemma pt_comp_family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (u : Fˣ) :
    (pt (RingHom.id F) (zpowersHom Fˣ u)).comp (family r c l) = pt r (c * powChar l u) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;>
    (rw [RingHom.comp_apply, family_single, pt_single, pt_single]
     simp [powChar_apply])

lemma spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

private lemma powChar_one {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) :
    GlobalTheory.GroupRingConst.powChar l (1 : G) = 1 := by
  refine MonoidHom.ext fun m => ?_
  rw [MonoidHom.one_apply, ← ofAdd_toAdd m, GlobalTheory.GroupRingConst.powChar_apply, one_zpow]

private lemma pt_eq_lemma_2 {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (φ : AddMonoidAlgebra R X →+* F) :
    φ = GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X)))
      ((φ.toMonoidHom.comp (AddMonoidAlgebra.of R X)).toHomUnits) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_)
  · simp [GlobalTheory.GroupRingConst.pt_single, AddMonoidAlgebra.coe_algebraMap]
  · simp [GlobalTheory.GroupRingConst.pt_single, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, _root_.one_mul]

private lemma step_lemma_3 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s)
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) (l : X →+ ℤ) (u : Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l u))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f := by
  obtain ⟨k, hk⟩ := h L (Spec.map (CommRingCat.ofHom r) ≫ s)
    (Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.family r c l)) ≫ f) (by
      rw [Category.assoc, hf, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.family_comp_algebraMap, ← GlobalTheory.GroupRingConst.spec_comp,
        Category.assoc])
  have key : ∀ v : Lˣ, Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l v))) ≫ f = k := by
    intro v
    rw [← GlobalTheory.GroupRingConst.pt_comp_family, ← GlobalTheory.GroupRingConst.spec_comp, Category.assoc, hk, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp,
      GlobalTheory.GroupRingConst.pt_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h1 := key 1
  rw [powChar_one, _root_.mul_one] at h1
  rw [key u, h1]

private lemma chain_lemma_4 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f = Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ t : Finset (Module.Free.ChooseBasisIndex ℤ X),
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (∏ i ∈ t,
        GlobalTheory.GroupRingConst.powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i)))))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, _root_.mul_comm (GlobalTheory.GroupRingConst.powChar _ _), step_lemma_3 p h s f hf, ih]
  conv_lhs => rw [GlobalTheory.GroupRingConst.eq_prod_powChar b c]
  exact key Finset.univ

private lemma pts_lemma_5 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (φ : AddMonoidAlgebra R X →+* L) :
    Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt (RingHom.id R) 1)) ≫ f := by
  rw [← Category.assoc, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.spec_comp]
  have e1 : (φ.comp (algebraMap R (AddMonoidAlgebra R X))).comp
      (GlobalTheory.GroupRingConst.pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)) =
      GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X))) (1 : Multiplicative X →* Lˣ) := by
    refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;> simp [GlobalTheory.GroupRingConst.pt_single]
  rw [e1]
  conv_lhs => rw [pt_eq_lemma_2 φ]
  exact chain_lemma_4 p h s f hf L _ _

end GlobalTheory.GroupRingConst

open GlobalTheory.GroupRingConst in
theorem GlobalTheory.groupRing_hom_const_of_laurent {S Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p]
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) :
    ∃ k : Spec (CommRingCat.of R) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ k := by
  classical
  have : UniqueSums X := UniqueSums.of_injective_addHom
    (Module.Free.chooseBasis ℤ X).repr.toLinearMap.toAddMonoidHom.toAddHom
    (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  have hcomp : (pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)).comp
      (algebraMap R (AddMonoidAlgebra R X)) = RingHom.id R := pt_comp_algebraMap _ _
  refine ⟨Spec.map (CommRingCat.ofHom (pt (RingHom.id R) 1)) ≫ f, ?_⟩
  refine ext_of_fromSpecResidueField_eq _ _ p Set.univ dense_univ (fun x _ => ?_) ?_
  · obtain ⟨φ, hφ⟩ : ∃ φ : AddMonoidAlgebra R X →+*
        ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).residueField x),
        Spec.map (CommRingCat.ofHom φ) = (Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x :=
      ⟨(Spec.preimage ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x)).hom,
        by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    rw [← hφ]
    exact pts_lemma_5 p h s f hf _ φ
  · rw [hf, Category.assoc, Category.assoc, hf,
      ← Category.assoc _ (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))), spec_comp, hcomp,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
end

section

open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Rigidity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

end Rigidity

section Series

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z

end Series

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

section Alternating

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end Alternating

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

end Lattice

end

end GlobalTheory.Doubling
end
