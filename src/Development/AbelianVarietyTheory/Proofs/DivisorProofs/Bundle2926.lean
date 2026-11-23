module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_generic_endomorphism_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  first | exact @GlobalTheory.Mum.genericEnd_extends | exact GlobalTheory.Mum.genericEnd_extends | (intros; apply GlobalTheory.Mum.genericEnd_extends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.ModelSection.main | exact GlobalTheory.Mum.ModelSection.main | (intros; apply GlobalTheory.Mum.ModelSection.main <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  first | exact @GlobalTheory.LowDat.exists_tateIso_toA | exact GlobalTheory.LowDat.exists_tateIso_toA | (intros; apply GlobalTheory.LowDat.exists_tateIso_toA <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  first | exact @GlobalTheory.TorusLift.exists_sec_sq_eq_one | exact GlobalTheory.TorusLift.exists_sec_sq_eq_one | (intros; apply GlobalTheory.TorusLift.exists_sec_sq_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | exact GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | (intros; apply GlobalTheory.Mum.exists_secB_zero_mem_basicOpen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.linear_uniformisations_character_iso_associated_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  first | exact @GlobalTheory.PelUnifUniqCoord.main | exact GlobalTheory.PelUnifUniqCoord.main | (intros; apply GlobalTheory.PelUnifUniqCoord.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical


theorem _root_.GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  first | exact @GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | exact GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | (intros; apply GlobalTheory.GenRestrict.exists_genericPoints_equiv_any <;> assumption)
end

section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.DomTuple

section Squares

variable {X : Type} [AddCommGroup X]

def IsSumSq (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → X), ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → F β = ∑ i, β (x i) (x i)

theorem IsSumSq.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : IsSumSq G := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨ι, _, x, fun β hβ => (e β hβ).trans (hx β hβ)⟩

theorem IsSumSq.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (h' : IsSumSq G) :
    IsSumSq fun β => F β + G β := by
  obtain ⟨ι, _, x, hx⟩ := h
  obtain ⟨κ, _, y, hy⟩ := h'
  exact ⟨ι ⊕ κ, inferInstance, Sum.elim x y, fun β hβ => by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hx β hβ, hy β hβ]⟩

theorem IsSumSq.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (n : ℕ) : IsSumSq fun β => n * F β := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨Fin n × ι, inferInstance, fun p => x p.2, fun β hβ => by
    simp [Fintype.sum_prod_type, hx β hβ]⟩

theorem isSumSq_one (v : X) : IsSumSq fun β => β v v :=
  ⟨Unit, inferInstance, fun _ => v, fun β _ => by simp⟩

variable {m : ℕ} (a : Fin m → X)

def Absorbed (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ C : ℕ, IsSumSq fun β => C * ∑ i, β (a i) (a i) + F β

variable {a}

theorem Absorbed.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : Absorbed a G := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.congr fun β hβ => by rw [e β hβ]⟩

theorem Absorbed.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (h' : Absorbed a G) :
    Absorbed a fun β => F β + G β := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  exact ⟨C + C', (h.add h').congr fun β _ => by push_cast; ring⟩

theorem Absorbed.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (n : ℕ) : Absorbed a fun β => n * F β := by
  obtain ⟨C, h⟩ := h
  exact ⟨n * C, (h.nsmul n).congr fun β _ => by push_cast; ring⟩

theorem absorbed_sq (v : X) : Absorbed a fun β => β v v :=
  ⟨0, (isSumSq_one v).congr fun β _ => by simp⟩

theorem absorbed_zero : Absorbed a fun _ => 0 :=
  (absorbed_sq 0).congr fun β _ => by simp

theorem absorbed_sum {ι : Type} (S : Finset ι) (F : ι → LinearMap.BilinForm ℤ X → ℤ) (h : ∀ i, Absorbed a (F i)) :
    Absorbed a fun β => ∑ i ∈ S, F i β := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using absorbed_zero
  | insert i S hi ih => exact ((h i).add ih).congr fun β _ => Finset.sum_insert hi

theorem absorbed_neg_sq (ha : Submodule.span ℤ (Set.range a) = ⊤) (v : X) : Absorbed a fun β => - β v v := by
  have hv : v ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, {i // i ≠ j}, inferInstance, fun i => a i.1, fun β _ => ?_⟩
    have := Fintype.sum_eq_add_sum_subtype_ne (fun i => β (a i) (a i)) j
    simp only [Nat.cast_one, one_mul]
    rw [this]; ring
  | zero => exact absorbed_zero.congr fun β _ => by simp
  | add x y _ _ hx hy =>
    refine (((hx.nsmul 2).add (hy.nsmul 2)).add (absorbed_sq (x - y))).congr fun β _ => ?_
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    push_cast; ring
  | smul n x _ hx =>
    refine (hx.nsmul (n.natAbs ^ 2)).congr fun β _ => ?_
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    push_cast; rw [sq_abs]; ring

theorem absorbed_two_mul_apply (ha : Submodule.span ℤ (Set.range a) = ⊤) (u v : X) : Absorbed a fun β => 2 * β u v := by
  refine (((absorbed_sq (u + v)).add (absorbed_neg_sq ha u)).add (absorbed_neg_sq ha v)).congr fun β hβ => ?_
  simp only [map_add (f := _), LinearMap.add_apply, hβ v u]
  ring

theorem absorbed_two_mul [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Absorbed a fun β => 2 * F β := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β => by
    refine LinearMap.BilinForm.ext_basis b fun k l => ?_
    simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  refine (absorbed_sum Finset.univ _ fun i => absorbed_sum Finset.univ _ fun j =>
    absorbed_two_mul_apply ha (F (E i j) • b i) (b j)).congr fun β _ => ?_
  conv_lhs => rw [hE β]

  simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Squares

theorem exists_tuple {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {a₀ : Fin m → X}
    (ha : Submodule.span ℤ (Set.range a₀) = ⊤) {s : ℕ} (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) {w : ℕ} (hw : 1 ≤ w)
    (hW : W 0 0 = w) (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (μ : Fin (s + 1) → X) (D₀ : ℕ) :
    ∃ (D l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), D₀ < D ∧ (∀ u, a (i₀, u) = μ u) ∧
      Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
        lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + (2 * w : ℕ) * lam β := by
  classical
  have h1 : Absorbed a₀ fun β => 2 * lam β + ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) :=
    (absorbed_two_mul ha lam).add (absorbed_sum _ _ fun u => absorbed_sum _ _ fun v => absorbed_two_mul_apply ha _ _)
  obtain ⟨C, ι, _, x, hx⟩ := h1
  let κ := Fin (2 * w) ⊕ (Fin (D₀ + 1) × Fin m) ⊕ ι
  let t : κ → Fin (s + 1) → X :=
    Sum.elim (fun _ => μ) (Sum.elim (fun p => Pi.single 0 (a₀ p.2)) fun i => Pi.single 0 (x i))
  let e := (Fintype.equivFin κ).symm
  refine ⟨w * (C + D₀ + 1), _, fun p => t (e p.1) p.2, e.symm (Sum.inl ⟨0, by omega⟩), by nlinarith, fun u => by simp [t],
    ?_, fun β hβ => ?_⟩
  · rw [eq_top_iff, ← ha]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨(e.symm (Sum.inr (Sum.inl (0, i))), 0), by simp [t]⟩
  · have hs : ∀ v : X, qW W β (Pi.single 0 v) = w * β v v := fun v => by
      simp [qW, Fin.sum_univ_succ, hW]
    have h2 : lin W (fun p : _ × _ => t (e p.1) p.2) β = ∑ k, qW W β (t k) := e.sum_comp fun k => qW W β (t k)
    have h3 := hx β hβ
    have h4 : ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) = -2 * qW W β μ := by
      simp only [qW, Finset.mul_sum, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [h4] at h3
    rw [h2]
    simp only [κ, t, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hs, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← h3]
    push_cast; ring

theorem exists_dominant (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (hφ : IsPolFanOn bar φ X) (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a₀ : Fin m → X) (hγ : IsCone bar φ γ) (hne : NoEquivRays O γ) (hpos : ∀ x, x ≠ 0 → ∃ j, 0 < γ j x x)
    (hs : Supports bar φ d γ a₀) (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) (hW : PosW W) (N₁ : ℕ) (hN : 3 ≤ N₁)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hlam : ∀ j, 0 ≤ lam (γ j)) (μ : Fin (s + 1) → X) :
    ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧
      Dominant bar φ (D * d) N₁ W γ a ∧
      ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  have hW0 : 0 < W 0 0 := by
    have h : (0 : ℝ) < ((W + W.transpose).map (Int.cast : ℤ → ℝ)) 0 0 := Matrix.PosDef.diag_pos hW
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, W 0 0 = w := ⟨_, (Int.toNat_of_nonneg hW0.le).symm⟩
  have hw1 : 1 ≤ w := by omega
  let lam' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ((2 * w : ℕ) : ℤ) • lam
  have hlam' : ∀ j, 0 ≤ lam' (γ j) := fun j => mul_nonneg (Int.natCast_nonneg _) (hlam j)
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_supportingForm_gap_off_smoothCone O bar φ d X hφ r m γ a₀ hγ hs lam' hlam' (∑ j, lam' (γ j) + 1)
  obtain ⟨D, l, a, i₀, hD, hμ, hsp, hlin⟩ := exists_tuple hs.span W hw1 hw lam μ D₀
  obtain ⟨hle, hgap⟩ := hD₀ D hD.le
  have hlin' : ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + lam' β := fun β hβ => hlin β hβ.1
  have key : ∀ (e : X ≃ₗ[O] X) j, pull e.toLinearMap (γ j) = γ j ∨
      lin W a (γ j) < lin W (fun i => e (a i)) (γ j) := fun e j => by
    by_cases h : ∃ j', pull e.toLinearMap (γ j) = γ j'
    · obtain ⟨j', h⟩ := h
      exact Or.inl (hne e j j' h ▸ h)
    right
    have hc : IsCone bar φ ![pull e.toLinearMap (γ j)] := by
      have := (hφ.face _ 1 γ ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩ hγ).pull_equiv e
      have h0 : ![pull e.toLinearMap (γ j)] = fun _ : Fin 1 => pull e.toLinearMap (γ j) := funext fun i => by simp
      rw [h0]
      exact this
    have h1 := hgap _ hc fun j' hj => h ⟨j', hj⟩
    rw [← hlin' _ (pull_mem _ (hγ.mem j)), evalZ_pull φ (r := e.toLinearMap) e.surjective, mul_assoc, hs.eq j] at h1
    have h2 : D * ∑ i, γ j (a₀ i) (a₀ i) + (∑ j, lam' (γ j) + 1) ≤ lin W a (pull e.toLinearMap (γ j)) := by
      exact_mod_cast h1
    have h3 : lam' (γ j) ≤ ∑ j, lam' (γ j) := Finset.single_le_sum (fun j _ => hlam' j) (Finset.mem_univ j)
    change _ < lin W a (pull e.toLinearMap (γ j))
    rw [hlin' _ (hγ.mem j)]
    omega
  refine ⟨D, 2 * w, l, a, i₀, by omega, by omega, hμ, ⟨hsp, fun β hβ hp => ?_, fun e _ j => ?_, fun e he hx => ?_⟩,
    fun β hβ => hlin β hβ.1⟩
  · rw [hlin' β hβ, Nat.cast_mul]
    exact hle β hβ hp
  · rcases key e j with h | h
    · change _ ≤ lin W a (pull e.toLinearMap (γ j))
      rw [h]
    · exact h.le
  · by_contra hn
    have hfix : ∀ j, pull e.toLinearMap (γ j) = γ j := fun j => (key e j).resolve_right fun h => hn ⟨j, h⟩
    have := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ j, γ j) (fun x hx => by
      obtain ⟨j, hj⟩ := hpos x hx
      simp only [LinearMap.sum_apply]
      exact Finset.sum_pos' (fun i _ => hγ.nonneg i x) ⟨j, Finset.mem_univ j, hj⟩) e.toAddEquiv.toIntLinearEquiv
      (fun x y => by
        simp only [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hfix j) x y) N₁ hN he
    obtain ⟨x, hx⟩ := hx
    exact hx (LinearEquiv.congr_fun this x)

end GlobalTheory.Poinc.DomTuple
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

theorem abelianPart_iso_of_twoUnif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  intro R _ _ _ hBase D A G _ _ hG U g _ a _ _ A₂ D₂ U₂ _
  have hR : AdmBase R (maximalIdeal R) := hBase.1
  have hN : IsNoetherianRing R := hR.1
  have hC : IsAdicComplete (maximalIdeal R) R := hR.2.2.2
  have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  obtain ⟨b₁, hb₁, h₁⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D₂ D A₂ A G G
    U₂.toUnifPre U.toUnifPre (𝟙 G) inferInstance
  obtain ⟨b₂, hb₂, h₂⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D D₂ A A₂ G G
    U.toUnifPre U₂.toUnifPre (𝟙 G) inferInstance

  have q₁ : ∀ e, (U.gt e).q = (U₂.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₁ := by
    intro e
    have := h₁ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have q₂ : ∀ e, (U₂.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₂ := by
    intro e
    have := h₂ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have epi : ∀ {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
      (V : UnifPre (maximalIdeal R) D' A' G) (e : ℕ), Epi (V.gt e).q := by
    intro D' A' V e
    have := (V.gt e).q_flat
    have := (V.gt e).q_surj
    have : Epi (V.gt e).q.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have k₁ : b₂ ≫ b₁ = 𝟙 _ := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U.toUnifPre n
    rw [← cancel_epi (U.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₂, ← q₁]
  have k₂ : b₁ ≫ b₂ = 𝟙 _ := by
    have := D₂.toPre.P.isAb.smooth
    have := D₂.toPre.P.isAb.geomConnected
    have := D₂.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U₂.toUnifPre n
    rw [← cancel_epi (U₂.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₁, ← q₂]
  refine ⟨⟨b₁, b₂, k₂, k₁⟩, hb₁, fun e => ?_⟩
  show (U₂.gt e).q.left ≫ (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left =
    (U.gt e).q.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left
  have m : ((Over.pullback (thick R (maximalIdeal R) e)).map b₁).left ≫
      (fstG (maximalIdeal R) e D.toPre.P.A).left = (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left :=
    pullback.lift_fst _ _ _
  rw [← m, q₁ e, Over.comp_left, Category.assoc]

end GlobalTheory.MumCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.TwistAV.exists_translate_pol | exact GlobalTheory.TwistAV.exists_translate_pol | (intros; apply GlobalTheory.TwistAV.exists_translate_pol <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartQF
theorem base_chartRing {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] {m e : ℕ}
    (C : Fam Xo c (ChartRing k m e)) : GlobalTheory.Mum.Base (ChartRing k m e) :=
  ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k m e, (C.b.charZero_iff C.b.injective).1 inferInstance⟩

end GlobalTheory.ChartQF
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def Deep.GalLab (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    (∀ E, (ε₀ E).left ≫ b = b ≫ (D.ε E).left ∧ (ε₀ E).left ≫ t = t ≫ (ε₀ E).left) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.Poinc
end
end
