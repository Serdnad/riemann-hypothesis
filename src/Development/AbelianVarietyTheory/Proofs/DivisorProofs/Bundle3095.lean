module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficient
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.characters_eightfold_product_eq_eighthPower : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  first | exact @GlobalTheory.Poinc.Eq8.Chars8.main | exact GlobalTheory.Poinc.Eq8.Chars8.main | (intros; apply GlobalTheory.Poinc.Eq8.Chars8.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.exists_grpPullback_uniformisingGroup_sameGenericFibre : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_ext | exact GlobalTheory.Poinc.Sep.Spz.exists_ext | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_compatible_symplectic_bases_levelPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  first | exact @GlobalTheory.SympQ.compatible_symplectic_bases | exact GlobalTheory.SympQ.compatible_symplectic_bases | (intros; apply GlobalTheory.SympQ.compatible_symplectic_bases <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isPullbackUniformisation_of_lineBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → ∃ (h : IsPullDeg ρ D₁.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf ρ)).obj G), bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = β ∧ IsPullUnif ρ h bc U₁ U' := by
  first | exact @GlobalTheory.Mum.isPullUnif_of_lbIso | exact GlobalTheory.Mum.isPullUnif_of_lbIso | (intros; apply GlobalTheory.Mum.isPullUnif_of_lbIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  first | exact @GlobalTheory.Mum.TransEven.evenOn_translate | exact GlobalTheory.Mum.TransEven.evenOn_translate | (intros; apply GlobalTheory.Mum.TransEven.evenOn_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  first | exact @GlobalTheory.Mum.exists_unif_move_iso_lbIso | exact GlobalTheory.Mum.exists_unif_move_iso_lbIso | (intros; apply GlobalTheory.Mum.exists_unif_move_iso_lbIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (a : Sp R' ⟶ U.left), FinExt ρ ∧ ρ.Etale ∧ a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.Mum.exists_finEtale_section_of_smooth | exact GlobalTheory.Mum.exists_finEtale_section_of_smooth | (intros; apply GlobalTheory.Mum.exists_finEtale_section_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cp_descent' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.Mum.exists_cp_descent | exact GlobalTheory.Mum.exists_cp_descent | (intros; apply GlobalTheory.Mum.exists_cp_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_near_fibres_of_finiteFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_near_of_finFlat | exact GlobalTheory.Mum.exists_gen_near_of_finFlat | (intros; apply GlobalTheory.Mum.exists_gen_near_of_finFlat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mum

theorem injective_gp_app {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) :
    Function.Injective (M.gp.app U).hom := by
  haveI := M.integral
  haveI := M.dominant
  by_cases hU : (U : Set M.S).Nonempty
  · obtain ⟨x, hx⟩ := M.gp.denseRange.exists_mem_open U.isOpen hU
    have h1 := germ_injective_of_isIntegral (X := M.S) (M.gp x) hx
    have h2 := M.gp.germ_stalkMap U x hx
    have hcl : closure {M.gp x} = (Set.univ : Set M.S) := by
      have hd := M.gp.denseRange
      have hr : Set.range M.gp = {M.gp x} := by
        ext y; constructor
        · rintro ⟨z, rfl⟩
          haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
          rw [Subsingleton.elim z x]; rfl
        · rintro rfl; exact ⟨x, rfl⟩
      rw [← hr]; exact hd.closure_range
    have hF := isField_stalk_of_closure_mem_irreducibleComponents M.S (M.gp x)
      (by rw [hcl]; simp [irreducibleComponents_eq_singleton])
    letI := hF.toField
    have h3 : Function.Injective (M.gp.stalkMap x).hom := RingHom.injective _
    intro a b h
    apply h1
    apply h3
    have ea := congrArg (fun φ => φ.hom a) h2
    have eb := congrArg (fun φ => φ.hom b) h2
    simp only [CommRingCat.comp_apply] at ea eb
    rw [ea, eb, h]
  · have : U = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hU ⟨y, hy⟩
    subst this
    intro a b _; exact Subsingleton.elim a b

def fracRes (R : Type) [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) : R →+* Γ(Sp (FractionRing R), V) :=
  ((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R)))

theorem isUnit_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) {r : R} (hr : r ≠ 0) :
    IsUnit (fracRes R V r) := by
  have : IsUnit (algebraMap R (FractionRing R) r) :=
    Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  exact this.map (((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)

theorem exists_mul_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens)
    (k : Γ(Sp (FractionRing R), V)) : ∃ a r : R, r ≠ 0 ∧ k * fracRes R V r = fracRes R V a := by
  haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  by_cases h : (V : Set (Sp (FractionRing R))).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hV : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    subst hV
    obtain ⟨⟨a, r⟩, hr⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k)
    refine ⟨a, r, nonZeroDivisors.ne_zero r.2, ?_⟩
    have hmap : ((Sp (FractionRing R)).presheaf.map (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)).op) = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      simp
    simp only [fracRes, RingHom.coe_comp, Function.comp_apply, hmap, CommRingCat.hom_id, RingHom.id_apply]
    have hk : k = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hk, ← map_mul, ← hr, IsLocalization.mk'_spec]
  · have hV : V = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    subst hV
    exact ⟨0, 1, one_ne_zero, Subsingleton.elim _ _⟩

theorem appLE_jK_eq_fracRes {R : Type} [CommRing R] [IsDomain R] (f : Sp (FractionRing R) ⟶ Sp R) (hf : f = jK R)
    (V : (Sp (FractionRing R)).Opens) (e : V ≤ f ⁻¹ᵁ ⊤) (x : R) :
    (f.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = fracRes R V x := by
  subst hf
  have h := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [fracRes, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rw [h]
  rfl

theorem gp_app_fracRes {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) (e : U ≤ M.π ⁻¹ᵁ ⊤) (r : R) :
    (M.gp.app U).hom ((M.π.appLE ⊤ U e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      fracRes R (M.gp ⁻¹ᵁ U) r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_jK_eq_fracRes _ M.gp_π _ _ r

theorem injective_and_exists_frac_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  haveI : Module.Flat Γ(M.S, U) Γ(G.left, W) := inferInstance
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have he1 : ∀ c : Γ(G.left, W), e (c ⊗ₜ 1) = (α.app W).hom c := fun c => by
    rw [Algebra.IsPushout.equiv_tmul, map_one, _root_.mul_one]; rfl
  have hinc := Algebra.TensorProduct.includeLeft_injective (S := Γ(M.S, U)) (R := Γ(M.S, U))
    (A := Γ(G.left, W)) (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)) (injective_gp_app M U)
  refine ⟨fun a b h => hinc (e.injective ?_), fun b => ?_⟩
  · change e (a ⊗ₜ 1) = e (b ⊗ₜ 1)
    rw [he1, he1, h]

  have eU : U ≤ M.π ⁻¹ᵁ ⊤ := fun x _ => trivial
  let σ : R →+* Γ(G.left, W) := (algebraMap Γ(M.S, U) Γ(G.left, W)).comp
    ((M.π.appLE ⊤ U eU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hσ : ∀ r : R, (α.app W).hom (σ r) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (fracRes R (M.gp ⁻¹ᵁ U) r) := fun r => by
    rw [← gp_app_fracRes M U eU r]
    change algebraMap Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) Γ(G.left, W) _) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) _ _)
    exact (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) _).symm.trans
      (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) _)
  have key : ∀ y : Γ(G.left, W) ⊗[Γ(M.S, U)] Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U),
      ∃ (c : Γ(G.left, W)) (r : R), r ≠ 0 ∧ e y * (α.app W).hom (σ r) = (α.app W).hom c := by
    intro y
    induction y with
    | tmul c k =>
      obtain ⟨a, r, hr, hk⟩ := exists_mul_fracRes (M.gp ⁻¹ᵁ U) k
      refine ⟨c * σ a, r, hr, ?_⟩
      rw [Algebra.IsPushout.equiv_tmul, hσ, map_mul, hσ, _root_.mul_assoc, ← map_mul, hk]
      rfl
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨c₁, r₁, hr₁, e₁⟩ := h₁
      obtain ⟨c₂, r₂, hr₂, e₂⟩ := h₂
      refine ⟨c₁ * σ r₂ + c₂ * σ r₁, r₁ * r₂, mul_ne_zero hr₁ hr₂, ?_⟩
      rw [map_add (f := _), add_mul, map_mul σ, map_mul, map_add (f := _), map_mul, map_mul, ← e₁, ← e₂]
      ring
  obtain ⟨c, r, hr, hc⟩ := key (e.symm b)
  refine ⟨c, σ r, ?_, ?_⟩
  · rw [hσ]; exact (isUnit_fracRes _ hr).map _
  · rw [← hc, e.apply_symm_apply]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_expansion_weightZero_coefficient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  first | exact @GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | exact GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | (intros; apply GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.Fam

open Classical

theorem finrank_le_min : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hB C
  obtain ⟨hadm, hch⟩ := hB
  haveI : IsNoetherianRing R := hadm.1
  haveI : CharZero R := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let g : FractionRing R →+* K := algebraMap (FractionRing R) K
  let f : R →+* K := g.comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ C.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK R = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UChart.Fam
end
end
