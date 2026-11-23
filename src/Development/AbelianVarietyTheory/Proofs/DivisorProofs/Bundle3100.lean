module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.traitFibreIso_comm_neg : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  first | exact @GlobalTheory.ThetaMove.negT_fibre_comm | exact GlobalTheory.ThetaMove.negT_fibre_comm | (intros; apply GlobalTheory.ThetaMove.negT_fibre_comm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.traitFibreIso_comm_translation : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  first | exact @GlobalTheory.Mum.trait_transl_comm | exact GlobalTheory.Mum.trait_transl_comm | (intros; apply GlobalTheory.Mum.trait_transl_comm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  first | exact @GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | exact GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | (intros; apply GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_carries_transport_uniformising_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k), ∃ σ'' : SecK C.P.L.L T.β k, T.Carries u σ' σ'' := by
  first | exact @GlobalTheory.Mum.Trait.exists_carries | exact GlobalTheory.Mum.Trait.exists_carries | (intros; apply GlobalTheory.Mum.Trait.exists_carries <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  first | exact @GlobalTheory.Mum.unit_nonfield | exact GlobalTheory.Mum.unit_nonfield | (intros; apply GlobalTheory.Mum.unit_nonfield <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.coverTrait_expansion_scale_both_scalars : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  first | exact @GlobalTheory.Mum.Trait.exp_mul_left | exact GlobalTheory.Mum.Trait.exp_mul_left | (intros; apply GlobalTheory.Mum.Trait.exp_mul_left <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_fibre_iso_genericFibre_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  first | exact @GlobalTheory.Mum.Trait.exists_fibre_iso | exact GlobalTheory.Mum.Trait.exists_fibre_iso | (intros; apply GlobalTheory.Mum.Trait.exists_fibre_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.gs_scal_base {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) {Z : Scheme.{0}}
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  have hc : ∀ {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (x : A),
      scal q (φ x) = scal (q ≫ spMap φ) x := by
    intro A B _ _ Y q φ x
    have e := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [e]
  rw [hc, hc]
  have hg : ∀ {A : Type} [CommRing A] {Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Sp A) (x : A),
      gs f z ⊤ (scal q x) = gs (f ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) :=
    fun f q x => gs_pull f q z ⊤ trivial _
  rw [hg, hg]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem Trait.exp_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  intro R _ _ _ D C W _ _ _ T k F s₁ s₂ r t u hrel hExp
  have h1 := GlobalTheory.Mum.Trait.exp_mul_left R D C W T k s₂ F 1 u (T.φ r) hExp
  rw [_root_.mul_one] at h1
  obtain ⟨σ, hσ, hs⟩ := h1
  refine ⟨σ, hσ, ?_⟩
  intro Z p p' hp z J hJ
  rw [hs Z p p' hp z J hJ, T.gs_scal_base p p' hp z r, T.gs_scal_base p p' hp z t]
  exact (hrel Z p' z J hJ).symm

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_scalar_cancel_of_isField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.cancel_field | exact GlobalTheory.Mum.cancel_field | (intros; apply GlobalTheory.Mum.cancel_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  first | exact @GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | exact GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | (intros; apply GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaValuePoint_lies_over_moduliPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  first | exact @GlobalTheory.Poinc.Sep.valPt_lies_over | exact GlobalTheory.Poinc.Sep.valPt_lies_over | (intros; apply GlobalTheory.Poinc.Sep.valPt_lies_over <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermWeight

theorem sval_eq_secRatio_mul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) (hz : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (GlobalTheory.ProjSpace.secRatio a b) * sval a r z J := by
  have hm : r z ∈ nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (GlobalTheory.ProjSpace.secRatio_on a b (fun k => J (r ≫ φ k))
    (W := nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k))) inf_le_left inf_le_right)
  exact (gs_res r z inf_le_right hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z inf_le_left hm _) (gs_res r z inf_le_right hm _))))

theorem isWt_secRatio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), (∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J → val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J) → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ (k : ℕ) (α : D.X) (b₀ : D.SecB k 0) (b : D.SecB k α) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → GlobalTheory.UU.IsWt i (nonzeroLocus τ₀) (GlobalTheory.ProjSpace.secRatio τ₀ τ) α := by
  intro R _ _ D Y i hi hk k α b₀ b τ₀ τ h₀ h
  have := Y.isMonHom_q
  refine GlobalTheory.GtCoordCompare.isWt_of_gs fun Z t g hg z => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have hq : (((t ≫ i) * g) ≫ Y.q).left = (g ≫ Y.q).left := GlobalTheory.GtCoordCompare.act_comp hk.w t g
  have z₁ : val ((Y.Φ Z ((t ≫ i) * g)).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have z₂ : val ((Y.Φ Z g).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have e₀ : sval τ₀ ((t ≫ i) * g).left z J = sval τ₀ g.left z J := by
    rw [h₀ Z _ z J hJ, h₀ Z g z J hJ, hq, z₁, z₂]
  have e : sval τ ((t ≫ i) * g).left z J =
      (gm t.left z ⊤ (charUnit (Sp R) D.X α)).val * sval τ g.left z J := by
    rw [h Z _ z J hJ, h Z g z J hJ, hq, hi α Z t g z J hJ, Units.val_mul, mul_left_comm]
  have hz : g.left z ∈ nonzeroLocus τ₀ := hg (Set.mem_univ z)
  have hu : IsUnit (sval τ₀ g.left z J) := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).2 hz
  have hz' : ((t ≫ i) * g).left z ∈ nonzeroLocus τ₀ := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).1 (e₀ ▸ hu)
  refine hu.mul_right_cancel ?_
  rw [_root_.mul_assoc, ← sval_eq_secRatio_mul τ₀ τ g.left z hJ hz, ← e, sval_eq_secRatio_mul τ₀ τ _ z hJ hz', e₀]

end GlobalTheory.Mum.TermWeight
end
end
