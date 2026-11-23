module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  first | exact @GlobalTheory.SiegAct.siegel_group_action | exact GlobalTheory.SiegAct.siegel_group_action | (intros; apply GlobalTheory.SiegAct.siegel_group_action <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y), ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧ (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  first | exact @GlobalTheory.Mum.closed_product_image | exact GlobalTheory.Mum.closed_product_image | (intros; apply GlobalTheory.Mum.closed_product_image <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  first | exact @GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | exact GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj | (intros; apply GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galois_closure_local_domain_extension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  first | exact @GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | exact GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | (intros; apply GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galois_quotient_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  first | exact @GlobalTheory.Mum.exists_galois_quotient | exact GlobalTheory.Mum.exists_galois_quotient | (intros; apply GlobalTheory.Mum.exists_galois_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_mul_point_on_pullback_containing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (N : Near M.π G'), ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π), (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧ h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left := by
  first | exact @GlobalTheory.Mum.Near.exists_mul_pt_pullback | exact GlobalTheory.Mum.Near.exists_mul_pt_pullback | (intros; apply GlobalTheory.Mum.Near.exists_mul_pt_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  first | exact @GlobalTheory.Mum.quot_affine_spec_invariants | exact GlobalTheory.Mum.quot_affine_spec_invariants | (intros; apply GlobalTheory.Mum.quot_affine_spec_invariants <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_invariant_functions_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app V).hom := by
  first | exact @GlobalTheory.Mum.InvFun.invariant_functions | exact GlobalTheory.Mum.InvFun.invariant_functions | (intros; apply GlobalTheory.Mum.InvFun.invariant_functions <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.glue_local_descents_near_closedFibre_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  first | exact @GlobalTheory.Mum.GlueNear.glue_near | exact GlobalTheory.Mum.GlueNear.glue_near | (intros; apply GlobalTheory.Mum.GlueNear.glue_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.groupLaw_descends_galois_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  first | exact @GlobalTheory.Mum.law_of_galAct_invariant | exact GlobalTheory.Mum.law_of_galAct_invariant | (intros; apply GlobalTheory.Mum.law_of_galAct_invariant <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalOrbit

variable {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'}

theorem spMap_gal_comp (σ : Gal ρ) : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
  rw [← Spec.map_comp]; congr 1; ext r; exact σ.2 r

theorem spMap_gal_mul (σ τ : Gal ρ) :
    spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_gal_one : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

variable {X Z : Scheme.{0}} {f : X ⟶ Sp R} {p : Z ⟶ X} {s : Z ⟶ Sp R'}
  (hpb : IsPullback p s f (spMap ρ))

def act (σ : Gal ρ) : Z ⟶ Z :=
  hpb.lift p (s ≫ spMap (Gal.hom σ)) (by rw [Category.assoc, spMap_gal_comp, hpb.w])

@[reassoc] theorem galoisBaseChangeSchemeAction_comp_snd (σ : Gal ρ) : act hpb σ ≫ s = s ≫ spMap (Gal.hom σ) := hpb.lift_snd _ _ _

theorem act_one : act hpb 1 = 𝟙 Z := by
  have hp : act hpb 1 ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.id_comp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, spMap_gal_one, Category.comp_id, Category.id_comp])

theorem act_mul (σ τ : Gal ρ) : act hpb (σ * τ) = act hpb σ ≫ act hpb τ := by
  have hp (g : Gal ρ) : act hpb g ≫ p = p := hpb.lift_fst _ _ _
  exact hpb.hom_ext (by rw [hp, Category.assoc, hp, hp])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, Category.assoc, galoisBaseChangeSchemeAction_comp_snd, galoisBaseChangeSchemeAction_comp_snd_assoc, spMap_gal_mul])

def actAut : Gal ρ →* Aut Z where
  toFun σ :=
    { asIso :=
        { hom := act hpb σ⁻¹
          inv := act hpb σ
          hom_inv_id := by rw [← act_mul, inv_mul_cancel, act_one]
          inv_hom_id := by rw [← act_mul, mul_inv_cancel, act_one] } }
  map_one' := Aut.ext (Iso.ext (by change act hpb 1⁻¹ = 𝟙 Z; rw [inv_one, act_one]))
  map_mul' σ τ := Aut.ext (Iso.ext (by
    change act hpb (σ * τ)⁻¹ = act hpb τ⁻¹ ≫ act hpb σ⁻¹
    rw [mul_inv_rev, act_mul]))

end GlobalTheory.Mum.GalOrbit

namespace GlobalTheory.Mum

theorem gal_transitive_on_fibres : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'],
    Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) →
    ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z),
      h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  intro R R' _ _ _ hinj hG Y hfl Z p s hpb z z' hzz
  have : Finite (Gal (algebraMap R R')) := hG.1
  have : Flat Y.hom := hfl
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hp (σ : Gal (algebraMap R R')) : GalOrbit.act hpb σ ≫ p = p := hpb.lift_fst _ _ _
  have hinv : ∀ W : Y.left.Opens, IsAffineOpen W → ∀ u : Γ(Z, p ⁻¹ᵁ W),
      GlobalTheory.IsInvariantSection (GalOrbit.actAut hpb) _ u → u ∈ Set.range (p.app W) := by
    intro W hW u hu
    refine (InvFun.affine_inv (algebraMap R R') hinj hG hpb (GalOrbit.act hpb) hp
      (GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb) hW).2 u fun σ hσ => ?_
    obtain ⟨h₁, h₂⟩ := hu σ⁻¹
    have key : ∀ (τ τ' : Gal (algebraMap R R')) (_ : τ = τ') (e : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ ⁻¹ᵁ (p ⁻¹ᵁ W))
        (e' : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ' ⁻¹ᵁ (p ⁻¹ᵁ W)),
        ((GalOrbit.act hpb τ).appLE _ _ e).hom u = ((GalOrbit.act hpb τ').appLE _ _ e').hom u := by
      rintro τ _ rfl _ _; rfl
    exact (key _ _ (inv_inv σ).symm hσ h₁).trans h₂
  obtain ⟨g, hg⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant (GalOrbit.actAut hpb) p
    (fun g => hp g⁻¹) hinv z z').1 hzz
  exact ⟨g⁻¹, GalOrbit.act hpb g⁻¹, hp _, GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb _, hg⟩

end GlobalTheory.Mum
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem eval₂_eq_of_sub_mem_of_coeff_mem_pow {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (I : Ideal R) (e : ℕ) (hbot : (I ^ (e + 1)).map φ = ⊥) (F : MvPolynomial σ R)
    (hF : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) (a b : σ → B) (hab : ∀ l, a l - b l ∈ I.map φ) :
    MvPolynomial.eval₂ φ a F = MvPolynomial.eval₂ φ b F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simp only [map_prod, map_pow]
    exact Finset.prod_congr rfl fun l _ => by rw [Ideal.Quotient.eq.2 (hab l)]
  have h2 : φ (AddMonoidAlgebra.coeff F m) * ((∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l) ∈
      (I ^ (e + 1)).map φ := by
    rw [pow_succ, Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hF m)) h1
  rw [hbot, Ideal.mem_bot, mul_sub, sub_eq_zero] at h2
  exact h2

theorem eval₂_mem_map_of_coeff_mem {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (J : Ideal R) (F : MvPolynomial σ R) (hF : ∀ m, AddMonoidAlgebra.coeff F m ∈ J) (a : σ → B) :
    MvPolynomial.eval₂ φ a F ∈ J.map φ := by
  rw [MvPolynomial.eval₂_eq]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m))

theorem Charts.ev_change (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hpb : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (n : ℕ) (C : Charts I Y β n)
    (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (hc : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) (i j : Fin (n + 1)) :
    C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧
      rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) =
        rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d *
          rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  obtain ⟨hbot, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hpb n C
  obtain ⟨-, hself, hcoc⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C
  have h1 : C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) :=
    eval₂_mem_map_of_coeff_mem _ _ F hc _
  refine ⟨h1, ?_, ?_⟩
  · have h := Ideal.mul_mem_mul (hself e i) h1
    have h' : (C.ρ e i i - 1) * C.ev e i F ∈ towerIdeal Y e (I ^ (e + 1)) (C.D e i) := by
      have hm : towerIdeal Y e (I ^ (e + 1)) (C.D e i) =
          towerIdeal Y e I (C.D e i) * towerIdeal Y e (I ^ e) (C.D e i) := by
        unfold towerIdeal
        rw [← Ideal.map_mul, ← pow_succ']
      rw [hm]
      exact h
    rw [hbot, Ideal.mem_bot, sub_mul, one_mul, sub_eq_zero] at h'
    exact h'
  · have hi : (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    have hj : (rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e j)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    simp only [Charts.ev, MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hi, hj, ← eval₂_scale _ _ _ hF]
    exact eval₂_eq_of_sub_mem_of_coeff_mem_pow _ I e (hbot e _) F hc _ _ fun l => hcoc e i j l

end GlobalTheory.FormalAlg
end
