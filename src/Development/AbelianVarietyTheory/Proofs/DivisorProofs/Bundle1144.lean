module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
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
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nhds_charUnit : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hk hχ y
  have hpb := GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hk
  have hpb' : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    hpb.map (Over.forget S)
  obtain ⟨W, m₁₂, m₂₃, m₁₃, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_kernelAction_triple_overlap S A N T i χ hi hχ
  have hpq : pmap q T = q ▷ T := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]
  have hsq := GlobalTheory.SemiRigid.isPullback_whiskerRight q T
  have hA : IsAffineHom (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hF : Flat (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hS : Surjective (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  exact GlobalTheory.T.locally_trivial_unit_cocycle_scheme _ _ _ _ (pmap q T).left (actMap i T).left (prMap A N T).left m₁₂ m₂₃ m₁₃ _
    hA hF hS hpb' h1 h2 h3 h4 y

end GlobalTheory.CharKer
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusPart

def GoodCover {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) : Prop :=
  ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen u V

def IsKer {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧ IsPullback u (toUnit _) q η[B]

def TorPol {O : Type} [CommRing O] (c : O →+* O) {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) {X : Type}
    [AddCommGroup X] (u : splitTorus S X ⟶ G) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (G' : Over (Sp K)) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G')
    (P : Out.PolAV (Sp K)) (q : G' ⟶ P.A) (j : OAct O P.A),
    IsActPull i' i x φ ∧ TorusCompat x φ u' u ∧ IsKer u' q ∧ (∀ a, i'.act a ≫ q = q ≫ j.act a) ∧ IsRosati c P j

def QFin {S : Scheme.{0}} (Z : Over S) : Prop :=
  Flat Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ LocallyQuasiFinite Z.hom

def RatOver {S : Scheme.{0}} (Z : Over S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∀ (Ω : Type) [Field Ω] (β : K →+* Ω) (y : Sp Ω ⟶ Z.left), y ≫ Z.hom = spMap β ≫ x →
    ∃ y₁ : Sp K ⟶ Z.left, y₁ ≫ Z.hom = x ∧ spMap β ≫ y₁ = y

def WtGeneric : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G),
    IsIntegral (splitTorus S X ⊗ G).left → ∀ (V : G.left.Opens) (f : Γ(G.left, V)) (χ : X) (Z : Over S)
      (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), IsDominant (lift t g).left →
      ∀ (h₁ : ⊤ ≤ ((t ≫ u) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
        (((t ≫ u) * g).left.appLE _ ⊤ h₁).hom f =
          t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom f → Wt u V f χ

theorem isKer_of_isQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsQuot u q) : IsKer u q :=
  have := h.2.2.2.2.1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, inferInstance, h.2.2.2.2.2.1⟩

theorem isKer_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (T : TorusExtension G) :
    letI := T.addCommGroup; letI := T.grpB; IsKer T.i T.q :=
  ⟨T.q_hom, T.q_flat, T.q_surjective, T.q_quasiCompact, T.isKernel⟩

theorem IsKer.comp_iso {S : Scheme.{0}} {T G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B'] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : B ≅ B') (he : IsMonHom (q ≫ e.hom)) : IsKer u (q ≫ e.hom) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨he, by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, h₅.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp) ?_⟩
  rw [Iso.refl_hom, Category.id_comp, ← IsMonHom.one_hom q, Category.assoc, IsMonHom.one_hom]

theorem IsKer.baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left}
    (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback B' B f ψ) {u : splitTorus S X ⟶ G} {u' : splitTorus S' X ⟶ G'}
    (hT : TorusCompat f φ u' u) {q : G ⟶ B} (h : IsKer u q) :
    ∃ q' : G' ⟶ B', IsKer u' q' ∧ IsPullback φ q'.left q.left ψ := by
  obtain ⟨e, he, heF⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  obtain ⟨d, hd, hdF⟩ := grpPullback_iso (isGrpPullback_pullback B f) hψ
  obtain ⟨_, _, _, _, h₅⟩ := h
  have sq := isPullback_pullback_map_left f q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : u' ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map u := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f u).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (u'.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ u.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback u' (toUnit _) (e.hom ≫ (Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
    refine (isPullback_kernel_baseChange f h₅).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hK : IsKer u' (e.hom ≫ (Over.pullback f).map q) := ⟨inferInstance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance, hk⟩
  refine ⟨_, hK.comp_iso d inferInstance, ?_⟩
  refine IsPullback.of_bot (v₂₁ := B'.hom) (v₂₂ := B.hom) ?_ ?_ hψ.1
  · rw [Over.w, Over.w]
    exact hφ.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hdF, ← heF, Category.assoc]
    exact congrArg (_ ≫ ·) sq.w

theorem IsKer.exists_oAct {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) {O : Type} [CommRing O] (i : OAct O G) (hu : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]) :
    ∃ j : OAct O B, ∀ a, i.act a ≫ q = q ≫ j.act a := by
  obtain ⟨_, _, _, _, h₅⟩ := h
  have := i.hom
  have : Epi q := FlatQuotient.epi_of_flat_surjective q
  choose fB hm hfB using fun a => FlatQuotient.exists_desc q u (i.act a ≫ q) h₅ (hu a)
  refine ⟨⟨fB, hm, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => (hfB a).symm⟩
  · rw [← cancel_epi q, hfB, i.one, Category.comp_id, Category.id_comp]
  · rw [← cancel_epi q, hfB, i.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · rw [← cancel_epi q, hfB, MonObj.comp_mul, hfB, hfB, i.add, MonObj.mul_comp]

theorem exists_isActPull {O : Type} [CommRing O] {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G]
    [IsCommMonObj G] (i : OAct O G) : IsActPull (OAct.pullback f G i) i f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ => pullback.lift_fst _ _ _⟩

end GlobalTheory.TorusPart
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevTrans

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frGL_conj {n : ℕ} (β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (u y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (β' * intGL F E n u * β⁻¹) * frGL β y * (β' * intGL F E n u * β⁻¹)⁻¹ = frGL β' (u * y * u⁻¹) := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem transport {n n' : ℕ} (h : n = n') (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β' x' : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (u : GL (Fin n') (Formalism.L2.Herm.intAf F E))
    (j : Matrix (Fin n') (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hc : HMul.hMul x'.val j = HMul.hMul j x.val)
    (hf : HMul.hMul j β.val = (β' * intGL F E n' u).val.submatrix id (Fin.cast h))
    (Pg : Finset (Pl E)) (hu : ∀ PP ∈ Pg, Formalism.UG.bc (resS F PP) u = 1) (r t : ℕ) (hr : r ≤ n) (hr' : r ≤ n') :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ PP ∈ Pg,
      (redFn β PP x ∈ blockTri (blkOf r t) ↔ redFn β' PP x' ∈ blockTri (blkOf r t)) ∧
        upperLeftBlock hr' (redFn β' PP x') = upperLeftBlock hr (redFn β PP x)) := by
  subst h
  have hf' : j * β.val = (β' * intGL F E n u).val := hf
  set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ
  have hj : j = J.val := by
    rw [hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hx : x' = J * x * J⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    show x'.val * J.val = J.val * x.val
    rw [← hj]
    exact hc
  have key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹) := frGL_conj β β' u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨u * y * u⁻¹, by rw [hx, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨u⁻¹ * y * u, ?_⟩
    have h1 := key (u⁻¹ * y * u)
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨y, rfl⟩ PP hP
    have h2 : redFn β' PP x' = redFn β PP (frGL β y) := by
      rw [hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]
      simp
    rw [h2]
    exact ⟨Iff.rfl, rfl⟩

end General

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem finE_unitary (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D))) := by
    ext i j
    exact fin_cA _
  rw [e1] at h2
  exact h2

theorem levtrans : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  intro D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ
  obtain ⟨h, u, hf, hu⟩ := hI.frame
  obtain ⟨h1, h2⟩ := transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
  · funext PP
    exact (h2 (parLev_St hm) PP.1 PP.2).2

end GlobalTheory.LevTrans

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqTrans

theorem asAlg_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (x : MonoidAlgebra ℂ H) :
    Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) x =
      ρ.asAlgebraHom (MonoidAlgebra.domCongr ℂ ℂ e x) := by
  have : Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) =
      ρ.asAlgebraHom.comp (MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · exact Subsingleton.elim _ _
  rw [this]; rfl

theorem killed_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (I : Set (MonoidAlgebra ℂ H)) (I' : Set (MonoidAlgebra ℂ H'))
    (h1 : ∀ x ∈ I, MonoidAlgebra.domCongr ℂ ℂ e x ∈ I')
    (h2 : ∀ x ∈ I', MonoidAlgebra.domCongr ℂ ℂ e.symm x ∈ I) :
    killed (ρ.comp e.toMonoidHom : Representation ℂ H X) I = killed ρ I' := by
  ext v
  rw [mem_killed, mem_killed]
  constructor
  · intro h x hx
    have := h _ (h2 x hx)
    rw [asAlg_comp, ← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply] at this
    exact this
  · intro h x hx
    rw [asAlg_comp]
    exact h _ (h1 x hx)

theorem isDC_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (J : Subgroup H) (J' : Subgroup H')
    (hJ : ∀ g, g ∈ J ↔ e g ∈ J') (x : H) (R : Finset H) (h : Bridge.IsDC J x R) :
    Bridge.IsDC J' (e x) (R.map e.toEquiv.toEmbedding) := by
  have hJ' : ∀ g' : J', e.symm g' ∈ J := fun g' => (hJ _).2 (by simp)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨⟨e k₁, (hJ _).1 k₁.2⟩, ⟨e k₂, (hJ _).1 k₂.2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 (e.symm k₁ * x * e.symm k₂) ⟨⟨_, hJ' k₁⟩, ⟨_, hJ' k₂⟩, rfl⟩
    refine ⟨e a, ⟨Finset.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · have := (hJ _).1 ha'
      simpa using this
    · rintro b ⟨hb, hb'⟩
      obtain ⟨b, hbR, rfl⟩ := Finset.mem_map.1 hb
      have : b = a := hu b ⟨hbR, (hJ _).2 (by simpa using hb')⟩
      rw [this]; rfl

variable {D : D7}

theorem mem_levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GfC V) :
    (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      finE V (k : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ∧
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (k : GA D V)) : G0 Pg r) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem levChi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GA D V) :
    levChi V β (withP (princDat V.rank r t hr Pg χ) P) k =
      ((ext1 P.H P.chi (rTup β (princDat V.rank r t hr Pg χ) (finE V k) : G0 Pg r) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  congr 1
  have h1 : (withP (princDat V.rank r t hr Pg χ) P).s = 0 := rfl
  have h2 : (withP (princDat V.rank r t hr Pg χ) P).Q = ∅ := rfl
  rw [h1, h2]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem map_mem (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank)
    (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃* GfC V')
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (hrk : V.rank = V'.rank)
    (h1 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔
      finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ'))
    (h2 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) →
      (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) =
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r))
    (h3 : ∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α))
    (x : MonoidAlgebra ℂ (GfC V)) (hx : x ∈ eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) :
    MonoidAlgebra.domCongr ℂ ℂ Φ x ∈ eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg := by
  have hlev : ∀ (P : LevelP Pg r ℂ) (k : GfC V), (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      (Φ k : GA D V') ∈ levG V' β' (withP (princDat V'.rank r t hr' Pg χ') P) := by
    intro P k
    rw [mem_levG, mem_levG]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(h1 k).1 a, by rw [h2 k a]; exact b⟩
    · rintro ⟨a, b⟩
      have a' := (h1 k).2 a
      exact ⟨a', by rw [← h2 k a']; exact b⟩
  rcases hx with (⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩
  · refine Or.inl (Or.inl ⟨Φ k, (hlev P k).1 hk, ?_⟩)
    rw [levChi_eq, levChi_eq, h2 k ((mem_levG V β r t hr Pg χ P k).1 hk).1, map_sub, MonoidAlgebra.domCongr_single,
      MonoidAlgebra.domCongr_single, map_one Φ]
  · refine Or.inl (Or.inr ⟨fun g => Φ (κ g), fun g => ⟨(Φ (κ g)).2, (h1 _).1 (hκ g).2.1, ?_⟩, ?_⟩)
    · exact (h2 _ (hκ g).2.1).trans (hκ g).2.2
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ]
        simp only [MonoidAlgebra.domCongr_single]
  · refine Or.inr ⟨P0, hP0, k, hrk ▸ hk, Φ α, R.map Φ.toEquiv.toEmbedding, (h3 P0 hP0 k α).1 hα, ?_, ?_⟩
    · rw [← map_inv Φ]
      exact isDC_map Φ _ _ (fun g => hlev (LevelP.triv Pg r ℂ) g) _ _ hR
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ, Finset.sum_map]
        simp only [MonoidAlgebra.domCongr_single]
        rfl

theorem killed_eqSet_comp : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  intro D V V' β β' r t hr hr' Pg χ χ' Φ G _ _ eG c P Pl0 ok pl q Sg X _ _ ρ hrk h1 h2 h3
  refine killed_comp ρ Φ.toMulEquiv _ _
    (map_mem V V' β β' r t hr hr' Pg χ χ' Φ.toMulEquiv eG c P ok pl q Sg hrk h1 h2 h3) ?_
  have e : ∀ κ : GfC V', Φ (Φ.toMulEquiv.symm κ) = κ := fun κ => Φ.toMulEquiv.apply_symm_apply κ
  refine map_mem V' V β' β r t hr' hr Pg χ' χ Φ.toMulEquiv.symm eG c P ok pl q Sg hrk.symm ?_ ?_ ?_
  · intro κ
    rw [h1, e]
  · intro κ hκ
    have := h2 (Φ.toMulEquiv.symm κ) ((h1 _).2 (by rw [e]; exact hκ))
    rw [e] at this
    exact this.symm
  · intro P0 hP0 k α
    rw [h3 P0 hP0, e]

end GlobalTheory.CuspMult.EqTrans
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.surjective_of_noetherian_case : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (exact GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (intros; apply GlobalTheory.EtC.gmPhi_surjective_of_noetherian  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) → ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i), pull _ (spMap (GlobalTheory.EtC.GmStep.laurentMap (algebraMap A S))) _ _ x = 0 → ∃ t : Finset S, pull _ (spMap (GlobalTheory.EtC.GmStep.laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  exact @GlobalTheory.EtC.GmStep.KillColim.kill_colim
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.mem_completedOrder_of_local_congruence_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) → z ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | exact GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | (intros; apply GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn <;> assumption)
end
