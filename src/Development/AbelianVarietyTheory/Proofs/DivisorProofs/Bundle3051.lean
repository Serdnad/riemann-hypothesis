module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_toricTorsion_label_closed_point : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  first | exact @GlobalTheory.Poinc.ToricLabel.exists_label | exact GlobalTheory.Poinc.ToricLabel.exists_label | (intros; apply GlobalTheory.Poinc.ToricLabel.exists_label <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  first | exact @GlobalTheory.Mum.exists_oneTrait | exact GlobalTheory.Mum.exists_oneTrait | (intros; apply GlobalTheory.Mum.exists_oneTrait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  first | exact @GlobalTheory.Mum.labTors_galConj | exact GlobalTheory.Mum.labTors_galConj | (intros; apply GlobalTheory.Mum.labTors_galConj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.Fib

theorem trait (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x₀ : M.S)
    (hx : M.π x₀ = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ :=
  GlobalTheory.T.exists_completeTrait_over_closedPoint_modification R hR M x₀ hx

theorem compositum (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X)
    (h : a (closedPoint K₁) = b (closedPoint K₂)) :
    ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b :=
  GlobalTheory.T.exists_common_field_of_fieldPoints_same_point X K₁ K₂ a b h

theorem baseChangeIso (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W']
    (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G ξ' β)
    (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W')
    (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y) (he' : IsMonHom e'.hom)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω')
    (i₂ : ResidueField W' →+* Ω') (hc : spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ')
    (hκ : io.comp κ = i₂.comp κ') :
    ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left),
      IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧
      e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') :=
  GlobalTheory.T.groupFibre_baseChange_common_field_iso S G W' G' ξ' β hβ k Y κ' e' he' Ω x κ Ω' io i₂ hc hκ

theorem toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ :=
  GlobalTheory.T.morphismToProjSpace_sectionPullback_comp R N X Y Z L s h g f hs₁ hs₂

theorem toProj_congr {R : Type} [CommRing R] {N : ℕ} {X Z : Scheme.{0}} {L : LB X} (s : Fin (N + 1) → L.Sec)
    {a b : Z ⟶ X} (hab : a = b) {f g : Z ⟶ Sp R} (hfg : f = g)
    (h₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) a) = ⊤) (h₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) b) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) a) h₁ = GlobalTheory.ProjSpace.toProj g (fun i => GlobalTheory.secPull (s i) b) h₂ := by
  subst hab; subst hfg; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem fib : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    (∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s) →
    ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ M.S) (κ : ResidueField R →+* Ω), x ≫ M.π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ (GlobalTheory.Mum.SecEmb.embH s).toScheme), IsMonHom e.hom ∧
      l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) ∧
      l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT hH Ω _ x κ hx
  have hcl : ∀ q : Sp Ω, M.π (x q) = closedPoint R := fun q => by
    rw [← Scheme.Hom.comp_apply, hx, Subsingleton.elim q (closedPoint Ω)]
    exact IsLocalRing.comap_closedPoint (κ.comp (residue R))
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξ0⟩ := trait R hR M _ (hcl (closedPoint Ω))
  obtain ⟨W', _, _, _, io', G', _, β, κ', e', hW', hio', hiof, hβ, hκ', he', hptw⟩ := hT W hW φ ξ hφi hφl hξ
  have hio0 : (spMap io') (closedPoint W') = closedPoint W := by
    letI := io'.toAlgebra
    have : Algebra.IsIntegral W W' := ⟨fun a => hiof.to_isIntegral a⟩
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) hiof.to_isIntegral (maximalIdeal W')))
  have hres0 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  have hpt0 : (spMap (residue W') ≫ spMap io' ≫ ξ) (closedPoint (ResidueField W')) = x (closedPoint Ω) := by
    show ξ (spMap io' (spMap (residue W') (closedPoint _))) = _
    rw [hres0, hio0, hξ0]
  obtain ⟨Ω', _, io, i₂, hc⟩ := compositum M.S Ω (ResidueField W') x _ hpt0.symm
  have hκ : io.comp κ = i₂.comp κ' := by
    have e1 : spMap ((io.comp κ).comp (residue R)) = spMap ((i₂.comp κ').comp (residue R)) := by
      rw [RingHom.comp_assoc, spMap_comp', ← hx, RingHom.comp_assoc, hκ', spMap_comp', spMap_comp', spMap_comp',
        ← hξ, ← Category.assoc, hc]
      simp only [Category.assoc]
    have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    ext a
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact congrArg (fun f : R →+* Ω' => f r) e2
  obtain ⟨e, τ, he, hτ, heτ⟩ := baseChangeIso M.S G W' G' (spMap io' ≫ ξ) β hβ (ResidueField R) Y κ' e' he' Ω x κ
    Ω' io i₂ hc hκ
  have hrange : Set.range (pullback.fst G.hom (spMap io ≫ x)) ⊆ Set.range (GlobalTheory.Mum.SecEmb.embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hH
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hcl _
  let l := IsOpenImmersion.lift (GlobalTheory.Mum.SecEmb.embH s).ι (pullback.fst G.hom (spMap io ≫ x)) hrange
  have hl : l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Ω', inferInstance, io, e, l, he, hl, ?_⟩
  have : IsReduced ((Over.pullback (spMap (io.comp κ))).obj Y).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd Y.hom (spMap (io.comp κ)))
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsReduced ((Over.pullback (spMap io ≫ x)).obj G).left := isReduced_of_isOpenImmersion e.hom.left
  have hsep : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.hom_ext_of_geometricPoints_dense (PSpace.str R N) _ _ ?_ Set.univ dense_univ ?_
  · have a1 : GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s ≫ PSpace.str R N = (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π :=
      GlobalTheory.ProjSpace.toProj_str _ _ _
    have eo : e.hom.left ≫ pullback.snd Y.hom (spMap (io.comp κ)) = pullback.snd G.hom (spMap io ≫ x) := Over.w e.hom
    have a2 : (l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap io ≫ x ≫ M.π := by
      rw [Category.assoc, a1, reassoc_of% hl, pullback.condition_assoc, Category.assoc]
    have a3 : (e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap (io.comp κ) ≫ spMap (residue R) := by
      rw [Category.assoc, Category.assoc, hj, pullback.condition_assoc, reassoc_of% eo]
    rw [a2, a3, hx, spMap_comp', spMap_comp']
    simp only [Category.assoc]
  · intro K _ _ q _
    obtain ⟨⟨hs, hproj⟩, -⟩ := hptw K (q ≫ τ) (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')))
      (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) (by simp) (by simp)
    have e3 : q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') ≫ j =
        (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) ≫ j := by simp only [Category.assoc]
    rw [reassoc_of% heτ, e3, ← hproj]
    have hqb : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β := by
      rw [Category.assoc, hl, ← hτ]; simp only [Category.assoc]
    have hbase : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π =
        (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ G'.hom ≫ spMap (io'.comp φ) := by
      have hqb' : q ≫ l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β := by
        simp only [Category.assoc] at hqb; exact hqb
      rw [Category.assoc q l, reassoc_of% hqb', hβ.1.w_assoc, Category.assoc (spMap io'), hξ, spMap_comp']
      simp only [Category.assoc]
    have hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι)) = ⊤ := by
      rw [hqb]; exact hs
    rw [← Category.assoc]
    show (q ≫ l) ≫ GlobalTheory.ProjSpace.toProj ((GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π)
      (fun i => GlobalTheory.secPull (s i) (GlobalTheory.Mum.SecEmb.embH s).ι) (GlobalTheory.Mum.SecEmb.iSup_nonzeroLocus_embH s) = _
    rw [← GlobalTheory.ProjSpace.toProj_secPull]
    exact (toProj_secPull_secPull R N _ _ _ B s _ (q ≫ l) _ _ hs₂).trans (toProj_congr s hqb hbase _ _)

end GlobalTheory.Mum.SecEmb.Fib
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.ThetaPt

theorem exists_trait_pt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x : M.S),
    M.π x = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧
      ξ (closedPoint W) = x := by
  intro R _ _ _ hR M x hx
  obtain ⟨⟨hRn, -, -, -⟩, hR0⟩ := hR
  haveI := M.integral
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  let A := M.S.presheaf.stalk x
  let ψc : CommRingCat.of R ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ M.π.appTop ≫ M.S.presheaf.germ ⊤ x trivial
  have hcomp : M.S.fromSpecStalk x ≫ M.π = Spec.map ψc := by
    simp only [ψc]
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hπinj : Function.Injective M.π.appTop.hom := fun a b h => GlobalTheory.Mum.jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  have hψi : Function.Injective ψc.hom := by
    simp only [ψc, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (germ_injective_of_isIntegral M.S (U := ⊤) x trivial).comp
      (hπinj.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective)
  have hψl : IsLocalHom ψc.hom := by
    refine ((IsLocalRing.local_hom_tfae ψc.hom).out 1 5).2 ?_
    have e1 : (Spec.map ψc) (closedPoint A) = closedPoint R := by
      have h0 := congrArg M.π (Scheme.fromSpecStalk_closedPoint (x := x))
      rw [hx] at h0
      rw [← hcomp]
      exact h0
    exact congrArg PrimeSpectrum.asIdeal e1
  haveI : CharZero A := charZero_of_injective_ringHom hψi
  obtain ⟨V, _, _, _, φ₀, hV, hφ₀i, hφ₀l⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V)
      (φ₀ : A →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ₀ ∧ IsLocalHom φ₀ := by
    by_cases h : IsField A
    · letI := h.toField
      refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
        PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) PowerSeries.C_injective
    · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
      exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
        ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, φ₀.comp ψc.hom, spMap φ₀ ≫ M.S.fromSpecStalk x, hV,
    hφ₀i.comp hψi, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom]
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint φ₀)) Scheme.fromSpecStalk_closedPoint)

theorem isLocalHom_of_finite {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') (hf : io.Finite) : IsLocalHom io := by
  letI := io.toAlgebra
  haveI : Module.Finite W W' := hf
  have hmax : (maximalIdeal W').comap (algebraMap W W') = maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W'))
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have : a ∈ (maximalIdeal W').comap (algebraMap W W') := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h
  exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 this) ha

theorem exists_closedFibre_pt {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') [IsLocalHom io] {S : Scheme.{0}} (G : Over S) (G' : Over (Sp W')) (ξ : Sp W ⟶ S)
    (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom (spMap io ≫ ξ)) (g : G.left)
    (hg : G.hom g = ξ (closedPoint W)) :
    ∃ q : ((Over.pullback (spMap (residue W'))).obj G').left, (pullback.fst G'.hom (spMap (residue W')) ≫ β) q = g := by
  have h1 : (spMap io) (closedPoint W') = closedPoint W := IsLocalRing.comap_closedPoint io
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') (by rw [hg]; exact (congrArg ξ h1).symm)
  have hg1 : β (h.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (h.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have h2 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (h.isoPullback.inv z) (closedPoint _) (hg2.trans h2.symm)
  exact ⟨q, by rw [Scheme.Hom.comp_apply, hq1, hg1]⟩

theorem toProj_congr {R : Type} [CommRing R] {M : ℕ} {Y : Scheme.{0}} {L : LB Y} {f f' : Y ⟶ Sp R}
    (e : f = f') (s : Fin (M + 1) → L.Sec) (hs hs' : ⨆ i, nonzeroLocus (s i) = ⊤) :
    GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.ProjSpace.toProj f' s hs' := by
  subst e; rfl

theorem mem_basicOpen_theta : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ (g : (GlobalTheory.Mum.SecEmb.embH s).toScheme) (y : Y.left), y ∈ O →
    M.π (G.hom ((GlobalTheory.Mum.SecEmb.embH s).ι g)) = closedPoint R → GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s g = j y →
    ∃ i : L.ι, (GlobalTheory.Mum.SecEmb.embH s).ι g ∈ G.left.basicOpen (θ.f i) := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT g y hy hgc hgj
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξx⟩ := exists_trait_pt R hR M _ hgc
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hiof, hpb, hκ, he, H⟩ := hT W hW φ ξ hφi hφl hξ
  haveI := isLocalHom_of_finite io hiof
  obtain ⟨q, hq⟩ := exists_closedFibre_pt io G G' ξ β hpb.1 _ hξx.symm
  let Ω : Type := (((Over.pullback (spMap (residue W'))).obj G').left).residueField q
  let p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left :=
    (((Over.pullback (spMap (residue W'))).obj G').left).fromSpecResidueField q
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨p', hp'⟩ : ∃ p', p' = p ≫ pullback.fst G'.hom (spMap (residue W')) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) := ⟨_, rfl⟩
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := H Ω p p' y' hp' hy'
  let pt : Sp Ω := closedPoint Ω
  have hpt : ∀ z : Sp Ω, z = pt := fun z => Subsingleton.elim _ _
  have hppt : p pt = q := Scheme.fromSpecResidueField_apply q pt
  have hg' : (p' ≫ β) pt = (embH s).ι g := by
    rw [hp', Category.assoc, Scheme.Hom.comp_apply, hppt]
    exact hq
  have hrange : Set.range (p' ≫ β) ⊆ Set.range (embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [hpt z, hg']
    exact ⟨g, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Sp Ω ⟶ (embH s).toScheme, l₀ ≫ (embH s).ι = p' ≫ β :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hl₀pt : l₀ pt = g := by
    apply (embH s).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hl₀, hg']
  obtain ⟨-, hs2, e2⟩ := GlobalTheory.Mum.toProj_secPull_of_gs (Z := Sp Ω) s (fun i => GlobalTheory.secPull (s i) (embH s).ι)
    ((embH s).ι ≫ G.hom ≫ M.π) (iSup_nonzeroLocus_embH s) (p' ≫ β) l₀ (fun z => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (Set.mem_univ ((p' ≫ β) z)))
      have hla : l₀ z ∈ (B.pull (embH s).ι).U (fun _ => a) := Set.mem_iInter.2 fun _ => by
        show (embH s).ι (l₀ z) ∈ B.U a
        rw [← Scheme.Hom.comp_apply, hl₀]; exact ha
      refine ⟨a, fun _ => a, 1, ha, hla, fun i => ?_⟩
      rw [Units.val_one, _root_.one_mul]
      refine Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull B (embH s).ι) (s i) l₀ z (fun _ => a) hla).symm
      rw [hl₀]; rfl)
  have hstr : p' ≫ G'.hom ≫ spMap (io.comp φ) = l₀ ≫ (embH s).ι ≫ G.hom ≫ M.π := by
    have hw : β ≫ G.hom ≫ M.π = G'.hom ≫ spMap io ≫ ξ ≫ M.π := by
      rw [← Category.assoc, hpb.1.w]; simp only [Category.assoc]
    have hc : spMap (io.comp φ) = spMap io ≫ spMap φ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [reassoc_of% hl₀, hw, hξ, hc]
  have key : y' ≫ j = l₀ ≫ embF (G.hom ≫ M.π) s := by
    rw [← hproj, toProj_congr hstr _ hs hs2]
    exact e2
  have hyy : y' pt = y := by
    apply hji.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, hl₀pt, hgj]
  have hθ := hnz pt (hyy ▸ hy)
  rw [hg'] at hθ
  exact TopologicalSpace.Opens.mem_iSup.1 hθ

end GlobalTheory.Mum.SecEmb.ThetaPt

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubical_structure_e8_power : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  first | exact @GlobalTheory.PowE8.exists_cp_e8LB | exact GlobalTheory.PowE8.exists_cp_e8LB | (intros; apply GlobalTheory.PowE8.exists_cp_e8LB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_symplecticBasis_e8Factor_torsion : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ N : ℕ), Odd N → ∀ (K : Type) [Field K] [IsAlgClosed K], (N : K) ≠ 0 →
  ∀ (z : Kˣ), IsPrimitiveRoot z N → ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (P'.A ⟶ B)), E8Fibration.IsProd pr →
  (∀ (s t s' t' : Fin 8 → ℤ), dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
    ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
    ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
      (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
      ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c) →
  ∃ b : Fin gQ ⊕ Fin gQ → (Out.baseOver (Sp K) ⟶ B), (∀ c, b c ^ N = 1) ∧
    ∀ (x y : Fin 8 → (Fin gQ ⊕ Fin gQ → ℤ)) (X Y : Out.baseOver (Sp K) ⟶ P'.A),
      (∀ u, X ≫ pr u = ∏ c, b c ^ x u c) → (∀ u, Y ≫ pr u = ∏ c, b c ^ y u c) →
      Out.WeilIs P'.A P'.L N X Y (unitOn z ^ ∑ u, ∑ v, E8Fibration.e8 W u v * omegaStd (x u) (y v)) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis.exists_basis | exact GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis.exists_basis | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis.exists_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_act_linComb_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | exact GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_act_prod_eq_one : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | exact GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id <;> assumption)
end
