module

public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Mathlib.Tactic.ENatToNat
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma scal {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) =
      (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appLE ⊤ W le_top ≫ C.germToFunctionField W =
      CommRingCat.ofHom (algebraMap k C.functionField) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k C.functionField))
  rw [h, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h1
  have hm : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map_id _
  have h2 : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv]
    refine h1.trans ?_
    simp only [Category.assoc]
    erw [hm, Category.comp_id]
  rw [h2]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact C.presheaf.germ_res (homOfLE le_top) (genericPoint C) _

theorem UpperTheory.baseChange_affine_sections_subalgebra_tensor :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsAffineOpen (u ⁻¹ᵁ W) ∧ ∃ e : L ⊗[k] B ≃+* Γ(X, u ⁻¹ᵁ W), (∀ (a : Γ(C, W)) (b : B), (b : C.functionField) = C.germToFunctionField W a → e ((1 : L) ⊗ₜ[k] b) = u.app W a) ∧ ∀ l : L, e (l ⊗ₜ[k] (1 : B)) = x.appLE ⊤ (u ⁻¹ᵁ W) le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) := by
  intro k L _ _ _ C X _ c u x H _ hK W _ hW B hB
  have hu : IsAffineHom u := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine ⟨hW.preimage u, ?_⟩
  let g0 : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hinj : Function.Injective g0 := C.germToFunctionField_injective W
  have hmem : ∀ a, g0 a ∈ B := fun a => by
    have : g0 a ∈ (B : Set C.functionField) := by rw [hB]; exact ⟨a, rfl⟩
    exact this
  let g1 : Γ(C, W) →+* B := g0.codRestrict B hmem
  have hbij : Function.Bijective g1 := by
    refine ⟨fun a a' h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    have : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
    rw [hB] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  let gB : Γ(C, W) ≃+* B := RingEquiv.ofBijective g1 hbij
  let iB : CommRingCat.of B ≅ Γ(C, W) := gB.symm.toCommRingCatIso
  have hP := (GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback H hW).flip
  have hT := CommRingCat.isPushout_tensorProduct k L B
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap k L)) (CommRingCat.ofHom (algebraMap k B))
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appLE ⊤ (u ⁻¹ᵁ W) le_top)
      (iB.hom ≫ u.app W) := by
    refine hP.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) iB.symm (Iso.refl _)
      (Scheme.ΓSpecIso_naturality _) ?_ (by simp) (by simp)
    rw [← Iso.inv_comp_eq]
    ext r
    exact congr($(scal c hK W).hom r)
  let E := IsPushout.isoIsPushout _ _ hT hP'
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro a b hab
    have h1 := congr($(IsPushout.inr_isoIsPushout_hom _ _ hT hP').hom b)
    have h2 : iB.hom b = a := by
      apply hinj
      have h3 := congrArg Subtype.val (gB.apply_symm_apply b)
      exact h3.trans hab
    rw [← h2]
    exact h1
  · intro l
    have h1 := congr($(IsPushout.inl_isoIsPushout_hom _ _ hT hP').hom l)
    exact h1
end
