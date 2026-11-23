module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses

theorem posDef_cT_inv_mul_inv (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E)
    (τ : E →+* ℂ) :
    ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  set B : Matrix (Fin n) (Fin n) E := (h⁻¹).val with hB
  have hc : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom B).map τ = (B.map τ)ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.map_mul, hc]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  have hu : IsUnit B := (h⁻¹).isUnit
  exact hu.map (RingHom.mapMatrix τ)

end GlobalTheory.UnitaryClasses
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepConj

theorem conj_of_charpoly_eq_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K),
    a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := by
  intro K _ n a b he hs
  exact GlobalTheory.BCT.ClsFin.conj_of_charpoly a b hs he

end GlobalTheory.SepConj
end

section

open AlgebraicGeometry CategoryTheory

open TopologicalSpace

namespace GlobalTheory.ZariskiSections

theorem bijective_of_finite_of_fractionRing {A B K : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : A →+* B) (hφ : φ.Finite) (θ : B →+* K) (hθ : Function.Injective θ)
    (h : ∀ a, θ (φ a) = algebraMap A K a) : Function.Bijective φ := by
  refine ⟨fun a a' e => IsFractionRing.injective A K (by rw [← h, ← h, e]), fun b => ?_⟩
  letI := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : _root_.IsIntegral A b := Algebra.IsIntegral.isIntegral b
  let θ' : B →ₐ[A] K := { θ with commutes' := fun a => h a }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hb.map θ')
  exact ⟨a, hθ (by rw [h]; exact ha)⟩

theorem finite_appTop_restrict {Y Z : Scheme.{0}} (π : Y ⟶ Z) [IsProper π] [IsLocallyNoetherian Z]
    {V : Z.Opens} (hV : IsAffineOpen V) : (π ∣_ V).appTop.hom.Finite := by
  let f : (π ⁻¹ᵁ V).toScheme ⟶ Spec (.of Γ(Z, V)) := (π ∣_ V) ≫ hV.isoSpec.hom
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := GlobalTheory.algebraΓOfHom f
  have h1 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule _) 0
  have h2 : Module.Finite Γ(Z, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) :=
    Module.Finite.equiv ((GlobalTheory.coh.zeroUnitEquiv _).restrictScalars Γ(Z, V))
  let e := (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ hV.isoSpec.hom.appTop
  haveI : IsIso hV.isoSpec.hom.appTop := by
    first
    | exact (inferInstance : IsIso (Scheme.Γ.map hV.isoSpec.hom.op))
    | exact Scheme.Hom.isIso_app _ ⊤ (by simp)
    | exact Scheme.Hom.isIso_app _ ⊤ (fun x _ => (ConcreteCategory.bijective_of_isIso hV.isoSpec.hom.base).2 x)
  haveI he' : IsIso e := by dsimp only [e]; infer_instance
  have h3 : (e ≫ (π ∣_ V).appTop).hom.Finite := by
    have he : e ≫ (π ∣_ V).appTop = (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ f.appTop := by
      simp only [e, f, Scheme.Hom.comp_appTop, Category.assoc]
    rw [he]
    exact h2
  have h4 : (π ∣_ V).appTop = inv e ≫ (e ≫ (π ∣_ V).appTop) := by rw [IsIso.inv_hom_id_assoc]
  rw [h4, CommRingCat.hom_comp]
  exact RingHom.Finite.comp h3
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (inv e)).2)

theorem bijective_appTop_restrict : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z →
    ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V →
    Function.Bijective (π ∣_ V).appTop := by
  intro Y Z π _ _ _ _ hN U hU hiso V hV
  have hV0 : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hO : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ = π ⁻¹ᵁ V := Scheme.Opens.ι_image_top _
  by_cases hne : (V : Set Z).Nonempty
  swap
  · have hVb : V = ⊥ := by
      ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    have s1 : Subsingleton Γ(Z, V.ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (hV0.trans hVb))
    have s2 : Subsingleton Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty (by
        rw [hO]; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        intro hx; exact hne ⟨_, hx⟩))
    exact ⟨fun a b _ => s1.elim a b, fun b => ⟨0, s2.elim _ _⟩⟩

  set η := genericPoint Z
  have hηU : η ∈ U := ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηV : η ∈ V := ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hne)

  obtain ⟨y', hy'⟩ := (π ∣_ U).surjective ⟨η, hηU⟩
  set y : Y := y'.1
  have hy : π y = η := by
    have := congrArg Subtype.val hy'
    simpa [morphismRestrict_base_coe] using this
  haveI : IsIso (π.stalkMap y) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap π U y') |>.mp
      (inferInstance : IsIso ((π ∣_ U).stalkMap y'))
  have hyO : y ∈ (π ⁻¹ᵁ V).ι ''ᵁ ⊤ := by rw [hO]; show π y ∈ V; rw [hy]; exact hηV
  haveI : Nonempty (V.ι ''ᵁ ⊤) := ⟨⟨η, hV0.symm ▸ hηV⟩⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  have hA : IsAffineOpen (V.ι ''ᵁ ⊤) := hV0.symm ▸ hV
  haveI := functionField_isFractionRing_of_isAffineOpen Z _ hA
  haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA
  let θ : Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) ⟶ Z.functionField :=
    Y.presheaf.germ _ y hyO ≫ inv (π.stalkMap y) ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq hy)).hom
  have hθ : Function.Injective θ.hom := by
    simp only [θ, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso _).1.comp (ConcreteCategory.bijective_of_isIso _).1).comp
      (germ_injective_of_isIntegral Y y hyO)
  refine bijective_of_finite_of_fractionRing (A := Γ(Z, V.ι ''ᵁ ⊤)) (K := Z.functionField)
    (π ∣_ V).appTop.hom (finite_appTop_restrict π hV) θ.hom hθ fun a => ?_
  have hle : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (V.ι ''ᵁ ⊤) := by rw [hO, hV0]
  have h1 : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op :=
    morphismRestrict_app π V ⊤
  have hyV : π y ∈ V.ι ''ᵁ ⊤ := by rw [hV0, hy]; exact hηV
  have key : (π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op) ≫ θ =
      Z.germToFunctionField (V.ι ''ᵁ ⊤) := by
    simp only [θ, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc, ← Scheme.Hom.germ_stalkMap_assoc π (V.ι ''ᵁ ⊤) y hyV,
      IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ (Inseparable.of_eq hy).specializes'
  have := congrArg (fun g => g.hom a) key
  rw [← h1] at this
  exact this

end GlobalTheory.ZariskiSections
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.cech_lineBundle_of_compatible_local_frames : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  first | exact @GlobalTheory.FramesBundle.frames_bundle | exact GlobalTheory.FramesBundle.frames_bundle | (intros; apply GlobalTheory.FramesBundle.frames_bundle <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.lift_local_units_along_nilpotent_thickening : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  first | exact @GlobalTheory.FormalAlg.lift_localUnits_of_thickening | exact GlobalTheory.FormalAlg.lift_localUnits_of_thickening | (intros; apply GlobalTheory.FormalAlg.lift_localUnits_of_thickening <;> assumption)
end
