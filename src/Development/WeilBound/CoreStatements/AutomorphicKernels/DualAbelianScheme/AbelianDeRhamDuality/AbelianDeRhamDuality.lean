module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
public import Mathlib.RingTheory.Flat.LocallyFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree, Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.AbelianDeRhamDuality

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne\npublic import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.DualRT

open CrystallinePoints.Pd GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

@[reducible] def ptOf {s : X ⟶ Sp R} (T : TT s) : Pt s := ⟨T.obj.B, pt T, pt_w T⟩

theorem pt_comp {s : X ⟶ Sp R} {T T' : TT s} (a : T ⟶ T') :
    spMap (a.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T = pt T' := by
  have key : (a.hom.φ : T.obj.B →+* T'.obj.B).comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
      = ((πe T').symm : T'.obj.B₀ →+* T'.obj.B).comp a.hom.φ₀ := by
    ext x
    obtain ⟨b, rfl⟩ := (πe T).surjective x
    apply (πe T').injective
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
      RingEquiv.apply_symm_apply, AlgHom.coe_toRingHom]
    simp only [πe, RingEquiv.ofBijective_apply]
    exact (a.hom.comm b).symm
  unfold pt
  rw [← a.hom.pt]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [key]

def ofPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (FP s) ((IsTriv s).ι ⋙ O (dp0 R) s) where
  G := { obj := ptOf
         map := fun a ↦ ⟨a.hom.φ, pt_comp a⟩
         map_id := fun _ ↦ CrystallinePoints.Pd.hom_ext' fun _ ↦ rfl
         map_comp := fun _ _ ↦ CrystallinePoints.Pd.hom_ext' fun _ ↦ rfl }
  α T := RingHom.id T.obj.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toPO (s : X ⟶ Sp R) : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
  ptCoef (F := FP s) (fun P ↦ P.x) (fun P ↦ P.w) fun _ _ a ↦ a.pt

theorem toPO_toH1O (s : X ⟶ Sp R) (c : FirstDeRham s) : (toPO s).pull1 (toH1O s c) = toP s c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

private theorem spMap_id_comp_spMap_symm_comp {A : Type} [CommRing A] [Algebra R A] {Y : Scheme} (e : A ≃+* A)
    (he : ∀ z, e z = z) (y : Sp A ⟶ Y) :
    spMap ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) ≫ spMap (e.symm : A →+* A) ≫ y = y := by
  have h1 : (e.symm : A →+* A) = RingHom.id A := by
    ext z
    apply e.injective
    show e (e.symm z) = e z
    rw [RingEquiv.apply_symm_apply, he]
  have h2 : ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = RingHom.id A := rfl
  rw [h1, h2]
  simp [spMap]

theorem toPO_ofPC (s : X ⟶ Sp R) (c : H1OnPoints s) : (toPO s).pull1 ((ofPC s).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  let θ : ((ofPC s).comp (toPO s)).G ⟶ (CoefMap.id (FP s)).G :=
    { app := fun P => ⟨AlgHom.id R P.B, spMap_id_comp_spMap_symm_comp _ (fun _ => rfl) P.x⟩
      naturality := fun _ _ _ => CrystallinePoints.Pd.hom_ext' fun _ => rfl }
  exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id (FP s)) θ (fun _ _ => rfl) c).trans (CoefMap.pullCohomologyOne_id c)

private theorem cmpO_toH1O_eq_toHO1_cmp1 (s : X ⟶ Sp R) (c : FirstDeRham s) :
    GlobalTheory.CechDR.cmpO s (toH1O s c) = toHO1 s (cmp1 s c) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  rfl

theorem toPicard_surjective (s : X ⟶ Sp R) (h₁ : Function.Surjective (cmp1 s)) (h₂ : Function.Surjective (toHO1 s)) :
    Function.Surjective (toP s) := by
  intro t
  obtain ⟨c, hc⟩ := (h₂.comp h₁) (GlobalTheory.CechDR.cmpO s ((ofPC s).pull1 t))
  refine ⟨c, ?_⟩
  have e : toH1O s c = (ofPC s).pull1 t :=
    GlobalTheory.CechDR.cmpO_injective R X s (by rw [cmpO_toH1O_eq_toHO1_cmp1]; exact hc)
  rw [← toPO_toH1O, e, toPO_ofPC]

theorem surjAll_of_hodge (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) : SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (hC.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (hH R A g hAb hsm).2.2.2.2.1.2.2

end PositivityTheory.DualRT
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.Flat.LocallyFree\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allPrim_of_abelianDeRhamFree (h : GlobalTheory.Published.AbelianDeRhamFree) (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  apply _root_.GlobalTheory.AbelianPrim.allPrim_of_free <;> assumption

theorem abelianDeRhamFree_toFree (h : GlobalTheory.Published.AbelianDeRhamFree) :
    GlobalTheory.Published.AbelianDeRham.Free := fun R _ A _ g hA hg =>
  ⟨allPrim_of_abelianDeRhamFree h R A g hA hg, h R A g hA hg⟩

theorem abelianDeRhamStructure_toFree (h : GlobalTheory.Published.AbelianDeRhamStructure) :
    GlobalTheory.Published.AbelianDeRham.Free :=
  abelianDeRhamFree_toFree h.1

end GlobalTheory
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.AbelianDeRhamDuality =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.AbelianDeRhamDuality", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective\npublic import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham\npublic import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure\n\n"}
section -- clump:auto
@[expose] public section

namespace PositivityTheory.DualRT

theorem surjAll : CrystallinePoints.Pd.SurjAll :=
  surjAll_of_hodge GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates

theorem duality : GlobalTheory.Published.AbelianDeRham.Duality :=
  GlobalTheory.abelianDeRham.2.2.2.2

theorem abelianDeRham : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham

end PositivityTheory.DualRT
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.AbelianDeRhamDuality =====
