module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  first | exact @GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | exact GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | (intros; apply GlobalTheory.DescIsoExists.lbIso_pull_fst_snd <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  first | exact @GlobalTheory.ShearLift.exists_lift_shear | exact GlobalTheory.ShearLift.exists_lift_shear | (intros; apply GlobalTheory.ShearLift.exists_lift_shear <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem exists_isGrpPullback_of_isModel : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  intro K W L _ _ _ _ _ A _ G _ hM A' _ ψ hψ
  obtain ⟨e, he⟩ := hM
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback A (spMap (algebraMap K L)))
  have : IsMonHom (e₁ ≪≫ e.symm).hom := inferInstanceAs (IsMonHom (e₁.hom ≫ e.inv))
  have h := (isGrpPullback_of_iso (e₁ ≪≫ e.symm)).comp (isGrpPullback_pullback G (spMap (algebraMap W L)))
  exact ⟨_, h.congr (Category.id_comp _) rfl⟩

end GlobalTheory.SS
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.star_idemOf_coeff_eq_self : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ) (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X → ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  first | exact @GlobalTheory.CuspMult.idemOf_coeff_real | exact GlobalTheory.CuspMult.idemOf_coeff_real | (intros; apply GlobalTheory.CuspMult.idemOf_coeff_real <;> assumption)
end

section

noncomputable section

open NumberField Polynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.FamSep

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero_at {P : Pl0} (hq : A.q P ≠ 0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem typesSep_of_local (hq : ∀ P : (A.fam.R A.fam.μ0).Pl, A.q ((A.fam.R A.fam.μ0).pl P) ≠ 0)
    (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (trScale_ne_zero_at A (hq P)) (A.const_of h0 Sg hSg _) (A.const_of h0 Sg' hSg' _) h)⟩

theorem typesSep_of_ok {s : ℕ} (hOk : A.fam.Ok s) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep :=
  typesSep_of_local A (fun P => ((hOk.what₂ A.fam.μ0).q_pos P).ne') h0

end General

section Real

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Real

end GlobalTheory.FamSep

end
end

section

open NumberField
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.frameStabiliser_mapsTo_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  first | exact @GlobalTheory.stab_hatL_mapsTo | exact GlobalTheory.stab_hatL_mapsTo | (intros; apply GlobalTheory.stab_hatL_mapsTo <;> assumption)
end

section

namespace GlobalTheory.RowPartsOrth

section Generic
open MeasureTheory Formalism.IndefR.Bridge GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

variable {μ Γ 𝓕}



theorem isDC_of_local {H : Type} [Group H] (J L : Subgroup H) (x : H) (A : Finset H) (hx : x ∈ L)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC (J ⊓ L) x A) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, e⟩ := hA.1 a ha
    exact ⟨⟨k₁, k₁.2.1⟩, ⟨k₂, k₂.2.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, e, hc⟩ := hs k₁ k₁.2
    have e2 : (k₁ : H) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, (hc x hx).eq]; simp only [mul_assoc]
    obtain ⟨r, ⟨hr, hr2⟩, hu⟩ := hA.2 (a * x) ⟨⟨a, ha, haL⟩, 1, by simp⟩
    rw [e2]
    refine ⟨r, ⟨hr, ?_⟩, fun r' hr' => hu r' ⟨hr'.1, ?_, ?_⟩⟩
    · have := J.mul_mem hr2.1 (J.mul_mem hb k₂.2)
      simpa only [mul_assoc] using this
    · have := J.mul_mem hr'.2 (J.inv_mem (J.mul_mem hb k₂.2))
      simpa [mul_assoc] using this
    · exact L.mul_mem (L.inv_mem (hL r' hr'.1)) (L.mul_mem haL hx)

end Generic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx NumberField IsDedekindDomain Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RowPartsOrth
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedHomLattice_finitelyGenerated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  first | exact @GlobalTheory.LatFinGen.latO_finitely_generated | exact GlobalTheory.LatFinGen.latO_finitely_generated | (intros; apply GlobalTheory.LatFinGen.latO_finitely_generated <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  first | exact @GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | exact GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | (intros; apply GlobalTheory.LocalLatStab.mem_latO_place_iff_actO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

variable {D : D7}

def frPt {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : D.what₂.Tau → Fin m → Fin n → ℂ :=
  fun τ => (B' τ * Matrix.of (Z τ) * (B τ)⁻¹ : Matrix (Fin m) (Fin n) ℂ)

def sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ := ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2

def gZ (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (Z : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  f (iotaW σ T S (frPt B B' Z)) * Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ)

def thY (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (δ : ℂ)
    (Y : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  gZ σ S T B B' f (δ⁻¹ • Y)

end GlobalTheory.VacRealForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem offS_not_type_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) → OffS D S P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
  intro D Pb Pg S P hPg hS hP
  have key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP h
    obtain ⟨x, hx, hxP⟩ := hP _ (hS PP h)
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
    refine ⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hx'
    refine hxP c' ?_ h1
    rw [h2]
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h => (key PP h).1
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := by
    intro PP h e
    apply (key PP h).2
    intro c hc
    rw [e] at hc
    exact ⟨Formalism.L2.Col.cO D.host.E c, hc, rfl⟩
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, key⟩
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_finset_latSum_thInd_eq_sum : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  first | exact @GlobalTheory.latSum_thInd_regroup | exact GlobalTheory.latSum_thInd_regroup | (intros; apply GlobalTheory.latSum_thInd_regroup <;> assumption)
end
