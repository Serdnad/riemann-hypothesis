module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle642
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocalBasis

theorem exists_isLieBasis_of_isLocalRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B]
    [IsCommMonObj B], Smooth B.hom → ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y := by
  intro R _ _ B _ _ hs
  haveI := hs
  obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart B
  obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
  have hu : IsUnit g := by
    by_contra h
    exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
  let L := Localization.Away g
  let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
  have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
  let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs B g
  have hpb : IsGrpPullback G' B (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst B.hom _) :=
    isGrpPullback_pullback B _
  have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
    simp only [spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
    exact Spec.map_id _
  let φ' : B.left ⟶ G'.left := pullback.lift (𝟙 _) (B.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
  have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hw : φ' ≫ G'.hom = B.hom ≫ spMap f' := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  have hid : IsGrpPullback B B (𝟙 (Sp R)) (𝟙 B.left) := (isGrpPullback_of_iso (Iso.refl B)).congr rfl rfl
  have hn : IsGrpPullback B B (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
    hid.congr hcomp.symm hφ.symm
  have hB : IsGrpPullback B G' (spMap f') φ' := hpb.cancel hn hw
  have hs' : Smooth G'.hom := by
    show Smooth (pullback.snd B.hom _)
    infer_instance
  obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' B φ' hB hs' n v hv
  exact ⟨n, v', hv'⟩

end GlobalTheory.LieLocalBasis
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel


theorem _root_.GlobalTheory.T.locallyOfFiniteType_of_isProjOver : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → LocallyOfFiniteType s := by
  first | exact @GlobalTheory.isProjOver_locallyOfFiniteType | exact GlobalTheory.isProjOver_locallyOfFiniteType | (intros; apply GlobalTheory.isProjOver_locallyOfFiniteType <;> assumption)
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem eq_ptMap' {O : Type} [CommRing O] {D B : Type} [CommRing D] [Algebra O D] [CommRing B] [Algebra O B]
    (x : specO O D ⟶ specO O B) : ∃ α : B →ₐ[O] D, x = ptMap α := by
  obtain ⟨f, hf⟩ := Spec.map_surjective x.left
  have hw : x.left ≫ (specO O B).hom = (specO O D).hom := Over.w x
  rw [← hf] at hw
  change Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) = Spec.map (CommRingCat.ofHom (algebraMap O D)) at hw
  rw [← Spec.map_comp] at hw
  have hc := Spec.map_injective hw
  refine ⟨{ f.hom with commutes' := fun c => congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of D => g.hom c) hc }, ?_⟩
  ext1
  rw [← hf]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

end GlobalTheory.FinPartAt
end
end
