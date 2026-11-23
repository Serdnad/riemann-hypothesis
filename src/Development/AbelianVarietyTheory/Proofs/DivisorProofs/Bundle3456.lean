module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W hWc hWi
  obtain ⟨hproj, hnorm, hopen, hcomp, hdense, W8, hE8, hTI⟩ := id hθ
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.exists_mem_genericPoints_closure_eq_of_isClopen F.X Z i hopen hdense W hWc hWi
  obtain ⟨X₁, -, hX₁⟩ := GlobalTheory.Poinc.GSetup.exists_setup g n hg hn hodd F Z z i hproj
    (fun x => ⟨hnorm.isDomain_stalk x, hnorm.isIntegrallyClosed_stalk x⟩) hopen hcomp hdense W8 hE8 hTI η hη 0
  have hr := GlobalTheory.Poinc.Setup.range_π_eq g n F W8 Z i X₁ η W hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ :=
    GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁ ι Y πY D hι X₁.projM hhom hprop hnY hsupp hord
  have hhomog : ∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β := by
    intro T k _
    have hrk : Module.finrank ℤ T.D.toPre.X ≤ g := by
      have := GlobalTheory.Poinc.Trait.dim_add_rank (by omega : 2 ≤ n) F T
      omega
    have hβ : T.β ∈ balForms (id : ℤ → ℤ) T.D.toPre.X := ⟨T.symm, fun a y z => by simp⟩
    rw [natCast_zsmul, StrictData.evalZ_eq, StrictData.evalZ_eq, StrictData.toReal_nsmul]
    exact (hφ _ hrk).homog _ (StrictData.toReal_mem_psdCone hβ fun y => T.mono.nonneg 0 y) _ (Nat.cast_nonneg k)
  obtain ⟨hs, ho⟩ := GlobalTheory.Poinc.ideal_orders_of_proper_model g n F W8 Z i φ X₁ Y πY hhom hprop ι' J₁ hsupp' hord' hhomog
  exact ⟨W8, X₁, ι', J₁, hι', hr, hs, ho⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_canonical_family_through_degenerating_family : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  first | exact @GlobalTheory.UCanon.exists_canon_through | exact GlobalTheory.UCanon.exists_canon_through | (intros; apply GlobalTheory.UCanon.exists_canon_through <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitaryCompactification_exists_boundary_ideal : UIdealSt := by
  first | exact @GlobalTheory.UPoinc.uIdealSt_holds | exact GlobalTheory.UPoinc.uIdealSt_holds | (intros; apply GlobalTheory.UPoinc.uIdealSt_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFamLocal

theorem exists_point_of_principal : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ β c hc
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  haveI : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F R (AdicCompletion (IsLocalRing.maximalIdeal R) R) β c hc ?_
  intro c' hc'
  have hp : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff c' c _).2 hc') hc
  exact GlobalTheory.T.siegelFamily_classifies_complete_noetherian_local g n hg hn hodd F (AdicCompletion (IsLocalRing.maximalIdeal R) R) inferInstance
    ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp β) c' hp

end GlobalTheory.SiegelFamLocal
end

section

theorem GlobalTheory.pointSeparationPair_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.PointSeparationPair := fun hP =>
  GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing hP (GlobalTheory.T.nadel_vanishing_pairs_of_principalisation hP) GlobalTheory.T.nefLineBundleNumericalTheorems_proof
end
