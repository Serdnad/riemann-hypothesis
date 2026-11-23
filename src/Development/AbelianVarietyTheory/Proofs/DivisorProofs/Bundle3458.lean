module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trait_chart_generic_fibres_same : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  first | exact @GlobalTheory.TChart.sameFib_trait_chart | exact GlobalTheory.TChart.sameFib_trait_chart | (intros; apply GlobalTheory.TChart.sameFib_trait_chart <;> assumption)
end

section

open GlobalTheory.UChart

theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tautological_chart_versality : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  first | exact @GlobalTheory.UCanon.exists_taut_through | exact GlobalTheory.UCanon.exists_taut_through | (intros; apply GlobalTheory.UCanon.exists_taut_through <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelNoeth

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_eq (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]
  exact Spec.map_id _

theorem classify_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ β c hc
  refine GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F (Sp R) (spMap β) c hc ?_
  intro x
  let 𝔭 : Ideal R := x.asIdeal
  haveI : 𝔭.IsPrime := x.isPrime
  have loc : ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)),
      SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) →
      ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧
        SiegPB c' F.univ f := by
    intro c' hc'
    have hP := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β)
      (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)) (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl
      (by rw [spMap_id_eq, Category.comp_id]; exact (spMap_comp_eq _ _).symm)).2.1 c c' hc' hc
    exact GlobalTheory.T.siegelFamily_classifies_noetherian_local g n hg hn hodd F (Localization.AtPrime 𝔭) ((algebraMap R (Localization.AtPrime 𝔭)).comp β) c' hP
  obtain ⟨r, hr, H⟩ := GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen g n hg hn hodd F R β c 𝔭 hc loc
  let j : Sp (Localization.Away r) ⟶ Sp R := spMap (algebraMap R (Localization.Away r))
  have e : spMap ((algebraMap R (Localization.Away r)).comp β) = j ≫ spMap β := spMap_comp_eq _ _
  rw [e] at H
  obtain ⟨cV, hcV⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.Away r)) (spMap β) (j ≫ spMap β) j rfl
      (by rw [spMap_id_eq, Category.comp_id])).1 c
  obtain ⟨f, hf, hfu⟩ := H cV hcV
  refine ⟨Sp (Localization.Away r), j, cV, IsOpenImmersion.of_isLocalization r, ?_, hcV, f, hf, hfu⟩
  have hu : Set.range j = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  rw [hu]
  exact hr

end GlobalTheory.SiegelNoeth
end
