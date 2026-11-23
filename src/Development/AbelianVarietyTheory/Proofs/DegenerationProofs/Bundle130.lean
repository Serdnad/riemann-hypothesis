module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralGauge

theorem exists_chart_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (ψ : Sp V ⟶ X) : ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j := by
  have h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩

theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  apply GlobalTheory.ValuesExist.exists_ext <;> assumption

theorem exists_integral_gauge (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) :
    ∃ J : (Sp F ⟶ D.P.A.left) → D.P.L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) ∧ ∀ x : TF (R := R) F ⟶ D.P.A,
      ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (J x.left) := by
  have key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧
      ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) →
        ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB x₀
      exact ⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB ψ
      exact ⟨j, hj, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩

end GlobalTheory.IntegralGauge
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_neutral_group_model' : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  first | exact @GlobalTheory.SS.exists_neutral_group_model | exact GlobalTheory.SS.exists_neutral_group_model | (intros; apply GlobalTheory.SS.exists_neutral_group_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GenSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.ConnFibre

theorem exists_geometricallyConnected : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  intro R K _ _ _ _ _ _ X X₀ f f₀ φ hb hs hp hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R X f hp
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hg₀ : Function.Injective g₀ := (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let y₀ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h₀ : IsPullback (pullback.fst f₀ y₀ ≫ φ) (pullback.snd f₀ y₀) f
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback f₀ y₀).paste_horiz hb
    erw [← Spec.map_comp] at this
    exact this
  have hs₀ : Smooth f₀ := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f₀ hs₀ hc
  have hint : IsIntegral (pullback f₀ y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback f₀ y₀)
  have hpr₀ : IsProper (pullback.snd f₀ y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback f₀ y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst f₀ y₀ ≫ φ) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hsurj : Surjective f := by
    have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range f := by
      refine ⟨(pullback.fst f₀ y₀ ≫ φ) x₀, ?_⟩
      have e : f ((pullback.fst f₀ y₀ ≫ φ) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd f₀ y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext (le_bot_iff.1 fun a ha => ?_))
      have ha' : g₀ a ∈ (pullback.snd f₀ y₀ x₀).asIdeal := ha
      by_contra hne
      have hne' : g₀ a ≠ 0 := fun h => hne (hg₀ (h.trans (map_zero g₀).symm))
      exact (PrimeSpectrum.isPrime (pullback.snd f₀ y₀ x₀)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ ha' (IsUnit.mk0 _ hne'))
    refine ⟨fun z => ?_⟩
    have hsp : (⊥ : PrimeSpectrum R) ⤳ (z : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hcl hbot
  refine ⟨δ, fun h => hδ (h ▸ map_zero g₀), fun R' _ g hg X' π f' hπ => ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have h' : IsPullback (fst ≫ π) snd f (Spec.map (CommRingCat.ofHom ((algebraMap R' F).comp g))) := by
    have := h.paste_horiz hπ
    erw [← Spec.map_comp] at this
    exact this
  have : Surjective snd := MorphismProperty.of_isPullback h' hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h' _ (hker F _ (hg.map (algebraMap R' F)))
  exact ⟨⟨z⟩⟩

end GlobalTheory.GenSpread
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcF_values_add_ker_onto : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  intro hG E _ _ _ H D R _ _ F _ _ _ A n hn
  obtain ⟨-, -, hadd, -, hQ⟩ := hG R A.D₀ A.even A.bimult F A.N A.ν
  refine ⟨fun a b => ?_, fun a b => ?_, fun q => ?_⟩
  · obtain ⟨p, h₁, h₂, h₃⟩ := A.I.add n hn a b
    obtain ⟨q, hq⟩ := ((hQ n).1 p).exists
    have e : q = A.q n a * A.q n b := by
      refine Subtype.ext (Prod.ext ?_ ((hadd _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hq.2).1 h₂))
      apply Multiplicative.toAdd.injective
      apply A.ν.eX.injective
      rw [hq.1, h₁, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
      rfl
    rw [← e]
    exact ((hQ n).2.2 _ _ _ _ hq (A.hq n _)).1 h₃
  · rw [← (hQ n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
    exact A.I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 q
    obtain ⟨a, ha⟩ := A.I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (A.hq n a) hp₀).1 ha⟩

end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Trait

def Along {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] (f : O' →+* R) (C : Type) [Field C]
    [Algebra (FractionRing O') C] [Algebra (FractionRing R) C] : Prop :=
  ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)

def RatTors {R : Type} [CommRing R] [IsDomain R] (B : PolAV (Sp R)) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (n : ℕ) : Prop :=
  ∀ x : TF (R := R) C ⟶ B.A, x ^ n = 1 → ∃ x₀ : TK R ⟶ B.A, x.left = jFK (R := R) C ≫ x₀.left

def wVal {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {P : DegPre R} {D₀ : DegPre O'} {C : Type}
    [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C] {N' N : NumD C} (ν' : NumOf P C N')
    (ν : NumOf D₀ C N) {ψ : P.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (x : N'.A) : C :=
  valF (ν'.eA x).left _ (w.s (fun _ => ν.J ((ν'.eA x).left ≫ ψ), ν'.J (ν'.eA x).left)).val
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {a : ArcIn D l β O' b} {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C]

def Labels (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) {o : Full D C} (M : Mdl o) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (k : ℕ) : Prop :=
  ∀ x (p : (A.N.twist A.be u).QT k) (q' : N'.QT k) p' z, TwRel A.be u (r k) (A.q _ x) p →
    q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev k x).left ≫ M.φ →
    M.P.ToA C k p' z

def Fit (A : Lift a C) (u : Cˣ) {o : Full D C} (M : Mdl o) (f : O' →+* M.W) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (ψ : M.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ)) (e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X) : Prop :=
  IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ ∧ w.IsGen ∧
    (∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left) ∧ (∀ y : A.N.X, e (A.ν.eX y) = ν'.eX (J.e y)) ∧
    (∀ x, wVal ν' A.ν w x ≠ 0) ∧ ∀ x : A.N.A, (J.h x : C) * wVal ν' A.ν w (J.φ x) = wVal ν' A.ν w 1
end

def AllS (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ)
    (_ : ℕ → Cˣ) {o : Full D C} (M : Mdl o) (_ : O' →+* M.W) {N' : NumD C} (_ : NumOf M.P.D.toPre C N'),
    NumD.Iso (A.N.twist A.be u) N' → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l)
    (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (b : O →+* O')
    (a : ArcIn D l β O' b) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o)
    (f : O' →+* M.W) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'),
    Roots u r → Along f C → P a A u r M f ν' J
end GlobalTheory.Ex.Trait
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.Mono

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨_, fun Z r z J hJ => ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem isFrame_pull {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂)
    (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) (x : Sp (FractionRing R₁) ⟶ S)
    (x' : Sp (FractionRing R₂) ⟶ S) (hx : spMap h' ≫ x = x') {n : ℕ} (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)))
    (hf : GlobalTheory.LN.IsFrame G L N x f) : ∃ f', GlobalTheory.LN.IsFrame (n := n) G L N x' f' := by
  let ρ : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap h') hx
  have e : ∀ _ : Fin 1, (ρ ▷ G).left ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left := fun _ => by
    rw [← Over.comp_left, whiskerRight_snd]
  choose f' hf' using fun i => exists_pull (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk x) G).left)
    (φ' := fun _ : Fin 1 => (snd (Over.mk x') G).left) (ε := fun _ => (N : ℤ)) (f i) (ρ ▷ G).left e
  refine ⟨f', fun W _ _ _ hW φ gam hg χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ x = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx, hχ]
  obtain ⟨b', hb, hs⟩ := hf W hW (φ.comp h) (gam.comp h') (fun r => by
    rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ hχ'
  refine ⟨b', hb, fun i => ?_⟩
  obtain ⟨s, h₁, h₂⟩ := hs i
  refine ⟨s, fun z J hJ => (h₁ z J hJ).trans ?_, h₂⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  refine congrArg _ (Eq.trans ?_ (hf' i _ _ z J hJ).symm)
  have hc : (Over.homMk (spMap (gam.comp h')) hχ' : Over.mk (jK W ≫ χ) ⟶ Over.mk x) =
      (Over.homMk (spMap gam) hχ : Over.mk (jK W ≫ χ) ⟶ Over.mk x') ≫ ρ := Over.OverMorphism.ext (sp_comp h' gam)
  rw [hc, comp_whiskerRight, Over.comp_left]

theorem mono : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), h.Finite → (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) → (GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.LN.TraitData Y a (h.comp g) (spMap h' ≫ y₁)) ∧ (RealAt Y a g y₁ → RealAt Y a (h.comp g) (spMap h' ≫ y₁)) ∧ ∀ (N n : ℕ) f, GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N (y₁ ≫ Y.j) f → ∃ f', GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N ((spMap h' ≫ y₁) ≫ Y.j) f' := by
  intro _ _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ R₁ _ _ g y₁ _ _ _ R₂ _ _ h h' hfin hh
  refine ⟨fun hT => ⟨?_, fun W _ _ _ hW φ gam hg χ hχ => ?_⟩, fun hR => hR.comp h h' hfin hh,
    fun N n f hf => isFrame_pull _ _ N h h' hh _ _ (Category.assoc _ _ _).symm f hf⟩
  · have e : spMap h' ≫ jK R₁ = jK R₂ ≫ spMap h :=
      (sp_comp (algebraMap R₁ _) h').symm.trans ((congrArg spMap (RingHom.ext hh)).trans (sp_comp h (algebraMap R₂ _)))
    rw [Category.assoc, hT.1, sp_comp, ← Category.assoc, e]
    simp only [Category.assoc]
  · exact hT.2 W hW (φ.comp h) (gam.comp h') (fun r => by rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ
      (by rw [sp_comp, Category.assoc, ← hχ, Category.assoc])

end GlobalTheory.Ex.Mono
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.FullExtend

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K), ∃ o' : Full D K', FullExt f o o' ∧ (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧ ∀ m j z v, 0 < j → o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  intro hV _ _ _ _ _ _ E _ _ _ H D K K' _ _ _ _ _ f o
  obtain ⟨o', h₁, h₂, h₃⟩ := exists_fullExt hV.1.1 D f o
  exact ⟨o', h₁, h₂, fun m j z v _ => h₃ m j z v⟩

end GlobalTheory.FullExtend
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.WeilValues

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem top_le_chart {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (φ : K → (Y ⟶ X))
    (r : Sp F ⟶ Y) : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun z _ =>
  Good.mem (L := L) (z := z) (J := J) (fun ψ => hJ ψ trivial) φ r

theorem vF_ne_zero {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : vF t r J ≠ 0 := by
  refine fun h => ?_
  exact (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (top_le_chart hJ φ r)).symm.trans h)

theorem valF_const_mul (r : Sp F ⟶ Y) (π : Y ⟶ Sp F) (h : r ≫ π = 𝟙 _) (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (z : F)
    (a : Γ(Y, U)) : valF r U (resTop U (π.appTop.hom (fnOf z)) * a) = z * valF r U a := by
  rw [valF, valF, dif_pos hU, dif_pos hU, map_mul, map_mul]
  congr 1
  have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom (fnOf z))) = (r ≫ π).appTop.hom (fnOf z) := by
    simp only [resTop]
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp F, ⊤) => g.hom (π.appTop.hom (fnOf z))) (Scheme.Hom.appLE_eq_app r (U := ⊤))
  rw [e, h]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply z
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F}

theorem famV_smul (ν : NumOf D F N) {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) (z : F) :
    ν.FamV (z • s) (z • f) := by
  intro α x
  have e : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  refine Eq.trans ?_ (valF_const_mul _ _ e _ (top_le_chart ν.good _ _) z _).symm
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h α x]
  rfl

theorem exists_phiRel (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (s : Fam D F k) :
    ∃ t, PhiRel D F k p w s t := by
  obtain ⟨t, ht⟩ := DVR.exists_phi GlobalTheory.globalFns_holds p w hw hB s
  exact ⟨t, (DVR.phiRel_iff GlobalTheory.globalFns_holds p w hw s t).2 ht⟩

theorem phi_ne_zero {k : ℕ} (q : N.QT k) (w : Fˣ) {f : N.X → N.A → F} (hf : f ≠ 0) : N.phi q w f ≠ 0 := by
  intro h
  refine hf (funext fun α => funext fun x => ?_)
  have := congrFun (congrFun h (α + q.1.1.toAdd)) (x * q.1.2.b⁻¹)
  simp only [NumD.phi, add_sub_cancel_right, inv_mul_cancel_right, Pi.zero_apply, Units.mul_right_eq_zero] at this
  exact this

theorem weil_eq_values : BrGtSt → BrFamSt → BrWpSt := by
  intro _ hF R _ _ D hE hB F _ _ _ N ν k hk p p' q q' z hq hq'
  obtain ⟨h1, h2, -, ⟨s₀, f₀, hs₀, hf₀⟩, -, h6⟩ := hF R D hE hB F N ν k hk
  have key : ∀ w w', w.IsGen → w'.IsGen → ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ → PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      ∀ f, ν.FamV s f → ∃ f₄, ν.FamV s₄ f₄ ∧ ν.FamV s₂ ((N.wp q q' : F) • f₄) ∧ (f ≠ 0 → f₄ ≠ 0) := by
    intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    obtain ⟨f₁, a₁, -⟩ := h1 s₁
    obtain ⟨f₂, a₂, -⟩ := h1 s₂
    obtain ⟨f₃, a₃, -⟩ := h1 s₃
    obtain ⟨f₄, a₄, -⟩ := h1 s₄
    let u : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w (𝟙 (Sp F)))
    let u' : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w' (𝟙 (Sp F)))
    have e₁ := (h6 p' q' w' u' s s₁ f f₁ hq' hw' rfl hf a₁).1 r₁
    have e₂ := (h6 p q w u s₁ s₂ f₁ f₂ hq hw rfl a₁ a₂).1 r₂
    have e₃ := (h6 p q w u s s₃ f f₃ hq hw rfl hf a₃).1 r₃
    have e₄ := (h6 p' q' w' u' s₃ s₄ f₃ f₄ hq' hw' rfl a₃ a₄).1 r₄
    refine ⟨f₄, a₄, ?_, fun h => ?_⟩
    · rw [e₄, e₃, ← (GlobalTheory.Ex.PhiOp.phi_main F N k q q' u u' f).2.2.1, ← e₁, ← e₂]
      exact a₂
    · rw [e₄, e₃]
      exact phi_ne_zero _ _ (phi_ne_zero _ _ h)
  constructor
  · intro H
    obtain ⟨w, hw⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p.g.b) (DegPre.lineε k)
    obtain ⟨w', hw'⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p'.g.b) (DegPre.lineε k)
    obtain ⟨s₁, r₁⟩ := exists_phiRel hB p' w' hw' s₀
    obtain ⟨s₂, r₂⟩ := exists_phiRel hB p w hw s₁
    obtain ⟨s₃, r₃⟩ := exists_phiRel hB p w hw s₀
    obtain ⟨s₄, r₄⟩ := exists_phiRel hB p' w' hw' s₃
    obtain ⟨f₄, a₄, a₂, hne⟩ := key w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f₀ hs₀
    have e := (DVR.isSmul_iff z s₄ s₂).1 (H w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄)
    have b := famV_smul ν a₄ z
    rw [← e] at b
    exact smul_left_injective F (hne hf₀) ((h1 s₂).unique b a₂)
  · rintro rfl w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
    obtain ⟨f, hf, -⟩ := h1 s
    obtain ⟨f₄, a₄, a₂, -⟩ := key w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    exact (DVR.isSmul_iff _ s₄ s₂).2 (h2 _ _ _ a₂ (famV_smul ν a₄ _))

end GlobalTheory.WeilValues
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.Recognition

theorem urec_of_abelian : UrCSt → URecSt := by
  intro hC R _ _ D D' h1 h2 h3 h4 C _ _ _ _ _ N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt
  obtain ⟨hA, hg⟩ := GlobalTheory.T.thetaRecognition_matched_parts_dim_eq C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt
  obtain ⟨e, hB, hT⟩ := GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA
  obtain ⟨I, hOB, hl, hG⟩ := hC R D D' h1 h2 h3 h4 C N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt hA hg e hB hT
  obtain ⟨J, hJ, hJe, hOG⟩ := GlobalTheory.T.exists_numD_iso_onG_of_allMatch C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA e hB hT I hOB
  subst hJ hJe
  exact ⟨J, GlobalTheory.T.thetaRecognition_labels_agree_of_iso C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA J hB hOG hl, hG⟩
end GlobalTheory.Ex.Recognition
end
