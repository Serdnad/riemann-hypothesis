module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

section Ident

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

end Ident

theorem exists_gen {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (hU : IsOpen U) (hd : Dense U) (y : X) : ∃ g ∈ U, g ⤳ y := by
  obtain ⟨o, ho, hne, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
      (irreducibleComponent_mem_irreducibleComponents y)
  obtain ⟨z, hzo, hzU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨g, hg⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    (isClosed_irreducibleComponent (x := y))
  exact ⟨g, (hg.specializes (hoZ hzo)).mem_open hU hzU, hg.specializes mem_irreducibleComponent⟩

theorem eq_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    {p : X} (hp : p ⤳ genPt ξ) : p = genPt ξ := by
  obtain ⟨hbij, -⟩ := h
  obtain ⟨q, rfl⟩ : p ∈ Set.range (X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  have hF : IsField (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hbij).toMulEquiv
  have hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))) := by
    letI := hF.toField
    infer_instance
  have hq : q = IsLocalRing.closedPoint (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    @Subsingleton.elim _ hsub q _
  rw [hq]
  exact Scheme.fromSpecStalk_closedPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

end GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def IsHTChartOf {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p n N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω]
    (D : HT.HTChart R K c p n N Ω) {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L]
    (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L) (j : Module.Dual R L →ₗ[R] Ω)
    (π : Multiplicative (Fin N → 𝓞 E) →* T) (ζ : Rˣ) : Prop :=
  D.om = LinearMap.range j ∧
  (∀ a w, D.ρΩ a (j w) = j (w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))) ∧
  ∀ y, ∃ (χ : T →* Rˣ) (w : Module.Dual R L), (∀ z, χ (π (Multiplicative.ofAdd z)) = ζ ^ (D.e y z).val) ∧
    D.h y = j w ∧ Γ.IsHT i M (p ^ n) χ w

def HTChartExists : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CharZero R] [Field K]
    [Algebra R K] [IsFractionRing R K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p n N : ℕ) [Fact p.Prime]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x (p ^ n) i → Smooth G.hom →
    ∀ (act : 𝓞 E → (G ⟶ G)), (∀ a, IsMonHom (act a)) →
    ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (ρ : 𝓞 E →+* Module.End R L), M.IsActOf act ρ →
    ∀ (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (j : Module.Dual R L →ₗ[R] Ω),
      IsBaseChange K j →
    ∀ (π : Multiplicative (Fin N → 𝓞 E) →* T), Function.Surjective π →
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') →
      (∀ (a : 𝓞 E) y, (Γ.pt (π (Multiplicative.ofAdd (a • y)))).left ≫ i =
        (Γ.pt (π (Multiplicative.ofAdd y))).left ≫ i ≫ (act a).left) →
    ∀ (ζ : Rˣ), ζ ^ (p ^ n) = 1 →
    ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)), (∀ y, e y y = 0) →
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) →
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) → (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') →
    ∃ D : HT.HTChart R K c p n N Ω, D.e = e ∧ IsHTChartOf D Γ i M ρ j π ζ

end GlobalTheory.CompanionTheory.Ar.BT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

def PropZ : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ →
    Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) →
    IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) →
    ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → TrivMod L (algebraMap O Ω ϖ) →
      (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def keyInOf {R : Type} [CommRing R] (t : SAB H (Sp R)) (th : t.PP.L.Sec) (g : ℕ) (hg : 1 ≤ g)
    (v : Fin g → (epsR R ⟶ t.G)) (hv : IsLieBasis v) (hab : IsAbelianScheme t.G)
    (hd : SmoothOfRelativeDimension g t.G.hom) (hs : Out.Sym t.G t.PP.L) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) (hth : ∀ s : Sp R, ∃ x : t.G.left, t.G.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn R where
  P := { A := t.G, isAb := hab, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB,
         rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs, ample := ha, ktriv := hk }
  g_pos := hg
  rig := t.PP.rig
  rig_gen := t.PP.rigGen
  th := th
  th_ne := hth
  v := v
  basis := hv

end GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel
end
end
