module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle045
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle168
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv

def rho {R : Type} [CommRing R] (φ : R →+* ℂ) :
    epsAt (spMap φ) ⟶ epsAt (𝟙 (Sp R)) :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    have hsq : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun r => ?_
      ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ
    rw [Category.comp_id, hsq])

theorem dualMap_comp_epsMul {R : Type} [CommRing R] (φ : R →+* ℂ) (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (GlobalTheory.CompanionTheory.Ar.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  refine RingHom.ext fun r => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem lieModel_pt_zero {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (u : Fin g → R) :
    IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left) := by
  have hF0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left :=
    congrArg (·.left) (ExpLift.ex_zero e hb)
  let T : (Fin g → R) → (epsPt (spMap (ψ b)) ⟶ G) := fun u => rho (ψ b) ≫ M.pt u
  have hTl : ∀ u, (T u).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left := fun _ => rfl
  have hadd : ∀ u u', T (u + u') = T u * T u' := fun u u' => by
    simp only [T, M.add, MonObj.comp_mul]
  have hone : (T 0).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (fun z => (e.ex b z).left) 0 := by
    let i₀ : epsPt (spMap (ψ b)) ⟶ Over.mk (spMap (ψ b)) :=
      Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
    have h1 : T 0 = i₀ ≫ (1 : Over.mk (spMap (ψ b)) ⟶ G) := by
      simp only [T, lieModel_pt_zero, MonObj.comp_one]
    rw [h1, hF0]
    rfl
  have h0 : IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((0 : Fin g → R) c)) (T 0).left := by
    rw [hone]
    have : (fun c => ψ b ((0 : Fin g → R) c)) = (0 : Fin g → ℂ) := by
      funext c; simp
    rw [this]
    exact GlobalTheory.LocalLift.isDerivAt0_const _ 0 fun _ _ _ => map_zero _
  have hsm : ∀ (c : R) (w : Fin g → R),
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (w c)) (T w).left →
      IsDerivAt0 (fun z => (e.ex b z).left) (fun d => ψ b ((c • w) d)) (T (c • w)).left := by
    intro c w h
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul h (ψ b c)
    have h2 : (T (c • w)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (ψ b c)) ≫ (T w).left := by
      rw [hTl, hTl, M.smul, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [dualMap_comp_epsMul]
    have h3 : (fun d => ψ b ((c • w) d)) = ψ b c • (fun d => ψ b (w d)) := by
      funext d; simp
    rw [h2, h3]
    exact h1
  have hsingle : ∀ a : Fin g,
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((Pi.single a 1 : Fin g → R) c))
        (T (Pi.single a 1)).left := by
    intro a
    have h3 : (fun c => ψ b ((Pi.single a 1 : Fin g → R) c)) = (Pi.single a 1 : Fin g → ℂ) := by
      funext c
      by_cases h : c = a
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h3]
    exact e.diff b hb a
  have hs : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left)
      (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c))
      (T (∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R))).left := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, hadd]
      have h1 := GlobalTheory.UnifCompare.isDerivAt0_mul (y := spMap (ψ b)) (G := G) hF0
        (hsm (u a) _ (hsingle a)) ih
      have h3 : (fun c => ψ b ((u a • (Pi.single a 1 : Fin g → R) +
          ∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) =
          (fun d => ψ b ((u a • (Pi.single a 1 : Fin g → R)) d)) +
            (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) := by
        funext c; simp only [Pi.add_apply, map_add (f := _)]
      rw [h3]
      exact h1
  have hu : ∑ a, u a • (Pi.single a 1 : Fin g → R) = u := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have := hs Finset.univ
  rw [hu] at this
  exact this

theorem isDerivAt0_frame_section : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ) (b : Fin n → ℂ), b ∈ B → ∀ u : Fin g → R, IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (spMap (dualMap (ψ b)) ≫ (M.pt u).left) :=
  fun _ _ _ _ _ _ _ _ _ _ e _ hb u => isDerivAt0_pt e hb u

end GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.FibPull

theorem fibPF_pull_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) :=
  PositivityTheory.HtPt.Cf.fibpf_pull

end GlobalTheory.CompanionTheory.Ar.FibPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GeomBC

theorem geomPF_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), (∀ (k k₂ : Type) [Field k] [Field k₂] (f : k →+* k₂) (x : Sp k ⟶ X0), GeomPF t x → GeomPF t (spMap f ≫ x)) ∧ ∀ (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (k : Type) [Field k] (x : Sp k ⟶ X₂), GeomPF t₂ x ↔ GeomPF t (x ≫ f) :=
  PositivityTheory.HtPt.Cf.geompf_bc

end GlobalTheory.CompanionTheory.Ar.GeomBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Unif

theorem geomPF_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) :=
  PositivityTheory.HtPt.Cg.unif_pf

end GlobalTheory.CompanionTheory.Ar.Unif
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.flag_model_common_refinement : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | exact GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem mem_of_isIntegral_of_isLocAt {Ω : Type} [Field Ω] [CharZero Ω] (R : Subring Ω) [IsFractionRing R Ω]
    (A : Subalgebra ℚ Ω) (hs : Algebra.Smooth ℚ A) (q : Ideal A) (hq : q.IsPrime) (h : IsLocAt A q R)
    (a : Ω) (ha : IsIntegral R a) : a ∈ R := by
  have hAR : ∀ b : A, (b : Ω) ∈ R := fun b =>
    (h b).2 ⟨1, fun h1 => hq.ne_top ((Ideal.eq_top_iff_one q).2 h1), by simp⟩
  letI : Algebra A R := (RingHom.codRestrict A.val.toRingHom R hAR).toAlgebra
  have hmap : ∀ b : A, ((algebraMap A R b : R) : Ω) = b := fun _ => rfl
  have hne : ∀ s : A, s ∉ q → (s : Ω) ≠ 0 := fun s hs0 h0 =>
    hs0 (by rw [show s = 0 from Subtype.ext h0]; exact q.zero_mem)
  haveI : IsLocalization.AtPrime R q :=
    { map_units := by
        rintro ⟨s, hs0⟩
        have hs1 : s ∉ q := hs0
        refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, (h _).2 ⟨s, hs1, ?_⟩⟩ : R) (Subtype.ext ?_)
        · rw [mul_inv_cancel₀ (hne s hs1)]; exact A.one_mem
        · simp [hmap, mul_inv_cancel₀ (hne s hs1)]
      surj := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs1, hsr⟩ := (h r).1 hr
        exact ⟨⟨⟨_, hsr⟩, ⟨s, hs1⟩⟩, Subtype.ext (by simp [hmap, mul_comm])⟩
      exists_of_eq := by
        intro x y hxy
        exact ⟨1, by
          have : (x : Ω) = y := by simpa [hmap] using congrArg (Subtype.val) hxy
          rw [Subtype.ext this]⟩ }
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := Ω)).1 ha
  exact r.2

end GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ X ξ N x e Ab hall htie hsnc
  let M0 : PModel ℤ x :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }
  obtain ⟨κ', _, y, M', f, hdom, hnorm, -, hat⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω (Fin (N + 1)) x M0 Ω
  have hdom' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ f (RingHom.id Ω) := hdom
  have hiso : ∀ q ∈ genFib ξ, IsoAt M'.ξ f (RingHom.id Ω) q := by
    intro q hq
    have hc : Char0 ξ q := fun r hr hf => hf (hq r hr.pos)
    obtain ⟨A, z, n, P, hp, hP, hloc⟩ := hsnc q hc
    haveI := (GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ htie.gen q).1
    exact GlobalTheory.T.normal_iso_of_integrally_closed X Ω ξ M'.X M'.ξ f q (hat q)
      (fun a ha => mem_of_isIntegral_of_isLocAt _ A hp.smooth P hP hloc a ha)
  obtain ⟨N', x', hx'⟩ := GlobalTheory.T.coord_over_int_of_finite_order M'.X Ω M'.ξ ℤ κ' y M'.tie
  have hone := GlobalTheory.T.coords_single_block_segre M'.X Ω M'.ξ N' x' hx'
  have hsnc' := GlobalTheory.T.snc_points_transfer_dominating Ω (Fin (N + 1)) _ x _ X M'.X ξ M'.ξ f e Ab hall M'.all htie hone hdom' hiso hsnc
  exact ⟨Unit, inferInstance, fun _ => Fin (N' + 1), fun _ => inferInstance, fun p => x' p.2,
    { X := M'.X, ξ := M'.ξ, s := M'.s, hover := M'.hover, all := M'.all, tie := hone }, f,
    inferInstance, hdom', hnorm, hsnc'⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncPull
open GlobalTheory.CompanionTheory.Ar.SncRefine

theorem adjoin_insert_eq {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) :
    Algebra.adjoin ℚ (insert t ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω) : Set Ω)) =
      Algebra.adjoin ℚ (insert t (Set.range (bratio y c))) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro b (rfl | hb)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · have h : Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) ≤
          (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).restrictScalars ℤ := Algebra.adjoin_le (by
        rintro _ ⟨d, rfl⟩
        exact seg_ratio_mem y c (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).toSubring
          (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) d)
      exact h hb
  · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
    rintro _ ⟨p, rfl⟩
    obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩

theorem map_mem_adjoin {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    {W : Set Ω₀} {W' : Set Ω} (hW : ∀ w ∈ W, algebraMap Ω₀ Ω w ∈ W') {b : Ω₀} (hb : b ∈ Algebra.adjoin ℚ W) :
    algebraMap Ω₀ Ω b ∈ Algebra.adjoin ℚ W' := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hW x hx)
  | algebraMap r =>
    have : algebraMap Ω₀ Ω (algebraMap ℚ Ω₀ r) = algebraMap ℚ Ω r := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_cover {R : Type} [CommRing R] (G : R → Prop) (h : ∀ P : Ideal R, P.IsPrime → ∃ t, t ∉ P ∧ G t) :
    ∃ (m : ℕ) (f a : Fin m → R), ∑ l, a l * f l = 1 ∧ ∀ l, G (f l) := by
  classical
  have hs : Ideal.span {t | G t} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht, hG⟩ := h M hM.isPrime
    exact ht (hle (Ideal.subset_span hG))
  have h1 : (1 : R) ∈ Ideal.span {t | G t} := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : R), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x • (x : R)

theorem isSncModel_pull : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  classical
  intro X X' Ω₀ Ω _ _ _ _ _ ξ ξ' f K _ J _ y N x' e bd I _ u hq hq' tie tie' hd hsm hu hadj hsnc c₁ hc₁
  let c : (k : K) → J k := fun k => c₁ (Sum.inr k)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc₁ (Sum.inr k) (show algebraMap Ω₀ Ω (y ⟨k, c k⟩) = 0 by rw [h, map_zero])
  have hv : ∀ p, algebraMap Ω₀ Ω (bratio y c p) = bratio (addY y x') c₁ (addV J N p) := fun p => map_div₀ _ _ _
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hxc₁ : seg (addY y x') c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc₁ k
  have hblk : ∀ p, bratio (addY y x') c₁ p ∈
      Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁) := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio (addY y x') c₁ hc₁ p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  obtain ⟨φ, hφ, hφs⟩ := GlobalTheory.T.dominant_smooth_map_coords X X' Ω₀ Ω ξ ξ' f (algebraMap Ω₀ Ω) _ _ (seg y) (seg (addY y x'))
    hq hq' tie tie' hd hsm c c₁ hxc hxc₁ (fun d => by
      have e1 : seg y d / seg y c = ∏ k, bratio y c ⟨k, d k⟩ := (Finset.prod_div_distrib _ _).symm
      rw [e1, map_prod]
      refine prod_mem fun k _ => ?_
      rw [hv]
      exact hblk _)
  obtain ⟨m, f₀, a₀, hf, ha, hsum, H⟩ := hsnc c hc
  have hfin := GlobalTheory.T.kaehler_rank_transcendence_degree Ω₀ Ω I u hu hadj
  have hW : ∀ w ∈ Set.range (bratio y c), algebraMap Ω₀ Ω w ∈ Set.range (bratio (addY y x') c₁) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hv p).symm⟩
  let R₁ := Algebra.adjoin ℚ (Set.range (bratio (addY y x') c₁))
  have hfr : ∀ (A : Subalgebra ℤ Ω₀) (S : Subalgebra ℚ Ω₀), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω₀, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω₀ := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hfr₁ : ∀ (A : Subalgebra ℤ Ω) (S : Subalgebra ℚ Ω), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hloc : ∀ P : Ideal R₁, P.IsPrime → ∃ t : R₁, t ∉ P ∧ ((t : Ω) ≠ 0 → ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range (bratio (addY y x') c₁))) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + Fintype.card I) → S') (n' : ℕ), n' ≤ e + Fintype.card I ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename (addV J N)), ∀ s : S',
              (s : Ω) = MvPolynomial.aeval (bratio (addY y x') c₁) g → s ∈ q) ↔
            ∃ i : Fin (e + Fintype.card I), (i : ℕ) < n' ∧ z' i ∈ q)) := by
    intro P hP
    let fl : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (f₀ l), map_mem_adjoin hW (hf l)⟩
    let al : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (a₀ l), map_mem_adjoin hW (ha l)⟩
    have hone : ∑ l, al l * fl l = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      show ∑ l, algebraMap Ω₀ Ω (a₀ l) * algebraMap Ω₀ Ω (f₀ l) = 1
      simp only [← map_mul]

      rw [← map_sum, hsum, map_one]
    obtain ⟨l, hl⟩ : ∃ l, fl l ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hcon l)))
    have h0 : f₀ l ≠ 0 := fun h => hl (by
      have : fl l = 0 := Subtype.ext (by show algebraMap Ω₀ Ω (f₀ l) = 0; rw [h, map_zero])
      rw [this]
      exact P.zero_mem)
    obtain ⟨hSm, z, n, hn, hli, hspan, hbd⟩ := H l h0 _ rfl
    have hle₀ : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ Algebra.adjoin ℚ
        ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω₀) : Set Ω₀) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
        rw [hd]
        exact Algebra.subset_adjoin (Algebra.subset_adjoin ⟨d, rfl⟩))
    obtain ⟨ψ, hψ, hψs⟩ := GlobalTheory.T.smooth_map_localization_compat Ω₀ Ω _ _ φ hφ hφs (f₀ l) (hle₀ (hf l)) h0
      (Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))))
      (Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))))
      (adjoin_insert_eq y c hc _).symm (adjoin_insert_eq (addY y x') c₁ hc₁ _).symm
    have hA₀ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c),
        a ∈ Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))) := fun a ha' => by
      rw [← adjoin_insert_eq y c hc]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    have hA₁ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁),
        a ∈ Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))) := fun a ha' => by
      rw [← adjoin_insert_eq (addY y x') c₁ hc₁]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    obtain ⟨t, ht, hG⟩ := GlobalTheory.T.kaehler_rank_localization_bound Ω₀ Ω _ _ (bratio y c) (bratio (addY y x') c₁) (addV J N) hv e _ bd hfin (f₀ l) h0 _ _ rfl rfl
      ψ hψ hψs (hfr _ _ hA₀ (GlobalTheory.T.fraction_field_coords_generated X Ω₀ ξ _ (seg y) tie c hxc))
      (hfr₁ _ _ hA₁ (GlobalTheory.T.fraction_field_coords_generated X' Ω ξ' _ (seg (addY y x')) tie' c₁ hxc₁)) hSm z n hn hli hspan hbd P hP (fl l) rfl hl
    exact ⟨t, ht, fun _ => hG⟩
  obtain ⟨m', f', a', hs', hG⟩ := exists_cover _ hloc
  refine ⟨m', fun l => (f' l : Ω), fun l => (a' l : Ω), fun l => (f' l).2, fun l => (a' l).2, ?_, fun l hl S' hS' => ?_⟩
  · have := congrArg (Subtype.val) hs'
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this
  · obtain ⟨h1, z', n', h2, h3, h4, h5⟩ := hG l hl S' hS'
    exact ⟨h1, z', n', h2, h3, h4, h5⟩

end GlobalTheory.CompanionTheory.Ar.SncPull
end
end

section

open NumberField GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_projector_denominator : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω), ∃ T ∈ Sandwich.opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | exact GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform <;> assumption)
end
