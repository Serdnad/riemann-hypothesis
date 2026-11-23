module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle006
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.regular_ring_determines_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_eigen_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (L : Lat ξ E) (T : Set (Cpt ξ)) (g : ℕ) (I : Type) [Fintype I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), IsCptGen ξ → Function.Injective σ → Fintype.card I = Module.finrank ℚ F → [CharZero Ω] → L.IsVBOn T g ⊤ → (∀ p ∈ T, ∀ a, ∀ e ∈ L p, ρ a e ∈ L p) → (∀ p ∈ T, ∀ s a, σ s a ∈ regAt ξ p) → (∀ p ∈ T, unitAt ξ p ((NumberField.discr F : ℤ) : Ω)) → (∀ s, (L.inter (eigSp ρ (σ s))).IsVBOn T (Module.finrank Ω (eigSp ρ (σ s))) (eigSp ρ (σ s))) ∧ ∀ p ∈ T, L p = ⨆ s, (L.inter (eigSp ρ (σ s))) p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lattice_frame_sub_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lattice_intersection_frame_subspace : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated | exact GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.generic_flag_triangular_change : ∀ (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ) (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L), LinearIndependent L f → LinearIndependent L b → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → (∀ k, g k = ∑ j, (v * w) j k • f j) → (∀ i : ℕ, GlobalTheory.CompanionTheory.Ar.flagStep L b i = GlobalTheory.CompanionTheory.Ar.flagStep L g i) → ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧ (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | exact GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.flag_coefficient_ratio_integral : ∀ (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ) (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω), LinearIndependent Ω b → (∀ j, flagStep Ω b j = flagStep Ω b₀ j) → (∀ j, flagStep Ω b' j = flagStep Ω b₀ j) → (∀ j, N • b' j ∈ Submodule.span W (Set.range b)) → b k - t • b₀ k ∈ flagStep Ω b₀ k → b' k - t' • b₀ k ∈ flagStep Ω b₀ k → N * (t' / t) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | exact GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_tensor_power_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | exact GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.minor_ratio_regular_of_invertible : ∀ (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r) (J : Fin ((k : ℕ) + 1) → Fin n), (∀ j l, A j l ∈ R) → (∀ l j, B l j ∈ R) → B * A = 1 → a ≠ 0 → ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0 → (∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det / ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) → ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_basis_change_integral : ∀ (K : Type) [Field K] (R : Subring K) [IsLocalRing R] (r : ℕ) (g : Fin r → Fin r → K), (∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1)) → ∃ P : Matrix (Fin r) (Fin r) K, (∀ a b, P a b ∈ R) ∧ P.det ≠ 0 ∧ P.det⁻¹ ∈ R ∧ ∀ i, flagStep K (fun k a => P a k) i = flagStep K g i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.generic_flag_trdeg_formula : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E] [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ), IsGenericFlag (Ω' := Ω) j V b₀ d → Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_stable_under_action : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable | exact GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagIso

theorem flag_graded_transport : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (φ : V ≃ₗ[Ω] V') (L : Lat ξ V) (L' : Lat ξ' V') (r : ℕ) (b : Fin r → V), ξ' ≫ e.hom = ξ → (∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : V), v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q) → (L.IsFlagVBOn Set.univ b ↔ L'.IsFlagVBOn Set.univ (fun i => φ (b i))) ∧ ∀ (i : Fin r) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), (L'.gr (fun i => φ (b i)) i q : Set Ω) = L.gr b i ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.flag_bundle_iff_under_isomorphism

end GlobalTheory.CompanionTheory.Ar.FlagIso
end
