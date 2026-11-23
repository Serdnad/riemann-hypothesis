module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle025
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle137
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle012
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.root_model_geometric_generic_number : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N) → M.geoFun (toA F) = genNum ℚ (extTo ℚ M.P) M.xdeg F [] / (M.δ : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq | exact GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.isometric_family_intersection_eq : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val | exact GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.arMono_eq_relined_isometric_vert : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA | exact GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effDiff_of_goodOrigin : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu :=
  @RootFieldNumerics.global_model_tower_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effective_mul_nef_nonneg : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) :=
  @RootFieldNumerics.intersection_section_log_integral

end GlobalTheory.CompanionTheory.Ar.Top
end
