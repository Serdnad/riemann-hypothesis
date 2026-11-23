module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle026
public import Development.WeilBound.CoreStatements.IdealCycleValues.CycListAdditiveFirstClass
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle110
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle027
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.localization_model_over_place : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], pointIdeal O y = (pointIdeal A y).map (MvPolynomial.map (algebraMap A O)) ∧ IsModelOver (pointIdeal O y) D ∧ ∀ (ϖ : O), Irreducible ϖ → ∀ (σ : Type) (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff (mCoordIdeal y) S → (T.map (Int.castRingHom O)).IsVert (pointIdeal O y) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.pl_model | exact GlobalTheory.CompanionTheory.Ar.Num.pl_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.pl_model <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.lin_root_remainder_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound | exact GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.vertical_number_local_cycle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | exact GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.power_sum_term_discrete_valuation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ), Q.IsHomogeneous (d + 1 - k) → (∀ i, (Hs i).IsHomogeneous (d - k)) → (k = d + 1 → ∀ i, Hs i = 0) → ∀ T : LocPair ι O (Ψ × Fin N), T.IsVert P ϖ → FlagChernComparison P d p j φ T → PowerSumsVanish P d (fun i : Fin N => T.x' (τ, i)) → T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr | exact GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycList_divCycle_add_first : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  exact @BaseChangeColon.cycList_additive_first_class

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rootLines_vert_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (x x' : CMType H × Fin (D.p + D.q) → K → ℤ) (e₀ e : CMType H × Fin (D.p + D.q) → Ω), (Fl.shrink S₀ h hvb hsub).RootLines x e₀ → Fl.RootLines x' e → ∃ f g : CMType H × Fin (D.p + D.q) → MvPolynomial (Σ k, J k) ℤ, (∀ r, aeval y (f r) = e r / e₀ r * aeval y (g r)) ∧ (⟨x, x', f, g⟩ : LocPair J ℤ (CMType H × Fin (D.p + D.q))).IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha Fl S₀ h hvb hsub x x' e₀ e h₀ h₁
  have key : ∀ r, ∃ f g : MvPolynomial (Σ k, J k) ℤ,
      (⟨fun _ => x r, fun _ => x' r, fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y)
        ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      aeval y f = e r / e₀ r * aeval y g := by
    intro r
    refine GlobalTheory.T.degree_lattices_prime_compare 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d ha ((Fl.shrink S₀ h hvb hsub).rootLat r) (Fl.rootLat r)
      (x r) (x' r) (e₀ r) (e r) (h₀ r) (h₁ r) _ ?_
    intro q hq
    exact GlobalTheory.T.flag_height_bound_arith_var E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha Fl S₀ h hvb hsub q
      (fun p hp hp' hf => hq ⟨p, 𝔐.S_prime p hp⟩ (Finset.mem_preimage.2 (Finset.mem_sdiff.2 ⟨hp, hp'⟩)) hf) r
  choose f g hv hr using key
  exact ⟨f, g, hr, fun r => hv r ()⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def relabGroup (H : Host E) : Subgroup (Equiv.Perm (CMType H)) where
  carrier := {s | ∃ g : HostAut H, ∀ τ, (s τ).1 = τ.1.comp g.σ.toRingHom}
  one_mem' := ⟨HostAut.refl H, fun τ => by ext x; rfl⟩
  mul_mem' := by
    rintro s₁ s₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨⟨g₁.σ.trans g₂.σ, by simp [g₁.fix, g₂.fix]⟩, fun τ => ?_⟩
    rw [Equiv.Perm.mul_apply, h₁, h₂]
    ext x; rfl
  inv_mem' := by
    rintro s ⟨g, h⟩
    refine ⟨g.symm, fun τ => ?_⟩
    have e := h (s⁻¹ τ)
    rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
    rw [e]
    ext x
    show _ = (s⁻¹ τ).1 (g.σ (g.σ.symm x))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA

open GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA in
theorem GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (S : ℕ → Finset ℕ) (n : ℕ) (tie : ∀ B k, HodgeTie Y (S B) n (T.M B k)), IsGalois ℚ E → Mono (spMap β) → T.Conv II → (∀ B k k', ∀ p ∈ S B, (tie B k').A.R p = (tie B k).A.R p) → (∀ (B : ℕ) (Φ : Xo.X ≅ Xo.X), Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm T.Comp, ∀ k, IsImageCpt Φ (tie B k).A (tie B (π k)).A) → T.PropA II := by
  intro hCmp hTw II hII E _ _ _ H D l Xo c O _ β Y _ T S n tie hGal hMono hConv hR hPerm
  refine GlobalTheory.T.tower_symmetry_limit_compat (CMType H) (D.p + D.q) T II (relabGroup H) hConv ?_ ?_ hII.1
  · intro τ τ'
    obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_host_aut_embedding E H τ.1 τ'.1 τ.2 τ'.2
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
    exact ⟨π, ⟨g, hπ⟩, Subtype.ext ((hπ τ).trans hg.symm)⟩
  · intro s hs B _
    obtain ⟨g₀, hg₀⟩ := hs
    have hinv : ∀ τ, (s⁻¹ τ).1 = τ.1.comp g₀.symm.σ.toRingHom := by
      intro τ
      have e := hg₀ (s⁻¹ τ)
      rw [show s (s⁻¹ τ) = τ from Equiv.apply_symm_apply s τ] at e
      rw [e]
      ext x
      show _ = (s⁻¹ τ).1 (g₀.σ (g₀.σ.symm x))
      rw [RingEquiv.apply_symm_apply]
    obtain ⟨⟨a⟩, hA⟩ := hTw E H D l Xo g₀.symm
    obtain ⟨h, Φ, hΦ, ⟨m⟩⟩ := hA a
    obtain ⟨πc, himg⟩ := hPerm B Φ hΦ
    refine ⟨πc, fun k w => ?_⟩
    have key := hCmp II hII E H D l Xo c O β Y g₀.symm Φ m.toSABMap s⁻¹ (S B) n (T.M B k) (T.M B (πc k))
      (tie B k) (tie B (πc k)) hMono hΦ hinv (himg k) (fun p hp => hR B k (πc k) p hp)
      (fun j => (s (w j).1, (w j).2))
    have e2 : ∀ x, s⁻¹ (s x) = x := fun x => Equiv.symm_apply_apply s x
    simpa only [e2, Prod.mk.eta] using key
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.log_integral_multilinear : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (ℓ j)) → (ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) = ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1)) ∧ (∀ (L L' : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)), (∀ k, IsSmoothHerm (L k)) → (∀ k, IsSmoothHerm (L' k)) → (∀ k, (L' k).a = (L (σ k)).a) → ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geo_multilin | exact GlobalTheory.CompanionTheory.Ar.Top.geo_multilin | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geo_multilin <;> assumption)
end
