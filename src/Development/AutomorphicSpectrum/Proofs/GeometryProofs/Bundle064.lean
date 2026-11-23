module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle010
public import Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle054
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.WtShift

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem ent_sub_smul (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) (i : ℕ) :
    ent (lam - s • nu) τ i = ent lam τ i - s * ent nu τ i := by
  simp only [ent]
  split_ifs <;> simp

theorem abs_ent_le (nu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent nu τ i| ≤ ‖nu‖ := by
  simp only [ent]
  split_ifs with h
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (nu τ) _).trans (norm_le_pi_norm nu τ)
  · simp

theorem dominant_of_step (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → ent mu τ (i + 1) ≤ ent mu τ i) : Dominant mu := by
  intro τ a b hab
  have key : ∀ k i, i + k < N → ent mu τ (i + k) ≤ ent mu τ i := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      exact (h τ (i + k) (by omega)).trans (ih i (by omega))
  have hab' : (a : ℕ) ≤ b := hab
  have hk := key ((b : ℕ) - a) a (by omega)
  rw [Nat.add_sub_cancel' hab'] at hk
  simpa [ent, a.2, b.2] using hk

theorem sub_small_dominant : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N →
    0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) →
      CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧
        ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  intro Ψ _ _ N j nu c₀ hj hjN hc₀
  have hM0 : 0 ≤ ‖nu‖ := norm_nonneg _
  refine ⟨min 1 (min (1 / (4 * (‖nu‖ + 1))) (c₀ / (2 * (‖nu‖ + 1)))), by positivity, min_le_left _ _, ?_⟩
  intro lam θ hlam hθ hθ₀ hgap hcg
  have hθ1 : θ ≤ 1 := hθ₀.trans (min_le_left _ _)
  have hA' : θ ≤ 1 / (4 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : θ ≤ c₀ / (2 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA := (le_div_iff₀ (by positivity)).1 hA'
  have hB := (le_div_iff₀ (by positivity)).1 hB'
  have hθM : θ * ‖nu‖ ≤ 1 / 4 := by nlinarith
  have hθM' : θ * ‖nu‖ ≤ c₀ / 2 := by nlinarith
  have hdiff : ∀ τ i i', ent nu τ i - ent nu τ i' ≤ 2 * ‖nu‖ := fun τ i i' => by
    have h1 := abs_le.1 (abs_ent_le nu τ i)
    have h2 := abs_le.1 (abs_ent_le nu τ i')
    linarith [h1.2, h2.1]
  have hsq : θ ^ 2 * (2 * ‖nu‖) ≤ θ / 2 := by nlinarith
  have hsq2 : θ ^ 2 * (2 * ‖nu‖) ≤ c₀ := by nlinarith
  refine ⟨dominant_of_step _ fun τ i hi => ?_, ?_, fun τ => ?_⟩
  · rw [ent_sub_smul, ent_sub_smul]
    have hd := mul_le_mul_of_nonneg_left (hdiff τ i (i + 1)) (sq_nonneg θ)
    by_cases hij : i + 1 = j
    · subst hij
      have hg := hgap τ
      simp only [gap, Nat.add_sub_cancel] at hg
      nlinarith
    · have hc := hcg τ i hi hij
      nlinarith
  · calc ‖lam - θ ^ 2 • nu‖ ≤ ‖lam‖ + ‖θ ^ 2 • nu‖ := norm_sub_le _ _
      _ = ‖lam‖ + θ ^ 2 * ‖nu‖ := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg θ)]
      _ ≤ 2 := by nlinarith
  · have hg := hgap τ
    have hd := mul_le_mul_of_nonneg_left (hdiff τ (j - 1) j) (sq_nonneg θ)
    simp only [gap] at hg ⊢
    rw [ent_sub_smul, ent_sub_smul]
    nlinarith

end GlobalTheory.CompanionTheory.Ar.WtShift
end
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.mem_btOrder_iff_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.valuation_centre_regular_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_decomposition_exact_sequence : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] (ρ₁ : 𝓞 E →+* Module.End k V₁) (ρ₂ : 𝓞 E →+* Module.End k V₂) (ρ₃ : 𝓞 E →+* Module.End k V₃) (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃), Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g → (∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) → (∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) → ∀ (τ : 𝓞 E →+* k) (r n : ℕ) (b₁ : Fin r → V₁) (b₂ : Fin n → V₂), LinearIndependent k b₁ → Submodule.span k (Set.range b₁) = eigSp ρ₁ τ → LinearIndependent k b₂ → Submodule.span k (Set.range b₂) = eigSp ρ₂ τ → r ≤ n ∧ ∃ b₃ : Fin (n - r) → V₃, LinearIndependent k b₃ ∧ Submodule.span k (Set.range b₃) = eigSp ρ₃ τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot | exact GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.component_generic_char_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | exact GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | (intros; apply GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.component_generic_is_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | exact GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_existsUnique_semilinear : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'), ∃! j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | exact GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.tangent_vector_sum_dual_number : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | exact GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.FracPts

variable {Ω : Type} [Field Ω]

theorem exists_prime_of_subset {k : Type} [CommRing k] [Algebra k Ω] (S : Subalgebra k Ω) (R : Subring Ω)
    (hR : IsLocalRing R) (h : ∀ s ∈ S, s ∈ R) :
    ∃ I : Ideal S, I.IsPrime ∧ ∀ s : S, s ∉ I ↔ ((s : Ω) ≠ 0 ∧ (s : Ω) ∈ R ∧ (s : Ω)⁻¹ ∈ R) := by
  let f : S →+* R := (S.val : S →+* Ω).codRestrict R (fun s => h s s.2)
  refine ⟨(IsLocalRing.maximalIdeal R).comap f, Ideal.IsPrime.comap f, fun s => ?_⟩
  have hs : (f s : Ω) = (s : Ω) := rfl
  rw [Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have hu' : ((u : R) : Ω) = (s : Ω) := by rw [hu, hs]
    rw [hu'] at h1
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, h s s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (((u⁻¹ : Rˣ) : R)).2
  · rintro ⟨h0, h1, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : R) (Subtype.ext ?_)
    change (s : Ω) * (s : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ h0

variable {X : Scheme.{0}}

theorem mem_regAt_of_unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (h : s * a ∈ regAt ξ p) : a ∈ regAt ξ p := by
  have : a = s⁻¹ * (s * a) := by rw [inv_mul_cancel_left₀ hs.1]
  rw [this]
  exact (regAt ξ p).mul_mem hs.2.2 h

theorem unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (ha : unitAt ξ p a) : unitAt ξ p (s * a) := by
  refine ⟨mul_ne_zero hs.1 ha.1, (regAt ξ p).mul_mem hs.2.1 ha.2.1, ?_⟩
  rw [mul_inv]
  exact (regAt ξ p).mul_mem hs.2.2 ha.2.2

variable (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F]
  [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω]


include F in
theorem algebraMap_ne_zero {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem adjoin_subset (S : Set Ω) : ∀ a ∈ Algebra.adjoin o S, a ∈ Algebra.adjoin F S := by
  have : Algebra.adjoin o S ≤ (Algebra.adjoin F S).restrictScalars o :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact fun a ha => this ha

theorem exists_mul_mem_adjoin (S : Set Ω) (b : Ω) (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ algebraMap o Ω d * b ∈ Algebra.adjoin o S := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := o) r
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d, hd0, ?_⟩
    have hF : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd0
    have : algebraMap o Ω d * algebraMap F Ω (algebraMap o F n / algebraMap o F d) = algebraMap o Ω n := by
      rw [IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, mul_div_cancel₀ _ hF,
        ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x + y) =
        algebraMap o Ω e * (algebraMap o Ω d * x) + algebraMap o Ω d * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ e) h) (mul_mem (Subalgebra.algebraMap_mem _ d) h')
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x * y) = (algebraMap o Ω d * x) * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem h h'

variable {W : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ W}
  {κ : Type} {t : κ → Ω}

theorem unitAt_algebraMap (hF : CoordTie F ξ' t) {c : κ} {p' : Cpt ξ'} (hc : InChart ξ' t c p') {d : o}
    (hd : d ≠ 0) : unitAt ξ' p' (algebraMap o Ω d) := by
  have hF0 : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd
  have hmem : ∀ r : F, algebraMap F Ω r ∈ regAt ξ' p' := fun r =>
    (hF.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  refine ⟨algebraMap_ne_zero o F hd, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply o F Ω]
    exact hmem _
  · rw [IsScalarTower.algebraMap_apply o F Ω, ← map_inv₀]
    exact hmem _

theorem regAt_eq_of_units (hA : CoordTie o ξ t) (hF : CoordTie F ξ' t) {c : κ} {p : Cpt ξ} {p' : Cpt ξ'}
    (hc : InChart ξ t c p) (hc' : InChart ξ' t c p')
    (hu : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), unitAt ξ p s ↔ unitAt ξ' p' s) :
    regAt ξ p = regAt ξ' p' := by
  have hB : ∀ b ∈ Algebra.adjoin F (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    (hF.ring c hc'.1 b).1 hb p' hc'
  have hA' : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    hB b (adjoin_subset o F _ b hb)
  have hAp : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ p := fun b hb =>
    (hA.ring c hc.1 b).1 hb p hc
  ext a
  constructor
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).1 ha
    exact mem_regAt_of_unitAt_mul ((hu s hs).1 hsu) (hA' _ hsa)
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization W Ω ξ' F κ t hF c p' hc' a).1 ha
    obtain ⟨d, hd, hds⟩ := exists_mul_mem_adjoin o F _ s hs
    obtain ⟨e, he, hes⟩ := exists_mul_mem_adjoin o F _ _ hsa
    have hunit : unitAt ξ' p' (algebraMap o Ω e * (algebraMap o Ω d * s)) :=
      unitAt_mul (unitAt_algebraMap o F hF hc' he) (unitAt_mul (unitAt_algebraMap o F hF hc' hd) hsu)
    have hmemA : algebraMap o Ω e * (algebraMap o Ω d * s) ∈
        Algebra.adjoin o (Set.range fun j => t j / t c) :=
      mul_mem (Subalgebra.algebraMap_mem _ e) hds
    refine (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).2
      ⟨_, hmemA, (hu _ hmemA).2 hunit, ?_⟩
    have : algebraMap o Ω e * (algebraMap o Ω d * s) * a =
        algebraMap o Ω d * (algebraMap o Ω e * (s * a)) := by ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ d) hes

theorem regAt_frac :
    ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω]
      [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type)
      (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t →
      (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧
        ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  intro o F _ _ _ _ _ Ω _ _ _ _ X W ξ ξ' κ t hA hF
  constructor
  · intro p'
    obtain ⟨c, hc⟩ := hF.cover p'
    have hloc : IsLocalRing (regAt ξ' p') := (regAt_isLocalRing_isFractionRing_stalk W Ω ξ' hF.gen p').1
    have hsub : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), s ∈ regAt ξ' p' := fun s hs =>
      (hF.ring c hc.1 s).1 (adjoin_subset o F _ s hs) p' hc
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ' p') hloc hsub
    obtain ⟨p, ⟨hp, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ t hA c hc.1 I hI
    refine ⟨p, regAt_eq_of_units o F hA hF hp hc fun s hs => ?_⟩
    exact (hpu ⟨s, hs⟩).symm.trans (hIu ⟨s, hs⟩)
  · intro p hd
    obtain ⟨c, hc⟩ := hA.cover p
    have hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hA.gen p).1
    have hsub : ∀ s ∈ Algebra.adjoin F (Set.range fun j => t j / t c), s ∈ regAt ξ p := fun s hs => by
      obtain ⟨d, hd0, hds⟩ := exists_mul_mem_adjoin o F _ s hs
      exact mem_regAt_of_unitAt_mul (hd d hd0) ((hA.ring c hc.1 _).1 hds p hc)
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ p) hloc hsub
    obtain ⟨p', ⟨hp', hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point W Ω ξ' F κ t hF c hc.1 I hI
    refine ⟨p', regAt_eq_of_units o F hA hF hc hp' fun s hs => ?_⟩
    have hsB := adjoin_subset o F _ s hs
    exact (hIu ⟨s, hsB⟩).symm.trans (hpu ⟨s, hsB⟩)

end GlobalTheory.CompanionTheory.Ar.SncBase.FracPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.lattice_basis_pullback_dominant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dominant_smooth_map_coords : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | exact GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing <;> assumption)
end
