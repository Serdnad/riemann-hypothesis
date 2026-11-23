module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Aesop.Main
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import GroundTheory.HeightsAndTheta.Heights.IterateExamples.Statements

@[expose] public section

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

noncomputable section
namespace LevelTowerAlt.Lin

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O]
    (ρ : O →+* Module.End R W) (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

def intVal (σ : 𝓞 E →+* L) (a : 𝓞 E) : 𝓞 L :=
  ⟨σ a, (NumberField.RingOfIntegers.isIntegral a).map σ.toIntAlgHom⟩

theorem intVal_coe (σ : 𝓞 E →+* L) (a : 𝓞 E) : ((intVal σ a : 𝓞 L) : L) = σ a := rfl

theorem intVal_smul (σ : 𝓞 E →+* L) (a : 𝓞 E) (x : V) : intVal σ a • x = σ a • x := by
  rw [← intVal_coe σ a]
  exact (algebraMap_smul L (intVal σ a) x).symm

structure Pre (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (V₀ : Type) [AddCommGroup V₀] [Module (𝓞 L) V₀]
    (B : HermitianBundle.{0} L) where
  ρ : 𝓞 E →+* Module.End L V
  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)
  fin : Module.Finite (𝓞 L) V₀
  j : V₀ →ₗ[𝓞 L] V
  j_inj : Function.Injective j
  span : Submodule.span L (Set.range j) = ⊤
  ρ₀ : 𝓞 E → V₀ → V₀
  j_ρ : ∀ a x, j (ρ₀ a x) = ρ a (j x)
  r : ℕ
  ε : Fin r → V₀
  ε_li : LinearIndependent (𝓞 L) ε
  I_stable : ∀ a, ∀ x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)),
    ρ a x ∈ AddSubgroup.closure (Set.range fun i => j (ε i))
  f : V₀ →ₗ[𝓞 L] B.carrier
  ker : LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε)
  full : ∀ y, ∃ (a : 𝓞 L) (x : V₀), a ≠ 0 ∧ f x = a • y
  ρ' : 𝓞 E → B.carrier → B.carrier
  f_ρ : ∀ a x, f (ρ₀ a x) = ρ' a (f x)
  bar : 𝓞 E → 𝓞 E
  bar_conj : ∀ (τ : 𝓞 E →+* ℂ), Function.Injective τ → ∀ a, τ (bar a) = starRingEnd ℂ (τ a)
  adj : ∀ (ι : L →+* ℂ) a x y, (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] y) =
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' (bar a) y)

variable {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] {B : HermitianBundle.{0} L} (P : Pre E L Ψ V V₀ B)

theorem Pre.eig {s : Ψ ⊕ Ψ} {x : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s)) (a : 𝓞 E) :
    P.ρ' a (P.f x) = intVal (P.σ s) a • P.f x := by
  have h1 : P.ρ₀ a x = intVal (P.σ s) a • x := by
    apply P.j_inj
    rw [P.j_ρ, map_smul, intVal_smul]
    exact (mem_eigSp _ _ _).1 hx a
  rw [← P.f_ρ, h1, map_smul]

theorem Pre.orth {s s' : Ψ ⊕ Ψ} (h : s ≠ s') (ι : L →+* ℂ) {x y : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s))
    (hy : P.j y ∈ eigSp P.ρ (P.σ s')) :
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, P.σ s a ≠ P.σ s' a := by
    by_contra hc
    push_neg at hc
    exact h (P.σ_bij.1 (RingHom.ext hc))
  have key : ∀ (c : 𝓞 L) (u : B.carrier), ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] (c • u) : Fibre ι B.carrier) =
      (ι (c : L) : ℂ) • ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] u) := by
    intro c u
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  have hτ : Function.Injective (ι.comp (P.σ s')) := ι.injective.comp (P.σ_inj s')
  have e := P.adj ι a (P.f x) (P.f y)
  rw [P.eig hx, P.eig hy, key, key, (B.metric.form ι).smul_left,
    InnerProductSpace.Core.inner_smul_right (c := (B.metric.form ι).toCore), intVal_coe, intVal_coe] at e
  have hb := P.bar_conj _ hτ a
  simp only [RingHom.comp_apply] at hb
  rw [hb] at e
  have hne : (starRingEnd ℂ) (ι (P.σ s a)) ≠ (starRingEnd ℂ) (ι (P.σ s' a)) := by
    intro heq
    exact ha (ι.injective ((starRingEnd ℂ).injective heq))
  have : ((starRingEnd ℂ) (ι (P.σ s a)) - (starRingEnd ℂ) (ι (P.σ s' a))) *
      (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
    rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem Pre.li {ι : Type} {x : ι → V₀} (hx : LinearIndependent (𝓞 L) x) : LinearIndependent L fun i => P.j (x i) := by
  have h := hx.map' P.j (LinearMap.ker_eq_bot.2 P.j_inj)
  exact h.localization (Rₛ := L) (S := nonZeroDivisors (𝓞 L))

def Pre.inv : LinearMap.range P.j →ₗ[𝓞 L] V₀ := (LinearEquiv.ofInjective P.j P.j_inj).symm.toLinearMap

theorem Pre.j_inv (x : LinearMap.range P.j) : P.j (P.inv x) = x := by
  have := (LinearEquiv.ofInjective P.j P.j_inj).apply_symm_apply x
  exact congrArg Subtype.val this

theorem Pre.inv_j (x : V₀) : P.inv ⟨P.j x, x, rfl⟩ = x := P.j_inj (P.j_inv _)

def Pre.lin : LinPt E L Ψ V where
  ρ := P.ρ
  σ := P.σ
  σ_bij := P.σ_bij
  σ_inj := P.σ_inj
  Λ := LinearMap.range P.j
  fg := by
    haveI := P.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span := P.span
  stable := by
    rintro a _ ⟨x, rfl⟩
    exact ⟨_, P.j_ρ a x⟩
  I := AddSubgroup.closure (Set.range fun i => P.j (P.ε i))
  I_le := fun x hx => (AddSubgroup.closure_le (LinearMap.range P.j).toAddSubgroup).2
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  I_stable := P.I_stable
  I_basis := ⟨P.r, _, P.li P.ε_li, rfl⟩
  Bq := B
  f := P.f.comp P.inv
  ker := fun x => by
    have e : Submodule.span (𝓞 L) (AddSubgroup.closure (Set.range fun i => P.j (P.ε i)) : Set V) =
        (Submodule.span (𝓞 L) (Set.range P.ε)).map P.j := by
      rw [Submodule.map_span, ← Set.range_comp]
      refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono AddSubgroup.subset_closure)
      exact (AddSubgroup.closure_le (Submodule.span (𝓞 L) (Set.range (P.j ∘ P.ε))).toAddSubgroup).2
        Submodule.subset_span hy
    rw [e, ← P.ker, LinearMap.comp_apply]
    constructor
    · intro h
      exact ⟨_, h, P.j_inv x⟩
    · rintro ⟨y, hy, hxy⟩
      have : P.inv x = y := P.j_inj ((P.j_inv x).trans hxy.symm)
      rw [this]
      exact hy
  full := fun y => by
    obtain ⟨a, x, ha, h⟩ := P.full y
    exact ⟨a, ⟨P.j x, x, rfl⟩, ha, by rw [LinearMap.comp_apply, P.inv_j, h]⟩
  orth := by
    rintro s s' h ι _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact P.orth h ι (by rw [P.j_inv]; exact hx) (by rw [P.j_inv]; exact hy)

include P in
theorem Pre.rank_le [Module.Finite L V] : Module.finrank (𝓞 L) B.carrier ≤ Module.finrank L V := by
  have h2 : Module.rank (𝓞 L) V₀ ≤ (Module.finrank L V : Cardinal) := by
    apply _root_.rank_le
    intro s hs
    have := (P.li hs).fintype_card_le_finrank
    simpa using this
  have hq : Module.rank (𝓞 L) (B.carrier ⧸ LinearMap.range P.f) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, x, ha, h⟩ := P.full y
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← h]
    exact ⟨x, rfl⟩
  have h1 : Module.rank (𝓞 L) B.carrier ≤ Module.rank (𝓞 L) V₀ := by
    rw [← rank_quotient_add_rank_of_isDomain (LinearMap.range P.f), hq, zero_add]
    exact rank_range_le P.f
  exact Module.finrank_le_of_rank_le (h1.trans h2)

end LevelTowerAlt.Lin
end
end

section

open Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open scoped ContDiff

namespace LevelTowerAlt.Reg

variable {n : ℕ}

theorem usc_comp {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : UpperSemicontinuousOn φ U)
    {g : (Fin n → ℂ) → Fin n → ℂ} (hg : Continuous g) : UpperSemicontinuousOn (fun t => φ (g t)) (g ⁻¹' U) := by
  intro z hz y hy
  have h1 : ∀ᶠ x in 𝓝[U] (g z), φ x < y := h _ hz y hy
  exact (hg.continuousWithinAt.tendsto_nhdsWithin (Set.mapsTo_preimage g U)).eventually h1

theorem isPsh_aff {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) (t₀ : Fin n → ℂ) (c : ℂ) :
    IsPsh ((fun t => t₀ + c • t) ⁻¹' U) fun t => φ (t₀ + c • t) := by
  refine ⟨usc_comp h.1 (by fun_prop), fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, t₀ + c • (z + ζ • w) = t₀ + c • z + ζ • (c • w) := fun ζ => by
    rw [smul_add, smul_comm c ζ, add_assoc]
  simp only [e]
  exact h.2 _ _ fun ζ hζ => e ζ ▸ hd ζ hζ

theorem isPsh_star {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) :
    IsPsh (star ⁻¹' U) fun t => φ (star t) := by
  refine ⟨usc_comp h.1 continuous_star, fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, star (z + ζ • w) = star z + star ζ • star w := fun ζ => by rw [star_add, star_smul]
  obtain ⟨h1, h2⟩ := h.2 (star z) (star w) fun ζ hζ => by
    have := hd (star ζ) (by rwa [norm_star])
    rwa [Set.mem_preimage, e, star_star] at this
  have hc : ∀ θ : ℝ, star (circleMap 0 1 θ) = circleMap 0 1 (2 * Real.pi - θ) := fun θ => by
    rw [sub_eq_add_neg, add_comm, periodic_circleMap]
    simp [circleMap, ← Complex.exp_conj]
  refine ⟨?_, h2.trans_eq ?_⟩
  · unfold CircleIntegrable at h1 ⊢
    simp only [e, hc]
    have := (h1.comp_sub_left (2 * Real.pi)).symm
    simpa using this
  · unfold Real.circleAverage
    simp only [e, hc]
    rw [intervalIntegral.integral_comp_sub_left (fun θ => φ (star z + circleMap 0 1 θ • star w))]
    simp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
  {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd)

theorem exp_le_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ χ.logR t := by
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm t i).trans ht.le))
  · exact le_rfl

theorem piece {F : (Fin n → ℂ) → ℝ} (hO : IsOpen {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFs : ContDiffOn ℝ ∞ F {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFp : IsPsh {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} F) {t₀ : Fin n → ℂ} {ε C Q : ℝ}
    (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (hsep : ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) (hC : 0 < C)
    (hb : ∀ t ∈ {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd}, ‖t - t₀‖ < 2 * ε →
      -(C * Real.log (χ.logR t)) ≤ F t ∧ F t ≤ C ∧
        ‖fderiv ℝ F t‖ ≤ C * χ.logR t ^ C * Real.exp (χ.logR t / 2))
    (L : (Fin n → ℂ) →L[ℝ] Fin n → ℂ) (hL : ∀ t i, ‖L t i‖ = ‖t i‖)
    (hLp : ∀ U φ, IsPsh U φ → IsPsh (L ⁻¹' U) fun t => φ (L t))
    {S : Finset (Fin n)} (hS : ∀ i, i ∈ S ↔ (i : ℕ) < χ.a ∧ t₀ i = 0) {q p : (Fin n → ℂ) → ℝ}
    (hq : ∀ t ∈ ball (0 : Fin n → ℂ) 1, |q t| ≤ Q)
    (hu : ∀ t ∈ ball (0 : Fin n → ℂ) 1, χ.γ (t₀ + (ε : ℂ) • L t) ∉ Bd → q t + p t = F (t₀ + (ε : ℂ) • L t)) :
    ContDiffOn ℝ ∞ (fun y => q y + p y) (ball 0 1 \ coordDiv S) ∧
      IsPsh (ball 0 1 \ coordDiv S) (fun y => q y + p y) ∧
      ∃ C' c : ℝ, 0 < C' ∧ ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, ∀ ρ : ℝ,
        Real.exp 1 + c + ∑ i ∈ S, Real.log (‖t i‖ ^ 2)⁻¹ ≤ ρ →
          p t ≤ C' ∧ -C' * Real.log ρ ≤ p t ∧
            ‖fderiv ℝ (fun y => q y + p y) t‖ ≤ C' * ρ ^ C' * Real.exp (ρ / 2) := by
  classical
  set O := {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} with hOdef
  have hLn : ∀ t, ‖L t‖ ≤ ‖t‖ := fun t =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (hL t i).trans_le (norm_le_pi_norm t i)
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
  have hT : ∀ t, ‖(ε : ℂ) • L t‖ ≤ ε * ‖t‖ := fun t => by
    rw [norm_smul, hεn]; exact mul_le_mul_of_nonneg_left (hLn t) hε.le
  have hTi : ∀ t i, ‖((ε : ℂ) • L t) i‖ = ε * ‖t i‖ := fun t i => by
    rw [Pi.smul_apply, norm_smul, hεn, hL]
  have hlow : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ∀ i, t₀ i ≠ 0 → ε ≤ ‖(t₀ + (ε : ℂ) • L t) i‖ := fun t ht i hi => by
    have h1 := hsep i hi
    have h2 := hTi t i
    have h3 := norm_sub_le ((t₀ + (ε : ℂ) • L t) i) (((ε : ℂ) • L t) i)
    rw [Pi.add_apply, add_sub_cancel_right] at h3
    rw [Pi.add_apply]
    nlinarith [norm_le_pi_norm t i]
  have hball : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ‖t₀ + (ε : ℂ) • L t‖ < 1 := fun t ht => by
    have := norm_add_le t₀ ((ε : ℂ) • L t)
    nlinarith [hT t, norm_nonneg t]
  have hmap : ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, t₀ + (ε : ℂ) • L t ∈ O := by
    rintro t ⟨ht, htS⟩
    rw [mem_ball_zero_iff] at ht
    have hb' := mem_ball_zero_iff.2 (hball t ht)
    refine ⟨hb', fun h => ?_⟩
    obtain ⟨i, hi, h0⟩ := (χ.boundary _ hb').1 h
    by_cases h1 : t₀ i = 0
    · refine htS ⟨i, (hS i).2 ⟨hi, h1⟩, ?_⟩
      have h2 := hTi t i
      rw [Pi.add_apply, h1, zero_add] at h0
      rw [h0, norm_zero] at h2
      exact norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hε.ne')
    · have := hlow t ht i h1
      rw [h0, norm_zero] at this
      linarith
  have hV : IsOpen (ball (0 : Fin n → ℂ) 1 \ coordDiv S) :=
    isOpen_ball.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have heq : Set.EqOn (fun t => F (t₀ + (ε : ℂ) • L t)) (fun y => q y + p y) (ball 0 1 \ coordDiv S) :=
    fun t ht => (hu t ht.1 (hmap t ht).2).symm
  have hσ : ContDiff ℝ ∞ fun t => t₀ + (ε : ℂ) • L t := contDiff_const.add (L.contDiff.const_smul _)
  have hpsh : IsPsh (ball 0 1 \ coordDiv S) (fun t => F (t₀ + (ε : ℂ) • L t)) := by
    have h := hLp _ _ (isPsh_aff hFp t₀ ε)
    exact ⟨h.1.mono hmap, fun z w hd => h.2 z w fun ζ hζ => hmap _ (hd ζ hζ)⟩
  have hpsh' : IsPsh (ball 0 1 \ coordDiv S) (fun t => q t + p t) := by
    refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
    · have h1 := hpsh.1 z hz y (by
        change F (t₀ + (ε : ℂ) • L z) < y
        simpa only [heq hz] using hy)
      filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
      simpa only [heq hxU] using hx
    · have hs : Set.EqOn (fun ζ : ℂ => F (t₀ + (ε : ℂ) • L (z + ζ • w)))
          (fun ζ => q (z + ζ • w) + p (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
        fun ζ hζ => heq (hd ζ (by simp at hζ; rw [hζ]))
      obtain ⟨h1, h2⟩ := hpsh.2 z w hd
      refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
      have hz : z ∈ ball 0 1 \ coordDiv S := by simpa using hd 0 (by simp)
      rw [← Real.circleAverage_congr_sphere hs, ← heq hz]
      exact h2
  refine ⟨(hFs.comp hσ.contDiffOn hmap).congr fun t ht => (heq ht).symm,
    hpsh', C + |Q|, n * Real.log (1 / ε ^ 2), by positivity,
    fun t ht ρ hρ => ?_⟩
  have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht.1
  set s := t₀ + (ε : ℂ) • L t with hs
  have hsO : s ∈ O := hmap t ht
  obtain ⟨b1, b2, b3⟩ := hb s hsO (by
    rw [hs, add_sub_cancel_left]
    nlinarith [hT t, norm_nonneg t])
  have hRe := exp_le_logR χ (hball t ht1)
  have hRρ : χ.logR s ≤ ρ := by
    refine le_trans ?_ hρ
    have hl0 : 0 ≤ Real.log (1 / ε ^ 2) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; nlinarith)
    have : ∑ i : Fin n, (if (i : ℕ) < χ.a then Real.log (1 / ‖s i‖ ^ 2) else 0) ≤
        ∑ i : Fin n, (Real.log (1 / ε ^ 2) + if i ∈ S then Real.log (‖t i‖ ^ 2)⁻¹ else 0) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (i : ℕ) < χ.a
      · by_cases h1 : t₀ i = 0
        · have hiS := (hS i).2 ⟨hi, h1⟩
          have hti : ‖t i‖ ≠ 0 := norm_ne_zero_iff.2 fun h => ht.2 ⟨i, hiS, h⟩
          rw [if_pos hi, if_pos hiS, hs, Pi.add_apply, h1, zero_add, hTi,
            ← Real.log_mul (by positivity) (by positivity)]
          refine le_of_eq (congrArg _ ?_)
          field_simp
        · rw [if_pos hi, if_neg fun h => h1 ((hS i).1 h).2, add_zero]
          have h2 := hlow t ht1 i h1
          have h3 : 0 < ‖s i‖ := hε.trans_le h2
          exact Real.log_le_log (by positivity)
            (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε.le h2 2))
      · rw [if_neg hi, if_neg fun h => hi ((hS i).1 h).1, add_zero]
        exact hl0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter] at this
    unfold SncChart.logR
    linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hl1 : 1 ≤ Real.log ρ := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hl2 : Real.log (χ.logR s) ≤ Real.log ρ := Real.log_le_log (by linarith) hRρ
  have hqt := abs_le.1 ((hq t ht.1).trans (le_abs_self Q))
  have hut : q t + p t = F s := hu t ht.1 hsO.2
  refine ⟨by linarith, by nlinarith [abs_nonneg Q], ?_⟩
  have hFd : HasFDerivAt F (fderiv ℝ F s) s :=
    ((hFs.contDiffAt (hO.mem_nhds hsO)).differentiableAt (by simp)).hasFDerivAt
  have hσd : HasFDerivAt (fun t => t₀ + (ε : ℂ) • L t) ((ε : ℂ) • L) t :=
    (L.hasFDerivAt.const_smul (ε : ℂ)).const_add t₀
  have hd : HasFDerivAt (fun y => q y + p y) ((fderiv ℝ F s).comp ((ε : ℂ) • L)) t :=
    (hFd.comp t hσd).congr_of_eventuallyEq
      (by filter_upwards [hV.mem_nhds ht] with y hy using (heq hy).symm)
  rw [hd.fderiv]
  have hn : ‖(fderiv ℝ F s).comp ((ε : ℂ) • L)‖ ≤ ‖fderiv ℝ F s‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    refine ((fderiv ℝ F s).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (hT v).trans ?_
    nlinarith [norm_nonneg v]
  refine hn.trans (b3.trans ?_)
  have hp : χ.logR s ^ C ≤ ρ ^ (C + |Q|) :=
    (Real.rpow_le_rpow (by linarith) hRρ hC.le).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_add_of_nonneg_right (abs_nonneg Q)))
  have hρ0 : 0 ≤ χ.logR s := by linarith
  have hρ1 : 0 ≤ ρ := by linarith
  have hC' : C ≤ C + |Q| := le_add_of_nonneg_right (abs_nonneg Q)
  exact mul_le_mul (mul_le_mul hC' hp (Real.rpow_nonneg hρ0 _) (by positivity))
    (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)

end LevelTowerAlt.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_im] using this
  have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_re] using this
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h2
      nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

end LevelTowerAlt
end
