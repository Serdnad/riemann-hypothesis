module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle024
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle014
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle019
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle022
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle015
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Top.Link

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def reline (M : RootModel Ψ N) (xdeg : Ψ × Fin N → M.K → ℤ) (x : ℝ → Ψ × Fin N → HermLine M.ι)
    (x_deg : ∀ t r, (x t r).a = xdeg r) (x_smooth : ∀ t r, IsSmoothHerm (x t r))
    (x_conj : ∀ t r, IsConjInvariantH (x t r)) (A : HermLine M.ι) (A_smooth : IsSmoothHerm A)
    (A_conj : IsConjInvariantH A) : RootModel Ψ N :=
  { M with xdeg := xdeg, x := x, x_deg := x_deg, x_smooth := x_smooth, x_conj := x_conj, A := A,
           A_smooth := A_smooth, A_conj := A_conj }

theorem arMono_reline (M : RootModel Ψ N) {d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁ d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂}
    (II : IntersectionSystem) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (hx : ∀ r, x₁ t r = x₂ t r) (hA : A₁ = A₂) :
    (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).arMono II t m = (reline M d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂).arMono II t m := by
  subst hA
  have hl : (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).line t = (reline M d₂ x₂ h₂ s₂ c₂ A₁ a₂ b₂).line t := by
    funext o
    cases o with
    | none => rfl
    | some r => exact hx r
  unfold RootModel.arMono
  rw [hl]
  rfl

def pullModel (M₀ : RootModel Ψ N) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (ha : IsArithVar (mCoordIdeal y) (dimFl Ψ N + 1)) (hb : Birational y)
    {κ : M₀.K → K} {v : (Σ k, M₀.ι k) → Σ k, J k} (hv : IsBlockMap κ v) (δ : ℕ) (hδ : 0 < δ) : RootModel Ψ N where
  K := K
  ι := J
  Ω := Ω
  y := y
  arith := ha
  birational := hb
  xdeg r := pullDeg κ (M₀.xdeg r)
  x t r := pullHerm hv (M₀.x t r)
  x_deg t r := by
    show pullDeg κ (M₀.x t r).a = _
    rw [M₀.x_deg]
  x_smooth t r := Chg.isSmoothHerm_pull hv (M₀.x_smooth t r)
  x_conj t r := Chg.isConj_pull hv (M₀.x_conj t r)
  kA := M₀.kA
  kA_pos := M₀.kA_pos
  A := pullHerm hv M₀.A
  A_smooth := Chg.isSmoothHerm_pull hv M₀.A_smooth
  A_conj := Chg.isConj_pull hv M₀.A_conj
  δ := δ
  δ_pos := hδ

end GlobalTheory.CompanionTheory.Ar.Top.Link
end
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable def fractionRingRingEquiv (A L : Type) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [IsFractionRing A L] : L ≃+* FractionRing A :=
  (FractionRing.algEquiv A L).toRingEquiv.symm

noncomputable def ratEquivFractionZP (p : Nat.Primes) : ℚ ≃+* FractionRing (ZP p) :=
  letI : Algebra (ZP p) ℚ :=
    (IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (S := ZP p)
      (g := algebraMap ℤ ℚ) (fun y => isUnit_iff_ne_zero.2 (by
        have hy : (y : ℤ) ≠ 0 := fun h => y.2 (h ▸ Ideal.zero_mem _)
        simpa using hy))).toAlgebra
  haveI : @IsScalarTower ℤ (ZP p) ℚ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsFractionRing (ZP p) ℚ :=
    IsFractionRing.isFractionRing_of_isLocalization
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl (ZP p) ℚ (Ideal.primeCompl_le_nonZeroDivisors _)
  fractionRingRingEquiv (ZP p) ℚ

theorem genFib_extTo_zp {K : Type} {ι : K → Type} (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) :
    genFib (extTo (ZP p) P) =
      (extTo ℚ P).map (MvPolynomial.map ((ratEquivFractionZP p : ℚ ≃+* FractionRing (ZP p)) :
        ℚ →+* FractionRing (ZP p))) := by
  unfold genFib extTo
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun f => ?_
  simp only [RingHom.comp_apply, MvPolynomial.map_map]
  exact congrArg (fun φ : ℤ →+* FractionRing (ZP p) => MvPolynomial.map φ f) (RingHom.ext_int _ _)

theorem genNum_zp_eq_rat (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
    (Q : List (K → ℤ)) :
    genNum (FractionRing (ZP p)) (genFib (extTo (ZP p) P)) cls H Q = genNum ℚ (extTo ℚ P) cls H Q := by
  unfold genNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [genFib_extTo_zp, GlobalTheory.T.intersection_number_field_equiv K ι ℚ (FractionRing (ZP p)) (ratEquivFractionZP p)]

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem abs_apply_le_of_monomial_bound {σ : Type} (G : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (F : MvPolynomial σ ℝ) {d : ℕ}
    (hF : F.IsHomogeneous d) {e : ℝ} (he : ∀ m : σ →₀ ℕ, m.degree = d → |G (monomial m 1)| ≤ e) :
    |G F| ≤ (∑ m ∈ F.support, |F.coeff m|) * e := by
  have h1 : G F = ∑ m ∈ F.support, F.coeff m * G (monomial m 1) := by
    conv_lhs => rw [F.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : monomial m (F.coeff m) = F.coeff m • monomial m (1 : ℝ) := by
      rw [smul_monomial]; simp
    rw [this, map_smul, smul_eq_mul]
  rw [h1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left (he m ?_) (abs_nonneg _)
  by_contra hne
  exact (mem_support_iff.mp hm) (hF.coeff_eq_zero hne)

theorem tendsto_coeffs_of_tests {a b R₁ R₂ E₁ E₂ : ℕ → ℝ} {v H₁ H₂ L₁ L₂ r₁ r₂ s₁ n s₂ t₂ : ℝ}
    (hv : v ≠ 0) (hn : n ≠ 0) (hs₂ : s₂ ≠ 0) (ht₂ : t₂ = 0)
    (hR₁ : Tendsto R₁ atTop (𝓝 r₁)) (hR₂ : Tendsto R₂ atTop (𝓝 r₂))
    (hE₁ : Tendsto E₁ atTop (𝓝 0)) (hE₂ : Tendsto E₂ atTop (𝓝 0))
    (h₁ : ∀ᶠ B in atTop, L₁ = v * (H₁ - a B * s₁ - b B * n + R₁ B) + E₁ B)
    (h₂ : ∀ᶠ B in atTop, L₂ = v * (H₂ - a B * s₂ - b B * t₂ + R₂ B) + E₂ B) :
    ∃ A b₀ : ℝ, Tendsto a atTop (𝓝 A) ∧ Tendsto b atTop (𝓝 b₀) := by
  subst ht₂
  have ha : Tendsto a atTop (𝓝 ((H₂ + r₂ + 0 / v - L₂ / v) / s₂)) := by
    have h := (((hR₂.const_add H₂).add (hE₂.div_const v)).sub_const (L₂ / v)).div_const s₂
    refine h.congr' ?_
    filter_upwards [h₂] with B hB
    rw [hB]
    field_simp
    ring
  have hb : Tendsto b atTop (𝓝 ((H₁ - (H₂ + r₂ + 0 / v - L₂ / v) / s₂ * s₁ + r₁ + 0 / v - L₁ / v) / n)) := by
    have h := (((((ha.mul_const s₁).const_sub H₁).add hR₁).add (hE₁.div_const v)).sub_const (L₁ / v)).div_const n
    refine h.congr' ?_
    filter_upwards [h₁] with B hB
    rw [hB]
    field_simp
    ring
  exact ⟨_, _, ha, hb⟩

theorem eq_of_tendsto_coeffs {a b R E : ℕ → ℝ} {v H L s t A b₀ r : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 b₀)) (hR : Tendsto R atTop (𝓝 r))
    (hE : Tendsto E atTop (𝓝 0))
    (h : ∀ᶠ B in atTop, L = v * (H - a B * s - b B * t + R B) + E B) :
    L = v * (H - A * s - b₀ * t + r) := by
  have h1 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop
      (𝓝 (v * (H - A * s - b₀ * t + r) + 0)) :=
    ((((((ha.mul_const s).const_sub H).sub (hb.mul_const t)).add hR).const_mul v)).add hE
  have h2 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop (𝓝 L) :=
    tendsto_const_nhds.congr' (h.mono fun B hB => hB)
  simpa using tendsto_nhds_unique h2 h1

theorem tendsto_const_mul_log_div (c C : ℝ) :
    Tendsto (fun B : ℕ => c * (C * Real.log B / B)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h2 := (h.const_mul C).const_mul c
  simp only [mul_zero] at h2
  refine h2.congr fun B => ?_
  simp [mul_div_assoc]

section

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem pk_mul_isHomogeneous (hN : 2 ≤ N) (τ : Ψ) {k : ℕ} (hk : k ≤ N) {Q : RP Ψ N}
    (hQ : Q.IsHomogeneous (dimFl Ψ N + 1 - k)) : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  have h1 : N - 1 ≤ N * (N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm N]
    exact Nat.mul_le_mul_left _ hN
  have h2 : N * (N - 1) / 2 ≤ dimFl Ψ N :=
    Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.mpr ⟨τ⟩)
  have h3 : k + (dimFl Ψ N + 1 - k) = dimFl Ψ N + 1 := by omega
  simpa [h3] using hpk.mul hQ

theorem exists_finite_identity (II : IntersectionSystem) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (hshape : FrobShape frob) (h6 : T.Prop6 II frob) (hBA : T.ThmBA II hh)
    (B₀ : ℕ) (hB₀ : 2 ≤ B₀) :
    ∃ a b : ℕ → ℝ, ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        T.PPt II B₀ (pk τ k * Q) = T.volT * (hh (pk τ k * Q) - a B * ∑ σ, Sh T.j σ (pk τ k * Q) -
          b B * ∑ σ, Tot σ (pk τ k * Q) +
          ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), restTerm T.j p (frob p τ) k Q) + E B := by
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.power_sum_delta_decomposition Ψ N T.j frob T.j_lt.le (by omega) hshape
  obtain ⟨-, hSh, hTot, -⟩ := GlobalTheory.T.flag_degree_linear_functionals Ψ N
  choose ΦS hΦS using hSh
  choose ΦT hΦT using hTot
  obtain ⟨C, B₁, hC⟩ := hBA
  choose! α β hαβ using hC
  let PL : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B => ∑ c, ((T.M B c).PP II).comp (rename some).toLinearMap
  have hPL : ∀ B F, PL B F = T.PPt II B F := by
    intro B F
    simp [PL, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  let G : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B =>
    PL B - T.volT • (hh - (α B - β B) • (∑ σ, ΦS T.j σ) - β B • (∑ σ, ΦT σ))
  have hG : ∀ B F, G B F = T.PPt II B F - T.volT * (hh F - (α B - β B) * ∑ σ, Sh T.j σ F -
      β B * ∑ σ, Tot σ F) := by
    intro B F
    simp [G, hPL, LinearMap.sum_apply, hΦS, hΦT]
  let S : ℕ → Finset ℕ := fun B => (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B => α B - β B + ∑ p ∈ S B, Real.log p / ((p : ℝ) - 1), fun B => β B - ∑ p ∈ S B, κ p,
    fun τ k hk1 hkN Q hQ => ?_⟩
  have hF := pk_mul_isHomogeneous hN τ hkN hQ
  refine ⟨fun B => G B (pk τ k * Q), ?_, ?_⟩
  · refine squeeze_zero_norm' ?_ (tendsto_const_mul_log_div (∑ m ∈ (pk τ k * Q : RP Ψ N).support,
      |(pk τ k * Q : RP Ψ N).coeff m|) C)
    filter_upwards [eventually_ge_atTop B₁] with B hB
    rw [Real.norm_eq_abs]
    refine abs_apply_le_of_monomial_bound (G B) _ hF fun m hm => ?_
    rw [hG]
    exact hαβ B hB m hm
  · filter_upwards [eventually_ge_atTop B₀] with B hB
    have hsum : T.PPt II B₀ (pk τ k * Q) = T.PPt II B (pk τ k * Q) +
        T.volT * ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q := by
      simp only [RootTower.PPt, RootTower.volT, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => h6 B₀ B hB₀ hB c τ k hk1 hkN Q hQ
    have hdelta : ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q =
        -(∑ p ∈ S B, Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh T.j σ (pk τ k * Q) +
          (∑ p ∈ S B, κ p) * ∑ σ, Tot σ (pk τ k * Q) + ∑ p ∈ S B, restTerm T.j p (frob p τ) k Q := by
      rw [Finset.sum_congr rfl fun p hp => hκ p τ k Q
        (Finset.mem_filter.mp hp).2.1.two_le hk1]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        Finset.sum_neg_distrib]
    show T.PPt II B₀ (pk τ k * Q) = _
    rw [hG, hsum, hdelta]
    ring

end

end GlobalTheory.CompanionTheory.Ar.Top

theorem GlobalTheory.CompanionTheory.Ar.Top.exists_identAt : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), T.Proportional → FrobShape frob →
    T.Prop6 II frob → T.ThmBA II hh → ∀ B₀ : ℕ, 2 ≤ B₀ → ∃ A₀ b₀ : ℝ, T.IdentAt II hh frob B₀ A₀ b₀ := by
  intro II Ψ _ _ N T hh frob hprop hshape h6 hBA B₀ hB₀
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨a, b, hid⟩ := exists_finite_identity II T hh frob hshape h6 hBA B₀ hB₀
  have hrest : ∀ (τ : Ψ) (k : ℕ) (Q : RP Ψ N), _ := fun τ k Q =>
    (GlobalTheory.T.remainder_term_summable Ψ N T.j T.bad frob τ k Q).2 B₀
  by_cases hΨ : Nonempty Ψ
  · obtain ⟨τ₀⟩ := hΨ
    obtain ⟨⟨Q₁, hQ₁, hd₁⟩, Q₂, hQ₂, hd₂⟩ := GlobalTheory.T.exists_flag_degree_one_polys Ψ N T.j τ₀ T.j_pos T.j_lt
    have hQ₁' : Q₁.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ₁
    have hQ₂' : Q₂.IsHomogeneous (dimFl Ψ N + 1 - 2) := by
      have : dimFl Ψ N + 1 - 2 = dimFl Ψ N - 1 := by omega
      rwa [this]
    obtain ⟨E₁, hE₁, h₁⟩ := hid τ₀ 1 le_rfl (by omega) Q₁ hQ₁'
    obtain ⟨E₂, hE₂, h₂⟩ := hid τ₀ 2 (by omega) hN Q₂ hQ₂'
    have hn : ∑ σ, Tot σ (pk τ₀ 1 * Q₁) ≠ 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 1 Q₁ le_rfl).2
      simp only [h5, hd₁]
      simp
      omega
    have hs₂ : ∑ σ, Sh T.j σ (pk τ₀ 2 * Q₂) ≠ 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 2 Q₂ (by omega)).1
      simp only [h5]
      simp [hd₂]
    have ht₂ : ∑ σ, Tot σ (pk τ₀ 2 * Q₂) = 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 2 Q₂ (by omega)).2
      simp [h5]
    obtain ⟨A₀, b₀, ha, hb⟩ := tendsto_coeffs_of_tests hvol.ne' hn hs₂ ht₂
      (hrest τ₀ 1 Q₁) (hrest τ₀ 2 Q₂) hE₁ hE₂ h₁ h₂
    refine ⟨A₀, b₀, fun τ k hk1 hkN Q hQ => ?_⟩
    obtain ⟨E, hE, h⟩ := hid τ k hk1 hkN Q hQ
    exact eq_of_tendsto_coeffs ha hb (hrest τ k Q) hE h
  · exact ⟨0, 0, fun τ => (hΨ ⟨τ⟩).elim⟩
end
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.local_pair_power_sum_value : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] [DecidableEq σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (r k : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) = ∑ μ ∈ G.support, G.coeff μ * (((T.comp e).ck P k (classList (Sum.elim T.x T.x') μ) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul | exact GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.vertical_pair_power_sum_vanish : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert P ϖ → ∀ (r : ℕ) (e : Fin r → σ), PowerSumsVanish P d (T.x' ∘ e) → ∀ k m : ℕ, 1 ≤ k → k + m = d → ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, (∀ i, (Gs i).IsHomogeneous m) → T.val P (fun i => (∑ a, X (Sum.inr (e a)) ^ k) * Gs i) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_component_factor_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y), Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | exact GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open | (intros; apply GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open <;> assumption)
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Root

theorem word_expand (hI : Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) {σ : Type} [Fintype σ] [DecidableEq σ]
    {d : ℕ} (hd : IsArithVar M.P d) (ℓ : σ → HermLine M.ι) (n : Fin d → σ → ℤ) (L : Fin d → HermLine M.ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hℓ : ∀ a, IsSmoothHerm (ℓ a))
    (ha : ∀ j, (L j).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).a)
    (hh : ∀ j, ∀ z ∈ mcPts M.P, (L j).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).h z) :
    II _ _ M.P d L = ∑ u : Fin d → σ, (∏ k, (n k (u k) : ℝ)) * II _ _ M.P d (fun k => ℓ (u k)) := by
  have hc : ∀ j, IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) := fun j =>
    (GlobalTheory.T.hermitian_combination_smooth_conj _ M.ι σ ℓ (n j)).1 hℓ
  rw [hI.metricLocal _ M.ι (II _ M.ι) (hII.1 _ M.ι) M.P d L (fun j => GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) hd hL hc ha hh]
  exact GlobalTheory.T.arith_intersection_multilinear_all II hII _ M.ι M.P d σ ℓ n hd hℓ

theorem cmp_root : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  intro hI II hII Ψ _ _ N M₁ M₂ σ _ _ ℓ₁ ℓ₂ n s e₁ e₂ he₁ hδ hev hnull w
  have hδ₁ : (M₁.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₁.δ_pos.ne'
  have hδ₂ : (M₂.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₂.δ_pos.ne'
  have he₁' : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he₁
  have hδR : (e₁ : ℝ) * M₁.δ = e₂ * M₂.δ := by exact_mod_cast hδ
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ))
    (fun u _ => (hnull u).const_mul (∏ k, (n (w k) (u k) : ℝ)))
  have hdiv := hsum.const_mul (((e₁ : ℝ) * M₁.δ)⁻¹)
  simp only [mul_zero, Finset.sum_const_zero] at hdiv
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [hev] with t ht
  obtain ⟨hsm, h1, h2⟩ := ht
  have E₁ := word_expand hI II hII M₁ M₁.arith (ℓ₁ t) (fun k => n (w k)) (fun j => M₁.x t (s (w j)))
    (fun j => M₁.x_smooth t _) (fun a => (hsm a).1) (fun j => (h1 (w j)).1) (fun j => (h1 (w j)).2)
  have E₂ := word_expand hI II hII M₂ M₂.arith (ℓ₂ t) (fun k => n (w k)) (fun j => M₂.x t (w j))
    (fun j => M₂.x_smooth t _) (fun a => (hsm a).2) (fun j => (h2 (w j)).1) (fun j => (h2 (w j)).2)
  rw [E₁, E₂]
  have hsplit : ∀ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
      (∏ k, (n (w k) (u k) : ℝ)) * ((e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j)) -
        (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) =
      (e₁ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) -
        (e₂ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) := fun u => by ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) = A
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) = B
  have hB : (e₂ : ℝ) * B / ((e₁ : ℝ) * M₁.δ) = B / M₂.δ := by
    rw [hδR]
    have he₂ : (e₂ : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hδR
      exact mul_ne_zero he₁' hδ₁ hδR
    field_simp
  rw [← hB]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Cmp.Root
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.root_model_arith_intersection_formula : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun | exact GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | exact GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem <;> assumption)
end
