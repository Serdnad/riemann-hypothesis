module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle042
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2Explicit
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil

theorem exists_bilin_ext {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] [Module ℚ V]
    (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ v : V, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ) := by
  classical
  choose k x hk hx using hs
  have hkq : ∀ u, (k u : ℚ) ≠ 0 := fun u => Nat.cast_ne_zero.mpr (hk u)
  let B0 : V → V → ℚ := fun u v => ((form (x u) (x v) : ℤ) : ℚ) / ((k u : ℚ) * (k v : ℚ))
  have key : ∀ (u v : V) (m n : ℕ) (p q : Λ), m ≠ 0 → n ≠ 0 → e p = m • u → e q = n • v →
      B0 u v = ((form p q : ℤ) : ℚ) / ((m : ℚ) * (n : ℚ)) := by
    intro u v m n p q hm hn hp hq
    have h1 : (k u) • p = m • x u := he (by
      rw [map_nsmul, map_nsmul, hp, hx, smul_comm])
    have h2 : (k v) • q = n • x v := he (by
      rw [map_nsmul, map_nsmul, hq, hx, smul_comm])
    have h3 : form ((k u) • p) ((k v) • q) = form (m • x u) (n • x v) := by rw [h1, h2]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
    have h4 : (k v : ℚ) * ((k u : ℚ) * ((form p q : ℤ) : ℚ))
        = (n : ℚ) * ((m : ℚ) * ((form (x u) (x v) : ℤ) : ℚ)) := by
      exact_mod_cast h3
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hu := hkq u
    have hv := hkq v
    simp only [B0]
    rw [div_eq_div_iff (mul_ne_zero hu hv) (mul_ne_zero hm' hn')]
    linear_combination (-1 : ℚ) * h4
  have hsm : ∀ (c : ℚ) (u : V), e (c.num • x u) = (c.den * k u) • (c • u) := by
    intro c u
    rw [map_zsmul, hx, ← Nat.cast_smul_eq_nsmul ℚ (k u) u, ← Nat.cast_smul_eq_nsmul ℚ (c.den * k u),
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    have := Rat.mul_den_eq_num c
    push_cast
    rw [← this]; ring
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ B0
    (by
      intro u u' v
      have := key (u + u') v (k u * k u') (k v) ((k u') • x u + (k u) • x u') (x v)
        (mul_ne_zero (hk u) (hk u')) (hk v)
        (by rw [map_add (f := _), map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k u') (k u)])
        (hx v)
      rw [this]
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, B0, nsmul_eq_mul]
      have hu := hkq u
      have hu' := hkq u'
      have hv := hkq v
      push_cast
      field_simp)
    (by
      intro c u v
      have := key (c • u) v (c.den * k u) (k v) (c.num • x u) (x v)
        (mul_ne_zero c.den_nz (hk u)) (hk v) (hsm c u) (hx v)
      rw [this]
      simp only [map_zsmul, LinearMap.smul_apply, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
    (by
      intro u v v'
      have := key u (v + v') (k u) (k v * k v') (x u) ((k v') • x v + (k v) • x v')
        (hk u) (mul_ne_zero (hk v) (hk v')) (hx u)
        (by rw [map_add (f := _), map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k v') (k v)])
      rw [this]
      simp only [map_add (f := _), map_nsmul, B0, nsmul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hv' := hkq v'
      push_cast
      field_simp)
    (by
      intro c u v
      have := key u (c • v) (k u) (c.den * k v) (x u) (c.num • x v)
        (hk u) (mul_ne_zero c.den_nz (hk v)) (hx u) (hsm c v)
      rw [this]
      simp only [map_zsmul, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
  refine ⟨B, fun p q => ?_⟩
  have := key (e p) (e q) 1 1 p q one_ne_zero one_ne_zero (one_smul _ _).symm (one_smul _ _).symm
  simpa [B, LinearMap.mk₂_apply] using this

theorem exists_rat_bilin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x, form x x = 0) → Function.Bijective form → (∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)) → ∃ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) ∧ (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) ∧ (∀ u v, B u v = - B v u) ∧ ∀ u, (∀ v, B v u = 0) → u = 0 := by
  intro E _ _ _ Λ _ _ _ _ N e he hlin hs form alt hbij adj
  obtain ⟨B, hB⟩ := exists_bilin_ext e he hs form
  have hskew : ∀ x y, form x y = - form y x := by
    intro x y
    have := alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, alt] at this
    linarith
  have halt : ∀ u, B u u = 0 := by
    intro u
    obtain ⟨k, x, hk, hx⟩ := hs u
    have h := hB x x
    rw [alt, hx, ← Nat.cast_smul_eq_nsmul ℚ k u] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    simpa [hk'] using h
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro a u v
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝓞 E, (a₀ : E) = n • a := ⟨⟨n • a, hint⟩, rfl⟩
    obtain ⟨a₀', ha₀'⟩ : ∃ a₀' : 𝓞 E, (a₀' : E) = IsCMField.complexConj E (a₀ : E) :=
      ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a₀, rfl⟩
    obtain ⟨k, x, hk, hx⟩ := hs u
    obtain ⟨l, y, hl, hy⟩ := hs v
    have h2 : B (e (a₀ • x)) (e y) = B (e x) (e (a₀' • y)) := by
      rw [hB, hB, adj a₀ a₀' ha₀' x y]
    rw [hlin, hlin, hx, hy] at h2
    have h3 : (a₀ : E) • (k • u) = ((n : ℚ) * (k : ℚ)) • (a • u) := by
      ext i
      simp [ha₀, Rat.smul_def]
      ring
    have h4 : (a₀' : E) • (l • v) = ((n : ℚ) * (l : ℚ)) • (IsCMField.complexConj E a • v) := by
      ext i
      simp [ha₀', ha₀, Rat.smul_def]
      ring
    have h5 : k • u = (k : ℚ) • u := (Nat.cast_smul_eq_nsmul ℚ k u).symm
    have h6 : l • v = (l : ℚ) • v := (Nat.cast_smul_eq_nsmul ℚ l v).symm
    rw [h3, h4, h5, h6] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hn' hk') hl') (by linear_combination h2)
  · intro u v
    exact (LinearMap.IsAlt.neg (B := B) halt v u).symm
  · intro u hu
    obtain ⟨k, y, hk, hy⟩ := hs u
    have hf : ∀ x, form x y = 0 := by
      intro x
      have h : B (e x) (e y) = 0 := by rw [hy, map_nsmul, hu (e x), smul_zero]
      rw [hB] at h
      exact_mod_cast h
    have h0 : form y = 0 := LinearMap.ext fun x => by
      rw [hskew, hf]; simp
    have y0 : y = 0 := hbij.1 (by rw [h0, map_zero])
    rw [y0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hy
    exact (smul_eq_zero.mp hy.symm).resolve_left (Nat.cast_ne_zero.mpr hk)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_phi_eq {A : FinHolAtlas e X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hφ : P.φ = Q.φ) (hP : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨W, hW, hzW, G, hG, hGe⟩ :=
    hQ.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hy.2, Q.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy.1, hzW⟩
  have ho : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (W ∩ Q.U x ∩ Q.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (Q.isOpen_U x)).inter (Q.isOpen_U _))
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy.1, ⟨hzW, hy.2⟩, Q.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have ho2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U ((A.chart j).symm y)) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)
  have h2 : ContDiffAt ℝ 2 (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((hQ.1 _ j).contDiffAt (ho2.mem_nhds ⟨hy.1, Q.mem_U _⟩)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 h2 hRe, levi_re_analytic hGa, mul_zero, add_zero, ← hφ]
  exact hP _ j y ⟨hy.1, P.mem_U _⟩ w

end PullTop

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullbackStatement : PullbackStatement := by
  intro e e' X X' _ _ _ _ _ _ A A' h hh Θ L Θ' s n n' m W m' W' hΘ hΘp hΘ' hΘ'p hL hs hsnc hs0
    hsnc' th ph phT C₅ C t₀ hSW hF hC2
  obtain ⟨hth, hSm, hPshOn, hbd⟩ := hSW
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘ'psh : IsPsh A' Θ' := TailBoundAlt.isPsh_of_isPosPot A' Θ' hΘ'p
  have hΘpb : IsPotential A' (Θ.pullback h hh.1) := isPotentialPullback A A' h hh Θ hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A' Θ' (Θ.pullback h hh.1) hΘ' hΘ'p hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  refine ⟨C', t₁, ⟨isPotentialPullback A A' h hh th hth, ?_, ?_, fun y hy => hbd (h y) hy⟩, ?_, ?_⟩
  · have := smoothOn_pull hh hU hSm
    rwa [Set.preimage_compl] at this
  · have := isPshOn_pull hh hU hth hSm hPshOn
    rwa [Set.preimage_compl] at this
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A'.Smooth (phT t ∘ h) := by
      have := smoothOn_pull hh isOpen_univ a1
      rwa [Set.preimage_univ] at this
    refine ⟨hsm, fun y => a2 (h y), fun y hy => a3 (h y) hy, fun y => a4 (h y), ?_,
      fun y hy hyr => a6 (h y) hy hyr, fun y hy => a7 (h y) hy,
      fun t' h1 h2 y => a8 t' h1 h2 (h y)⟩

    set ε : ℝ := epsT |C| t with hε
    have hq := loglog_quot_nonneg ht (htt.trans ht₁e)
    have hε0 : 0 ≤ ε := by
      rw [hε, epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
    have hε' : epsT C' t = M * ε := by
      rw [hε, epsT, epsT, hC']; ring
    have hεK : 0 ≤ M * ε - K * ε := by nlinarith
    have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
      isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
        (isPotentialRsmul A ε Θ hΘ)
    have hD : IsPotential A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1)) :=
      isPotentialAdd A' _ _ (isPotentialRsmul A' K Θ' hΘ') (isPotentialRsmul A' (-1) _ hΘpb)
    have hS1 := isPotentialPullback A A' h hh _ hP0
    have hS1p := isPsh_pull hh hP0 b5
    have hS2 := isPotentialRsmul A' ε _ hD
    have hS2p := isPshRsmul A' ε _ hε0 hD hKpsh
    have hS3 := isPotentialRsmul A' (M * ε - K * ε) Θ' hΘ'
    have hS3p := isPshRsmul A' (M * ε - K * ε) Θ' hεK hΘ' hΘ'psh
    have hS := isPshAdd A' _ _ (isPotentialAdd A' _ _ hS1 hS2) hS3
      (isPshAdd A' _ _ hS1 hS2 hS1p hS2p) hS3p
    have hT : IsPotential A' (th.pullback h hh.1 + LocPot.ofFun (phT t ∘ h) + Θ'.rsmul (epsT C' t)) :=
      isPotentialAdd A' _ _ (isPotentialAdd A' _ _ (isPotentialPullback A A' h hh th hth)
        (isPotential_ofFun A' _ hsm)) (isPotentialRsmul A' _ Θ' hΘ')
    refine isPsh_of_phi_eq hT ?_ hS
    funext x y
    show th.φ (h x) (h y) + phT t (h y) + ε * Θ.φ (h x) (h y) +
        ε * (K * Θ'.φ x y + -1 * Θ.φ (h x) (h y)) + (M * ε - K * ε) * Θ'.φ x y =
      th.φ (h x) (h y) + phT t (h y) + epsT C' t * Θ'.φ x y
    rw [hε']
    ring
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact regular_family_C2_pullback_of_open A A' h hh s ph phT hU hSm hev hC2

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.regularization_glue_C2_explicit : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (Θ th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ), A.Compatible B → (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsClosed (bdry s) → A.SmoothOn (bdry s)ᶜ ph → ∃ K : ℝ, 0 < K ∧ ∀ (t₀ : ℝ) (δ : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ), 0 < t₀ → Tendsto δ (𝓝[>] 0) (𝓝 0) → (∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧ (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧ (∃ Mb : ℝ, ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb) ∧ (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f t j))) ∧ ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t) → (∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm)) (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t) → ∃ F : ℝ → X → ℝ, (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * δ t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * δ t) ∧ IsRegFamilyC2 A s ph F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 | exact GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.smooth_on_atlas_continuous : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ), A.Smooth f → Continuous f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | exact GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth <;> assumption)
end
