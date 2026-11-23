module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Mathlib.Analysis.CStarAlgebra.Classes
import Aesop.Main
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle100
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdProperty
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise

namespace GlobalTheory.CompanionTheory.HeckeMul

section Generic

variable {G : Type} [Group G]

theorem out_mk_of_right_inv {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hφ x h h.2

theorem finsum_out_translate {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun q : G ⧸ K => φ q.out)]
  refine finsum_congr fun q => ?_
  have h : (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) q = (QuotientGroup.mk (a * q.out) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h, out_mk_of_right_inv K φ hφ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_mem (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' C) :=
    hC.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end Generic

section Hecke

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isHk_right {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (x * k) = e x := by
  simpa using h.2.2.2 1 K.one_mem k hk' x

theorem isHk_left {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (k * x) = e x := by
  simpa using h.2.2.2 k hk' 1 K.one_mem x

theorem support_hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by
  intro g hg
  obtain ⟨q, hq⟩ : ∃ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (Function.mem_support.1 hg) ?_
    unfold hconv
    simp only [h]
    exact finsum_zero
  exact Set.mem_mul.2 ⟨q.out, subset_tsupport _ (left_ne_zero_of_mul hq), q.out⁻¹ * g,
    subset_tsupport _ (right_ne_zero_of_mul hq), mul_inv_cancel_left _ _⟩

theorem hconv_biinv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by
  have hφ : ∀ x, ∀ k ∈ K, (fun y => e₁ y * e₂ (y⁻¹ * g)) (x * k) = (fun y => e₁ y * e₂ (y⁻¹ * g)) x := by
    intro x k hk'
    show e₁ (x * k) * e₂ ((x * k)⁻¹ * g) = e₁ x * e₂ (x⁻¹ * g)
    rw [isHk_right h₁ x hk', mul_inv_rev, mul_assoc, isHk_left h₂ _ (K.inv_mem hk')]
  have ht := finsum_out_translate K (fun y => e₁ y * e₂ (y⁻¹ * g)) hφ k₁⁻¹
  unfold hconv
  rw [← ht]
  refine finsum_congr fun q => ?_
  show e₁ q.out * e₂ (q.out⁻¹ * (k₁ * g * k₂)) = e₁ (k₁⁻¹ * q.out) * e₂ ((k₁⁻¹ * q.out)⁻¹ * g)
  rw [isHk_left h₁ _ (K.inv_mem hk₁), ← mul_assoc, isHk_right h₂ _ hk₂]
  simp [mul_assoc]

theorem isHk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (hconv K e₁ e₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, fun k₁ hk₁ k₂ hk₂ g => hconv_biinv h₁ h₂ hk₁ hk₂ g⟩
  have hc : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul h₁.2.2.1 h₂.2.2.1
  exact HasCompactSupport.of_support_subset_isCompact hc (support_hconv K e₁ e₂)

theorem hk_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by
  unfold hk
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  refine Finset.mem_coe.2 (hA q fun h0 => (Function.mem_support.1 hq) ?_)
  show e q.out • ρ q.out w = 0
  rw [h0, zero_smul]

theorem hk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V}
    (hv : v ∈ fixed ρ K) :
    hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have c1 : IsCompact (tsupport e₁) := h₁.2.2.1
  have c2 : IsCompact (tsupport e₂) := h₂.2.2.1
  have c12 : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul c1 c2
  let A := (finite_out_mem K h₁.1 c1).toFinset
  let A₂ := (finite_out_mem K h₁.1 c2).toFinset
  let B := (finite_out_mem K h₁.1 c12).toFinset
  have memA : ∀ q : GL ι F ⧸ K, q ∈ A ↔ q.out ∈ tsupport e₁ := fun q => by simp [A]
  have memA₂ : ∀ q : GL ι F ⧸ K, q ∈ A₂ ↔ q.out ∈ tsupport e₂ := fun q => by simp [A₂]
  have memB : ∀ q : GL ι F ⧸ K, q ∈ B ↔ q.out ∈ tsupport e₁ * tsupport e₂ := fun q => by simp [B]
  have hc : ∀ g, hconv K e₁ e₂ g = ∑ q ∈ A, e₁ q.out * e₂ (q.out⁻¹ * g) := fun g => by
    unfold hconv
    refine finsum_eq_sum_of_support_subset _ ?_
    intro q hq
    exact Finset.mem_coe.2 ((memA q).2 (subset_tsupport _ (left_ne_zero_of_mul hq)))
  have hL := hk_eq_sum ρ K (hconv K e₁ e₂) v B
    (fun s hs => (memB s).2 (support_hconv K e₁ e₂ hs))
  have hT : ∀ x : GL ι F, ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (x * r.out) v
      = ∑ᶠ s : GL ι F ⧸ K, e₂ (x⁻¹ * s.out) • ρ s.out v := fun x => by
    have hr : ∀ y, ∀ k ∈ K, (fun y => e₂ (x⁻¹ * y) • ρ y v) (y * k) = (fun y => e₂ (x⁻¹ * y) • ρ y v) y := by
      intro y k hk'
      show e₂ (x⁻¹ * (y * k)) • ρ (y * k) v = e₂ (x⁻¹ * y) • ρ y v
      rw [← mul_assoc, isHk_right h₂ _ hk', map_mul, Module.End.mul_apply, hvk k hk']
    have ht := finsum_out_translate K (fun y => e₂ (x⁻¹ * y) • ρ y v) hr x
    simpa only [inv_mul_cancel_left] using ht
  have hI : ∀ q ∈ A, ρ q.out (hk ρ K e₂ v) = ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    intro q hq
    have hq' := (memA q).1 hq

    rw [hk_eq_sum ρ K e₂ v A₂ (fun r hr => (memA₂ r).2 (subset_tsupport _ hr)), map_sum]
    have h1 : ∑ r ∈ A₂, ρ q.out (e₂ r.out • ρ r.out v) = ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (q.out * r.out) v := by
      symm
      rw [finsum_eq_sum_of_support_subset (s := A₂)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
      · intro r hr
        refine Finset.mem_coe.2 ((memA₂ r).2 (subset_tsupport _ fun h0 => (Function.mem_support.1 hr) ?_))
        show e₂ r.out • ρ (q.out * r.out) v = 0
        rw [h0, zero_smul]
    rw [h1, hT]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro s hs
    refine Finset.mem_coe.2 ((memB s).2 (Set.mem_mul.2 ⟨q.out, hq', q.out⁻¹ * s.out,
      subset_tsupport _ fun h0 => (Function.mem_support.1 hs) ?_, mul_inv_cancel_left _ _⟩))
    show e₂ (q.out⁻¹ * s.out) • ρ s.out v = 0
    rw [h0, zero_smul]
  have hR : hk ρ K e₁ (hk ρ K e₂ v)
      = ∑ q ∈ A, e₁ q.out • ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    rw [hk_eq_sum ρ K e₁ _ A (fun q hq => (memA q).2 (subset_tsupport _ hq))]
    exact Finset.sum_congr rfl (fun q hq => by rw [hI q hq])
  rw [hL, hR]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Hecke

end GlobalTheory.CompanionTheory.HeckeMul
end
end

section

open GlobalTheory.SplitFlip

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAdj

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) {φ : G → ℂ} (hφ : HasCompactSupport φ) :
    {q : G ⧸ K | φ q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport φ) :=
    hφ.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport φ hq, QuotientGroup.out_eq' q⟩

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_coset (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by
  have e : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q} = (fun h => q.out⁻¹ * h) ⁻¹' (K : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  rw [e, measure_preimage_mul]

theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hF := finite_out_ne_zero K hKo hφ
  set S : Finset (G ⧸ K) := hF.toFinset with hS
  have hmeas : ∀ q : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) := fun q =>
    ((isOpen_discrete ({q} : Set (G ⧸ K))).preimage QuotientGroup.continuous_mk).measurableSet
  have hout : ∀ g : G, φ ((g : G ⧸ K)).out = φ g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hr g k k.2]
  have hsum : φ = fun g => ∑ q ∈ S, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g := by
    funext g
    have : ∀ q : G ⧸ K, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g =
        if (g : G ⧸ K) = q then φ q.out else 0 := fun q => by
      simp [Set.indicator_apply]
    simp only [this, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · have : φ ((g : G ⧸ K)).out = 0 := by
        by_contra h0
        exact h (hF.mem_toFinset.2 h0)
      rw [← hout g, this]
  have hint : ∀ q ∈ S, Integrable (((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out)) μ := by
    intro q _
    refine (integrable_indicator_iff (hmeas q)).2 (integrableOn_const ?_)
    rw [measure_coset]
    exact hfin
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun q hq => hF.mem_toFinset.2 hq)]
  conv_lhs => rw [hsum]
  rw [MeasureTheory.integral_finsetSum S hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hmeas q)]
  simp only [Measure.real, measure_coset]

theorem adjoint_of_inv (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (e : G → ℂ) (he : HasCompactSupport e)
    (hbi : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (v w : V) (hv : ∀ k ∈ K, ρ k v = v) (hw : ∀ k ∈ K, ρ k w = w) :
    B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w =
      B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) := by
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.real (K : Set G) ≠ 0 :=
    (ENNReal.toReal_pos (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne' hfin).ne'
  set φ₁ : G → ℂ := fun g => e g * B (ρ g v) w with hφ₁
  set φ₂ : G → ℂ := fun g => e g⁻¹ * B v (ρ g w) with hφ₂
  have hinv : ∀ g, φ₂ g = φ₁ g⁻¹ := fun g => by
    have h := hB g (ρ g⁻¹ v) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    simp only [hφ₁, hφ₂, h]
  have he' : HasCompactSupport (fun g : G => e g⁻¹) := he.comp_homeomorph (Homeomorph.inv G)
  have hc₁ : HasCompactSupport φ₁ := he.mul_right
  have hc₂ : HasCompactSupport φ₂ := he'.mul_right
  have hr₁ : ∀ g, ∀ k ∈ K, φ₁ (g * k) = φ₁ g := fun g k hk => by
    have h1 : e (g * k) = e g := by simpa using hbi 1 K.one_mem k hk g
    simp only [hφ₁, h1, map_mul, Module.End.mul_apply, hv k hk]
  have hr₂ : ∀ g, ∀ k ∈ K, φ₂ (g * k) = φ₂ g := fun g k hk => by
    have h1 : e (g * k)⁻¹ = e g⁻¹ := by
      rw [mul_inv_rev]
      simpa using hbi k⁻¹ (K.inv_mem hk) 1 K.one_mem g⁻¹
    simp only [hφ₂, h1, map_mul, Module.End.mul_apply, hw k hk]
  have hs₁ : (Function.support fun q : G ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_out_ne_zero K hKo he).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  have hs₂ : (Function.support fun q : G ⧸ K => starRingEnd ℂ (e q.out⁻¹) • ρ q.out w).Finite :=
    (finite_out_ne_zero K hKo he').subset fun q hq h0 => hq (by simp [show e q.out⁻¹ = 0 from h0])
  have l₁ : B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w = ∑ᶠ q : G ⧸ K, φ₁ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B x w) (by simp)) hs₁
    simpa [hφ₁] using this
  have l₂ : B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) = ∑ᶠ q : G ⧸ K, φ₂ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B v x) (by simp)) hs₂
    simpa [hφ₂] using this
  have hI : ∫ g, φ₂ g ∂μ = ∫ g, φ₁ g ∂μ := by
    simp only [hinv]
    exact integral_inv_eq_self φ₁ μ
  rw [integral_eq_sum μ K hKo hfin hc₁ hr₁, integral_eq_sum μ K hKo hfin hc₂ hr₂] at hI
  rw [l₁, l₂]
  exact (smul_right_injective ℂ hpos hI).symm

end Abstract

section GeneralLinearIntegers

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isInvInvariant [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hne : μ (K : Set (GL ι F)) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hnt : μ (K : Set (GL ι F)) ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure (GL ι F) => m (K : Set (GL ι F))) hc
  open scoped Pointwise in
  have hKi : (K : Set (GL ι F))⁻¹ = K := inv_coe_set
  simp only [Measure.inv_apply, hKi, Measure.coe_nnreal_smul_apply] at h2
  have h3 : ((Measure.haarScalarFactor μ.inv μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  have h4 : Measure.haarScalarFactor μ.inv μ = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GeneralLinearIntegers

theorem hk_adjoint : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by
  intro F _ _ _ _ ι _ _ K e he
  obtain ⟨hKo, hKc, hc, hbi⟩ := he
  refine ⟨⟨hKo, hKc, ?_, ?_⟩, ?_⟩
  · have h1 : HasCompactSupport (fun g : GL ι F => e g⁻¹) := hc.comp_homeomorph (Homeomorph.inv _)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro k₁ h₁ k₂ h₂ g
    show starRingEnd ℂ (e (k₁ * g * k₂)⁻¹) = starRingEnd ℂ (e g⁻¹)
    rw [show (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ by group, hbi _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
  · intro V _ _ ρ B hB v hv w hw
    borelize F
    haveI := isInvInvariant (Measure.haar : Measure (GL ι F)) K hKo hKc
    exact adjoint_of_inv Measure.haar K hKo hKc e hc hbi ρ B hB v w
      (fun k hk => by simpa using hv ⟨k, hk⟩) (fun k hk => by simpa using hw ⟨k, hk⟩)

end GlobalTheory.CompanionTheory.HeckeAdj
end
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfDer | exact GlobalTheory.CompanionTheory.RgHeFrame.pfDer | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfDer <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
end

section


theorem _root_.GlobalTheory.T.lattice_third_property : PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement → PositivityTheory.Rg.Tf.Loc.L1 → PositivityTheory.Rg.Tf.Loc.L3 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | exact GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset | (intros; apply GlobalTheory.CompanionTheory.TfLoc.Descent.unramified_descent_coset <;> assumption)
end
