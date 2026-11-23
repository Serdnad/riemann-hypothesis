module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  haveI := hν
  have hcK : IsCompact (Set.range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbd⟩ := hmaj _ hcK
  obtain ⟨B, hB⟩ := (isCompact_univ (X := KR n)).exists_bound_of_continuousOn hκ.continuousOn
  let F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ := fun q' k =>
    κ k * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) q'
  have hcont : ∀ q', Continuous (F q') := by
    intro q'
    have h := Far.cont_hz hD hL hG z (yy i) (GlobalTheory.Eis.term Pp Γ id g q')
    refine hκ.mul ?_
    simpa [GlobalTheory.Eis.term, mul_assoc] using h
  have hbound : ∀ q' k, ‖F q' k‖ ≤ B * u q' := by
    intro q' k
    rw [norm_mul]
    exact mul_le_mul (hB k trivial) (hbd _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_trans (norm_nonneg _) (hB k trivial))
  have hint : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B * u q')) (hcont q').aestronglyMeasurable
      (ae_of_all _ (hbound q'))
  have hsumm : Summable fun q' => ∫ k, ‖F q' k‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun q' => integral_nonneg fun _ => norm_nonneg _)
      (fun q' => integral_mono (hint q').norm (integrable_const (B * u q')) (hbound q'))
      ?_
    simp only [integral_const, smul_eq_mul]
    exact (hu.mul_left B).mul_left _
  have hq : ∀ q', ∫ k, F q' k ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q' := by
    intro q'
    have h := Far.pointId hD hL hG hMid z i (GlobalTheory.Eis.term Pp Γ id g q')
    simpa [F, GlobalTheory.Eis.term, mul_assoc] using h
  have hzero : ∀ q', u q' = 0 → F q' = fun _ => 0 := by
    intro q' h0
    funext k
    have h1 := hbound q' k
    rw [h0, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let S : Set (GlobalTheory.Eis.Cosets Pp Γ) := Function.support u
  haveI : Countable S := hu.countable_support.to_subtype
  have hout : ∀ q', q' ∉ S → u q' = 0 := fun q' h => Function.notMem_support.mp h
  have e1 : ∀ k, ∑' q', F q' k = ∑' q' : S, F q' k := by
    intro k
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show F q' k = 0
    rw [hzero q' (hout q' h)]
  have e2 : ∑' q', ∫ k, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν := by
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show ∫ k, F q' k ∂ν = 0
    rw [hzero q' (hout q' h)]
    simp
  have hL1 : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∫ k, ∑' q' : S, F q' k ∂ν := by
    congr 1
    funext k
    rw [← e1 k]
    simp only [F, GlobalTheory.Eis.cosetSum]
    rw [tsum_mul_left]
  have hswap : ∫ k, ∑' q' : S, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν :=
    (integral_tsum_of_summable_integral_norm (F := fun (q' : S) k => F q' k)
      (fun q' => hint q') (hsumm.subtype (fun x => x ∈ S))).symm
  rw [hL1, hswap, ← e2]
  simp_rw [hq]
  rw [Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  rfl

end PositivityTheory.Rg.Sw.AbsSt.Far

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRight : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRight := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  obtain ⟨σ, h1, h2, hmaj⟩ := Far.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact Far.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_theta [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (I1 : G → ℂ) (hIc : Continuous I1)
    (hTS : ∀ (g : G) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I1 (g * ι ((k : GR n) * y)) ∂μ =
      I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * y) ∂μ) (g : G) :
    Top μ ι p q e a b nb ψ I1 g = cz 0 * I1 g := by
  have hswap : ∀ Φ : GR n → ℂ, Continuous Φ →
      ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ =
      ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * Φ ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    intro Φ hΦ
    have hcont : Continuous (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine Continuous.mul ?_ (Continuous.mul ?_ (hψc.comp continuous_snd))
      · exact ((continuous_weight_factor hD p q e).comp (continuous_subtype_val.comp continuous_fst)).inv₀
          (fun z => spherical_section_ne_zero hD p q e _)
      · exact hΦ.comp ((((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
          (hnbc.comp continuous_snd)).mul continuous_const)
    have hsupp : HasCompactSupport (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine HasCompactSupport.intro' (K := univ ×ˢ tsupport ψ) (isCompact_univ.prod hψs)
        (isClosed_univ.prod (isClosed_tsupport ψ)) ?_
      intro z hz
      have hz2 : z.2 ∉ tsupport ψ := fun h => hz ⟨mem_univ _, h⟩
      simp [image_eq_zero_of_notMem_tsupport hz2]
    have hint := hcont.integrable_of_hasCompactSupport (μ := μ.prod volume) hsupp
    calc _ = ∫ k : KR n, (∫ x, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) ∂μ := by
          congr 1
          funext k
          exact (integral_const_mul _ _).symm
      _ = ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ) :=
          integral_integral_swap
            (f := fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
              (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) hint
      _ = _ := by
          congr 1
          funext x
          rw [← integral_mul_const]
          congr 1
          funext k
          simp only [mul_assoc]
  have h1 := hswap (fun y => I1 (g * ι y)) (hIc.comp (continuous_const.mul hιc))
  have h2 := hswap (F0 p q e) (continuous_weight_factor hD p q e)
  have hc := hceig 0 1
  simp only [Complex.cpow_zero, one_mul, mul_one, weight_factor_one] at hc
  unfold Top
  rw [h1]
  simp_rw [hTS g]
  have hpull : ∫ x, (I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x =
      I1 g * ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull, ← h2, hc, mul_comm]

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  have hCc : IsCompact (range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbu⟩ := hmaj _ hCc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hκ.continuousOn
  set B' := max B 0 with hB'
  set F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ :=
    fun q' k => κ k * hz Ht sec s₀ z 1 (((q'.out : Γ) : G) * (g * ι ((k : GR n) * yy i))) with hFdef
  have hFb : ∀ q' k, ‖F q' k‖ ≤ B' * u q' := by
    intro q' k
    simp only [hFdef, norm_mul]
    exact mul_le_mul ((hB k (mem_univ _)).trans (le_max_left _ _)) (hbu _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_max_right _ _)
  have hFc : ∀ q', Continuous (F q') := by
    intro q'
    have := cont_hz hD hL hG z (yy i) (((q'.out : Γ) : G) * g)
    simp only [hFdef]
    refine hκ.mul ?_
    simpa only [mul_assoc] using this
  have hFi : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B' * u q')) (hFc q').aestronglyMeasurable (ae_of_all _ (hFb q'))
  have hFn : ∀ q', ∫ k, ‖F q' k‖ ∂ν ≤ B' * u q' * ν.real univ := by
    intro q'
    calc ∫ k, ‖F q' k‖ ∂ν ≤ ∫ _k, B' * u q' ∂ν := integral_mono (hFi q').norm (integrable_const _) (hFb q')
      _ = B' * u q' * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hF0 : ∀ q', q' ∉ Function.support u → ∀ k, F q' k = 0 := by
    intro q' hq k
    have h0 : u q' = 0 := Function.notMem_support.mp hq
    have := hFb q' k
    rw [h0, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL1 : ∀ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) =
      ∑' s : Function.support u, F s k := by
    intro k
    rw [tsum_subtype_eq_of_support_subset (f := fun q' => F q' k) ?_]
    · simp only [hFdef, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
      rw [tsum_mul_left]
    · intro q' hq
      by_contra h
      exact hq (hF0 q' h k)
  have hsumn : Summable fun s : Function.support u => ∫ k, ‖F s k‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hFn s)
      (((hu.subtype _).mul_left B').mul_right (ν.real univ))
  have hint : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑' s : Function.support u, ∫ k, F s k ∂ν := by
    simp_rw [hL1]
    exact (integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) k => F s k)
      (fun s => hFi s) hsumn).symm
  have hint2 : ∑' s : Function.support u, ∫ k, F s k ∂ν = ∑' q', ∫ k, F q' k ∂ν := by
    refine tsum_subtype_eq_of_support_subset (f := fun q' => ∫ k, F q' k ∂ν) ?_
    intro q' hq
    by_contra h
    exact hq (by simp only [hF0 q' h, integral_zero])
  have hpt : ∀ q', ∫ k, F q' k ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) (((q'.out : Γ) : G) * g) := by
    intro q'
    have := pointId hD hL hG hMid z i (((q'.out : Γ) : G) * g)
    simpa only [hFdef, mul_assoc] using this
  rw [hint, hint2, tsum_congr hpt]
  have hS : HasSum (fun b => ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g b)
      (∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) :=
    hasSum_sum fun j _ => ((hsum j).hasSum).mul_left (M (z - s₀) i j)
  exact hS.tsum_eq

end PositivityTheory.Rg.Sw.AbsSt.FarK

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRightC : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRightC := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I hG
  obtain ⟨σ, h1, h2, hmaj⟩ := FarK.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact FarK.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt
end
end
