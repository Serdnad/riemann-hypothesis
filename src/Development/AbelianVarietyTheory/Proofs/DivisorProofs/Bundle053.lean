module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

section

open MeasureTheory Filter Topology

namespace GlobalTheory.FiberPointwise

lemma lintegral_indicator_translate {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by
  rw [← lintegral_add_right_eq_self (μ := μ) _ z]
  congr 1
  funext x
  show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x
  have hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S) := by rw [map_add (f := _), hz, add_sub_cancel_right]
  by_cases hxs : P x ∈ S
  · rw [Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs),
      Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]
  · rw [Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')),
      Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]

theorem vanish_at_point : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  intro X _ _ _ _ _ _ μ _ P hPc hPP Φ Ψ hΦ hΨ K hK hΦK y hΦy hyp
  by_contra hne
  set δ : NNReal := ‖Ψ y‖₊ / 2 with hδ
  have hΨpos : 0 < ‖Ψ y‖₊ := nnnorm_pos.mpr hne
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ‖Ψ y‖₊ := NNReal.half_lt_self hΨpos.ne'
  let V : Set X := {x | δ < ‖Ψ x‖₊}
  have hVo : IsOpen V := isOpen_lt continuous_const hΨ.nnnorm
  have hyV : y ∈ V := hδlt
  have hsum : P y + (y - P y) = y := by abel
  have hpre : (fun p : X × X => p.1 + p.2) ⁻¹' V ∈ 𝓝 (P y, y - P y) := by
    apply continuous_add.continuousAt.preimage_mem_nhds
    simp only [hsum]
    exact hVo.mem_nhds hyV
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨s1, hs1, hs1u, hs1c⟩ := local_compact_nhds hu
  obtain ⟨s2, hs2, hs2v, hs2c⟩ := local_compact_nhds hv
  set U1 := interior s1 with hU1
  set O2 := interior s2 with hO2
  have hU1o : IsOpen U1 := isOpen_interior
  have hO2o : IsOpen O2 := isOpen_interior
  have hPyU1 : P y ∈ U1 := mem_interior_iff_mem_nhds.mpr hs1
  have hQyO2 : y - P y ∈ O2 := mem_interior_iff_mem_nhds.mpr hs2
  have hUV : ∀ a ∈ U1, ∀ b ∈ O2, a + b ∈ V := fun a ha b hb =>
    huv (Set.mk_mem_prod (hs1u (interior_subset ha)) (hs2v (interior_subset hb)))
  set PK := P '' K with hPK
  have hPKc : IsCompact PK := hK.image hPc
  have hPKfix : ∀ a ∈ PK, P a = a := by rintro _ ⟨k, -, rfl⟩; exact hPP k
  obtain ⟨t, htPK, hcover⟩ := hPKc.elim_nhds_subcover (fun a => {w | w - (a - P y) ∈ U1}) (by
    intro a _
    apply (hU1o.preimage (continuous_id.sub continuous_const)).mem_nhds
    show a - (a - P y) ∈ U1
    rwa [sub_sub_cancel])
  set N := t.card with hN
  set ε : NNReal := δ / (N + 1) with hεdef
  have hεpos : 0 < ε := div_pos hδpos (by positivity)
  have hε : ε ^ 2 * N < δ ^ 2 := by
    rw [hεdef, ← NNReal.coe_lt_coe]; push_cast
    have hδr : (0:ℝ) < δ := hδpos
    have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
    rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδr 2, mul_nonneg (pow_pos hδr 2).le (sq_nonneg (N:ℝ)), mul_nonneg (pow_pos hδr 2).le hNr]
  have htube : ∀ᶠ b in 𝓝 (y - P y), ∀ a ∈ PK, ‖Φ (a + b)‖₊ < ε := by
    apply hPKc.eventually_forall_of_forall_eventually
    intro a ha
    have h0 : Φ (a + (y - P y)) = 0 := by
      have := hΦy (a - P y) (by rw [map_sub, hPKfix a ha, hPP])
      rwa [show y + (a - P y) = a + (y - P y) by abel] at this
    have hcont : Continuous fun p : X × X => ‖Φ (p.2 + p.1)‖₊ :=
      (hΦ.comp (continuous_snd.add continuous_fst)).nnnorm
    have hmem : {p : X × X | ‖Φ (p.2 + p.1)‖₊ < ε} ∈ 𝓝 (y - P y, a) :=
      (isOpen_lt hcont continuous_const).mem_nhds (by simp [h0, hεpos])
    exact hmem
  obtain ⟨O3, hO3sub, hO3o, hQyO3⟩ := eventually_nhds_iff.mp htube
  let O : Set X := {w | w - P y ∈ O2 ∩ O3}
  have hOo : IsOpen O := (hO2o.inter hO3o).preimage (continuous_id.sub continuous_const)
  have hyO : y ∈ O := ⟨hQyO2, hQyO3⟩
  obtain ⟨h, hhm, hh1, hinv, hsupp, ⟨O', hO'o, hyO', hO'⟩, heq⟩ := hyp O hOo hyO
  have hsupp' : ∀ x, h x ≠ 0 → x - P x ∈ O2 ∧ x - P x ∈ O3 := by
    intro x hx
    have := hsupp x hx
    simp only [O, Set.mem_setOf_eq] at this
    rwa [show x + (P y - P x) - P y = x - P x by abel] at this
  have hdec : ∀ x : X, P x + (x - P x) = x := fun x => by abel
  set A : Set X := {x | P x ∈ U1} with hA
  set I := ∫⁻ x, A.indicator h x ∂μ with hI
  have hlow : (δ:ENNReal) ^ 2 * I ≤ ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ := by
    rw [hI, ← lintegral_const_mul' _ _ (by simp)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx0 : h x = 0
      · simp [hx0]
      · have hxV : x ∈ V := by
          have := hUV (P x) hxA (x - P x) (hsupp' x hx0).1
          rwa [hdec] at this
        rw [mul_comm]
        gcongr
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr hxV.le
    · simp [hxA]
  have hup : ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ ≤ (ε:ENNReal) ^ 2 * (N * I) := by
    have hpt : ∀ x, h x * ‖Φ x‖ₑ ^ 2 ≤
        (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
      intro x
      by_cases hx0 : h x = 0
      · simp [hx0]
      by_cases hΦ0 : Φ x = 0
      · simp [hΦ0]
      have hPx : P x ∈ PK := ⟨P x, hΦK x hΦ0, hPP x⟩
      obtain ⟨a, hat, hxa⟩ : ∃ a ∈ t, P x - (a - P y) ∈ U1 := by
        have := hcover hPx
        simp only [Set.mem_iUnion] at this
        obtain ⟨a, ha, h'⟩ := this
        exact ⟨a, ha, h'⟩
      have hsmall : ‖Φ x‖₊ < ε := by
        have := hO3sub _ (hsupp' x hx0).2 (P x) hPx
        rwa [hdec] at this
      calc h x * ‖Φ x‖ₑ ^ 2 ≤ h x * (ε:ENNReal) ^ 2 := by
            gcongr
            rw [enorm_eq_nnnorm]
            exact ENNReal.coe_le_coe.mpr hsmall.le
        _ = (ε:ENNReal) ^ 2 * Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            rw [Set.indicator_of_mem (show x ∈ {x | P x - (a - P y) ∈ U1} from hxa), mul_comm]
        _ ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            gcongr
            exact Finset.single_le_sum (f := fun a => Set.indicator {x | P x - (a - P y) ∈ U1} h x)
              (fun _ _ => bot_le) hat
    calc _ ≤ ∫⁻ x, (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ :=
          lintegral_mono hpt
      _ = (ε:ENNReal) ^ 2 * ∑ a ∈ t, ∫⁻ x, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ := by
          rw [lintegral_const_mul' _ _ (by simp), MeasureTheory.lintegral_finsetSum]
          intro a _
          exact hhm.indicator ((hU1o.preimage (hPc.sub continuous_const)).measurableSet)
      _ = (ε:ENNReal) ^ 2 * (N * I) := by
          congr 1
          rw [Finset.sum_congr rfl (fun a ha => lintegral_indicator_translate μ P h hinv U1 (a - P y)
            (by rw [map_sub, hPKfix a (htPK a ha), hPP])), Finset.sum_const, nsmul_eq_mul]
  have hIpos : I ≠ 0 := by
    let W := O' ∩ {x | Ψ x ≠ 0} ∩ A
    have hWo : IsOpen W := (hO'o.inter (isOpen_ne_fun hΨ continuous_const)).inter (hU1o.preimage hPc)
    have hyW : y ∈ W := ⟨⟨hyO', hne⟩, hPyU1⟩
    have hWpos : 0 < μ W := hWo.measure_pos μ ⟨y, hyW⟩
    have hle : (1/2 : ENNReal) * μ W ≤ I := by
      rw [← lintegral_indicator_const hWo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW.2]
        exact hO' x hxW.1.1 hxW.1.2
      · simp [hxW]
    intro h0
    rw [h0] at hle
    exact (mul_ne_zero (by simp) hWpos.ne') (le_zero_iff.mp hle)
  have hIfin : I ≠ ⊤ := by
    have hC : IsCompact ((fun p : X × X => p.1 + p.2) '' (s1 ×ˢ s2)) :=
      (hs1c.prod hs2c).image continuous_add
    obtain ⟨U, hCU, hUo, hUfin⟩ := hC.exists_open_superset_measure_lt_top μ
    have hle : I ≤ μ U := by
      rw [← lintegral_indicator_one hUo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA]
        by_cases hx0 : h x = 0
        · simp [hx0]
        · have hxU : x ∈ U := hCU ⟨(P x, x - P x),
            ⟨interior_subset hxA, interior_subset (hsupp' x hx0).1⟩, hdec x⟩
          rw [Set.indicator_of_mem hxU]
          simpa using hh1 x
      · simp [hxA]
    exact ne_top_of_le_ne_top hUfin.ne hle
  have hchain : (δ:ENNReal) ^ 2 * I ≤ ((ε:ENNReal) ^ 2 * N) * I := by
    calc _ ≤ _ := hlow
      _ = _ := heq
      _ ≤ _ := hup
      _ = _ := by ring
  have h2 := (ENNReal.mul_le_mul_iff_left hIpos hIfin).mp hchain
  have h3 : ((δ ^ 2 : NNReal) : ENNReal) ≤ ((ε ^ 2 * N : NNReal) : ENNReal) := by
    push_cast; exact h2
  exact absurd (ENNReal.coe_le_coe.mp h3) (not_le.mpr hε)

end GlobalTheory.FiberPointwise
end

section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem dualform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  intro F _ _ κ _ ℓ hℓ lam
  set M := mixedEmbedding.mixedSpace F
  let Φ : (κ → M) →ₗ[ℝ] Module.Dual ℝ (κ → M) :=
    { toFun := fun u =>
        { toFun := fun x => ℓ (∑ k, x k * u k)
          map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intro c x; simp [smul_mul_assoc, ← Finset.smul_sum] }
      map_add' := by
        intro u v; refine LinearMap.ext fun x => ?_
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u; refine LinearMap.ext fun x => ?_
        simp [mul_smul_comm, ← Finset.smul_sum] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    by_contra hne
    obtain ⟨w, hw⟩ := hℓ (u k) hne
    apply hw
    have := LinearMap.congr_fun hu (Pi.single k w)
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [Finset.sum_eq_single k] at this
    · simpa [mul_comm] using this
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hsurj : Function.Surjective Φ := by
    have : Module.finrank ℝ (κ → M) = Module.finrank ℝ (Module.Dual ℝ (κ → M)) :=
      (Subspace.dual_finrank_eq).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨u, hu⟩ := hsurj lam
  exact ⟨u, fun x => by rw [← hu]; rfl⟩

end GlobalTheory
end

section

open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

end
end

section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory

noncomputable def quotCosetProdEquiv (R : Type) [CommRing R] (M : Ideal R) : (R ⧸ M) × M ≃ R where
  toFun p := Quotient.out p.1 + (p.2 : R)
  invFun α := (Ideal.Quotient.mk M α, ⟨α - Quotient.out (Ideal.Quotient.mk M α), by
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm⟩)
  left_inv p := by
    obtain ⟨c, μ⟩ := p
    have hc : Ideal.Quotient.mk M (Quotient.out c + (μ : R)) = c := by
      rw [map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.eq_zero_iff_mem.mpr μ.2, add_zero]
    ext
    · exact hc
    · simp only [hc]; ring
  right_inv α := by simp

theorem tsum_eq_sum_quotient_tsum_ideal (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)]
    (h : R → ℂ) (hs : Summable h) :
    ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  rw [← (quotCosetProdEquiv R M).tsum_eq h]
  have hs' : Summable (h ∘ quotCosetProdEquiv R M) := (quotCosetProdEquiv R M).summable_iff.mpr hs
  rw [show (∑' c : (R ⧸ M) × ↥M, h (quotCosetProdEquiv R M c)) = ∑' p, (h ∘ quotCosetProdEquiv R M) p from rfl,
    hs'.tsum_prod, tsum_fintype]
  rfl

theorem cosets_main : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) :=
  fun R _ M _ h hs => tsum_eq_sum_quotient_tsum_ideal R M h hs

end GlobalTheory
end

section

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Pc3

section
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (L : Submodule ℂ U)
  [FiniteDimensional ℂ L]

theorem sum_inner_mul_inner_proj [L.HasOrthogonalProjection] (a c : U) :
    ∑ j, ⟪a, (stdOrthonormalBasis ℂ L j : U)⟫_ℂ * ⟪(stdOrthonormalBasis ℂ L j : U), c⟫_ℂ =
      ⟪a, c⟫_ℂ - ⟪a - L.starProjection a, c - L.starProjection c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ L
  have h1 : ∀ j, ⟪a, (e j : U)⟫_ℂ = ⟪(⟨L.starProjection a, L.starProjection_apply_mem a⟩ : L), e j⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right a (e j : U)
    rw [this, L.starProjection_eq_self_iff.2 (e j).2]
  have h2 : ∀ j, ⟪(e j : U), c⟫_ℂ = ⟪e j, (⟨L.starProjection c, L.starProjection_apply_mem c⟩ : L)⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right (e j : U) c
    rw [← this, L.starProjection_eq_self_iff.2 (e j).2]
  simp_rw [h1, h2]
  rw [e.sum_inner_mul_inner, Submodule.coe_inner]
  simp only
  have ha := L.sub_starProjection_mem_orthogonal a
  have hc := L.sub_starProjection_mem_orthogonal c
  have o1 : ⟪L.starProjection a, c - L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem a) hc
  have o2 : ⟪a - L.starProjection a, L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.starProjection_apply_mem c) ha
  have e1 : ⟪a, c⟫_ℂ = ⟪L.starProjection a + (a - L.starProjection a),
      L.starProjection c + (c - L.starProjection c)⟫_ℂ := by simp
  rw [e1, inner_add_left, inner_add_right, inner_add_right, o1, o2]
  ring

end

theorem conjDeriv : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, inner ℂ (x t v) (x t w) = inner ℂ v w) → (∀ t v w, inner ℂ v (y t w) = inner ℂ (x t v) w) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) → (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) → HasDerivAt (fun t => ∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U) (x t (A (y t (stdOrthonormalBasis ℂ L j : U))))) 0 0 := by
  intro U _ _ _ L _ x y A hx0 hxi hy hxd hA hAd
  set e := stdOrthonormalBasis ℂ L
  set E : Fin (Module.finrank ℂ L) → U := fun j => (e j : U)
  set b : Fin (Module.finrank ℂ L) → U := fun k => ContinuousLinearMap.adjoint A (E k)

  have hexp : ∀ u, A u = ∑ k, ⟪E k, A u⟫_ℂ • E k := by
    intro u
    have := e.sum_repr' (⟨A u, hA u⟩ : L)
    have h := congrArg (fun z : L => (z : U)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hterm : ∀ t, (∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) =
      ∑ k, (⟪x t (b k), x t (E k)⟫_ℂ - ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ) := by
    intro t
    have h1 : ∀ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ = ∑ k, ⟪x t (b k), E j⟫_ℂ * ⟪E j, x t (E k)⟫_ℂ := by
      intro j

      rw [hexp (y t (E j)), map_sum, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_inner_mul_inner_proj L _ _
  have hconst : ∀ t k, ⟪x t (b k), x t (E k)⟫_ℂ = ⟪b k, E k⟫_ℂ := fun t k => hxi t _ _
  simp_rw [hconst] at hterm
  have hfun : (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) = fun t =>
      (∑ k, ⟪b k, E k⟫_ℂ) - ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ := by
    funext t; rw [hterm t, Finset.sum_sub_distrib]
  show HasDerivAt (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) 0 0
  rw [hfun]
  have hbL : ∀ k, b k ∈ L := fun k => hAd _
  have hEL : ∀ k, E k ∈ L := fun k => (e k).2
  have hd : ∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v - L.starProjection (x t v)) w 0 ∧
      x 0 v - L.starProjection (x 0 v) = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := hxd v hv
    have hP : HasDerivAt (fun t => L.starProjection (x t v)) (L.starProjection w) 0 :=
      (L.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw
    refine ⟨w - L.starProjection w, hw.sub hP, ?_⟩
    rw [hx0, ContinuousLinearMap.one_apply, L.starProjection_eq_self_iff.2 hv, sub_self]
  have hsum : HasDerivAt (fun t => ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
      x t (E k) - L.starProjection (x t (E k))⟫_ℂ) 0 0 := by
    have : (0 : ℂ) = ∑ _k : Fin (Module.finrank ℂ L), (0 : ℂ) := by simp
    rw [this]
    refine HasDerivAt.fun_sum fun k _ => ?_
    obtain ⟨w1, h1, z1⟩ := hd _ (hbL k)
    obtain ⟨w2, h2, z2⟩ := hd _ (hEL k)
    have := h1.inner ℂ h2
    rw [z1, z2, inner_zero_left, inner_zero_right, add_zero] at this
    exact this
  have := hsum.const_sub (∑ k, ⟪b k, E k⟫_ℂ)
  rwa [neg_zero] at this

end GlobalTheory.Pc3
end
end
