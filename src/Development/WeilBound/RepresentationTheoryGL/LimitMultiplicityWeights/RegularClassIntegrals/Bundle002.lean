module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PSmoothSum

lemma le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

end MainStatements.WeightKernel.PSmoothSum

namespace MainStatements.WeightKernel

open PSmoothSum in
theorem smoothSum : SmoothSum := by
  intro X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : X)
  let φ : ContDiffBump (0 : X) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : X × P → ℂ := fun q => ((φ q.1 : ℝ) : ℂ) * W q
  have hG : ContDiff ℝ ∞ G :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW
  have hsupp : tsupport G ⊆ tsupport φ ×ˢ univ := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)
    intro q hq
    refine ⟨subset_tsupport _ ?_, mem_univ _⟩
    intro h0
    apply hq
    simp [G, h0]
  have hcpt : IsCompact (tsupport φ ×ˢ K) := φ.hasCompactSupport.isCompact.prod hK
  have hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn
    refine ⟨max M 0, fun x y hy => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)
    · have : (x, y) ∉ tsupport G := fun h => hx (hsupp h).1
      have h0 : iteratedFDeriv ℝ k G (x, y) = 0 := by
        by_contra hne
        exact this (support_iteratedFDeriv_subset k hne)
      simp [h0]
  choose M hM using hbound
  let L : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  have hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K →
      ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k := by
    intro y k x hy
    have heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L := by
      funext z
      simp [L]
    have hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y))) := hG.comp (contDiff_id.add contDiff_const)
    rw [heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hxy : L x + (0, y) = (x, y) := by simp [L]
    rw [hxy]
    exact mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩
  · refine contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_
    · intro i
      exact contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))
    · intro k _
      exact ha.mul_right _
    · intro k i x _
      have hci : ContDiffAt ℝ k (fun z => G (z, p i)) x :=
        ((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt
      have := iteratedFDeriv_const_smul_apply' (a := a i) hci
      simp only [smul_eq_mul] at this
      rw [this]
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))
  · intro x hx
    have hx' : dist x 0 ≤ R := hR hx
    have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      show dist x 0 ≤ max R 0 + 1
      linarith [le_max_left R 0])
    simp [G, h1]

end MainStatements.WeightKernel
end
end

section

open MeasureTheory Set Filter Topology

noncomputable section

namespace MainStatements.WeightKernel.PClosedGraph

variable {Ω I : Type} [MeasurableSpace Ω] {m : Measure Ω} {u : I → Ω → ℂ}

lemma summable_norm_lp (a : lp (fun _ : I => ℂ) 1) : Summable (fun i => ‖a i‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)
  simpa using h

lemma norm_lp_eq (a : lp (fun _ : I => ℂ) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

lemma summable_mul {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : I → ℂ) (ha : Summable fun i => ‖a i‖) :
    Summable (fun i => a i * u i x) := by
  refine Summable.of_norm_bounded (ha.mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

lemma norm_tsum_mul_le {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : lp (fun _ : I => ℂ) 1) :
    ‖∑' i, a i * u i x‖ ≤ ‖a‖ * M := by
  have ha := summable_norm_lp a
  have hs := summable_mul hM a ha
  calc ‖∑' i, a i * u i x‖ ≤ ∑' i, ‖a i * u i x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, ‖a i‖ * M := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
    _ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]

lemma tsum_single [DecidableEq I] (i : I) (x : Ω) : ∑' j, (lp.single 1 i (1 : ℂ) : lp (fun _ : I => ℂ) 1) j * u j x = u i x := by
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

end MainStatements.WeightKernel.PClosedGraph

open MainStatements.WeightKernel.PClosedGraph in
theorem MainStatements.WeightKernel.closedGraph : MainStatements.WeightKernel.ClosedGraph := by
  intro Ω I _ m u hbd hint
  choose M hM using hbd
  let Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ := fun a x => ∑' i, a i * u i x
  have hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m := fun a => hint a (summable_norm_lp a)
  have hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b := by
    intro a b
    funext x
    simp only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]
    exact Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a))
      (summable_mul (hM x) b (summable_norm_lp b))
  have hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x := by
    intro c a
    funext x
    simp only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  let T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m :=
    { toFun := fun a => Integrable.toL1 (Tf a) (hTi a)
      map_add' := by
        intro a b
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hadd a b))
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hsmul c a)) }
  have hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a) := fun a => rfl
  have hcont : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun s a y hs hy => ?_
    have hmeas := tendstoInMeasure_of_tendsto_Lp hy
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    apply Lp.ext
    filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)]
      with x hx1 hx2 hx3
    rw [hTapp a, hx2]
    have hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]
          exact hs
        simpa using h0.mul_const (M x)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have e : Tf (s n) x - Tf a x = Tf (s n - a) x := by
        have := congrFun (hadd (s n - a) a) x
        simp only [sub_add_cancel, Pi.add_apply] at this
        rw [this]
        ring
      rw [e]
      exact norm_tsum_mul_le (hM x) (s n - a)
    have hsub := hpt.comp hns.tendsto_atTop
    refine tendsto_nhds_unique hx1 ?_
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hTapp, hx3]
  let T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m := ⟨T, hcont⟩
  refine ⟨‖T'‖, fun i => ?_⟩
  classical
  let e : lp (fun _ : I => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have hTe : Tf e = u i := funext fun x => tsum_single i x
  have hint_i : Integrable (u i) m := hTe ▸ hTi e
  refine ⟨hint_i, ?_⟩
  have hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(hTi e).coeFn_toL1] with x hx
    rw [hTapp, hx, hTe]
  have hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖ := T'.le_opNorm e
  have he : ‖e‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  rw [← hn]
  calc ‖T e‖ = ‖T' e‖ := rfl
    _ ≤ ‖T'‖ * ‖e‖ := hle
    _ = ‖T'‖ := by rw [he, mul_one]
end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PIdentOne

def gR {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℝ :=
  B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) * φ (h⁻¹ * s * h)

def G {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℂ :=
  (gR ι s B φ z h : ℂ)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} {ι : H →* Matrix (Fin n) (Fin n) ℂ}
    {s : H} {B : Mx n × Mx n → ℝ} {φ : H → ℝ}

theorem gR_cont (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (hφc : Continuous φ) (z : H) :
    Continuous (gR ι s B φ z) := by
  unfold gR
  have hBc : Continuous B := hB.smooth.continuous
  exact (hBc.comp (continuous_const.prodMk (hι.comp (continuous_const.mul continuous_id)))).mul
    (hφc.comp ((continuous_inv.mul continuous_const).mul continuous_id))

theorem gR_supp (hB : IsWeight ι s B) (hφ : HasCompactSupport φ) (z : H) :
    HasCompactSupport (gR ι s B φ z) := by
  obtain ⟨K, hK, hKp⟩ := hB.proper {z⁻¹ * s * z} (tsupport φ) isCompact_singleton hφ
  refine HasCompactSupport.intro (hK.image (continuous_const_mul z)) fun h hh => ?_
  by_contra hne
  apply hh
  refine ⟨z⁻¹ * h, hKp z (z⁻¹ * h) (Set.mem_singleton _) ?_ ?_, mul_inv_cancel_left z h⟩
  · rw [mul_inv_cancel_left z h]
    exact subset_tsupport _ (fun h0 => hne (by simp [gR, h0]))
  · exact fun h0 => hne (by simp [gR, h0])

theorem fiber (hB : IsWeight ι s B) (dt : Measure (cent s)) [dt.IsMulRightInvariant] (z h : H) :
    ∫ t : cent s, G ι s B φ z (t * h) ∂dt = ∫ t : cent s, G ι s B φ 1 (t * h) ∂dt := by
  obtain ⟨t₀, ht₀, e⟩ := hB.shift z h 1 h
  have key : ∀ v : H, v * s = s * v → (v * h)⁻¹ * s * (v * h) = h⁻¹ * s * h := fun v hv => by
    calc (v * h)⁻¹ * s * (v * h) = h⁻¹ * (v⁻¹ * (s * v)) * h := by group
      _ = h⁻¹ * (v⁻¹ * (v * s)) * h := by rw [hv]
      _ = h⁻¹ * s * h := by group
  have hc : ∀ u : cent s, ((u : H) * h)⁻¹ * s * (u * h) = h⁻¹ * s * h := fun u => key u (mem_cent.1 u.2)
  calc ∫ t : cent s, G ι s B φ z (t * h) ∂dt
        = ∫ t : cent s, G ι s B φ 1 (((t * ⟨t₀, ht₀⟩ : cent s) : H) * h) ∂dt := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [G, gR]
          rw [hc t, hc (t * ⟨t₀, ht₀⟩), ← mul_assoc z⁻¹, e t t.2]
          simp [mul_assoc]
    _ = _ := integral_mul_right_eq_self (fun t : cent s => G ι s B φ 1 ((t : H) * h)) ⟨t₀, ht₀⟩

theorem integral_eq (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (z : H) :
    ∫ h, G ι s B φ z h ∂μ = ∫ h, G ι s B φ 1 h ∂μ := by
  have hi : ∀ w, Integrable (G ι s B φ w) μ := fun w =>
    (Complex.continuous_ofReal.comp (gR_cont hι hB hφc w)).integrable_of_hasCompactSupport
      ((gR_supp hB hφ w).comp_left Complex.ofReal_zero)
  have w1 := (weil_integral (dt := dt) (isClosed_cent s) (hi z)).2.2
  have w2 := (weil_integral (dt := dt) (isClosed_cent s) (hi 1)).2.2
  rw [← w1, ← w2]
  exact congrArg (quotInt _ dt μ) (funext fun x => fiber hB dt z x)

theorem orig_eq (μ : Measure H) [μ.IsHaarMeasure] (z : H) :
    ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ =
      ∫ h, G ι s B φ z h ∂μ := by
  refine (integral_mul_left_eq_self (μ := μ) (fun k => (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) *
    (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ)) z⁻¹).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [G, gR, Complex.ofReal_mul]
  rw [show (z⁻¹ * h)⁻¹ * (z⁻¹ * s * z) * (z⁻¹ * h) = h⁻¹ * s * h by group]

theorem ne_zero (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (hφc : Continuous φ) (hφ : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφs : 0 < φ s) :
    ∫ h, G ι s B φ 1 h ∂μ ≠ 0 := by
  have hpos : 0 < ∫ h, gR ι s B φ 1 h ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (gR_cont hι hB hφc 1)
      (gR_supp hB hφ 1) (fun h => mul_nonneg (hB.nonneg _) (hφ0 _)) ?_
    simp only [gR, inv_one, one_mul, mul_one]
    exact (mul_pos hB.pos hφs).ne'
  simp only [G]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end MainStatements.WeightKernel.PIdentOne

theorem MainStatements.WeightKernel.identOne : IdentOne := by
  intro H _ _ _ _ _ _ _ _ n ι hι s B hB μ _ dt _ _ φ hφc hφ hφ0 hφs
  exact ⟨_, PIdentOne.ne_zero hι hB μ hφc hφ hφ0 hφs, fun z =>
    (PIdentOne.orig_eq μ z).trans (PIdentOne.integral_eq hι hB μ dt hφc hφ z)⟩

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PShiftT

def rho (S : ℂ → ℝ) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then ((Real.sqrt (S z) : ℝ) : ℂ)
  else if ‖z‖ < 1 then (((Real.sqrt (S (star z)⁻¹) : ℝ) : ℂ))⁻¹ else 1

lemma key (S : ℂ → ℝ) (hS : ∀ z, 0 < S z) (z w : ℂ) (h : star z * w = 1) :
    star (rho S z) * rho S w = 1 := by
  have hz : z ≠ 0 := by rintro rfl; simp at h
  have hw : w = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hw
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, norm_star]
  have hcc : (star (star z)⁻¹)⁻¹ = z := by rw [star_inv₀, star_star, inv_inv]
  have e : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hipos : 0 < ‖z‖⁻¹ := inv_pos.mpr hpos
  rcases lt_trichotomy 1 ‖z‖ with h1 | h1 | h1
  · have h2 : ‖z‖⁻¹ < 1 := by nlinarith
    have hs : (((Real.sqrt (S z)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS z)).ne'
    simp only [rho, hn, hcc]
    rw [if_pos h1, if_neg (by linarith), if_pos h2, Complex.star_def, Complex.conj_ofReal]
    exact mul_inv_cancel₀ hs
  · have h2 : ‖z‖⁻¹ = 1 := by rw [← h1, inv_one]
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    simp
  · have h2 : 1 < ‖z‖⁻¹ := by nlinarith
    have hs : (((Real.sqrt (S (star z)⁻¹)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS _)).ne'
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_pos h1, if_pos h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact inv_mul_cancel₀ hs

end MainStatements.WeightKernel.PShiftT

namespace MainStatements.WeightKernel

open MainStatements.WeightKernel.PShiftT in
theorem shiftT : ShiftT := by
  intro n J l hl hJ σ hσ
  classical
  let S : ℂ → ℝ := fun z => if h : ∃ i, l i = z then σ (Classical.choose h) else 1
  have hSpos : ∀ z, 0 < S z := by
    intro z
    simp only [S]
    split_ifs
    · exact hσ _
    · exact zero_lt_one
  have hSl : ∀ i, S (l i) = σ i := by
    intro i
    have h : ∃ j, l j = l i := ⟨i, rfl⟩
    simp only [S, dif_pos h]
    rw [hl (Classical.choose_spec h)]
  refine ⟨fun i => rho S (l i), ?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply] at hij ⊢
    by_cases h0 : J i j = 0
    · simp [h0]
    have e1 : star (l i) * l j = 1 := by
      have : (star (l i) * l j) * J i j = 1 * J i j := by rw [one_mul]; calc _ = star (l i) * J i j * l j := by ring
          _ = J i j := hij
      exact mul_right_cancel₀ h0 this
    have e2 : star (rho S (l i)) * rho S (l j) = 1 := key S hSpos _ _ e1
    calc _ = (star (rho S (l i)) * rho S (l j)) * J i j := by ring
      _ = J i j := by rw [e2, one_mul]
  · intro i hi
    show ‖rho S (l i)‖ ^ 2 = σ i
    rw [rho, if_pos hi, hSl, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hσ i).le]

end MainStatements.WeightKernel

end
end
