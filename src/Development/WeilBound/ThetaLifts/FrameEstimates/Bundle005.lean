module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientCompactness

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topRing : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
    change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
    rw [infEmb_tmul, map_one, mul_one]
    rfl
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

theorem continuous_sz {n d : ℕ} : Continuous (sz τ : Ten F E n d → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_piInf (τ w)).comp ((continuous_apply j).comp (continuous_apply i))).norm

theorem sz_nonneg {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem entry_le_sz {n d : ℕ} (z : Ten F E n d) (w : InfinitePlace F) (i : Fin n) (j : Fin d) :
    ‖piInf (τ w) (z i j)‖ ≤ sz τ z := by
  unfold sz
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖piInf (τ w) (z i j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem sz_mul_mul_le {n d : ℕ} (A : Ten F E n n) (B : Ten F E d d) (z : Ten F E n d) :
    sz τ (A * z * Bᵀ : Ten F E n d) ≤ (n * d * (sz τ A * sz τ B)) * sz τ z := by
  have hA := sz_nonneg τ A
  have hB := sz_nonneg τ B
  have key : ∀ w i j, ‖piInf (τ w) ((A * z * Bᵀ : Ten F E n d) i j)‖ ≤
      (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ := by
    intro w i j

    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := entry_le_sz τ A w i k
    have h2 := entry_le_sz τ B w j l
    calc _ ≤ sz τ A * ‖piInf (τ w) (z k l)‖ * sz τ B := by gcongr
      _ = _ := by ring
  calc sz τ (A * z * Bᵀ : Ten F E n d)
      ≤ ∑ w, ∑ _i : Fin n, ∑ _j : Fin d, (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key w i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show sz τ z = ∑ w, ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

theorem maj_nonneg {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : 0 ≤ maj τ C N z := by
  have := sz_nonneg τ z
  unfold maj
  split_ifs
  · positivity
  · exact le_rfl

theorem maj_le {n d : ℕ} (C C' : Set (Ten F E n d)) (N : ℕ) (A : Ten F E n n) (B : Ten F E d d) (K : ℝ) (hK : 1 ≤ K)
    (hAB : n * d * (sz τ A * sz τ B) ≤ K) (hC : ∀ c ∈ C, (A * c * Bᵀ : Ten F E n d) ∈ C') (z : Ten F E n d) :
    maj τ C N z ≤ K ^ N * maj τ C' N (A * z * Bᵀ : Ten F E n d) := by
  by_cases h : ∃ c ∈ C, At (evI F) (z - c)
  · have h' : ∃ c ∈ C', At (evI F) ((A * z * Bᵀ : Ten F E n d) - c) := by
      obtain ⟨c, hc, hz⟩ := h
      refine ⟨_, hC c hc, fun u hu => ?_⟩
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu, Matrix.mul_zero,
        Matrix.zero_mul]
    unfold maj
    rw [if_pos h, if_pos h']
    have h0 := sz_nonneg τ z
    have h1 := sz_nonneg τ (A * z * Bᵀ : Ten F E n d)
    have h2 : 1 + sz τ (A * z * Bᵀ : Ten F E n d) ≤ K * (1 + sz τ z) := by
      have := (sz_mul_mul_le τ A B z).trans (mul_le_mul_of_nonneg_right hAB h0)
      linarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 N
  · have := maj_nonneg τ C' N (A * z * Bᵀ : Ten F E n d)
    rw [maj, if_neg h]
    positivity

theorem continuous_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g :=
  Units.continuous_val.comp continuous_subtype_val

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g κ : UA σ J) : mat κ * mat (g * κ)⁻¹ = mat g⁻¹ := by
  rw [← mat_mul, mul_inv_rev, mul_inv_cancel_left]

end LatticeQuotientCompactness


open LatticeQuotientCompactness in
theorem latCpt_of : LatCpt := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ Ω Ω' hΩ hΩ' C N hC
  have := topRing (F := F) (E := E)
  obtain ⟨M, hM⟩ := (hΩ.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  obtain ⟨M', hM'⟩ := (hΩ'.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  let K : ℝ := max 1 (n * d * (M * M'))
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K ^ N := by positivity
  let f : UA σ J × Ten F E n d × UA σ J' → Ten F E n d := fun p => mat p.1 * p.2.1 * (mat p.2.2)ᵀ
  have hf : Continuous f :=
    ((continuous_mat.comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_mat.comp (continuous_snd.comp continuous_snd)).matrix_transpose
  refine ⟨f '' (Ω ×ˢ C ×ˢ Ω'), ⟨K ^ N, hK0⟩, (hΩ.prod (hC.prod hΩ')).image hf, fun S g h κ hκ κ' hκ' => ?_⟩
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have a1 : sz τ (mat κ) ≤ M := hM ⟨κ, hκ, rfl⟩
  have a2 : sz τ (mat κ') ≤ M' := hM' ⟨κ', hκ', rfl⟩
  have b1 := sz_nonneg τ (mat κ)
  have b2 := sz_nonneg τ (mat κ')
  have hAB : n * d * (sz τ (mat κ) * sz τ (mat κ')) ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ M := b1.trans a1
    gcongr
  have key := maj_le τ C (f '' (Ω ×ˢ C ×ˢ Ω')) N (mat κ) (mat κ') K hK hAB
    (fun c hc => ⟨(κ, c, κ'), ⟨hκ, hc, hκ'⟩, rfl⟩) (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ)
  have e : mat κ * (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ) * (mat κ')ᵀ =
      mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ := by
    rw [← mat_mul_inv g κ, ← mat_mul_inv h κ', Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at key
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_eq_coe_nnreal hK0]
  rfl

end PositivityTheory.ThKEst

end
end

section

open MeasureTheory Filter Topology GlobalTheory.WeilM

noncomputable section
namespace PositivityTheory.ThKEst.W

theorem real_bound (h : CoefReal) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (β : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hβ : ∀ y, β y = 0 → y = 0) :
    ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ N : ℕ, ∃ p : Seminorm ℂ (SchwartzMap Y ℂ), Continuous p ∧
      ∀ (f₁ f₂ : SchwartzMap Y ℂ) (x y : Y), ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) *
        (starRingEnd ℂ) (f₂ u) ∂ν‖ * (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ Y))
  let T : V ≃L[ℝ] Y := (toEuclidean (E := Y)).symm
  refine ⟨Measure.map T volume, T.isAddHaarMeasure_map _, fun N => ?_⟩
  obtain ⟨p, hp, hb⟩ := h V N
  let S : Y →ₗ[ℝ] (V →L[ℝ] ℝ) := (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
    (β.compl₂ T.toLinearEquiv.toLinearMap)
  have hS : ∀ y v, S y v = β y (T v) := fun _ _ => rfl
  obtain ⟨K₁, -, hK₁⟩ := S.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 fun y hy => hβ y (LinearMap.ext fun u => by
    have := hS y (T.symm u)
    rw [hy, T.apply_symm_apply] at this
    exact this.symm))
  let K : NNReal := 1 + K₁ + ‖(T : V →L[ℝ] Y)‖₊
  have hK : (K : ℝ) = 1 + K₁ + ‖(T : V →L[ℝ] Y)‖ := rfl
  let c := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  refine ⟨K ^ N • p.comp c.toLinearMap, (hp.comp c.continuous).const_smul (K ^ N), fun f₁ f₂ x y => ?_⟩
  have h1 := hb (c f₁) (c f₂) (T.symm x) ((InnerProductSpace.toDual ℝ V).symm (S y))
  have e : ∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)
      ∂(Measure.map T volume) = ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ u ((InnerProductSpace.toDual ℝ V).symm (S y)) : ℝ)) * c f₁ (u + T.symm x) * (starRingEnd ℂ) (c f₂ u) := by
    rw [show Measure.map T volume = Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [real_inner_comm _ u, InnerProductSpace.toDual_symm_apply, hS]
    simp [c]
  rw [e]
  rw [LinearIsometryEquiv.norm_map] at h1
  have hx : ‖x‖ ≤ ‖(T : V →L[ℝ] Y)‖ * ‖T.symm x‖ := by simpa using (T : V →L[ℝ] Y).le_opNorm (T.symm x)
  have hy : ‖y‖ ≤ K₁ * ‖S y‖ := by
    have := hK₁.le_mul_dist y 0
    rwa [map_zero, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at this
  have n1 := norm_nonneg (T : V →L[ℝ] Y)
  have n2 := norm_nonneg (T.symm x)
  have n3 := norm_nonneg (S y)
  have n4 := K₁.coe_nonneg
  have h2 : 1 + ‖x‖ + ‖y‖ ≤ K * (1 + ‖T.symm x‖ + ‖S y‖) := by
    rw [hK]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n4 n2]
  have hK1 : (1 : ℝ) ≤ K ^ N := one_le_pow₀ (by rw [hK]; linarith)
  have q := mul_nonneg (apply_nonneg p (c f₁)) (apply_nonneg p (c f₂))
  calc _ ≤ _ * (K * (1 + ‖T.symm x‖ + ‖S y‖)) ^ N := by gcongr
    _ = K ^ N * (_ * (1 + ‖T.symm x‖ + ‖S y‖) ^ N) := by rw [mul_pow, mul_left_comm]
    _ ≤ K ^ N * (p (c f₁) * p (c f₂)) := by gcongr
    _ ≤ K ^ N * (K ^ N * (p (c f₁) * p (c f₂))) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left q hK1) (zero_le_one.trans hK1)
    _ = _ := by
      simp only [Seminorm.smul_apply, Seminorm.comp_apply, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
      ring

theorem sb_inv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {φ : G → ℂ} (hφ : φ ∈ SB G) :
    ∀ᶠ k in 𝓝 (0 : G), ∀ x, φ (x + k) = φ x := by
  have h1 : ∀ᶠ k in 𝓝 (0 : G), ∀ x ∈ tsupport φ, φ (x + k) = φ x ∧ φ (x - k) = φ x :=
    hφ.2.isCompact.eventually_forall_of_forall_eventually fun x _ => by
      have a := (hφ.1.comp_continuous (f := fun z : G × G => z.2 + z.1) (by fun_prop)).eventually_eq (0, x)
      have b := (hφ.1.comp_continuous (f := fun z : G × G => z.2 - z.1) (by fun_prop)).eventually_eq (0, x)
      have c := (hφ.1.comp_continuous (f := fun z : G × G => z.2) (by fun_prop)).eventually_eq (0, x)
      filter_upwards [a, b, c] with z a b c
      simp only [Function.comp, add_zero, sub_zero] at a b c
      exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h1] with k hk x
  by_cases hx : x ∈ tsupport φ
  · exact (hk x hx).1
  by_cases hx' : x + k ∈ tsupport φ
  · simpa using (hk _ hx').2.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem fin_bound {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] (ν : Measure G) [ν.IsAddHaarMeasure] (χ : H → G → ℂ) (hn : ∀ y u, ‖χ y u‖ = 1)
    (ha : ∀ y u u', χ y (u + u') = χ y u * χ y u')
    (hd : ∀ U ∈ 𝓝 (0 : G), ∃ K, IsCompact K ∧ ∀ y, (∀ u ∈ U, χ y u = 1) → y ∈ K) {φ₁ φ₂ : G → ℂ} (h₁ : φ₁ ∈ SB G)
    (h₂ : φ₂ ∈ SB G) : ∃ (C : ℝ) (K : Set (G × H)), IsCompact K ∧ ∀ x y,
      ‖∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν‖ ≤ C ∧
      (∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν ≠ 0 → (x, y) ∈ K) := by
  obtain ⟨C, hC⟩ := h₁.1.continuous.bounded_above_of_compact_support h₁.2
  obtain ⟨K, hK, hK'⟩ := hd _ ((sb_inv h₁).and (sb_inv h₂))
  have hi : Integrable φ₂ ν := h₂.1.continuous.integrable_of_hasCompactSupport h₂.2
  refine ⟨∫ u, C * ‖φ₂ u‖ ∂ν, ((fun z : G × G => z.1 - z.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) ×ˢ K,
    ((h₁.2.isCompact.prod h₂.2.isCompact).image (by fun_prop)).prod hK, fun x y => ⟨?_, fun h0 => ⟨?_, hK' y fun k hk => ?_⟩⟩⟩
  · refine norm_integral_le_of_norm_le (hi.norm.const_mul C) (.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, hn, one_mul, RCLike.norm_conj]
    gcongr
    exact hC _
  · by_contra hx
    refine h0 (integral_eq_zero_of_ae (.of_forall fun u => ?_))
    by_contra hu
    simp only [Pi.zero_apply, mul_eq_zero, not_or, map_eq_zero] at hu
    exact hx ⟨(u + x, u), ⟨subset_tsupport _ hu.1.2, subset_tsupport _ hu.2⟩, add_sub_cancel_left _ _⟩
  · refine (mul_eq_right₀ h0).1 ?_
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ k]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only
    rw [ha, add_right_comm, hk.1, hk.2]
    ring

end PositivityTheory.ThKEst.W
end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem denom_fin {K : Set (Af F)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : F, algebraMap F (Af F) x ∈ K → IsIntegral ℤ ((m : F) * x) := by
  have hopen : IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hNe : Nonempty {M : ℕ // 0 < M} := ⟨⟨1, Nat.one_pos⟩⟩
  obtain ⟨M, hM⟩ := hK.elim_directed_cover
    (fun M : {M : ℕ // 0 < M} => ⋃ d ∈ {d : ℕ | 0 < d ∧ d ∣ M.1},
      (fun a : Af F => (d : Af F) * a) ⁻¹' {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v})
    (fun M => isOpen_biUnion fun d _ => hopen.preimage (continuous_const.mul continuous_id))
    (fun a _ => by
      obtain ⟨d, hd, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
      exact Set.mem_iUnion.2 ⟨⟨d, hd⟩, Set.mem_iUnion₂.2 ⟨d, ⟨hd, dvd_refl d⟩, h⟩⟩)
    (fun M N => ⟨⟨M.1 * N.1, Nat.mul_pos M.2 N.2⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_right _⟩, h⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_left _⟩, h⟩⟩)
  refine ⟨M.1, M.2, fun x hx => ?_⟩
  obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 (hM hx)
  have h2 : ∀ v, (algebraMap F (Af F) ((d : F) * x)) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_mul, map_natCast]
    exact h
  obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h2
  have hdx : IsIntegral ℤ ((d : F) * x) := by
    rw [hy]
    exact y.isIntegral_coe
  obtain ⟨e, he⟩ := hd.2
  have hei : IsIntegral ℤ (e : F) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := F) (x := (e : ℤ))
    simpa using h3
  rw [he, Nat.cast_mul, mul_comm (d : F) (e : F), mul_assoc]
  exact hei.mul hdx


variable (F) in
def uFin : AF F := pairA F 0 1

theorem evI_uFin : evI F (uFin F) = 0 := by
  unfold evI uFin pairA
  exact map_zero _

theorem snd_uFin_mul (a : AF F) : sndA F (uFin F * a) = sndA F a := by
  show (1 : Af F) * a.2 = a.2
  exact one_mul _

theorem uFin_mul_rId (t : ℝ) : uFin F * rId F t = uFin F := by
  show pairA F 0 1 * rId F t = pairA F 0 1
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * (rId F t).1 = 0
    exact zero_mul _
  · show (1 : Af F) * ((1 : Af F) + 0) = 1
    simp

theorem exists_int_mul (x : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
  have hq : IsAlgebraic ℚ x := (Algebra.IsIntegral.isIntegral x).isAlgebraic
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hq
  obtain ⟨d, hd, hy⟩ := hz.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hy
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · refine ⟨k, by omega, ?_⟩
    simpa using hy
  · refine ⟨k, by omega, ?_⟩
    have h2 := hy.neg
    simpa using h2
private theorem isIntegral_natCast_mul_of_dvd {A : Type} [CommRing A] {a b : ℕ} (hab : a ∣ b) {y : A}
    (h : IsIntegral ℤ ((a : A) * y)) : IsIntegral ℤ ((b : A) * y) := by
  obtain ⟨e, rfl⟩ := hab
  have he : IsIntegral ℤ (e : A) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := A) (x := (e : ℤ))
    simpa using h3
  rw [Nat.cast_mul, mul_comm (a : A) (e : A), mul_assoc]
  exact he.mul h

theorem denom_AE {K : Set (AE F E)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : E, (∃ c ∈ K, uFin F • inclR (F := F) (AF F) x = uFin F • c) → IsIntegral ℤ ((m : E) * x) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hcont : ∀ i, Continuous fun c : AE F E => sndA F (B.coord i c) := fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (B.coord i))
  choose m hm hint using fun i => denom_fin (hK.image (hcont i))
  choose n hn hbi using fun i => exists_int_mul (b i)
  refine ⟨(∏ i, m i) * ∏ i, n i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i) (Finset.prod_pos fun i _ => hn i), ?_⟩
  rintro x ⟨c, hcK, hxc⟩
  have hcoord : ∀ i, algebraMap F (Af F) (b.repr x i) = sndA F (B.coord i c) := by
    intro i
    have h1 := congrArg (fun y => sndA F (B.coord i y)) hxc
    simp only [LinearMap.map_smul, smul_eq_mul, snd_uFin_mul] at h1
    rw [← h1]
    simp [B, inclR, Algebra.TensorProduct.basis_repr_tmul]
  have hr : ∀ i, IsIntegral ℤ (((∏ j, m j : ℕ) : F) * b.repr x i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (hint i _ ⟨c, hcK, (hcoord i).symm⟩)
  have hbb : ∀ i, IsIntegral ℤ (((∏ j, n j : ℕ) : E) * b i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (hbi i)
  have hx : (((∏ i, m i) * ∏ i, n i : ℕ) : E) * x =
      ∑ i, algebraMap F E (((∏ j, m j : ℕ) : F) * b.repr x i) * (((∏ j, n j : ℕ) : E) * b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hx]
  exact (integralClosure ℤ E).sum_mem fun i _ => (hr i).algebraMap.mul (hbb i)

omit [NumberField E] in
theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb]

omit [NumberField E] in
theorem piInf_rId {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  simp only [piInf, compInf, infEmb, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  show InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = ((Real.exp t : ℝ) : ℂ)
  have hy : InfiniteAdeleRing.ringEquiv_mixedSpace F (rId F t).1 =
      ((fun _ => Real.exp t), (fun _ => ((Real.exp t : ℝ) : ℂ))) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace F) (Real.exp t - 1))) = _
    rw [map_add (f := _), map_one, RingEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_ <;> funext v <;> simp
  by_cases hw : w.IsReal
  · have h1 := congrArg (fun z => z.1 ⟨w, hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h1]
  · have h1 := congrArg (fun z => z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    exact h1

end PositivityTheory.ThKEst

end
end
