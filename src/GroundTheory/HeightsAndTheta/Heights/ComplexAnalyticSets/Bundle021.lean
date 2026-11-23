module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix MvPolynomial

noncomputable section

def genericMatrix (d n : ℕ) : Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) :=
  Matrix.of fun i k => X (i, k)

def detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) : MvPolynomial (Fin d × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j => ∑ k, genericMatrix d n i k * C (M k j))

theorem eval_detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) (x : Fin d × Fin n → ℂ) :
    eval x (detPoly M) = (Matrix.of (fun i k => x (i, k)) * M).det := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.mul_apply]

theorem GeneralProjection.proof : GeneralProjection.Statement := by
  intro n d m L hL
  classical
  set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM
  have hne : ∀ b, detPoly (M b) ≠ 0 := by
    intro b h
    obtain ⟨g, hg⟩ := (L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))
    have h1 : LinearMap.toMatrix' g * M b = 1 := by
      rw [hM]; dsimp only
      rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    have := congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h
    rw [eval_detPoly, map_zero] at this
    have h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g := by
      ext i k; rfl
    rw [h2, h1, det_one] at this
    exact one_ne_zero this
  have hprod : (∏ b, detPoly (M b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hne b
  obtain ⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by
    by_contra hcon
    refine hprod (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine ⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩
  rw [map_prod] at hx
  have hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0 := by
    rw [← eval_detPoly]
    exact (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
  have key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u := by
    intro u
    rw [← Matrix.mulVec_mulVec, hM]
    dsimp only
    rw [LinearMap.toMatrix'_mulVec]
  simp only [key] at hvw
  have h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem areaJacobian_eq_abs_det_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by
  have h1 : areaJacobian L = L.normDet := by
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [areaJacobian, ← h, Real.sqrt_sq L.normDet_nonneg]
  rw [h1, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ φ.toLinearEquiv.finrank_eq.symm,
    φ.toLinearIsometry.normDet_eq_one, one_mul]

theorem encard_iUnion_nat_eq_tsum {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem lintegral_abs_det_eq_lintegral_encard {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A) (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) :
    ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ =
      ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) ↔ (x ∈ B)
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)
  calc ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, μ (f '' P n) := tsum_congr fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image₀ μ (hPm n) (hderP n) (hinj n)
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator 1 y ∂μ :=
        tsum_congr fun n => (lintegral_indicator_one₀ (himg n)).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator 1 y ∂μ :=
        (lintegral_tsum fun n => aemeasurable_one.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
        have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
          ext x
          simp only [mem_ofPred_eq, mem_iUnion]
          constructor
          · rintro ⟨hxA, hxy⟩
            have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
            obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
            exact ⟨n, ⟨hxB, hn⟩, hxy⟩
          · rintro ⟨n, hxP, hxy⟩
            exact ⟨hPA n hxP, hxy⟩
        rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
          (sep_subset _ _))]
        refine tsum_congr fun n => ?_
        by_cases hyn : y ∈ f '' P n
        · obtain ⟨x, hx, rfl⟩ := hyn
          have hs : {z ∈ P n | f z = f x} = {x} := by
            ext z
            simp only [mem_ofPred_eq, mem_singleton_iff]
            exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
          rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
          simp
        · have hs : {z ∈ P n | f z = y} = ∅ := by
            ext z
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            exact fun hz e => hyn ⟨z, hz, e⟩
          rw [hs, encard_empty]
          simp [hyn]

theorem AreaMultiplicity.proof : AreaMultiplicity.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hE hF A f f' hA hf'
  subst hE
  let φ : F ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hF)
  let g : E → E := fun x => φ (f x)
  let g' : E → E →L[ℝ] E := fun x => (φ.toContinuousLinearEquiv : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ A, HasFDerivWithinAt g (g' x) A x := fun x hx =>
    (φ.toContinuousLinearEquiv : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hJ : ∀ x, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) =
      ENNReal.ofReal |(g' x).det| := by
    intro x
    rw [areaJacobian_eq_abs_det_comp φ]
    rfl
  have hN : ∀ y, {x ∈ A | f x = y} = {x ∈ A | g x = φ y} := by
    intro y; ext x; simp [g]
  simp_rw [hJ, hN]
  rw [lintegral_abs_det_eq_lintegral_encard μH[(finrank ℝ E : ℝ)] hA hg']
  have hφ : MeasurePreserving φ (μH[(finrank ℝ E : ℝ)] : Measure F) μH[(finrank ℝ E : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have hφe : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  exact (hφ.lintegral_comp_emb hφe (fun z => (({x ∈ A | g x = z}.encard : ℕ∞) : ℝ≥0∞))).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem NormalModel.exists_clear_denominators {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hb : ∀ i, eval x (b i) ≠ 0) (q : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (r : MvPolynomial (Fin n) ℂ),
      rename Sum.inl ((∏ i, b i) ^ N) * q - rename Sum.inl r ∈ M.ideal ∧
        eval x r = eval x (∏ i, b i) ^ N *
          eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q := by
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  set w : Fin n ⊕ Fin M.m → ℂ := Sum.elim x fun i => eval x (a i) / eval x (b i) with hw
  induction q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C c, ?_, ?_⟩
    · simp
    · simp
  | add p q hp hq =>
    obtain ⟨N₁, r₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, r₂, h₂, e₂⟩ := hq
    refine ⟨N₁ + N₂, B ^ N₂ * r₁ + B ^ N₁ * r₂, ?_, ?_⟩
    · have hid : rename Sum.inl (B ^ (N₁ + N₂)) * (p + q) - rename Sum.inl (B ^ N₂ * r₁ + B ^ N₁ * r₂) =
          rename Sum.inl (B ^ N₂) * (rename Sum.inl (B ^ N₁) * p - rename Sum.inl r₁) +
            rename Sum.inl (B ^ N₁) * (rename Sum.inl (B ^ N₂) * q - rename Sum.inl r₂) := by
        simp only [map_mul, map_add (f := _), map_pow]
        ring
      rw [hid]
      exact M.ideal.add_mem (M.ideal.mul_mem_left _ h₁) (M.ideal.mul_mem_left _ h₂)
    · rw [eval_add, eval_add, eval_mul, eval_mul, e₁, e₂, eval_pow, eval_pow]
      ring
  | mul_X p s hp =>
    obtain ⟨N, r, h, e⟩ := hp
    rcases s with j | i
    · refine ⟨N, r * X j, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ N) * (p * X (Sum.inl j)) - rename Sum.inl (r * X j) =
            X (Sum.inl j) * (rename Sum.inl (B ^ N) * p - rename Sum.inl r) := by
          simp only [map_mul, rename_X]
          ring
        rw [hid]
        exact M.ideal.mul_mem_left _ h
      · rw [eval_mul, eval_mul, e, eval_X, eval_X]
        simp only [hw, Sum.elim_inl]
        ring
    · set Cᵢ : MvPolynomial (Fin n) ℂ := ∏ j ∈ Finset.univ.erase i, b j with hC
      have hBC : B = b i * Cᵢ := (Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)).symm
      refine ⟨N + 1, r * a i * Cᵢ, ?_, ?_⟩
      · have hid : rename Sum.inl (B ^ (N + 1)) * (p * X (Sum.inr i)) - rename Sum.inl (r * a i * Cᵢ) =
            rename Sum.inl Cᵢ * (rename Sum.inl (b i) * X (Sum.inr i)) *
                (rename Sum.inl (B ^ N) * p - rename Sum.inl r) +
              rename Sum.inl Cᵢ * rename Sum.inl r *
                (rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i)) := by
          rw [pow_succ, hBC]
          simp only [map_mul, map_pow]
          ring
        rw [hid]
        exact M.ideal.add_mem (M.ideal.mul_mem_left _ h) (M.ideal.mul_mem_left _ (hab i))
      · rw [eval_mul, eval_mul, eval_mul, eval_X, pow_succ, hBC]
        have e' : eval x r = eval x (b i * Cᵢ) ^ N * eval w p := by rw [← hBC]; exact e
        rw [e']
        simp only [hw, Sum.elim_inr, eval_mul]
        field_simp [hb i]

theorem NormalModel.graph_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hx : x ∈ zeroSetIn J) (hb : ∀ i, eval x (b i) ≠ 0) :
    (Sum.elim x fun i => eval x (a i) / eval x (b i)) ∈ zeroSetIn M.ideal := by
  intro q hq
  obtain ⟨N, r, h, e⟩ := M.exists_clear_denominators a b hab x hb q
  have hr : rename Sum.inl r ∈ M.ideal := by
    have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl ((∏ i, b i) ^ N)) hq) h
    simpa using this
  have hrJ : r ∈ J := by
    rw [← M.comap_eq]
    exact hr
  have hBx : eval x (∏ i, b i) ^ N ≠ 0 := by
    rw [map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hb i)
  have h0 : eval x (∏ i, b i) ^ N * eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q = 0 := by
    rw [← e]
    exact hx r hrJ
  exact (mul_eq_zero.1 h0).resolve_left hBx

theorem NormalModel.eq_graph_of_mem_zeroSetIn {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (w : Fin n ⊕ Fin M.m → ℂ) (hw : w ∈ zeroSetIn M.ideal) (hb : ∀ i, eval (firstCoords w) (b i) ≠ 0) :
    w = Sum.elim (firstCoords w) fun i => eval (firstCoords w) (a i) / eval (firstCoords w) (b i) := by
  funext s
  rcases s with j | i
  · rfl
  · have h := hw _ (hab i)
    simp only [map_sub, map_mul, eval_rename, eval_X] at h
    simp only [Sum.elim_inr]
    rw [eq_div_iff (hb i)]
    have hc : (w ∘ Sum.inl) = firstCoords w := rfl
    rw [hc] at h
    linear_combination h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

open MvPolynomial

def linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) : MvPolynomial (Fin n) k :=
  ∑ j, C (φ (Pi.single j 1)) * X j

theorem eval_linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]

  simp [linearFormPoly, map_sum, mul_comm]

theorem GenericPrimitive.proof : GenericPrimitive.Statement := by
  intro k K L _ _ _ _ _ _ _ _ _ n x hx
  have hfin : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)
  have := Fintype.ofFinite (IntermediateField K L)
  classical

  let f : (Fin n → k) →ₗ[k] L := Fintype.linearCombination k x
  have hf : ∀ c, f c = ∑ j, c j • x j := fun c => Fintype.linearCombination_apply k x c

  let W : IntermediateField K L → Submodule k (Fin n → k) := fun M =>
    (M.toSubalgebra.toSubmodule.restrictScalars k).comap f
  have hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤ := by
    intro M hM
    refine lt_top_iff_ne_top.2 fun htop => hM ?_
    have hxM : Set.range x ⊆ M := by
      rintro _ ⟨j, rfl⟩
      have hj : (Pi.single j 1 : Fin n → k) ∈ W M := htop ▸ Submodule.mem_top
      have : f (Pi.single j 1) = x j := by
        rw [hf]; simp [Pi.single_apply]
      simpa [W, this] using hj
    exact eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)
  have hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k,
      M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ := by
    intro M
    by_cases hM : M = ⊤
    · exact ⟨0, fun h => (h hM).elim⟩
    · obtain ⟨φ, h0, hle⟩ := (W M).exists_le_ker_of_lt_top (hW M hM)
      exact ⟨φ, fun _ => ⟨h0, hle⟩⟩
  choose φ hφ using hφ
  let S : Finset (IntermediateField K L) := Finset.univ.filter (· ≠ ⊤)
  refine ⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    have hM' : M ≠ ⊤ := (Finset.mem_filter.1 hM).2
    obtain ⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by
      by_contra h
      exact (hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))
    intro h0
    apply hc
    rw [← eval_linearFormPoly, h0, map_zero]
  · intro c hc
    by_contra hne
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    have hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    apply hc _ hmem
    rw [eval_linearFormPoly]
    apply (hφ _ hne).2
    show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}
    rw [hf]
    exact IntermediateField.mem_adjoin_simple_self K _

end

end GroundTheory.Heights₂.Heights.ComplexSets
end
