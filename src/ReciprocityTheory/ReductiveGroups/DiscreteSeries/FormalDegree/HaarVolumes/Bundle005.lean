module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

variable {P Q : ℕ}

def gToLieMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool} (s : GCo ε) :
    Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Matrix.reindex e.symm e.symm (gMat s)

theorem gToLieMat_mem (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    gToLieMat e s ∈ Formalism.BasicNotions.lieU P Q :=
  (OmegaPQAux.mem_reindex_iff e he1 he2 (gMat s)).2 (OmegaPQAux.gMat_mem s)

def gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Formalism.BasicNotions.lieU P Q :=
  ⟨gToLieMat e s, gToLieMat_mem e he1 he2 s⟩

namespace OmegaPQAux

def gToLieL (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    GCo ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun := gToLie e he1 he2
  map_add' s t := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_add]
  map_smul' c s := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_smul]

theorem gToLieL_bij (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Function.Bijective (gToLieL e he1 he2) := by
  have hre : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    intro M; rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
  constructor
  · intro s t h
    have h2 := congrArg (fun X : Formalism.BasicNotions.lieU P Q =>
      Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) h
    simp only [gToLieL, LinearMap.coe_mk, AddHom.coe_mk, gToLie, gToLieMat, hre] at h2
    rw [← coordOf_gMat s, ← coordOf_gMat t, h2]
  · intro X
    set Y := Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) with hYdef
    have hX : Matrix.reindex e.symm e.symm Y = X := by
      rw [hYdef, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    have hY := (mem_reindex_iff e he1 he2 Y).1 (by rw [hX]; exact X.2)
    refine ⟨coordOf Y, Subtype.ext ?_⟩
    change Matrix.reindex e.symm e.symm (gMat (coordOf (ε := ε) Y)) = X
    rw [gMat_coordOf Y hY, hX]

end OmegaPQAux

theorem isOmegaLeb_gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) • Measure.map (gToLie e he1 he2) volume) := by
  have : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩
  set Lin := LinearEquiv.ofBijective _ (OmegaPQAux.gToLieL_bij e he1 he2) with hLin
  set CL := Lin.toContinuousLinearEquiv with hCL
  have hcoe : (CL : GCo ε → Formalism.BasicNotions.lieU P Q) = gToLie e he1 he2 := rfl
  have hG : Measurable (gToLie e he1 he2) := by rw [← hcoe]; exact CL.continuous.measurable
  constructor
  · have hd : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hk : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hp : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hK : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have hGv : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have h1 := ContinuousLinearEquiv.isAddHaarMeasure_map CL (volume : Measure (GCo ε))
    rw [hcoe] at h1
    exact Measure.IsAddHaarMeasure.smul _ (by simp) ENNReal.ofReal_ne_top
  · have hSF : SigmaFinite (volume : Measure (GCo ε)) := Measure.prod.instSigmaFinite
    set c := ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) with hc
    set E : Fin n × Fin n ≃ (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) := (e.prodCongr e).symm with hE
    set R := MeasurableEquiv.piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E
    have hGl : Measurable (OmegaPQAux.Gl ε) :=
      (LinearMap.continuous_of_finiteDimensional (OmegaPQAux.Gl ε)).measurable
    have hPm : Measurable (OmegaPQAux.pairMap ε) := by
      rw [OmegaPQAux.pairMap_eq]
      exact (OmegaPQAux.mp_Amap ε).measurable.comp (hGl.comp (OmegaPQAux.mp_Fmap ε).measurable)
    have hcomp : (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) ∘
          Prod.map (gToLie e he1 he2) (gToLie e he1 he2) = R ∘ OmegaPQAux.pairMap ε := by
      funext st ij
      obtain ⟨i, j⟩ := ij
      have hij : ((i, j) : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)) = E (e i, e j) := by simp [hE]
      conv_rhs => rw [hij]
      simp only [Function.comp_apply, R, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      simp [Formalism.BasicNotions.entries, gToLie, gToLieMat, OmegaPQAux.pairMap, Matrix.reindex_apply]
    have hval : ∀ i j, Measurable (fun X : Formalism.BasicNotions.lieU P Q =>
        (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j) := fun i j =>
      (continuous_subtype_val.matrix_elem i j).measurable
    have hFm : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
      refine Measurable.of_eval fun ij => ?_
      have h1 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_fst
      have h2 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_snd
      exact h1.add (measurable_const.mul h2)
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul _ hFm.aemeasurable,
      Measure.map_prod_map _ _ hG hG, Measure.map_map hFm (hG.prodMap hG), hcomp,
      ← Measure.map_map R.measurable hPm, ← Measure.volume_eq_prod, OmegaPQAux.map_pairMap,
      Measure.map_smul _ R.measurable.aemeasurable,
      (volume_measurePreserving_piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E).map_eq,
      smul_smul, hc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow]
    norm_num

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, Matrix.add_apply]
  simp only [kMat, pmat, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [Complex.ofReal_add, star_add, mul_add, neg_add, add_zero]) <;>
    (try ring)

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = (RingHom.id ℝ c) • gMat s := by
  ext a b
  simp only [gMat, RingHom.id_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [kMat, pmat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> (try simp only [Complex.real_smul, Complex.ofReal_mul, star_mul', Complex.star_def,
    Complex.conj_ofReal, smul_add, smul_zero, smul_neg, add_zero, mul_neg]) <;>
    (try simp only [smul_eq_mul, Complex.ofReal_mul]) <;> (try ring_nf)

def gL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' := gMat_add
  map_smul' := gMat_smul

theorem gL_injective (ε : Fin n → Bool) : Function.Injective (gL ε) := by
  intro s t h
  have h' : gMat s = gMat t := h
  rw [← gCo_gMat s, ← gCo_gMat t, h']

abbrev gV (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := LinearMap.range (gL ε)

def gE (ε : Fin n → Bool) : GCo ε ≃ₗ[ℝ] gV ε := LinearEquiv.ofInjective (gL ε) (gL_injective ε)

def ujMat (ε : Fin n → Bool) : UJ ε →* Matrix (Fin n) (Fin n) ℂ :=
  (Units.coeHom _).comp (UJ ε).subtype

theorem ujMat_apply (ε : Fin n → Bool) (g : UJ ε) : ujMat ε g = toM g := rfl

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_inUJ_small (ε : Fin n → Bool) : ∀ᶠ Z in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ),
    inUJ ε (NormedSpace.exp Z) → inG ε Z := by
  unfold inG
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) 0 := hasStrictFDerivAt_exp_zero
  obtain ⟨s, hs, hap⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))

  have hinj : ∀ x ∈ s, ∀ y ∈ s, NormedSpace.exp x = NormedSpace.exp y → x = y := by
    intro x hx y hy hxy
    have h := hap x hx y hy
    rw [hxy, sub_self] at h
    change ‖0 - (x - y)‖ ≤ ((1 / 2 : NNReal) : ℝ) * ‖x - y‖ at h
    rw [zero_sub, norm_neg, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two] at h
    have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hc1 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    simpa using hcont.tendsto 0
  have hc2 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => -Z) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : Matrix (Fin n) (Fin n) ℂ))
  filter_upwards [hc1.eventually hs, hc2.eventually hs] with Z h1 h2 hU
  unfold inUJ at hU
  have hE : NormedSpace.exp (Jm ε * Zᴴ * Jm ε) = NormedSpace.exp (-Z) := by
    have hL : Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z = 1 := by
      calc Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z
          = Jm ε * ((NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, hJJ]
    rw [show Jm ε * Zᴴ * Jm ε = Jm ε * Zᴴ * (Jm ε)⁻¹ by rw [hJi], Matrix.exp_conj _ _ hJu, hJi,
      Matrix.exp_conjTranspose, Matrix.exp_neg]
    exact (Matrix.inv_eq_left_inv hL).symm
  have hZ := hinj _ h1 _ h2 hE
  calc Zᴴ * Jm ε + Jm ε * Z = Jm ε * (Jm ε * Zᴴ * Jm ε) + Jm ε * Z := by
        simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    _ = 0 := by rw [hZ, Matrix.mul_neg, neg_add_cancel]

def ujChart (ε : Fin n → Bool) : Chart (gV ε) (UJ ε) where
  mat := ujMat ε
  emb := (isClosedEmbedding_toM ε).isEmbedding
  H1 := fun X => by
    obtain ⟨s, hs⟩ := X.2
    have h : NormedSpace.exp (gMat s) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]
      have := exp_smul_mem_UJset (gMat_inG s) 1
      simp only [Complex.ofReal_one, one_smul] at this
      exact this
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    rw [ujMat_apply, ← hs]
    exact hg
  H2 := by
    filter_upwards [exp_inUJ_small ε] with Z hZ hg
    obtain ⟨g, hg⟩ := hg
    have h1 : inUJ ε (ujMat ε g) := g.2
    rw [hg] at h1
    exact ⟨gCo ε Z, gMat_gCo (hZ h1)⟩

end Normed

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end
