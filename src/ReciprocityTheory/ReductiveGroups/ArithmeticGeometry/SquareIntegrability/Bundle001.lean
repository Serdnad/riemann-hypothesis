module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

def cubeIco (κ : Type) : Set (κ → ℝ) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

theorem cubeIco_eq (κ : Type) : cubeIco κ = Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 := by
  ext x
  simp [cubeIco, Set.mem_pi]

theorem cubeIco_meas (κ : Type) [Finite κ] : MeasurableSet (cubeIco κ) := by
  rw [cubeIco_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem vol_cubeIco (κ : Type) [Fintype κ] : volume (cubeIco κ) = 1 := by
  rw [cubeIco_eq, Real.volume_pi_Ico]
  simp

theorem cube_ae_eq (κ : Type) [Fintype κ] :
    cubeIco κ =ᵐ[volume] {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  have h2 : {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [Set.mem_pi]
  rw [cubeIco_eq, h2]
  exact (Measure.univ_pi_Ico_ae_eq_Icc).trans (Measure.univ_pi_Ioc_ae_eq_Icc).symm

theorem avg_fd_cube {ι κ : Type} [Fintype ι] [Fintype κ]
    (B : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (f : EuclideanSpace ℂ ι → ℝ) :
    ⨍ v in ZSpan.fundamentalDomain B, f v = ∫ x in cubeIco κ, f (B.equivFun.symm x) := by
  classical
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (κ → ℝ) := B.equivFun.toContinuousLinearEquiv
  have hfd : ZSpan.fundamentalDomain B = e ⁻¹' cubeIco κ := by
    ext v
    simp [ZSpan.mem_fundamentalDomain, cubeIco, e]
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  set μ : Measure (κ → ℝ) := (volume : Measure (EuclideanSpace ℂ ι)).map e with hμ
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have hsm : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  set c := μ.addHaarScalarFactor volume with hcdef
  have hvol : volume (ZSpan.fundamentalDomain B) = (c : ENNReal) := by
    rw [hfd, ← hme.map_apply, ← hμ, hsm]
    simp [vol_cubeIco]
  have hc : c ≠ 0 := by
    intro h0
    have h' : μ = 0 := by rw [hsm, h0, zero_smul]
    exact (NeZero.ne μ) h'
  have hint : ∫ v in ZSpan.fundamentalDomain B, f v = (c : ℝ) * ∫ x in cubeIco κ, f (e.symm x) := by
    have h3 : ∫ v in e ⁻¹' cubeIco κ, f v = ∫ v in e ⁻¹' cubeIco κ, (fun x => f (e.symm x)) (e v) := by
      simp
    have key := hme.setIntegral_map (μ := (volume : Measure (EuclideanSpace ℂ ι)))
      (fun x => f (e.symm x)) (cubeIco κ)
    rw [hfd, h3, ← key, ← hμ]
    conv_lhs => rw [hsm]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    all_goals rw [NNReal.smul_def, smul_eq_mul]
  rw [setAverage_eq, hint, Measure.real, hvol]
  have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [ENNReal.coe_toReal, smul_eq_mul]
  field_simp
  rfl

theorem avg_fd_swap {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (B₁ : Module.Basis κ₁ ℝ (EuclideanSpace ℂ ι)) (B₂ : Module.Basis κ₂ ℝ (EuclideanSpace ℂ ι))
    (h : Submodule.span ℤ (Set.range B₁) = Submodule.span ℤ (Set.range B₂))
    (f : EuclideanSpace ℂ ι → ℝ)
    (hf : ∀ γ ∈ Submodule.span ℤ (Set.range B₁), ∀ v, f (γ + v) = f v) :
    ⨍ v in ZSpan.fundamentalDomain B₁, f v = ⨍ v in ZSpan.fundamentalDomain B₂, f v := by
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range B₁)) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have h1 := ZSpan.isAddFundamentalDomain B₁ (volume : Measure (EuclideanSpace ℂ ι))
  have h2 := ZSpan.isAddFundamentalDomain B₂ (volume : Measure (EuclideanSpace ℂ ι))
  rw [← h] at h2
  have hinv : ∀ (g : Submodule.span ℤ (Set.range B₁)) (x : EuclideanSpace ℂ ι), f (g +ᵥ x) = f x :=
    fun g x => hf g g.2 x
  rw [setAverage_eq, setAverage_eq, h1.setIntegral_eq h2 hinv]
  simp only [Measure.real, h1.measure_eq h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem emb_indep (g : (E →+* ℂ) → ℂ) (h : ∀ β : 𝓞 E, ∑ σ, σ (β : E) * g σ = 0) : g = 0 := by
  have hb : ∀ i, ∑ σ : E →+* ℂ, σ (integralBasis E i) * g σ = 0 := fun i => by
    rw [integralBasis_apply]
    exact h _
  have hE : ∀ x : E, ∑ σ : E →+* ℂ, σ x * g σ = 0 := by
    intro x
    rw [← (integralBasis E).sum_repr x]

    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ σ : E →+* ℂ, σ ((integralBasis E).repr x i • integralBasis E i) * g σ =
        ((integralBasis E).repr x i : ℂ) * (σ (integralBasis E i) * g σ) := fun σ => by
      rw [map_rat_smul, Rat.smul_def, mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, hb i, mul_zero]
  have hli : LinearIndependent ℂ (fun σ : E →+* ℂ => ((σ : E →* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
      (fun a b hab => RingHom.ext fun x => DFunLike.congr_fun hab x)
  rw [Fintype.linearIndependent_iff] at hli
  funext σ
  refine hli g ?_ σ
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hE x]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [mul_comm]

def ConjSymm (t : (E →+* ℂ) → ℂ) : Prop :=
  ∀ σ, t (ComplexEmbedding.conjugate σ) = (starRingEnd ℂ) (t σ)

theorem conjSymm_canonical (x : E) : ConjSymm (canonicalEmbedding E x) := fun σ => by
  simp only [canonicalEmbedding.apply_at, ComplexEmbedding.conjugate_coe_eq]

theorem conjSymm_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (v : ι → (E →+* ℂ) → ℂ)
    (hv : ∀ i, ConjSymm (v i)) : ConjSymm (∑ i ∈ s, c i • v i) := fun σ => by

  rw [Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, hv i σ, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

theorem eq_of_commMap (t t' : (E →+* ℂ) → ℂ) (ht : ConjSymm t) (ht' : ConjSymm t')
    (h : mixedEmbedding.commMap E t = mixedEmbedding.commMap E t') : t = t' := by
  funext σ
  obtain ⟨w, hwdef⟩ : ∃ w, w = InfinitePlace.mk σ := ⟨_, rfl⟩
  have hcases := InfinitePlace.embedding_mk_eq σ
  rw [← hwdef] at hcases
  have key : t w.embedding = t' w.embedding := by
    by_cases hw : w.IsReal
    · have h1 := congrArg (fun m => m.1 ⟨w, hw⟩) h
      simp only [mixedEmbedding.commMap_apply_of_isReal] at h1
      have hr : ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      have a1 : starRingEnd ℂ (t w.embedding) = t w.embedding := by rw [← ht, hr]
      have a2 : starRingEnd ℂ (t' w.embedding) = t' w.embedding := by rw [← ht', hr]
      apply Complex.ext h1
      rw [Complex.conj_eq_iff_im.mp a1, Complex.conj_eq_iff_im.mp a2]
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have h1 := congrArg (fun m => m.2 ⟨w, hw'⟩) h
      simpa only [mixedEmbedding.commMap_apply_of_isComplex] using h1
  rcases hcases with he | he
  · rw [he] at key
    exact key
  · rw [he, ht, ht'] at key
    simpa using congrArg (starRingEnd ℂ) key

theorem real_span (t : (E →+* ℂ) → ℂ) (ht : ConjSymm t) :
    ∃ c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      t = ∑ k, c k • canonicalEmbedding E (integralBasis E k) := by
  refine ⟨fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k, ?_⟩
  apply eq_of_commMap t _ ht (conjSymm_sum Finset.univ
    (fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k)
    (fun k => canonicalEmbedding E (integralBasis E k)) fun k => conjSymm_canonical _)

  rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (mixedEmbedding.latticeBasis E).sum_repr (mixedEmbedding.commMap E t)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, mixedEmbedding.commMap_canonical_eq_mixed]

theorem conjugate_ne [_root_.NumberField.IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.mpr h
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk σ))
    ⟨σ, hr, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

open scoped Matrix

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)

def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

def All : Prop :=
  PackingCount ∧ GaussianTailBound ∧ BallVolume ∧ GHadamard ∧ NearestPlane ∧ CauchyBinetMax ∧
    DetPerturbation ∧ DetPerturbNumeric ∧ DetProductRest

end ReciprocityTheory.ChartRestriction.G.I2.Ext
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open Real

theorem ct_expo_num (q c : ℕ) (hq : 1 ≤ q) {U y M1 r : ℝ} (hU : 0 ≤ U) (hy : 0 ≤ y)
    (hM : M1 ≤ q / 2) (hr0 : 0 ≤ r) (hr : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ≤ c)
    (ht : 28 * (c : ℝ) ≤ q * y ^ 2) :
    q * π * r ^ 2 / 2 + 2 * π * r * (U + q * y) - π * (q - M1) * y ^ 2 ≤
      1.07 * c - 1.33 * (q * y ^ 2) := by
  have hπ1 : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hS0 : 0 ≤ Real.sqrt (q * (c + 1)) := Real.sqrt_nonneg _
  have hS2 : Real.sqrt (q * (c + 1)) ^ 2 = q * (c + 1) := Real.sq_sqrt (by positivity)
  have hA : 0 ≤ 2 * π * r * U := by positivity
  have h1 : 2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) ≤ c := by
    linarith
  have ha0 : 0 ≤ r * Real.sqrt (q * (c + 1)) := mul_nonneg hr0 hS0
  have ha : r * Real.sqrt (q * (c + 1)) ≤ c / 5 := by linarith
  have hX : (q * r ^ 2) * (c + 1) = (r * Real.sqrt (q * (c + 1))) ^ 2 := by
    rw [mul_pow, hS2]; ring
  have hX0 : 0 ≤ q * r ^ 2 := by positivity
  have hXa : q * r ^ 2 ≤ (r * Real.sqrt (q * (c + 1))) / 5 := by
    have h2 : (q * r ^ 2) * (c + 1) ≤ (r * Real.sqrt (q * (c + 1))) / 5 * (c + 1) := by
      rw [hX]; nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have ht0 : 0 ≤ q * y ^ 2 := by positivity
  have hP : 2 * (r * q * y) ≤ 20 * (q * r ^ 2) + (q * y ^ 2) / 20 := by
    nlinarith [sq_nonneg (20 * (q * r ^ 2) - (q * y ^ 2) / 20)]
  have F1 : π * (q * r ^ 2) ≤ 3.15 * (q * r ^ 2) := mul_le_mul_of_nonneg_right hπ2.le hX0
  have F2 : π * (2 * (r * q * y)) ≤ π * (20 * (q * r ^ 2) + (q * y ^ 2) / 20) :=
    mul_le_mul_of_nonneg_left hP Real.pi_pos.le
  have F3 : π * (q * y ^ 2) ≤ 3.15 * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ2.le ht0
  have F3' : 3.14 * (q * y ^ 2) ≤ π * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ1.le ht0
  have F4 : π * (q / 2) * y ^ 2 ≤ π * (q - M1) * y ^ 2 := by
    have : (q : ℝ) / 2 ≤ q - M1 := by linarith
    have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
    nlinarith
  linarith [F1, F2, F3, F3', F4, h1, hXa, ha, ht, hA]

theorem ct_base_num (q c : ℕ) (hq : 1 ≤ q) {t0 : ℝ}
    (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0) :
    (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c ≤ Real.exp (0.14 * t0) := by
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero] at hC5 ⊢
    exact Real.one_le_exp (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hqc1 : (1 : ℝ) ≤ q * c := by nlinarith
  have hL0 : 0 ≤ Real.log (q * c) := Real.log_nonneg hqc1
  have hS : 0 < Real.sqrt (q * (c + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < 6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1)) := by positivity
  have hlogB : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) =
      Real.log 6.5 + 1.07 + Real.log (q * (c + 1)) / 2 := by
    rw [Real.log_mul (by positivity) hS.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt (by positivity)]
  have h65 : Real.log 6.5 ≤ 3 * Real.log 2 := by
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  have hqc : Real.log (q * (c + 1)) ≤ Real.log 2 + Real.log (q * c) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have key : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ≤
      0.56 * (7 + Real.log (q * c)) := by
    rw [hlogB]; linarith
  rw [← Real.exp_log hB, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left key hc0
  linarith

theorem ct_B_num (gA gB dK dst : ℕ) {t0 Bsq : ℝ} (hBsq0 : 0 ≤ Bsq) (hBsq : Bsq ≤ 12 * (5.12 : ℝ) ^ gB)
    (hgB : gB ≤ gA) (hdK : dK ≤ dst) (hC6 : (gA : ℝ) * Real.log 2 ≤ t0) :
    Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by
  have hsq : Real.sqrt Bsq ≤ 3.4642 * 2.263 ^ gA := by
    have hm : 12 * (5.12 : ℝ) ^ gB ≤ (3.4642 * 2.263 ^ gA) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm gA 2, pow_mul]
      apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
      calc (5.12 : ℝ) ^ gB ≤ (2.263 ^ 2) ^ gB := pow_le_pow_left₀ (by norm_num) (by norm_num) gB
        _ ≤ (2.263 ^ 2) ^ gA := pow_le_pow_right₀ (by norm_num) hgB
    calc Real.sqrt Bsq ≤ Real.sqrt ((3.4642 * 2.263 ^ gA) ^ 2) := Real.sqrt_le_sqrt (hBsq.trans hm)
      _ = 3.4642 * 2.263 ^ gA := Real.sqrt_sq (by positivity)
  have h3 : (2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0)) ≤ 2 ^ gA := by
    have hl : Real.log 2.263 * 100 ≤ Real.log 2 * 119 := by
      have h := Real.log_le_log (by positivity) (show (2.263 : ℝ) ^ 100 ≤ 2 ^ 119 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have hg0 : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
    have hm := mul_le_mul_of_nonneg_left hl hg0
    rw [← Real.exp_log (show (0 : ℝ) < 2.263 by norm_num), ← Real.exp_nat_mul,
      ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h4 : (3 : ℝ) ^ dK ≤ 4.3 ^ dst :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) dK).trans (pow_le_pow_right₀ (by norm_num) hdK)
  calc Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))
      ≤ (3.4642 * 2.263 ^ gA) * (2 * 4.3 ^ dst) * Real.exp (-(0.19 * t0)) := by gcongr
    _ = 6.9284 * ((2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0))) * 4.3 ^ dst := by ring
    _ ≤ 6.9284 * 2 ^ gA * 4.3 ^ dst := by gcongr
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by gcongr; norm_num

theorem jet_product_le (q c dK gA dst : ℕ) (hq : 1 ≤ q) {n U t0 Bsq : ℝ} (hn : 1 ≤ n) (hU0 : 0 ≤ U)
    (hU : 2 * π * U ≤ 1.5 * n) (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0)
    (hB : Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst) :
    (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hS1 : 1 ≤ Real.sqrt (q * (c + 1)) := Real.one_le_sqrt.mpr (by nlinarith)
  have hbase : 2 * π * U + 5 * Real.sqrt (q * (c + 1)) ≤ 6.5 * Real.sqrt (q * (c + 1)) * n := by
    nlinarith
  have hpow : (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c ≤
      (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c := by
    have e : (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) =
        (6.5 * Real.sqrt (q * (c + 1))) ^ c := by
      rw [mul_comm (6.5 : ℝ) (Real.exp 1.07), mul_assoc, mul_pow, ← Real.exp_nat_mul, mul_comm,
        ← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase c
  have hbn := ct_base_num q c hq hC5
  calc (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0))))
      ≤ (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) := by
        gcongr
    _ = (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
        (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        have : Real.exp (-(1.07 * c)) * Real.exp (1.07 * c) = 1 := by
          rw [← Real.exp_add]; simp
        linear_combination ((6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
          (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0))) * this
    _ ≤ Real.exp (0.14 * t0) * n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        gcongr
    _ = (Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))) * Real.exp (-t0) * n ^ c := by
        have : Real.exp (0.14 * t0) * Real.exp (-(1.33 * t0)) =
            Real.exp (-(0.19 * t0)) * Real.exp (-t0) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        linear_combination (n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK))) * this
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by gcongr

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem amgm_sum_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ℝ) (hP : 0 ≤ P) (hprod : P ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, a i := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (fun _ _ => zero_le_one)
    (by simpa using hn') (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ hn'] at h
  have h2 : P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
    Real.rpow_le_rpow hP hprod (by positivity)
  calc (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹)
      ≤ (Fintype.card ι : ℝ) * (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hn'.le
    _ = (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) * Fintype.card ι := mul_comm _ _
    _ ≤ ∑ i, a i := h

theorem inv_sq_rpow_inv (D : ℝ) (hD : 0 < D) (n : ℝ) :
    ((D ^ 2)⁻¹) ^ n⁻¹ = ((D ^ n⁻¹) ^ 2)⁻¹ := by
  rw [Real.inv_rpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (D ^ n⁻¹), ← Real.rpow_mul hD.le,
    ← Real.rpow_mul hD.le, mul_comm]

theorem sum_ge_of_prod_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : ℝ) (hD : 0 < D) (hprod : (D ^ 2)⁻¹ ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) / (D ^ ((Fintype.card ι : ℝ)⁻¹)) ^ 2 ≤ ∑ i, a i := by
  have h := amgm_sum_ge a ha _ (by positivity) hprod hn
  rwa [inv_sq_rpow_inv D hD, ← div_eq_mul_inv] at h

end ReciprocityTheory.ChartRestriction.G.I2
end
