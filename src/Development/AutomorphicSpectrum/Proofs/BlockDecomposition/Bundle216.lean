module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

private theorem sum_amat_first_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ a, Formalism.REAL.Amat l a j = l j - ((j : ℕ) : ℂ) := by
  have h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0) := by
    intro a
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : a = j
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  simp [sub_eq_add_neg]

private theorem sum_amat_second_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ b, Formalism.REAL.Amat l j b = l j - ((n - 1 - j : ℕ) : ℂ) := by
  have h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0) := by
    intro b
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : j = b
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi]
  simp [sub_eq_add_neg]

private theorem gelfVal_two_eq_sum_sq_sub_sq {n : ℕ} (c : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal c 2 = ∑ j, (c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
  have key : ∀ j : Fin n,
      (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
        (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) =
        c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2 := by
    intro j
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    rw [sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    ring
  calc GlobalTheory.Dec.gelfVal c 2
      = ∑ j, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
          (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) := by
        simp only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => key j

theorem conj_cas_of_isHerm {n : ℕ} {χ : Inf n} (h : IsHerm χ) : conj (cas χ) = cas χ := by
  obtain ⟨σ, hσ⟩ := h
  have hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2 := by
    rw [← Equiv.sum_comp σ (fun a => χ false a ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσ a, neg_sq]
  have hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2 := by
    have h2 := congrArg conj hT

    simpa [map_sum, map_pow] using h2.symm
  have hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) := by
    intro j
    simp only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]
  have hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) =
      ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
    intro x

    rw [gelfVal_two_eq_sum_sq_sub_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sub, map_pow, map_pow, hK]
  simp only [cas]
  rw [map_mul, map_add (f := _), hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]
  simp only [Finset.sum_sub_distrib]
  rw [hT, hF]
  ring

theorem conj_cosh_mul_sqrt {c : ℂ} (hc : conj c = c) (t : ℝ) :
    conj (Complex.cosh (t * c ^ (1 / 2 : ℂ))) = Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  have hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    have h := Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero
    simpa [one_div] using h
  have hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [← map_pow, hw2, hc]
  rw [← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · rw [h, mul_neg, Complex.cosh_neg]

theorem conj_coshT_cas : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T →
    conj (coshT g (cas χ)) = coshT g (cas χ) := by
  intro n χ g T hχ _
  have hc := conj_cas_of_isHerm hχ
  simp only [coshT]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Convolution
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.AvgJoint

theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun y : Mat n => y.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem avg_joint_smooth : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    IsBump g T → ContDiffOn ℝ ∞ (Function.uncurry fun t x => ∫ s, (g s : ℂ) • U (t + s) x) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ _ U g T hU hg
  obtain ⟨hgs, hev, hsupp⟩ := hg
  set S : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hS
  have hSo : IsOpen S := isOpen_univ.prod (isOpen_invertible_matrices n)
  let h : ℝ × Mat n → ℝ → V := fun p y => ((g (-y) : ℝ) : ℂ) • U (p.1 - y) p.2
  have hh : ContDiffOn ℝ ∞ (Function.uncurry h) (S ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => ((g (-q.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hgs.comp contDiff_snd.neg)
    have h2 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => (q.1.1 - q.2, q.1.2)) :=
      ((contDiff_fst.comp contDiff_fst).sub contDiff_snd).prodMk (contDiff_snd.comp contDiff_fst)
    have h3 : ContDiffOn ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => Function.uncurry U (q.1.1 - q.2, q.1.2)) (S ×ˢ Set.univ) := by
      refine hU.comp h2.contDiffOn ?_
      rintro ⟨⟨t, x⟩, y⟩ ⟨hp, -⟩
      exact ⟨Set.mem_univ _, hp.2⟩
    exact h1.contDiffOn.smul h3
  have hk : IsCompact (Metric.closedBall (0 : ℝ) |T|) := isCompact_closedBall 0 |T|
  have hz : ∀ p, ∀ x, p ∈ S → x ∉ Metric.closedBall (0 : ℝ) |T| → h p x = 0 := by
    intro p x _ hx
    have hx' : |T| < |x| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    have : g (-x) = 0 := hsupp _ (by rw [abs_neg]; exact lt_of_le_of_lt (le_abs_self T) hx')
    simp [h, this]
  have hloc : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) (volume : Measure ℝ) :=
    (continuous_const).locallyIntegrable
  have hc := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure ℝ)) (n := ⊤)
    (f := fun _ : ℝ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V) hSo hk hz hloc hh
  have hcomp : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((fun _ : ℝ => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h p) 0) S := by
    refine hc.comp (contDiff_id.prodMk contDiff_const).contDiffOn ?_
    intro p hp
    exact ⟨hp, Set.mem_univ _⟩
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ -
  simp [convolution_def, h, Function.uncurry]

end GlobalTheory.CompanionTheory.WaveMult.AvgJoint
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgBcC

def coneW (n : ℕ) (v : Fin n × Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (((hOf v).det.re ^ n)⁻¹)

def coneMeas (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  (volume.restrict (cone n)).withDensity (coneW n)

end GlobalTheory.CompanionTheory.ConeHaar
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveKer

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_germ (X : Mat n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Rd X f =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [Rd, Pi.zero_apply]
  rw [hy.fderiv_eq]
  have : fderiv ℝ (0 : Mat n → V) y = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : V)
  rw [this]
  rfl

theorem Eu_germ (s : Bool) (a b : Fin n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Eu s a b f =ᶠ[𝓝 x] 0 := by
  filter_upwards [Rd_germ (Matrix.single a b 1) h, Rd_germ (Matrix.single a b Complex.I) h]
    with y h1 h2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, Pi.zero_apply, smul_zero, add_zero]

theorem Epow_germ (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} {x : Mat n}
    (h : f =ᶠ[𝓝 x] 0) : Epow s m a b f =ᶠ[𝓝 x] 0 := by
  induction m generalizing a b with
  | zero =>
    by_cases hab : a = b
    · simpa [Epow, hab] using h
    · simp [Epow, hab]
  | succ m ih =>
    have : ∀ᶠ y in 𝓝 x, ∀ c, Eu s a c (Epow s m c b f) y = 0 :=
      eventually_all.2 fun c => Eu_germ s a c (ih c b)
    filter_upwards [this] with y hy
    simp [Epow, Finset.sum_apply, hy]

theorem gel_germ (s : Bool) (m : ℕ) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    gel s m f =ᶠ[𝓝 x] 0 := by
  have : ∀ᶠ y in 𝓝 x, ∀ a, Epow s m a a f y = 0 :=
    eventually_all.2 fun a => Epow_germ s m a a h
  filter_upwards [this] with y hy
  simp [gel, Finset.sum_apply, hy]

theorem zOp_germ (w : List (Bool × ℕ)) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    zOp w f =ᶠ[𝓝 x] 0 := by
  induction w with
  | nil => simpa [zOp] using h
  | cons p w ih => exact gel_germ p.1 p.2 ih

end Local

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem mul_mem_GLs {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [det_mul, h, mul_zero, det_one] at h1
  exact zero_ne_one h1

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage hc

theorem lg_one_nonneg (hL : LgFacts) (n : ℕ) : 0 ≤ lg (1 : Mat n) := by
  have h := (hL n).1 1 (one_mem_GLs n) 1 (one_mem_GLs n)
  rw [one_mul] at h
  linarith

theorem ker_support (hL : LgFacts) (hE : WaveEx) (hU : KerUniq) {n : ℕ}
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (c₀ : ℝ)
    (hc : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (t : ℝ), ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ c₀ * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0)
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)} (hT : 0 ≤ T)
    (hg : IsBump g T) (hk : IsKer μ E w g k) {y : Mat n} (hy : y ∈ GLs n)
    (hlt : (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) < lg y) : k y = 0 := by
  obtain ⟨hsub, -, hinv, hsm, -, -, -⟩ := hL n
  have hL0 := lg_one_nonneg hL n
  have hM0 : 0 ≤ max c₀ 0 := le_max_right _ _
  have hGo := isOpen_GLs n
  set A : ℝ := (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) with hA
  have hUo : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi A) :=
    hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Ioi
  refine hU n μ E k (GLs n ∩ lg ⁻¹' Set.Ioi A) hUo Set.inter_subset_left ?_
    hk.1.continuousOn ?_ ?_ y ⟨hy, hlt⟩
  · intro z hz k₂
    refine ⟨mul_mem_GLs hz.1 (unitary_mem_GLs k₂), ?_⟩
    have h := hinv z hz.1 1 k₂
    simp only [OneMemClass.coe_one, one_mul] at h
    simpa [h] using hz.2
  · intro z hz k₂
    have h := hk.2.2.1 z hz 1 k₂
    simpa using h
  · intro f hf _ hoff
    obtain ⟨u, hu, hu0⟩ := hE n E f hf
    have hact : act μ E k f 1 = act μ E k (u 0) 1 := by
      simp only [act]
      congr 1
      funext z
      rw [one_mul, hu0 _ (val_mem_GLs z)]
    have hzero : ∀ x ∈ GLs n, lg x < lg (1 : Mat n) + 1 → ∀ t, |t| ≤ T → u t x = 0 := by
      intro x hx hlx t ht
      refine hc E u hu t x hx fun z hz hlz => ?_
      rw [hu0 _ (mul_mem_GLs hx hz)]
      refine hoff _ (mul_mem_GLs hx hz) ?_
      rintro ⟨-, hbig⟩
      have hbig' : A < lg (x * z) := hbig
      have h0 := hsub x hx z hz
      have h1 : c₀ * (1 + |t|) ≤ max c₀ 0 * (1 + |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h2 : max c₀ 0 * (1 + |t|) ≤ max c₀ 0 * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0
      have h3 : lg (1 : Mat n) + 1 ≤ (lg (1 : Mat n) + 1) * (1 + T) := by nlinarith
      have h4 : A = max c₀ 0 * (1 + T) + (lg (1 : Mat n) + 1) * (1 + T) := by rw [hA]; ring
      linarith
    have hF : (fun x' => ∫ t, (g t : ℂ) • u t x') =ᶠ[𝓝 (1 : Mat n)] 0 := by
      have hN : GLs n ∩ lg ⁻¹' Set.Iio (lg (1 : Mat n) + 1) ∈ 𝓝 (1 : Mat n) :=
        (hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Iio).mem_nhds
          ⟨one_mem_GLs n, Set.mem_preimage.2 (Set.mem_Iio.2 (lt_add_one _))⟩
      filter_upwards [hN] with x hx
      have h0 : ∀ t, (g t : ℂ) • u t x = 0 := by
        intro t
        by_cases ht : |t| ≤ T
        · rw [hzero x hx.1 hx.2 t ht, smul_zero]
        · rw [hg.2.2 t (not_le.1 ht)]
          simp
      simp [h0]
    rw [hact, hk.2.2.2 u hu 1 (one_mem_GLs n)]
    exact (zOp_germ w hF).self_of_nhds

theorem asmKerEx : AsmKerEx := by
  intro hL _ hS hE hU hO n
  obtain ⟨c₀, hc⟩ := hS n
  refine ⟨max c₀ 0 + lg (1 : Mat n) + 1, ?_⟩
  intro _ _ μ _ E
  refine ⟨fun w g T hg => hO n μ E w g T hg, ?_⟩
  rintro k val T hT ⟨m, c, w, g, ks, hi, hsum, -⟩ y hy hlt
  rw [hsum y hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ker_support hL hE hU μ E c₀ hc hT (hi i).1 (hi i).2 hy hlt, smul_zero]

end GlobalTheory.CompanionTheory.WaveKer
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

end GlobalTheory.CompanionTheory.WaveK.Base
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SobGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Idx (n : ℕ) := Bool × Fin n × Fin n

def cm {n : ℕ} (t : Idx n → ℝ) : Mat n := ∑ p, t p • bs p

def pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List ι → ((ι → ℝ) → V) → ((ι → ℝ) → V) :=
  fun L F => L.foldr (fun i H t => fderiv ℝ H t (Pi.single i 1)) F

def Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Idx n) → (Mat n → V) → (Mat n → V) :=
  fun L f => L.foldr (fun p H y => fderiv ℝ H y (bs p)) f

theorem pd_nil {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ι → ℝ) → V) : pd [] F = F := rfl

theorem pd_cons {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (L : List ι) (F : (ι → ℝ) → V) :
    pd (i :: L) F = fun t => fderiv ℝ (pd L F) t (Pi.single i 1) := rfl

theorem Dw_nil {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Mat n → V) :
    Dw [] f = f := rfl

theorem Dw_cons {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Idx n)
    (L : List (Idx n)) (f : Mat n → V) :
    Dw (p :: L) f = fun y => fderiv ℝ (Dw L f) y (bs p) := rfl

end GlobalTheory.CompanionTheory.SobGL
end
end

section

noncomputable section

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

def Lap {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) : Mat n → V :=
  fun g => -∑ p, Rd (bs p) (Rd (bs p) f) g

end GlobalTheory.CompanionTheory.FcSmooth
end
end
