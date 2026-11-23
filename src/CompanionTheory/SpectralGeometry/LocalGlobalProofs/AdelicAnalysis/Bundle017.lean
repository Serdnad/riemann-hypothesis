module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle012
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BlockAlg

section Entries

variable {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)

theorem blockOne_zero_zero : blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

end Entries

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : (blockOne t A).submatrix Fin.succ (Fin.succAbove (0 : Fin (M + 1))) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [h0, Finset.sum_eq_zero]
  · simp [blockOne_zero_zero]
  · intro j _
    simp [blockOne_zero_succ]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_blockOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t a b : E)
    (x y : Fin M → E) :
    hE σ (blockOne t J) (Fin.cons a x : Fin (M + 1) → E) (Fin.cons b y : Fin (M + 1) → E) =
      σ a * t * b + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, blockOne_zero_zero,
    blockOne_zero_succ, blockOne_succ_zero, blockOne_succ_succ]
  simp

theorem hE_zero_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y : Fin M → E) :
    hE σ J 0 y = 0 := by
  simp [hE, hform]

theorem hE_zero_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    hE σ J x 0 = 0 := by
  simp [hE, hform]

theorem gramE_consTup (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) {n : ℕ}
    (X : Fin n → Fin M → E) :
    gramE σ (blockOne t J) (consTup X) = blockOne t (gramE σ J X) := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 1 (fun _ => 0)) = t
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 0 (X b)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 1 (fun _ => 0)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_right]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 0 (X b)) = hE σ J (X a) (X b)
    rw [hE_blockOne_cons]
    simp

theorem exists_consTup_of_gramE (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E}
    (ht : t ≠ 0) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E)
    (h0 : Y 0 = Fin.cons 1 (fun _ => 0)) (hY : gramE σ (blockOne t J) Y = blockOne t T) :
    ∃ X, gramE σ J X = T ∧ Y = consTup X := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hsplit : ∀ a : Fin n, Y a.succ = Fin.cons (Y a.succ 0) (Fin.tail (Y a.succ)) := fun a =>
    (Fin.cons_self_tail _).symm
  have hfirst : ∀ a : Fin n, Y a.succ 0 = 0 := by
    intro a
    have h := congrFun (congrFun hY 0) a.succ
    change hE σ (blockOne t J) (Y 0) (Y a.succ) = blockOne t T 0 a.succ at h
    rw [h0, hsplit a, hE_blockOne_cons, hz, hE_zero_left, blockOne_zero_succ] at h
    simpa [ht] using h
  have hY' : ∀ a : Fin n, Y a.succ = Fin.cons 0 (Fin.tail (Y a.succ)) := by
    intro a
    conv_lhs => rw [hsplit a, hfirst a]
  refine ⟨fun a => Fin.tail (Y a.succ), ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun hY a.succ) b.succ
    change hE σ (blockOne t J) (Y a.succ) (Y b.succ) = blockOne t T a.succ b.succ at h
    rw [hY' a, hY' b, hE_blockOne_cons, blockOne_succ_succ] at h
    change hE σ J (Fin.tail (Y a.succ)) (Fin.tail (Y b.succ)) = T a b
    simpa using h
  · funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact h0
    · exact hY' a

theorem block_alg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  intro F E _ _ _ _ _ σ _ M J t
  refine ⟨det_blockOne _ _, ?_, fun n X => gramE_consTup σ J _ X, ?_⟩
  · intro hJ a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ a b
  · intro ht n T Y h0 hY
    have ht' : algebraMap F E t ≠ 0 := by
      simpa using ht
    exact exists_consTup_of_gramE σ J ht' T Y h0 hY

end GlobalTheory.CompanionTheory.SW.BlockAlg
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatRat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv

def latR {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

def Good {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) : Prop :=
  ∀ k l, algebraMap F (Fv F v) (b.repr (b k * e) l) ∈ v.adicCompletionIntegers F

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (y : Fv F v ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (y * inclR (Fv F v) e) l =
      ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        algebraMap F (Fv F v) (b.repr (b k * e) l) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]

  rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  simp [inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

theorem mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)

theorem sum_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k

  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k

theorem eventually_good {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Good b v e :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _

theorem eventually_good_matrix {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _

omit [NumberField F] in
theorem rmul_rmul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [NumberField F] in
theorem rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : Matrix (Fin n) (Fin n) E} (hg : ∀ i j, Good b v (g i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v := by
  intro a i
  exact sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))

theorem actTup_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))

omit [NumberField F] in
theorem actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by
  funext a
  simp only [actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem one_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem consTup_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i

theorem latV_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b n M
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X
    refine ⟨fun hX => ?_, rmul_mem h1⟩
    have hmul : g.map (inclR (F := F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.map_one _ (map_zero _) (map_one _)]
    have := rmul_mem h2 hX
    rwa [rmul_rmul, hmul, rmul_one] at this
  · filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E),
      eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X
    refine ⟨fun hX => ?_, actTup_mem h1⟩
    have := actTup_mem (g := g⁻¹) h2 hX
    rwa [actTup_inv] at this
  · have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
        algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k)
    filter_upwards [h0] with v h X
    exact consTup_mem_iff h X

end GlobalTheory.CompanionTheory.SW.LatRat
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramEmpty

theorem fibre_eq_dirac_of_unique {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by
  have h1 := h (fun _ => 1) measurable_const
  have hc : (fun b => ∫⁻ _, (1 : ℝ≥0∞) ∂(m b)) = fun _ => m S Set.univ := by
    funext b
    rw [Subsingleton.elim b S]
    simp
  rw [hc] at h1
  simp only [lintegral_const, one_mul, hμ, hν, mul_one] at h1
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Subsingleton.eq_univ_of_nonempty hs, ← h1]
    simp

end GlobalTheory.CompanionTheory.SW.GramEmpty

open GlobalTheory.CompanionTheory.SW.GramEmpty in
theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ d b lam _ m hm S
  obtain ⟨-, h2, -⟩ := hm
  haveI : Subsingleton (HermR R σ 0) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ := by
    ext X
    simp
  have hμ : coordW R b lam 0 M Set.univ = 1 := by
    unfold coordW
    rw [Measure.pi_of_empty]
    simp
  have hν : coordHerm R σ b lam 0 Set.univ = 1 := by
    unfold coordHerm
    rw [Measure.comap_apply _ (Function.injective_of_subsingleton _)
      (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
    have : (Set.univ : Set ((Fin 0 → R) × ({p : Fin 0 × Fin 0 // p.1 < p.2} → R ⊗[F] E))) =
        Set.univ ×ˢ Set.univ := by simp
    rw [Set.image_univ_of_surjective, this, Measure.prod_prod, Measure.pi_of_empty, Measure.pi_of_empty]
    · simp
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine fibre_eq_dirac_of_unique _ _ m _ hμ hν (fun φ hφ => ?_) S
  have := h2 φ hφ
  rw [hU, Measure.restrict_univ] at this
  exact this
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hform_mulVec {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ x y : Fin m → A, hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [key, key, hs]
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  congr 1
  change cT σ g *ᵥ (J *ᵥ (g *ᵥ y)) = J *ᵥ y
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

theorem isClosed_HR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) _) := by
    refine ((Continuous.matrix_transpose (Continuous.matrix_map hv hs)).matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

end

theorem topH_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3, h4, hs, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl := isClosed_HR R σ hs J
  haveI g1 : IsTopologicalGroup (HR R σ J) := inferInstance
  haveI g2 : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI g3 : SecondCountableTopology (HR R σ J) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI g4 : T2Space (HR R σ J) := inferInstance
  refine ⟨g1, g2, g3, g4, ⟨rfl⟩, fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) =>
        ((HA.mat R σ J p.1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    exact continuous_pi fun a => hm.matrix_mulVec ((continuous_apply a).comp continuous_snd)
  · intro X
    funext a
    exact Matrix.one_mulVec (X a)
  · intro g h X
    funext a
    change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (HA.mat R σ J h : Matrix (Fin M) (Fin M) _)) *ᵥ X a = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  · intro h X
    funext a b
    exact hform_mulVec (sigR R σ) (JR R J) _ h.2 (X a) (X b)

end GlobalTheory.CompanionTheory.SW.TopH
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Rescale

theorem isGramFib_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ n μ ν m _ _ h a c _ hc
  exact isFibreFamily_rescale _ _ _ μ ν _ _ _ _ m h a c hc

end GlobalTheory.CompanionTheory.SW.Rescale
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.adelic_character_exponential_formula : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ a y : ι → F, chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | exact GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.gram_transpose_dual_trace_identity : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | exact GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace <;> assumption)
end
