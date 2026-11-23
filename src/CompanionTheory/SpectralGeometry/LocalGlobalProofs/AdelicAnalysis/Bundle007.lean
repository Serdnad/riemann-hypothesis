module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Coprime.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonal
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Iwasawa

variable {F : Type} [Field F] [NumberField F]

def IntAt (b : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  algebraMap F (A F) b v ∈ v.adicCompletionIntegers F


open Classical in
def idem (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : IntAt b v
    · simpa [h] using (v.adicCompletionIntegers F).one_mem
    · simpa [h] using (v.adicCompletionIntegers F).zero_mem⟩


open Classical in
def scale (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else (algebraMap F (A F) b v)⁻¹,
    Filter.Eventually.of_forall fun v => by
      by_cases h : IntAt b v
      · simpa [h] using (v.adicCompletionIntegers F).one_mem
      · simpa [h] using ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h⟩


open Classical in
def scaleInv (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else algebraMap F (A F) b v, by
    filter_upwards [(algebraMap F (A F) b).2] with v hv
    have h : IntAt b v := hv
    simpa [h] using (v.adicCompletionIntegers F).one_mem⟩

theorem mul_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x * y) v = x v * y v := rfl
theorem add_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x + y) v = x v + y v := rfl
theorem sub_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x - y) v = x v - y v := rfl
theorem one_at (v : HeightOneSpectrum (𝓞 F)) : (1 : A F) v = 1 := rfl

theorem idem_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : idem b v = 1 :=
  if_pos h
theorem idem_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) : idem b v = 0 :=
  if_neg h
theorem scale_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scale b v = 1 :=
  if_pos h
theorem scale_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scale b v = (algebraMap F (A F) b v)⁻¹ :=
  if_neg h
theorem scaleInv_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scaleInv b v = 1 :=
  if_pos h
theorem scaleInv_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scaleInv b v = algebraMap F (A F) b v :=
  if_neg h

theorem ne_zero_of_not_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    algebraMap F (A F) b v ≠ 0 := fun h0 =>
  h (by unfold IntAt; rw [h0]; exact (v.adicCompletionIntegers F).zero_mem)

theorem scale_mul_scaleInv (b : F) : scale b * scaleInv b = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [mul_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, scaleInv_int h, one_mul]
  · rw [scale_not h, scaleInv_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]

theorem scale_combo (b : F) :
    scale b * idem b + (1 - idem b) * (scale b * algebraMap F (A F) b) = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [add_at, mul_at, mul_at, mul_at, sub_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, idem_int h]; ring
  · rw [scale_not h, idem_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]; ring

theorem idem_mem (b : F) : idem b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [idem_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [idem_not h]; exact (v.adicCompletionIntegers F).zero_mem

theorem scale_mem (b : F) : scale b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [scale_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [scale_not h]
    exact ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h

theorem Oh_one : (1 : A F) ∈ Oh F := fun v => (v.adicCompletionIntegers F).one_mem

theorem Oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).neg_mem _ (hx v)

theorem Oh_sub {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).sub_mem (hx v) (hy v)

theorem Oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).mul_mem _ _ (hx v) (hy v)

theorem scale_mul_mem (b : F) : scale b * algebraMap F (A F) b ∈ Oh F := fun v => by
  rw [mul_at]
  by_cases h : IntAt b v
  · rw [scale_int h, one_mul]; exact h
  · rw [scale_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]
    exact (v.adicCompletionIntegers F).one_mem

def scaleUnit (b : F) : (A F)ˣ :=
  ⟨scale b, scaleInv b, scale_mul_scaleInv b, by rw [mul_comm]; exact scale_mul_scaleInv b⟩

def kMat (b : F) : SL(2, A F) :=
  ⟨!![idem b - 1, idem b; -scale b, -(scale b * algebraMap F (A F) b)], by
    rw [Matrix.det_fin_two_of]
    linear_combination scale_combo b⟩

theorem image_scale (b : F) :
    (fun x => scale b * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨Oh_mul (scale_mem b) ho, ?_⟩
    have : algebraMap F (A F) b * (scale b * o) = (scale b * algebraMap F (A F) b) * o := by ring
    show algebraMap F (A F) b * (scale b * o) ∈ Oh F
    rw [this]
    exact Oh_mul (scale_mul_mem b) ho
  · rintro ⟨hx, hbx⟩
    refine ⟨scaleInv b * x, fun v => ?_, ?_⟩
    · rw [mul_at]
      by_cases h : IntAt b v
      · rw [scaleInv_int h, one_mul]; exact hx v
      · rw [scaleInv_not h]; exact hbx v
    · show scale b * (scaleInv b * x) = x
      rw [← mul_assoc, scale_mul_scaleInv, one_mul]

theorem w_n_eq {R : Type} [CommRing R] (β e : R) (u : Rˣ) (k : SL(2, R))
    (h00 : k 0 0 = e - 1) (h01 : k 0 1 = e) (h10 : k 1 0 = -(u : R))
    (h11 : k 1 1 = -((u : R) * β)) (h : (u : R) * e + (1 - e) * ((u : R) * β) = 1) :
    wMat * nMat β = nMat ((e - 1) * (u : R)) * mMat u * k := by
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hk : (k : Matrix (Fin 2) (Fin 2) R) = !![e - 1, e; -(u : R), -((u : R) * β)] := by
    rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) R), h00, h01, h10, h11]
  apply Subtype.ext
  change (!![0, 1; -1, 0] * !![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) R) =
    !![1, (e - 1) * (u : R); 0, 1] * !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] *
      (k : Matrix (Fin 2) (Fin 2) R)
  rw [hk]
  simp only [Matrix.mul_fin_two]
  have entries : ∀ a b c d a' b' c' d' : R, a = a' → b = b' → c = c' → d = d' →
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d'] := by
    rintro _ _ _ _ _ _ _ _ rfl rfl rfl rfl
    rfl
  refine entries _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination ((e - 1) * (u : R)) * hu
  · linear_combination -h + ((e - 1) * (u : R) * β) * hu
  · linear_combination hu
  · linear_combination β * hu

theorem iwasawa_w_n : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F,
    ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧
      wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧
      (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  intro F _ _ b
  refine ⟨(idem b - 1) * scale b, scaleUnit b, kMat b, ?_, ?_, image_scale b⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact Oh_sub (idem_mem b) Oh_one
    · exact idem_mem b
    · exact Oh_neg (scale_mem b)
    · exact Oh_neg (scale_mul_mem b)
  · exact w_n_eq _ (idem b) (scaleUnit b) (kMat b) rfl rfl rfl rfl (scale_combo b)

end GlobalTheory.CompanionTheory.SW.Iwasawa
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
  have h2 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]

theorem expand {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (u : R ⊗[F] E) :
    u = ∑ k, ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr u]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

def trGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

theorem trace_entry [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * ((1 : R) ⊗ₜ[F] e) * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  conv_lhs => rw [expand b R u, expand b R v]

  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : sigR R σ (((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k) =
      ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] σ (b k) := by
    simp [sigR]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul]
  simp only [mul_one]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem trace_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig h)) (AlgHom.ext (sig_sig h))) x

theorem trGram_isSymm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).IsSymm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, trGram]
  rw [← trace_sig h (σ (b l) * J j i * b k)]
  simp only [map_mul, sig_sig h, hJ.1]
  congr 1
  ring

theorem trGram_det_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set y : Fin M → E := fun j => ∑ l, v (j, l) • b l with hy
  have key : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h0 := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, trGram, Pi.zero_apply] at h0
    rw [← h0]

    simp only [Matrix.mulVec, dotProduct, hy, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have key2 : ∀ i (e : E), Algebra.trace F E (e * (J *ᵥ y) i) = 0 := by
    intro i e
    have he : e = ∑ k, (b.repr (σ e) k) • σ (b k) := by
      have h3 := congrArg σ (b.sum_repr (σ e))

      rw [sig_sig h, map_sum] at h3
      exact h3.symm.trans (Finset.sum_congr rfl fun k _ => σ.toLinearMap.map_smul _ _)
    rw [he]

    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, key, smul_zero,
    Finset.sum_const_zero]
  have hw : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact key2 i e
  have hy0 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hw
  apply hv
  funext ⟨j, l⟩
  have := congrFun hy0 j
  have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun l => v (j, l)) this l
  simpa using h2

end CM

end GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem trace_form_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2) := by
  intro F E _ _ _ _ _ σ h M J hJ d b
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite b
  refine ⟨TraceFormGram.trGram σ J b, TraceFormGram.trGram_isSymm h hJ b, TraceFormGram.trGram_det_ne_zero h hJ b, ?_⟩
  intro R _ _ x y
  have hh : hR R σ J x y = ∑ i, ∑ j, sigR R σ (x i) * ((1 : R) ⊗ₜ[F] J i j) * y j := rfl
  rw [hh]

  simp only [map_sum, TraceFormGram.trace_entry σ b R]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply, TraceFormGram.trGram,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end GlobalTheory.CompanionTheory.SW
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]


omit [IsTopologicalRing R] in
theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def coordHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem isHomeomorph_coord {d : ℕ} (b : Module.Basis (Fin d) F E) :
    IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k :=
  (coordHomeo R b).isHomeomorph

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

omit [IsTopologicalRing R] in
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem continuous_trace [Module.Finite F E] : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  exact IsModuleTopology.continuous_of_linearMap _

end

theorem topTens_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e := coordHomeo R (Module.finBasis F E)
  haveI h1 : IsTopologicalRing (R ⊗[F] E) := isTopRing R
  haveI h2 : LocallyCompactSpace (R ⊗[F] E) := e.isOpenEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI h4 : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  haveI h5 : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hs := continuous_sigR R σ
  refine ⟨h1, h2, h3, h4, hs, continuous_trace R, fun d b => isHomeomorph_coord R b,
    fun n M => inferInstance, fun n => ?_, fun n M J => ?_⟩
  · have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold gramR hR hform
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end GlobalTheory.CompanionTheory.SW.TopK
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.matrix_induction_transvection_diagonal : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | exact GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | (intros; apply GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_covolume_unimodular : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_compact_for_measure_preserving_endos : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ → ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C → (∀ y, ∃ l, y - j l ∈ C) → ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ → ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | exact GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | (intros; apply GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.group_action_haar_scaling_continuous : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V), (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) → (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) → ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | exact GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | (intros; apply GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus <;> assumption)
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V') [μ'.IsAddHaarMeasure] (e : V ≃+ V'), Continuous e → Continuous e.symm → (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧ ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty → (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | exact GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar | (intros; apply GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar <;> assumption)
end
