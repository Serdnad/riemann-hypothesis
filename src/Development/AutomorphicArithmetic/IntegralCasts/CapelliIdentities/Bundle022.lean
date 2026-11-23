module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

namespace UpperTheory.Reformulated.B.InvolutionInvariants

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {n} ε => Matrix.diagonal fun a => if ε a = Bool.true then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {n} ε g =>
    g.conjTranspose * Jm ε * g =
      Jm ε

theorem aux3 : ∀ {n : ℕ} (ε : Fin n → Bool)
  {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
      g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g h hg hh
  change inUJ ε _ at hg hh ⊢
  unfold inUJ at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h.val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val) * h.val := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem aux4 : ∀ {n : ℕ} (ε : Fin n → Bool),
  (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 =
    Jm ε := by
  intro n ε
  simp

theorem aux5 : ∀ {n : ℕ} (ε : Fin n → Bool)
  {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g hg
  change inUJ ε _ at hg ⊢
  unfold inUJ at hg ⊢
  have h1 : g.val * (g⁻¹).val = 1 := Units.mul_inv g
  calc _ = ((g⁻¹).val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val)
          * (g⁻¹).val := by rw [hg]
    _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

noncomputable def UJ : {n : ℕ} →
  (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  fun {n} ε =>
    { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val},
      mul_mem' := @aux3 n ε,
      one_mem' := aux4 ε,
      inv_mem' := @aux5 n ε }

@[reducible] noncomputable def instMeasurableSpaceUJ : (n : ℕ) →
  (ε : Fin n → Bool) → MeasurableSpace ↥(UJ ε) :=
  fun n ε => borel ↥(UJ ε)

attribute [local instance] instMeasurableSpaceUJ

theorem aux8 : ∀ {n : ℕ} (ε : Fin n → Bool),
  IsTopologicalGroup ↥(UJ ε) := by
  intro n ε
  infer_instance

theorem aux9 : ∀ (n : ℕ) (ε : Fin n → Bool),
  BorelSpace ↥(UJ ε) := by
  intro n ε
  exact ⟨rfl⟩

theorem laurent_T_neg_one_mul_T_one : ∀ (n : ℕ) (ε : Fin n → Bool),
  LocallyCompactSpace ↥(UJ ε) := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      (g.val).conjTranspose * Jm ε * g.val = Jm ε} :=
    isClosed_eq ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const
  exact hc.locallyCompactSpace

noncomputable def muG : {n : ℕ} →
  (ε : Fin n → Bool) → MeasureTheory.Measure ↥(UJ ε) :=
  fun {n} ε => by
    letI := aux8 ε
    letI := aux9 n ε
    letI := laurent_T_neg_one_mul_T_one n ε
    exact MeasureTheory.Measure.haar

noncomputable def Unimodular : Prop :=
∀ (n : ℕ) (ε : Fin n → Bool) (g : ↥(UJ ε)),
  MeasureTheory.Measure.map (fun x => x * g) (muG ε) =
    muG ε

noncomputable def InvInvariant : Prop :=
∀ (n : ℕ) (ε : Fin n → Bool),
  MeasureTheory.Measure.map (fun x => x⁻¹) (muG ε) =
    muG ε

open scoped Pointwise in
open MeasureTheory MeasureTheory.Measure in
private theorem haar_map_inv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (h : ∀ g : G, Measure.map (fun x => x * g) (haar : Measure G) = haar) :
    Measure.map (fun x => x⁻¹) (haar : Measure G) = haar := by
  haveI : (haar : Measure G).IsMulRightInvariant := ⟨h⟩
  haveI : (haar : Measure G).Regular := regular_haarMeasure
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, (haar : Measure G).inv = c • haar :=
    ⟨haarScalarFactor (haar : Measure G).inv haar,
      isMulLeftInvariant_eq_smul_of_regular (haar : Measure G).inv haar⟩
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : (haar : Measure G) K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : (haar : Measure G) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h1 : ∀ s : Set G, (haar : Measure G) s⁻¹ = c * haar s := fun s => by
    rw [← MeasureTheory.Measure.inv_apply, hc, Measure.smul_apply, smul_eq_mul]
  have h2 : c ^ 2 * (haar : Measure G) K = 1 ^ 2 * (haar : Measure G) K := by
    rw [pow_two, mul_assoc, ← h1, ← h1, inv_inv, one_pow, one_mul]
  have h3 : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj h0 ht).1 h2)
  rw [h3, one_smul] at hc
  exact hc

theorem invInvariant_of : Unimodular →
  InvInvariant := by
  intro h n ε
  haveI := aux8 ε
  haveI := aux9 n ε
  haveI := laurent_T_neg_one_mul_T_one n ε
  exact haar_map_inv (G := ↥(UJ ε)) (h n ε)

end UpperTheory.Reformulated.B.InvolutionInvariants
end

section

namespace UpperTheory.Reformulated.B.DYhb7

open NumberField NumberField.InfinitePlace Finset

private lemma algebra_trace_pi_eq_sum_trace {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (x : ι → A) :
    Algebra.trace ℝ (ι → A) x = ∑ i, Algebra.trace ℝ A (x i) := by
  classical
  let b := Module.Free.chooseBasis ℝ A
  let B := Pi.basis (fun _ : ι => b)
  rw [Algebra.trace_eq_matrix_trace B]
  simp_rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  simp [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply]

open scoped Classical in
private lemma fiber_embeddings_eq_pair {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    ({φ | mk φ = w} : Finset (F →+* ℂ)) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  conv_lhs => rw [← mk_embedding w, mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; simp [ComplexEmbedding.conjugate])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; simp [ComplexEmbedding.conjugate])

open scoped Classical in
private lemma sum_embeddings_eq_real_add_complex {F : Type} [Field F] [NumberField F] (y : F) :
    ∑ φ : F →+* ℂ, φ y =
      (∑ w : {w : InfinitePlace F // IsReal w}, (embedding_of_isReal w.2 y : ℂ)) +
      ∑ w : {w : InfinitePlace F // IsComplex w}, (((2 * (w.1.embedding y).re : ℝ)) : ℂ) := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => mk φ), sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, conjugate_embedding_eq_of_isReal w.2]
    simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, Finset.sum_pair]
    · rw [ComplexEmbedding.conjugate_coe_eq]
      push_cast
      rw [Complex.add_conj]
      push_cast
      rfl
    · intro h
      exact (isComplex_iff.mp w.2) (ComplexEmbedding.isReal_iff.mpr h.symm)

end UpperTheory.Reformulated.B.DYhb7

theorem UpperTheory.Reformulated.B.DYhb7.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
      (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
          ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
        (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  apply Complex.ofReal_injective
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ y := by
    have := _root_.trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f y) _ fun _ => by
      simp [RingHom.equivRatAlgHom_apply]).symm
  rw [Complex.ofReal_ratCast, h1, UpperTheory.Reformulated.B.DYhb7.sum_embeddings_eq_real_add_complex, Algebra.trace_prod_apply,
    UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace, UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace]
  simp [Algebra.trace_complex_apply]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf27.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qf27.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qf27.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qf27.infEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ τ θ θ' h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ c : F, (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F) c) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] (algebraMap F E c) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : (fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h2 h2' ?_
    funext c
    simp only [Function.comp_apply]
    rw [key, h1, h1']
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h1, h1', congrFun hA a]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh26.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qh26.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qh26.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qh26.isInfEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] (τ : E →+* ℂ)
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ _ τ θ θ' h h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ x : F, (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F) x) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : (fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h.2 h'.2 ?_
    funext x
    simp only [Function.comp_apply]
    rw [key, h.1, h'.1]
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    have hs : a ⊗ₜ[F] e = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs, map_mul, map_mul, h.1, h'.1, congrFun h1 a]
end

section

private def UpperTheory.Reformulated.B.ShiftMap.shift {G H : Type} [Group G] [Group H] (p : G →* H) :
    G →* ((H → ℂ) →ₗ[ℂ] (H → ℂ)) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun z => (p g)⁻¹ * z)
  map_one' := by
    ext φ z
    simp [LinearMap.funLeft]
  map_mul' g h := by
    ext φ z
    simp [LinearMap.funLeft, mul_assoc]

private lemma UpperTheory.Reformulated.B.ShiftMap.shift_apply {G H : Type} [Group G] [Group H] (p : G →* H)
    (g : G) (φ : H → ℂ) (z : H) : UpperTheory.Reformulated.B.ShiftMap.shift p g φ z = φ ((p g)⁻¹ * z) := rfl

theorem UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : Group H] [inst_4 : TopologicalSpace H] [IsTopologicalGroup H] (p : G →* H),
    Continuous (⇑p : G → H) →
      ∀ (f : H → ℂ),
        Continuous f →
          FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f (((p : G → H) k)⁻¹ * z))) →
            ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ),
              Continuous (⇑ρ : G → Matrix (Fin d) (Fin d) ℂ) ∧
                ∀ (x : G →₀ ℂ),
                  (x.sum fun (k : G) (c : ℂ) ↦ c • (ρ : G → Matrix (Fin d) (Fin d) ℂ) k) =
                      (0 : Matrix (Fin d) (Fin d) ℂ) →
                    ∀ (z : H), (x.sum fun (k : G) (c : ℂ) ↦ c * f (((p : G → H) k)⁻¹ * z)) = (0 : ℂ) := by
  intro G H _ _ _ _ _ _ p hp f hf hfd
  set V : Submodule ℂ (H → ℂ) :=
    Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f ((p k)⁻¹ * z)) with hV
  have hinv : ∀ g : G, ∀ φ ∈ V, UpperTheory.Reformulated.B.ShiftMap.shift p g φ ∈ V := by
    intro g
    have h : V ≤ V.comap (UpperTheory.Reformulated.B.ShiftMap.shift p g) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨g * k, ?_⟩
      funext z
      simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc]
    exact fun φ hφ => h hφ
  have hcont : ∀ φ ∈ V, Continuous φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨k, rfl⟩ := h
      exact hf.comp (continuous_const.mul continuous_id)
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hfV : f ∈ V := Submodule.subset_span ⟨1, by funext z; simp⟩
  let σ : G →* (V →ₗ[ℂ] V) :=
    { toFun := fun g => (UpperTheory.Reformulated.B.ShiftMap.shift p g).restrict (hinv g)
      map_one' := by
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply]
      map_mul' := by
        intro g h
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc] }
  have hσ : ∀ (g : G) (φ : V) (z : H), (σ g φ : H → ℂ) z = (φ : H → ℂ) ((p g)⁻¹ * z) :=
    fun _ _ _ => rfl
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  refine ⟨Module.finrank ℂ V, (e.toAlgHom.toRingHom.toMonoidHom).comp σ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun g : G => σ g (b j) := by
      refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
      exact (hcont _ (b j).2).comp (hp.inv.mul continuous_const)
    have h2 : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    refine (h2.comp h1).congr fun g => ?_
    change _ = LinearMap.toMatrixAlgEquiv b (σ g) i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    rfl
  · intro x hx z
    have h1 : (x.sum fun k c => c • σ k) = 0 := by
      apply e.injective

      rw [map_zero, ← hx, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      rfl
    have h2 := congrArg (fun T : V →ₗ[ℂ] V => (T ⟨f, hfV⟩ : H → ℂ) z) h1
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, hσ] using h2
end

section

theorem UpperTheory.exists_smooth_extension_near :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
      IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
        ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro E _ _ _ V _ _ m U hU F hF x hx
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hsub : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact hball
  refine ⟨fun y => b y • F y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (b.contDiff (n := m)).contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hy))
    · have h0 : (b : E → ℝ) =ᶠ[nhds y] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hsub h)
      have h1 : (fun z => b z • F z) =ᶠ[nhds y] fun _ => (0 : V) := by
        filter_upwards [h0] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · filter_upwards [b.eventuallyEq_one] with z hz
    simp [hz]
end
