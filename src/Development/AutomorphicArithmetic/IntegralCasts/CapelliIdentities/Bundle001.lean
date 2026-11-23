module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.InnerProductSpace.Defs
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

open MeasureTheory Set

private noncomputable def mulE {n : ℕ} (a x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  Matrix.of.symm (Matrix.of a * Matrix.of x)

private lemma mulE_apply {n : ℕ} (a x : Fin n → Fin n → ℂ) (i j : Fin n) :
    mulE a x i j = ∑ k, a i k * x k j := by
  simp [mulE, Matrix.mul_apply]

private lemma continuous_mulE {n : ℕ} :
    Continuous (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => mulE p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulE_apply]
  fun_prop

private lemma measurable_mulE {n : ℕ} (a : Fin n → Fin n → ℂ) : Measurable (mulE a) :=
  (continuous_mulE.comp (Continuous.prodMk_right a)).measurable

private lemma continuous_detE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ => (Matrix.of v).det) :=
  Continuous.matrix_det (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma continuous_adjE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ =>
      (Matrix.of.symm (Matrix.of v).adjugate : Fin n → Fin n → ℂ)) :=
  Continuous.matrix_adjugate (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma haarE (n : ℕ) :
    (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure ℂ)
  exact Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure (Fin n → ℂ))

private lemma exists_pair (n : ℕ) :
    ∃ V K : Set (Fin n → Fin n → ℂ), IsCompact V ∧ IsCompact K ∧ 0 < volume V ∧
      ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K := by
  haveI := haarE n
  have hU : IsOpen {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} :=
    isOpen_ne_fun continuous_detE continuous_const
  have h1 : (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) ∈
      {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} := by
    simp only [Set.mem_ofPred_eq, Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨V, hV, hi, hsub⟩ := exists_compact_subset hU h1
  refine ⟨V, (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    ((Matrix.of p.2).det)⁻¹ • mulE p.1 (Matrix.of.symm (Matrix.of p.2).adjugate)) '' (V ×ˢ V),
    hV, ?_, Measure.measure_pos_of_nonempty_interior _ ⟨_, hi⟩, ?_⟩
  · refine (hV.prod hV).image_of_continuousOn ?_
    refine ContinuousOn.fun_smul ?_ ?_
    · exact (continuous_detE.comp continuous_snd).continuousOn.inv₀ fun p hp => hsub hp.2
    · exact (continuous_mulE.comp
        (continuous_fst.prodMk (continuous_adjE.comp continuous_snd))).continuousOn
  · rintro y v hv w hw rfl
    refine ⟨(mulE y v, v), ⟨hw, hv⟩, ?_⟩
    have hd : (Matrix.of v).det ≠ 0 := hsub hv
    have : mulE (mulE y v) (Matrix.of.symm (Matrix.of v).adjugate) = (Matrix.of v).det • y := by
      simp only [mulE, Equiv.apply_symm_apply, Matrix.mul_assoc, Matrix.mul_adjugate,
        Matrix.mul_smul, Matrix.mul_one]
      rfl
    simp only [this, smul_smul, inv_mul_cancel₀ hd, one_smul]

private lemma mulE_cancel {n : ℕ} {a y v w : Fin n → Fin n → ℂ} (ha : (Matrix.of a).det ≠ 0)
    (h : mulE (mulE a y) v = mulE a w) : mulE y v = w := by
  have hu : IsUnit (Matrix.of a) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit ha)
  have h' : Matrix.of a * (Matrix.of y * Matrix.of v) = Matrix.of a * Matrix.of w := by
    rw [← Matrix.mul_assoc]
    exact h
  exact hu.mul_left_cancel h'

private lemma key {n : ℕ} {G : Set (Fin n → Fin n → ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
    [SFinite μ] (hG : μ Gᶜ = 0) (hdet : ∀ a ∈ G, (Matrix.of a).det ≠ 0)
    (hvol : ∀ a ∈ G, Measure.map (mulE a) volume = volume)
    (hinv : ∀ a ∈ G, Measure.map (mulE a) μ = μ)
    {V K B D : Set (Fin n → Fin n → ℂ)} (hV : IsCompact V) (hB : IsCompact B)
    (hD : MeasurableSet D)
    (hK : ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K)
    (hBD : ∀ g ∈ B, ∀ v ∈ V, mulE g v ∈ D) :
    volume V * μ B ≤ μ K * volume D := by
  set S : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    (fun p => (p.1, mulE p.1 p.2)) '' (B ×ˢ V) with hS
  have hSm : MeasurableSet S :=
    ((hB.prod hV).image (continuous_fst.prodMk continuous_mulE)).measurableSet
  have hae : ∀ᵐ g ∂μ, g ∈ G := hG
  have h1 : volume V * μ B ≤ (μ.prod volume) S := by
    rw [Measure.prod_apply hSm, ← lintegral_indicator_const hB.measurableSet]
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hgB : g ∈ B
    · rw [indicator_of_mem hgB]
      have hm : MeasurableSet (Prod.mk g ⁻¹' S) := measurable_prodMk_left hSm
      calc volume V ≤ volume (mulE g ⁻¹' (Prod.mk g ⁻¹' S)) :=
            measure_mono fun v hv => ⟨(g, v), ⟨hgB, hv⟩, rfl⟩
        _ = volume (Prod.mk g ⁻¹' S) := by
            rw [← Measure.map_apply (measurable_mulE g) hm, hvol g hg]
    · rw [indicator_of_notMem hgB]
      exact zero_le
  have h2 : (μ.prod volume) S ≤ μ K * volume D := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const hD]
    refine lintegral_mono fun x => ?_
    have hm : MeasurableSet ((fun g => (g, x)) ⁻¹' S) := measurable_prodMk_right hSm
    by_cases hne : (((fun g => (g, x)) ⁻¹' S) ∩ G).Nonempty
    · obtain ⟨a, ⟨⟨a', w⟩, ⟨haB, hw⟩, he⟩, haG⟩ := hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      show μ _ ≤ _
      rw [indicator_of_mem (hBD _ haB _ hw), ← hinv _ haG,
        Measure.map_apply (measurable_mulE _) hm, hinv _ haG]
      refine measure_mono ?_
      rintro y ⟨⟨g, v⟩, ⟨-, hv⟩, he'⟩
      obtain ⟨rfl, h'⟩ := Prod.mk.inj he'
      exact hK y v hv w hw (mulE_cancel (hdet _ haG) h')
    · have : μ ((fun g => (g, x)) ⁻¹' S) = 0 := by
        refine measure_mono_null ?_ hG
        intro g hg hgG
        exact hne ⟨g, hg, hgG⟩
      show μ _ ≤ _
      rw [this]
      exact zero_le
  exact h1.trans h2
end

section

theorem UpperTheory.Reformulated.B.DYhd3.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (u u' : V), (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u') = ((B : V → V →ₗ[ℂ] ℂ) u' : V → ℂ) u) →
        (∀ (u : V), (0 : ℝ) ≤ (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u).re) →
          ∀ (x y : V),
            ‖((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
              (((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ B hsymm hpos x y
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun u v => B u v
      conj_inner_symm := fun u v => hsymm v u
      re_inner_nonneg := fun u => hpos u
      add_left := fun u v w => by simp
      smul_left := fun u v r => by simp }
  have h : ‖B x y‖ * ‖B y x‖ ≤ (B x x).re * (B y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  have h2 : ‖B y x‖ = ‖B x y‖ := by
    rw [← hsymm x y]; exact RCLike.norm_conj _
  rw [h2] at h
  rw [sq]
  exact h
end

section

theorem UpperTheory.Reformulated.B.Ra9.exists_semi :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : Field K] (M : Type) [inst_2 : AddCommGroup M] [inst_3 : _root_.Module A M] [inst_4 : Algebra A K]
    [Module.Free A M] {C W : Type} [inst_6 : Field C] [inst_7 : AddCommGroup W] [inst_8 : _root_.Module C W] (ι : K ≃+* C)
    (sp : M →+ W),
    (∀ (a : A) (m : M), (sp : M → W) (a • m) = (ι : K → C) ((Algebra.algebraMap A K : A → K) a) • (sp : M → W) m) →
      (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun (i : κ) ↦ (sp : M → W) ((b : κ → M) i)) →
        ∃ (Ψ : TensorProduct A K M →+ W),
          (∀ (k : K) (m : M), (Ψ : TensorProduct A K M → W) (k ⊗ₜ[A] m) = (ι : K → C) k • (sp : M → W) m) ∧
            (∀ (k : K) (v : TensorProduct A K M),
                (Ψ : TensorProduct A K M → W) (k • v) = (ι : K → C) k • (Ψ : TensorProduct A K M → W) v) ∧
              Function.Injective (⇑Ψ : TensorProduct A K M → W) ∧
                ∀ (w : W),
                  w ∈ Submodule.span C (Set.range (⇑sp : M → W)) ↔
                    ∃ (v : TensorProduct A K M), (Ψ : TensorProduct A K M → W) v = w := by
  intro A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli
  classical
  let f : K →+ M →+ W :=
    { toFun := fun k =>
        { toFun := fun m => ι k • sp m
          map_zero' := by simp
          map_add' := by intro x y; simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := by intro x y; ext m; simp [add_smul] }
  have hfa : ∀ (k : K) (m : M), f k m = ι k • sp m := fun _ _ => rfl
  have hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m) := by
    intro r k m
    have h := hsp r m
    rw [hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]
  let Ψ : TensorProduct A K M →+ W := TensorProduct.liftAddHom f hf
  have hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m := fun k m => by
    simp only [Ψ, TensorProduct.liftAddHom_tmul, hfa]
  have hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  refine ⟨Ψ, hΨ, hsemi, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Ψ).2 ?_
    intro v hv
    let b := Module.Free.chooseBasis A M
    let bK := Algebra.TensorProduct.basis K b
    have hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i))
        ((bK.repr v).mapRange ι (map_zero ι)) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      conv_lhs => rw [← bK.linearCombination_repr v]

      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]
    have hl := (linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)
    have hr : bK.repr v = 0 := by
      ext i
      have h := DFunLike.congr_fun hl i
      simpa using h
    simpa using hr
  · intro w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩
      | zero => exact ⟨0, map_zero Ψ⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add Ψ a c⟩
      | smul c x _ hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨v, rfl⟩
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul k m =>
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
end

section

theorem UpperTheory.filtration_exponent_bound :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module O D] [Module A D]
        [IsScalarTower O A D] (N : Submodule O D) (γ : D →ₗ[O] D) (ϖ : A) (l : O) (E e : ℕ → ℕ) (lam : ℕ → O),
        Monotone E → Monotone e → (∀ y, E y ≤ e y) →
        (∀ r : ℕ, ∃ u : Oˣ, lam (r + 1) = (u : O) * l ^ (E (r + 1) - E r)) →
        lam 0 = 0 → (∀ x ∈ N, ϖ • x ∈ N) →
        (∀ (r : ℕ), ∀ x ∈ N, ∃ x' ∈ N,
          γ (ϖ ^ r • x) - ϖ ^ r • x = lam r • (ϖ ^ r • x) + ϖ ^ (r + 1) • x') →
        ∀ w ∈ N, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ N) ∧ ∀ K : ℕ, ∃ t ∈ N,
          l ^ e K • (γ w - w) - ∑ y ∈ Finset.range K, l ^ (e K - e y) •
            (γ (ϖ ^ y • (l ^ (e y - E y) • c y)) - ϖ ^ y • (l ^ (e y - E y) • c y)) = ϖ ^ K • t := by
  intro O A D _ _ _ _ _ _ _ N γ ϖ l E e lam hE he hEe hlam hlam0 hϖ hγ w hw
  choose u hu using hlam
  have hγ' : ∀ (r : ℕ) (x : N), ∃ x' : N,
      γ (ϖ ^ r • (x : D)) - ϖ ^ r • (x : D) = lam r • (ϖ ^ r • (x : D)) + ϖ ^ (r + 1) • (x' : D) := by
    intro r x
    obtain ⟨x', h1, h2⟩ := hγ r x x.2
    exact ⟨⟨x', h1⟩, h2⟩
  choose f hf using hγ'
  have h0 : γ w - w = ϖ • (f 0 ⟨w, hw⟩ : D) := by
    have := hf 0 ⟨w, hw⟩
    simpa [hlam0] using this
  let s : ℕ → N := fun K => Nat.rec (l ^ E 0 • f 0 ⟨w, hw⟩)
    (fun k sk => - f (k + 1) (((u k)⁻¹ : Oˣ).val • sk)) K
  have hs0 : s 0 = l ^ E 0 • f 0 ⟨w, hw⟩ := rfl
  have hsS : ∀ k, s (k + 1) = - f (k + 1) (((u k)⁻¹ : Oˣ).val • s k) := fun _ => rfl
  let c : ℕ → N := fun K => Nat.casesOn K 0 (fun k => ((u k)⁻¹ : Oˣ).val • s k)
  have hc0 : c 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = ((u k)⁻¹ : Oˣ).val • s k := fun _ => rfl
  clear_value c s
  have key : ∀ K, l ^ E K • (γ w - w) - ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
      (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = ϖ ^ (K + 1) • (s K : D) := by
    intro K
    induction K with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, hc0, hs0, h0, ZeroMemClass.coe_zero, smul_zero,
        map_zero, sub_zero, pow_one, Submodule.coe_smul]
      rw [smul_comm]
    | succ K ih =>
      have hK : E K ≤ E (K + 1) := hE (Nat.le_succ K)
      have hsum : ∑ y ∈ Finset.range (K + 1), l ^ (E (K + 1) - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) =
          l ^ (E (K + 1) - E K) • ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' : E y ≤ E K := hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      have hp : l ^ E (K + 1) = l ^ (E (K + 1) - E K) * l ^ E K := by
        rw [← pow_add]
        congr 1
        omega
      have hl : lam (K + 1) • (ϖ ^ (K + 1) • (c (K + 1) : D)) =
          l ^ (E (K + 1) - E K) • (ϖ ^ (K + 1) • (s K : D)) := by
        rw [hcS, Submodule.coe_smul, smul_comm (ϖ ^ (K + 1)), smul_smul, hu]
        congr 1
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [Finset.sum_range_succ _ (K + 1), hsum, hp, mul_smul, ← sub_sub, ← smul_sub, ih, hf, hl,
        hsS, ← hcS]
      simp
  refine ⟨fun y => (c y : D), by simp [hc0], fun y => (c y).2, fun K => ?_⟩
  cases K with
  | zero =>
    refine ⟨l ^ e 0 • (ϖ • (f 0 ⟨w, hw⟩ : D)), N.smul_mem _ (hϖ _ (f 0 ⟨w, hw⟩).2), ?_⟩
    simp [h0]
  | succ K =>
    have hK : E K ≤ e (K + 1) := (hEe K).trans (he (Nat.le_succ K))
    refine ⟨l ^ (e (K + 1) - E K) • (s K : D), N.smul_mem _ (s K).2, ?_⟩
    have hp : l ^ e (K + 1) = l ^ (e (K + 1) - E K) * l ^ E K := by
      rw [← pow_add]
      congr 1
      omega
    rw [smul_comm (ϖ ^ (K + 1)), ← key, smul_sub (l ^ (e (K + 1) - E K)), ← mul_smul, ← hp,
      Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyK : y ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    have h1 : E y ≤ E K := hE hyK
    have h2 : e y ≤ e (K + 1) := he (hyK.trans (Nat.le_succ K))
    have h3 := hEe y
    rw [smul_comm (ϖ ^ y), map_smul, ← smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
end

section

private theorem UpperTheory.Reformulated.B.LayerApproximation.first_layer {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ (2 : ℕ)) :
    ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2 := by
  have hspan : ∀ y ∈ Ideal.span T, ∃ a ∈ A, a ∈ m ∧ y - a ∈ m ^ 2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨t, (hT t ht).1, (hT t ht).2, by simp⟩
    | zero => exact ⟨0, A.zero_mem, m.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨b, hb, hbm, hvb⟩ := hv
      refine ⟨a + b, A.add_mem ha hb, m.add_mem ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb
    | smul r u _ hu =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨c, hc⟩ := h0 r
      refine ⟨algebraMap O R c * a, A.mul_mem (A.algebraMap_mem c) ha,
        m.mul_mem_left _ ham, ?_⟩
      have e : r • u - algebraMap O R c * a = r * (u - a) + (r - algebraMap O R c) * a := by
        rw [smul_eq_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hc ham
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hm hx)
  obtain ⟨a, ha, ham, hya⟩ := hspan y hy
  refine ⟨a, ha, ham, ?_⟩
  have e : y + z - a = (y - a) + z := by ring
  rw [e]
  exact Ideal.add_mem _ hya hz

private theorem UpperTheory.Reformulated.B.LayerApproximation.all_layers {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (h1 : ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2) (N : ℕ) :
    ∀ x ∈ m ^ N, ∃ a ∈ A, a ∈ m ^ N ∧ x - a ∈ m ^ (N + 1) := by
  induction N with
  | zero =>
    intro x _
    obtain ⟨c, hc⟩ := h0 x
    exact ⟨algebraMap O R c, A.algebraMap_mem c, by simp, by simpa using hc⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨a, ha, ham, hya⟩ := ih y hy
      obtain ⟨b, hb, hbm, hzb⟩ := h1 z hz
      refine ⟨a * b, A.mul_mem ha hb, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have e : y * z - a * b = y * (z - b) + (y - a) * b := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show N + 1 + 1 = N + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hy hzb
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hya hbm
    · rintro u v ⟨a, ha, ham, hua⟩ ⟨b, hb, hbm, hvb⟩
      refine ⟨a + b, A.add_mem ha hb, Ideal.add_mem _ ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb

theorem UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : CommRing R]
    [inst_2 : Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R),
    (∀ (x : R), ∃ (a : O), x - (Algebra.algebraMap O R : O → R) a ∈ m) →
      (∀ t ∈ T, t ∈ A ∧ t ∈ m) → m ≤ Ideal.span T ⊔ m ^ (2 : ℕ) → ∀ (N : ℕ) (x : R), ∃ a ∈ A, x - a ∈ m ^ N := by
  intro O R _ _ _ m A T h0 hT hm N x
  have h1 := UpperTheory.Reformulated.B.LayerApproximation.first_layer m A T h0 hT hm
  induction N with
  | zero => exact ⟨0, A.zero_mem, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    obtain ⟨b, hb, -, hab⟩ := UpperTheory.Reformulated.B.LayerApproximation.all_layers m A h0 h1 N _ hxa
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have e : x - (a + b) = x - a - b := by ring
    rw [e]
    exact hab
end
