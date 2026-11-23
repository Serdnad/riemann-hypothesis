module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Covering.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

@[expose] public section

section

open scoped Matrix

namespace GlobalTheory

theorem sq_scalar_character : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  intro G G' M H _ _ _ _ _ _ _ _ _ pr s om ω ε hcov hsurj hker hε hs hom hω hrel
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  have huniq : ∀ g (g₁ g₂ : G') (a b : ℂ), pr g₁ = s g → pr g₂ = s g →
      (∀ v, ω g v = a • om g₁ v) → (∀ v, ω g v = b • om g₂ v) → a ^ 2 = b ^ 2 := by
    intro g g₁ g₂ a b h₁ h₂ ha hb
    have hw : om g₁ v₀ ≠ 0 := by
      intro h; apply hv₀; exact (om g₁).map_eq_zero_iff.mp h
    have hk : pr (g₁⁻¹ * g₂) = 1 := by simp [map_mul, map_inv, h₁, h₂]
    rcases hker _ hk with h | h
    · have h2 : g₂ = g₁ := by rw [← mul_inv_cancel_left g₁ g₂, h, mul_one]
      subst h2
      have : a • om g₂ v₀ = b • om g₂ v₀ := by rw [← ha, ← hb]
      have hab : a = b := smul_left_injective ℂ hw this
      rw [hab]
    · have h2 : g₂ = g₁ * ε := by rw [← h, mul_inv_cancel_left]
      have : a • om g₁ v₀ = (-b) • om g₁ v₀ := by
        rw [← ha, hb, h2, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hε,
          map_neg, smul_neg, neg_smul]
      have hab : a = -b := smul_left_injective ℂ hw this
      rw [hab]; ring
  have hlift : ∀ g, ∃ g', pr g' = s g := fun g => hsurj (s g)
  choose L hL using hlift
  choose A hA using fun g => hrel g (L g) (hL g)
  refine ⟨fun g => A g ^ 2, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmul : pr (L g * L h) = s (g * h) := by simp [map_mul, hL]
    have hsc : ∀ v, ω (g * h) v = (A g * A h) • om (L g * L h) v := by
      intro v
      rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hA h, LinearIsometryEquiv.map_smul,
        hA g, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, smul_smul, mul_comm (A h)]
    have := huniq (g * h) (L (g * h)) (L g * L h) _ _ (hL _) hmul (hA _) hsc
    simp only
    rw [this]; ring
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨e, he, hpe⟩ := hcov.isLocalHomeomorph (L g₀)
    have hopen : IsOpen (s ⁻¹' e.target) := e.open_target.preimage hs
    have hmem : g₀ ∈ s ⁻¹' e.target := by
      show s g₀ ∈ e.target
      rw [← hL g₀, hpe]; exact e.map_source he
    let f : G → ℂ := fun g => (inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀) ^ 2
    have hf : ContinuousAt f g₀ := by
      have h1 : ContinuousAt (fun g => om (e.symm (s g)) v₀) g₀ :=
        (hom v₀).continuousAt.comp ((e.continuousAt_symm hmem).comp hs.continuousAt)
      exact ((h1.inner (hω v₀).continuousAt).div_const _).pow 2
    refine hf.congr ?_
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hpr : pr (e.symm (s g)) = s g := by rw [hpe]; exact e.right_inv hg
    obtain ⟨c, hc⟩ := hrel g _ hpr
    have hcval : c = inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀ := by
      rw [hc, inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_assoc,
        div_self (inner_self_ne_zero.2 hv₀), mul_one]
    show f g = A g ^ 2
    simp only [f]
    rw [← hcval]
    exact huniq g _ _ c (A g) hpr (hL g) hc (hA g)
  · intro g
    refine pow_ne_zero 2 ?_
    intro h0
    have := hA g v₀
    rw [h0, zero_smul] at this
    exact hv₀ ((ω g).map_eq_zero_iff.mp this)
  · intro g g' a hg' ha
    exact huniq g g' (L g) a (A g) hg' (hL g) ha (hA g)

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

private theorem measurePreserving_piCurry_symm_fin_two (ι : Type) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm
      volume volume := by
  classical
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  symm
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.piCurry _).symm.map_apply]
  have hpre : (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun k => s ⟨i, k⟩ := by
    ext x
    simp [Set.mem_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry]
  rw [hpre, volume_pi_pi]
  simp only [volume_pi_pi]
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

theorem measurePreserving_of_norm_sq_eq_sum_complex_coords
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] (e : V ≃L[ℝ] (ι → ℂ))
    (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) : MeasurePreserving e volume volume := by
  classical
  let Φ : (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (LinearEquiv.piCongrRight fun _ => Complex.basisOneI.equivFun).trans
      ((LinearEquiv.piCurry ℝ fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (WithLp.linearEquiv 2 ℝ _).symm)
  have hΦ : ∀ z, ‖Φ z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ∀ k, Φ z ⟨i, k⟩ = Complex.basisOneI.repr (z i) k := fun k => rfl
    simp only [hc, Fin.sum_univ_two, Complex.coe_basisOneI_repr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  let F : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    { toLinearEquiv := e.toLinearEquiv.trans Φ
      norm_map' := fun v => by
        have h : ‖Φ (e v)‖ ^ 2 = ‖v‖ ^ 2 := by rw [hΦ, he]
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h }
  let G : (ι → ℂ) ≃ᵐ EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (MeasurableEquiv.piCongrRight fun _ => Complex.measurableEquivPi).trans
      ((MeasurableEquiv.piCurry fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (MeasurableEquiv.toLp 2 _))
  have hG : MeasurePreserving G volume volume :=
    (PiLp.volume_preserving_toLp _).comp ((measurePreserving_piCurry_symm_fin_two ι).comp
      (volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi))
  have hFG : (F : V → EuclideanSpace ℝ (Σ _ : ι, Fin 2)) = G ∘ e := by
    funext v
    rfl
  have hF : MeasurePreserving (G ∘ e) volume volume := hFG ▸ F.measurePreserving
  exact hG.comp_left_iff.1 hF

end GlobalTheory
end

section

open Topology Filter

namespace GlobalTheory.SmoothFix

theorem eq_one_of_pow_norm_sub_one_le_half {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_nhds_fix : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this

end GlobalTheory.SmoothFix
end

section

open NumberField MeasureTheory

namespace GlobalTheory.OrbitUnfold

theorem hasSum_integral_translate {I : Type} [Fintype I] {U : Type} [Countable U]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : U → I → ℝ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hsum : ∀ y, HasSum (fun u => p (y - t u)) 1) (h : (I → ℝ) → E) (hh : Integrable h) :
    HasSum (fun u => ∫ y, p y • h (y + t u)) (∫ y, h y) := by
  have key : ∀ u, ∫ y, p y • h (y + t u) = ∫ y, p (y - t u) • h y := by
    intro u
    have := integral_add_right_eq_self (μ := (volume : Measure (I → ℝ)))
      (fun y => p (y - t u) • h y) (t u)
    simpa using this
  simp_rw [key]
  refine hasSum_integral_of_dominated_convergence (fun u y => p (y - t u) * ‖h y‖) ?_ ?_ ?_ ?_ ?_
  · intro u
    exact ((hp.comp (measurable_sub_const (t u))).aestronglyMeasurable).smul
      hh.aestronglyMeasurable
  · intro u
    refine ae_of_all _ (fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hp0 _)]
  · exact ae_of_all _ (fun y => ((hsum y).mul_right ‖h y‖).summable)
  · refine hh.norm.congr (ae_of_all _ (fun y => ?_))
    simp only [((hsum y).mul_right ‖h y‖).tsum_eq, one_mul]
  · refine ae_of_all _ (fun y => ?_)
    simpa using (hsum y).smul_const (h y)

theorem orbit_unfold : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ)
    (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) →
    ∀ g : (I → ℝ) → ℂ, Integrable g →
      HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧
      HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  intro I _ U _ t p hp hp0 hsum g hg
  refine ⟨?_, ?_⟩
  · have := hasSum_integral_translate t p hp hp0 hsum g hg
    simpa [Complex.real_smul] using this
  · have := hasSum_integral_translate t p hp hp0 hsum (fun y => ‖g y‖) hg.norm
    simpa [smul_eq_mul] using this

end GlobalTheory.OrbitUnfold
end

section

open NumberField MeasureTheory

namespace GlobalTheory

theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
end

section

namespace GlobalTheory.DenseEmbeddingProduct

open NumberField NumberField.InfinitePlace

theorem denseRange_embedding_pi {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by
  let Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ) :=
    fun y w ↦ Completion.extensionEmbedding w (y w)
  have hc : Continuous Φ := continuous_pi fun w ↦
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hs : Function.Surjective Φ := by
    intro f
    choose y hy using fun w : InfinitePlace E ↦
      Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)
    exact ⟨y, funext hy⟩
  have h := hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
  convert h using 1
  funext x w
  simp [Φ]

end GlobalTheory.DenseEmbeddingProduct
end
