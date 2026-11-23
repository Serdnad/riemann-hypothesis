module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

end GlobalTheory.TransInv
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem exists_detIdeal_abstract {R K V ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (B : V → V →ₗ[K] K) (hB : ∀ (s : ℕ) (y x : V), B ((s : K) • y) x = (s : K) * B y x)
    (Y : Set V) (b₀ : ι → V)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, B y x ∈ (algebraMap R K).range)
    (h0 : ∀ i, ∃ s : ℕ, 0 < s ∧ (s : K) • b₀ i ∈ Y) :
    ∃ I : Submodule R K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap R K).range) ∧
      ∀ (p : ℕ) (b : ι → V), (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) →
        (∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : ι → R,
          (s : K) • y = ∑ i, algebraMap R K (c i) • b i) →
        (∃ s : ℕ, Nat.Coprime s p ∧ (s : K) * (Matrix.of fun i j => B (b₀ i) (b j)).det ∈ I) ∧
        ∀ x ∈ I, ∃ (s : ℕ) (c : R), Nat.Coprime s p ∧
          (s : K) * x = algebraMap R K c * (Matrix.of fun i j => B (b₀ i) (b j)).det := by
  have hcol : ∀ (s : ι → ℕ) (y : ι → V),
      (Matrix.of fun i j => B (b₀ i) ((s j : K) • y j)).det =
        ((∏ j, s j : ℕ) : K) * (Matrix.of fun i j => B (b₀ i) (y j)).det := by
    intro s y
    rw [Nat.cast_prod, ← Matrix.det_mul_row]
    congr 1
    ext i j
    simp
  refine ⟨Submodule.span R {d | ∃ y : ι → V, (∀ j, y j ∈ Y) ∧
    d = (Matrix.of fun i j => B (b₀ i) (y j)).det}, ?_, ?_⟩
  · choose s hs hsY using h0
    refine ⟨∏ i, s i, Finset.prod_pos fun i _ => hs i, ?_⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      choose c hc using fun i j => hY (y j) (hy j) _ (hsY i)
      refine ⟨(Matrix.of c).det, ?_⟩
      rw [RingHom.map_det, Nat.cast_prod, ← Matrix.det_mul_column]
      congr 1
      ext i j
      simp [hc, hB]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨a, rfl⟩ hx
  · intro p b h1 h2
    constructor
    · choose s hs hsY using h1
      refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
      rw [← hcol]
      exact Submodule.subset_span ⟨_, hsY, rfl⟩
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem d hd =>
        obtain ⟨y, hy, rfl⟩ := hd
        choose s hs c hc using fun j => h2 (y j) (hy j)
        refine ⟨∏ i, s i, (Matrix.of c).det, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
        rw [← hcol, RingHom.map_det, mul_comm, ← Matrix.det_transpose (RingHom.mapMatrix _ _),
          ← Matrix.det_mul]
        congr 1
        ext i j
        simp [hc, Matrix.mul_apply, mul_comm]
      | zero => exact ⟨1, 0, by simp, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, c, hs, hc⟩ := hx
        obtain ⟨t, d, ht, hd⟩ := hy
        refine ⟨s * t, t * c + s * d, Nat.Coprime.mul_left hs ht, ?_⟩
        simp only [Nat.cast_mul, map_add (f := _), map_mul, map_natCast]
        linear_combination (t : K) * hc + (s : K) * hd
      | smul a x _ hx =>
        obtain ⟨s, c, hs, hc⟩ := hx
        refine ⟨s, a * c, hs, ?_⟩
        rw [Algebra.smul_def, map_mul]
        linear_combination (algebraMap R K a) * hc

noncomputable def detIdealForm (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, RingHom.id_apply]

theorem exists_detIdeal : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  intro D N N' r Y b₀ hY h0
  have hsm : ∀ (s : ℕ) (y : Matrix (Fin N') (Fin N) D.host.E),
      (s : D.host.K) • y = (s : D.host.E) • y := by
    intro s y
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨I, hI1, hI2⟩ := exists_detIdeal_abstract (R := 𝓞 D.host.K) (K := D.host.K)
    (detIdealForm D) (by
      intro s y x
      change hYY D x _ = _ * hYY D x y
      rw [hsm, ← smul_eq_mul, hYY, hYY, ← map_smul, Nat.cast_smul_eq_nsmul D.host.K, nsmul_eq_mul]
      congr 1
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum, mul_left_comm])
    (Y : Set (Matrix (Fin N') (Fin N) D.host.E)) b₀ hY (by simpa only [hsm, SetLike.mem_coe] using h0)
  refine ⟨I, hI1, fun p b hb => hI2 p b ?_ ?_⟩
  · simpa only [hsm, SetLike.mem_coe] using hb.2.1
  · intro y hy
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
    exact ⟨s, hs, c, by rw [hsm, hc]; rfl⟩

end GlobalTheory.NormSum
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCoordLine

open Matrix
open scoped ComplexOrder

noncomputable def coordEquiv (D : D7) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g) :
    (Fin g → ℂ) ≃L[ℂ] VC D N N' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w τ i j => w (e (τ, i, j))
      invFun := fun z k => z (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by ext k; simp
      right_inv := fun z => by ext τ i j; simp }

theorem Hf_coordEquiv (D : D7) (T : Tor D) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g)
    (z a : Fin g → ℂ) :
    star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z =
      Hf D T (coordEquiv D N N' g e z) (coordEquiv D N N' g e a) := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Hf, dotProduct,
    ← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

theorem norm_al (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

theorem transl_of_mem (D : D7) (T : Tor D) {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {x : VC D N N'} (hx : x ∈ A) (z : VC D N N') :
    G (z + x) = (al D T x)⁻¹ * Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) * G z := by
  have h := hG.2 x hx z
  have h0 : al D T x ≠ 0 := fun h => by simpa [h] using norm_al D T x
  have h1 : Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [← h, U]
  have h2 := inv_mul_cancel₀ h0
  linear_combination (-(G (z + x)) * (Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2))) * h2 - G (z + x) * h1

theorem exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  intro D T N N' A ha hd hA F hF G hG h0
  let e := Fintype.equivFin (D.what₂.Tau × Fin N' × Fin N)
  set g := Fintype.card (D.what₂.Tau × Fin N' × Fin N)
  let L := coordEquiv D N N' g e
  have hH : ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (inv_pos.2 ha)
  let Λ : AddSubgroup (Fin g → ℂ) := A.comap L.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hΛ : ∀ a, a ∈ Λ ↔ L a ∈ A := fun a => Iff.rfl
  haveI : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := fun a : Λ => (⟨L a, a.2⟩ : A))
      (Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (L.injective (congrArg Subtype.val h)))
  have hsw : ∀ v a, (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im =
      -(Hf D T (L v) (L a)).im := fun v a => by
    rw [ThetaTranslSpan.herm_swap hH, Hf_coordEquiv D T N N' g e]; simp [L]
  have htr : ∀ P ∈ ThSp D T A, ∀ a ∈ Λ, ∀ z, (P ∘ L) (z + a) = (al D T (L a))⁻¹ * Complex.exp
      (Real.pi * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z) +
        Real.pi / 2 * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a)) *
          (P ∘ L) z := fun P hP a haΛ z => by
    rw [Hf_coordEquiv D T N N' g e, Hf_coordEquiv D T N N' g e, Function.comp_apply, map_add (f := _)]
    exact transl_of_mem D T hP ((hΛ a).1 haΛ) _
  have hsd : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ,
      (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im = k) ↔ v ∈ Λ := by
    intro v
    rw [hΛ, hA]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (L.symm y) (by simpa [hΛ] using hy)
      rw [hsw, L.apply_symm_apply] at hk
      exact ⟨-k, by push_cast; linarith⟩
    · intro h a haΛ
      obtain ⟨k, hk⟩ := h (L a) ((hΛ a).1 haΛ)
      exact ⟨-k, by rw [hsw, hk]; push_cast; rfl⟩
  obtain ⟨c, hc⟩ := ThetaTranslSpan.exists_eq_smul hH Λ hsd (fun a => (al D T (L a))⁻¹)
    (G ∘ L) (F ∘ L) (fun a _ => by rw [norm_inv, norm_al, inv_one])
    (hG.1.comp L.differentiable)
    (fun h => h0 (funext fun z => by simpa using congrFun h (L.symm z)))
    (htr G hG) (hF.1.comp L.differentiable) (htr F hF)
  exact ⟨c, funext fun z => by simpa using congrFun hc (L.symm z)⟩

end GlobalTheory.ThetaCoordLine
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real

namespace GlobalTheory.LatticeAreaBound

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ}
    (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹
  have h2 := tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹
  simp only [eisG, PeriodPair.G, one_div]
  refine h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    TaylorLogMetric.discr Λ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]
  rfl

theorem area_eq {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hA : 0 < ‖a‖ ^ 2 * τ.im := by positivity
  have key : ∀ m n m' n' : ℤ,
      ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im
        = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im) := fun m n m' n' => by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩
  · rw [key, abs_of_nonneg (by simpa using hA.le)]
    simp
  · rintro b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h₁
    obtain ⟨m', n', rfl⟩ := (h _).1 h₂
    rw [key, abs_mul, abs_of_pos hA] at hb ⊢
    have h0 : n * m' - m * n' ≠ 0 := fun e => by simp [e] at hb
    have h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_left hA.le h1

theorem exists_bound_discriminant :
    ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ 6 * ‖ModularForm.discriminant τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  have hy := τ.im_pos
  rw [CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
  rwa [mul_comm]

theorem area_bounded_of_discr_eq_one : ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → 0 < area Λ ∧ area Λ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_discriminant
  refine ⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩
  rintro Λ ⟨w₁, w₂, hi, rfl⟩ hd
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice := fun z => by
    rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  rw [area_eq ha fun x => (hL x).trans (h x)]
  rw [discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h] at hd
  have e := congrArg norm hd
  rw [norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at e
  have hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C := by
    calc (‖a‖ ^ 2 * τ.im) ^ 6 = ‖a‖ ^ 12 * τ.im ^ 6 := by ring
      _ = (2 * π) ^ 12 * (τ.im ^ 6 * ‖ModularForm.discriminant τ‖) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC τ) (by positivity)
  refine ⟨by positivity, ?_⟩
  rcases le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)

end GlobalTheory.LatticeAreaBound
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  first | exact @GlobalTheory.augSpan_one_mem_of_orthogonal_three | exact GlobalTheory.augSpan_one_mem_of_orthogonal_three | (intros; apply GlobalTheory.augSpan_one_mem_of_orthogonal_three <;> assumption)
end
