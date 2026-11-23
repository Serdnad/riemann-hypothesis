module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

namespace GlobalTheory

theorem hasSum_conjClasses_tsum_of_finite_support {G : Type} [Group G] (g : G → ℂ) (hg : (Function.support g).Finite)
    (R : G → Prop) (hR : ∀ δ, g δ ≠ 0 → R δ) :
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      (∑' δ, g δ) := by
  classical
  let c : G → Set G := fun δ => {δ' | IsConj δ δ'}
  have hsum : HasSum g (∑' δ, g δ) := (summable_of_hasFiniteSupport hg).hasSum
  have h1 := hsum.tsum_fiberwise c
  have hfib : ∀ γ : G, c ⁻¹' {c γ} = c γ := by
    intro γ; ext b
    simp only [c, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have : b ∈ {δ' | IsConj b δ'} := IsConj.refl b
      rw [h] at this; exact this
    · intro h; ext x; simp only [Set.mem_setOf_eq]
      exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩
  have hsupp : Function.support (fun s : Set G => ∑' b : c ⁻¹' {s}, g b)
      ⊆ {s | ∃ γ, R γ ∧ s = {δ | IsConj γ δ}} := by
    intro s hs
    by_contra hns
    apply hs
    have : ∀ b : c ⁻¹' {s}, g b = 0 := by
      intro ⟨b, hb⟩
      by_contra hgb
      exact hns ⟨b, hR b hgb, (hb : c b = s).symm⟩
    simp [this]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at h1
  have key : (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      = fun i => (fun s : Set G => ∑' b : c ⁻¹' {s}, g b) i.1 := by
    funext i
    obtain ⟨s, γ, _, hs⟩ := i
    subst hs
    dsimp only
    rw [show c ⁻¹' {{δ | IsConj γ δ}} = {δ | IsConj γ δ} from hfib γ]
  rw [key]; exact h1

theorem classSum_regroup : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite →
    ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) →
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} =>
      {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator
        (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by
  classical
  intro G _ g hg R P hR hP
  refine ⟨hasSum_conjClasses_tsum_of_finite_support g hg R hR, ?_⟩
  let g' : G → ℂ := fun δ => if P δ then g δ else 0
  have hg' : (Function.support g').Finite := by
    refine hg.subset ?_
    intro δ h
    by_cases hp : P δ <;> simp_all [g']
  have hR' : ∀ δ, g' δ ≠ 0 → R δ := by
    intro δ h; apply hR; by_cases hp : P δ <;> simp_all [g']
  have H := hasSum_conjClasses_tsum_of_finite_support g' hg' R hR'
  have htot : ∑' δ, g' δ = ∑' δ : {δ // P δ}, g δ := by
    rw [show (∑' δ : {δ // P δ}, g δ) = ∑' δ : ({δ | P δ} : Set G), g δ from rfl, tsum_subtype]
    congr 1
  rw [htot] at H
  convert H using 1
  funext i
  obtain ⟨s, γ, hγ, rfl⟩ := i
  rw [Set.indicator_apply]
  split_ifs with hall
  · congr 1; funext δ
    obtain ⟨δ, hδ⟩ := δ
    simp [g', hall δ hδ]
  · have hall' : ¬ ∀ δ ∈ ({δ | IsConj γ δ} : Set G), P δ := hall
    push_neg at hall'
    obtain ⟨δ0, hδ0, hnP⟩ := hall'
    symm
    have : ∀ δ : ({δ | IsConj γ δ} : Set G), g' δ = 0 := by
      intro ⟨δ, hδ⟩
      have hnδ : ¬ P δ := fun h => hnP (hP δ δ0 ((hδ : IsConj γ δ).symm.trans hδ0) h)
      simp [g', hnδ]
    simp [this]

end GlobalTheory
end

section

open scoped ContDiff
open scoped Nat

noncomputable section

namespace GlobalTheory

theorem norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by
  have hd : ∀ s, DifferentiableAt ℝ h s := fun s =>
    (hh.differentiable (by simp)).differentiableAt
  have hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s := by
    funext s
    exact (L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]
  have hfh : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp

theorem norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring

end GlobalTheory
end
end

section

noncomputable section

open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform

namespace GlobalTheory.RealWeil

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def gau (u : V) : ℂ := cexp (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2)

def IsHeis (om : V → V → ℝ) (ρ : V → B →L[ℂ] B) : Prop :=
  (∀ f, ρ 0 f = f) ∧ (∀ u v f, ρ u (ρ v f) = cexp (π * I * (om u v : ℂ)) • ρ (u + v) f) ∧
    (∀ u f, ‖ρ u f‖ = ‖f‖) ∧ ∀ f, Continuous fun u => ρ u f

def Sm (ρ : V → B →L[ℂ] B) (f : B) : Prop := ContDiff ℝ ∞ fun v => ρ v f

def IsOsc (ρ : V → B →L[ℂ] B) {G : Type} [Group G] (k : G → V → V) (Ω : G → B → B) : Prop :=
  (∀ g f f', Sm ρ f → Sm ρ f' → Ω g (f + f') = Ω g f + Ω g f') ∧
  (∀ g (a : ℂ) f, Sm ρ f → Ω g (a • f) = a • Ω g f) ∧
  (∀ g f, Sm ρ f → Sm ρ (Ω g f)) ∧
  (∀ f, Sm ρ f → Ω 1 f = f) ∧
  (∀ g g' f, Sm ρ f → Ω (g * g') f = Ω g (Ω g' f)) ∧
  (∀ g v f, Sm ρ f → Ω g (ρ v f) = ρ (k g v) (Ω g f)) ∧
  (∀ g (A : B →L[ℂ] B), (∀ v f, A (ρ v f) = ρ v (A f)) → ∀ f, Sm ρ f → Ω g (A f) = A (Ω g f)) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H),
    (∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) → ∀ g f, Sm ρ f → ‖Φ (Ω g f)‖ = ‖Φ f‖

theorem norm_gau (u : V) : ‖gau u‖ = Real.exp (-(π / 2) * ‖u‖ ^ 2) := by
  unfold gau
  rw [Complex.norm_exp]
  congr 1
  have : (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-(π / 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]

theorem gau_ne_zero (u : V) : gau u ≠ 0 := Complex.exp_ne_zero _

theorem gau_zero : gau (0 : V) = 1 := by simp [gau]

theorem gau_neg (u : V) : gau (-u) = gau u := by simp [gau]

theorem continuous_gau : Continuous (gau : V → ℂ) := by unfold gau; fun_prop

theorem IsHeis.twist {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) (g : V →L[ℝ] V)
    (hg : ∀ x y, om (g x) (g y) = om x y) : IsHeis om fun v => ρ (g v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hg, map_add (f := _)], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp g.continuous⟩

theorem IsHeis.continuous {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) {Y : Type} [TopologicalSpace Y]
    {a : Y → V} {x : Y → B} (ha : Continuous a) (hx : Continuous x) : Continuous fun y => ρ (a y) (x y) := by
  have : Continuous fun p : B × V => ρ p.2 p.1 :=
    continuous_prod_of_continuous_lipschitzWith (fun p : B × V => ρ p.2 p.1) 1
      (fun f => h.2.2.2 f) fun v => LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub, h.2.2.1]; simp
  exact this.comp (hx.prodMk ha)

end General

def dP {ι : Type} [Fintype ι] [DecidableEq ι] (s g : Matrix ι ι ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)).det

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def omJ (J : V ≃ₗᵢ[ℝ] V) (x y : V) : ℝ := ⟪x, J y⟫

def lam (g : V → V) : ℂ := ∫ u, gau u * gau (g u)

def mu (J : V ≃ₗᵢ[ℝ] V) (g₁ g₂ : V → V) : ℂ :=
  ∫ u, ∫ v, gau u * gau v * (cexp (π * I * (omJ J (g₁ u) (g₂ v) : ℂ)) * gau (g₁ u + g₂ v))

theorem integrable_gau : Integrable (gau : V → ℂ) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 2 : ℂ)) (by simpa using Real.pi_pos) 0 0
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gau]

variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

omit [CompleteSpace B] in
theorem IsHeis.integrable (h : IsHeis om ρ) (f : B) : Integrable fun u => gau u • ρ u f := by
  refine Integrable.mono' ((integrable_gau (V := V)).norm.mul_const ‖f‖)
    (continuous_gau.smul (h.2.2.2 f)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, h.2.2.1]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B] in
theorem IsHeis.continuous_gau_smul (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f :=
  continuous_gau.smul (h.2.2.2 f)

def proj (h : IsHeis om ρ) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, gau u • ρ u f
      map_add' := fun f f' => by
        rw [← integral_add (h.integrable f) (h.integrable f')]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm a] }
    (∫ u : V, ‖gau u‖) fun f => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, h.2.2.1]
      rw [integral_mul_const]

omit [CompleteSpace B] in
theorem proj_apply (h : IsHeis om ρ) (f : B) : proj h f = ∫ u, gau u • ρ u f := rfl

def Good (h : IsHeis om ρ) (f : B) : Prop := ∀ n : ℕ, Integrable fun w => ‖w‖ ^ n * ‖proj h (ρ (-w) f)‖

variable {J : V ≃ₗᵢ[ℝ] V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem omJ_skew (hJ : ∀ x, J (J x) = -x) (x y : V) : omJ J y x = -omJ J x y := by
  unfold omJ
  rw [← J.inner_map_map, hJ, inner_neg_right, real_inner_comm]

theorem proj_translate (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (w : V) :
    proj h (ρ (-w) f) = ρ (-w) (𝓕 (fun u => gau u • ρ u f) (J w)) := by
  rw [proj_apply, Real.fourier_eq', ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_smul, h.2.1, smul_smul]
    rw [add_comm (-w) u, omJ_skew hJ u (-w)]
    congr 1
    have e : omJ J u (-w) = -⟪u, J w⟫ := by simp [omJ]
    rw [e, mul_right_comm _ (gau u), ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  · have := (Real.fourierIntegral_convergent_iff (J w)).2 (h.integrable f)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul, Complex.ofReal_neg] using this

theorem Good.fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) (n : ℕ) :
    Integrable fun w => ‖w‖ ^ n * ‖𝓕 (fun u => gau u • ρ u f) w‖ := by
  have := hf n
  simp only [proj_translate hJ, h.2.2.1] at this
  rw [← J.measurePreserving.integrable_comp_emb J.toHomeomorph.measurableEmbedding]
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp

theorem continuous_fourier_gau (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (h.integrable f)

theorem Good.integrable_fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable (𝓕 fun u => gau u • ρ u f) := by
  have := hf.fourier hJ 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff (continuous_fourier_gau h f).aestronglyMeasurable).1 this

theorem Good.inversion (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    ∫ w, ρ w (proj h (ρ (-w) f)) = f := by
  have e : ∀ w, ρ w (proj h (ρ (-w) f)) = 𝓕 (fun u => gau u • ρ u f) (J w) := by
    intro w
    have h0 : omJ J w (-w) = 0 := by
      have := omJ_skew hJ w w
      have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
      linarith
    rw [proj_translate hJ, h.2.1, h0, add_neg_cancel, h.1]
    simp
  simp only [e]
  rw [J.measurePreserving.integral_comp J.toHomeomorph.measurableEmbedding]
  have := congrFun ((h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f)
    (hf.integrable_fourier hJ)) 0
  rw [Real.fourierInv_eq] at this
  simpa [gau_zero, h.1] using this

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_gau_inv : ContDiff ℝ ∞ fun u : V => (gau u)⁻¹ := by
  have : (fun u : V => (gau u)⁻¹) = fun u => cexp ((π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    rw [gau, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [this]
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)))

theorem Good.sm (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) : Sm ρ f := by
  have h1 := (h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f) (hf.integrable_fourier hJ)
  have h2 : ContDiff ℝ ∞ (𝓕 (𝓕 fun u => gau u • ρ u f)) := Real.contDiff_fourier fun n _ => hf.fourier hJ n
  have h3 : ContDiff ℝ ∞ fun u => gau u • ρ u f := by
    rw [← h1]
    have : 𝓕⁻ (𝓕 fun u => gau u • ρ u f) = fun u => 𝓕 (𝓕 fun u => gau u • ρ u f) (-u) := by
      funext u; rw [Real.fourierInv_eq_fourier_neg]
    rw [this]
    exact h2.comp contDiff_neg
  have : ContDiff ℝ ∞ fun u => (gau u)⁻¹ • gau u • ρ u f := (contDiff_gau_inv (V := V)).smul h3
  simpa only [smul_smul, inv_mul_cancel₀ (gau_ne_zero _), one_smul, Sm] using this

end Inner

end GlobalTheory.RealWeil

end
end

section

namespace GlobalTheory

theorem exp_conj_entries_hasFDerivAt_zero : ∀ (n : ℕ) (ι : Type) [Fintype ι] (A : (ι → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (p : ι → Fin n × Fin n), (∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = A w (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0) ∧ ∀ s : Matrix (Fin n) (Fin n) ℂ, ∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = (s * A w - A w * s) (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (-A w) * s * NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0 := by
  intro n ι _ A p
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun M x => M (p x).1 (p x).2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ec := LinearMap.toContinuousLinearMap E
  let Ac := LinearMap.toContinuousLinearMap A
  have hA0 : Ac 0 = 0 := map_zero _
  have hnA0 : (-Ac) 0 = 0 := map_zero _
  have h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0) := by
    rw [hA0]; exact hasFDerivAt_exp_zero
  have h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0) := by
    rw [hnA0]; exact hasFDerivAt_exp_zero
  have hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0 :=
    h1.comp (0 : ι → ℂ) Ac.hasFDerivAt
  have hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0 :=
    h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt
  refine ⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩
  · intro w x; rfl
  · have hprod := (hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA
    refine ⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩
    intro w x
    have hA0' : A 0 = 0 := map_zero A
    simp only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]
    change ((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2
    rw [one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]

end GlobalTheory
end
