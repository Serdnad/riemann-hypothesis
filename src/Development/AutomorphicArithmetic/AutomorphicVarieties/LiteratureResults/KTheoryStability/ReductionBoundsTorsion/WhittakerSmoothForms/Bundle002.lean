module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.KB.WhittakerCocycle

theorem posDef_of_sphere {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian)
    (h : ∀ v : Fin N → ℂ, ‖v‖ = 1 → 0 < (star v ⬝ᵥ (M *ᵥ v)).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hM, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set u : Fin N → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hr.ne']
  have key : star x ⬝ᵥ (M *ᵥ x) = ((‖x‖ ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [hu, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  rw [RCLike.pos_iff]
  refine ⟨?_, hM.im_star_dotProduct_mulVec_self x⟩
  rw [key]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) (h u hu1)

theorem isOpen_posW {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) :
    IsOpen {h : HS L N | (mat h w).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro h0 h0p
  have hm : Continuous fun z : HS L N × (Fin N → ℂ) => mat z.1 w := by
    show Continuous fun z : HS L N × (Fin N → ℂ) => (z.1.1 w : Matrix (Fin N) (Fin N) ℂ)
    exact (continuous_apply w).comp (continuous_subtype_val.comp continuous_fst)
  have hg : Continuous fun z : HS L N × (Fin N → ℂ) => (star z.2 ⬝ᵥ (mat z.1 w *ᵥ z.2)).re :=
    Complex.continuous_re.comp ((continuous_snd.star).dotProduct (hm.matrix_mulVec continuous_snd))
  have hK : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1) := isCompact_sphere 0 1
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := h0)
    (P := fun h v => 0 < (star v ⬝ᵥ (mat h w *ᵥ v)).re) (fun v hv => by
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hv
      have hpos : 0 < (star v ⬝ᵥ (mat h0 w *ᵥ v)).re := by
        have := (show (mat h0 w).PosDef from h0p).re_dotProduct_pos hv0
        simpa using this
      exact (isOpen_lt continuous_const hg).mem_nhds hpos)
  filter_upwards [hev] with h hh
  exact posDef_of_sphere (mat_herm h w) fun v hv => hh v (by simpa using hv)

theorem pos_open_convex (L : Type) [Field L] [NumberField L] (N : ℕ) :
    IsOpen (Pos L N) ∧ Convex ℝ (Pos L N) := by
  refine ⟨?_, ?_⟩
  · have : Pos L N = ⋂ w, {h : HS L N | (mat h w).PosDef} := by
      ext h
      simp [Pos]
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_posW w
  · intro x hx y hy a b ha hb hab w
    show (mat (a • x + b • y) w).PosDef
    rw [mat_add, mat_smul, mat_smul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy w
    · exact ((hx w).smul ha').add_posSemidef ((hy w).posSemidef.smul hb)

theorem actL_scal {L : Type} [Field L] [NumberField L] {N : ℕ} (s : InfinitePlace L → ℂˣ)
    (hs : ∀ w w', ‖(s w : ℂ)‖ = ‖(s w' : ℂ)‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : HS L N, actL (scal L N s) h = r • h := by
  by_cases hne : Nonempty (InfinitePlace L)
  · obtain ⟨w0⟩ := hne
    have hs0 : (s w0 : ℂ) ≠ 0 := (s w0).ne_zero
    refine ⟨(‖(s w0 : ℂ)‖ ^ 2)⁻¹, by positivity, fun h => HS_ext fun w => ?_⟩
    have e : ((((scal L N s) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        Matrix.scalar (Fin N) ((s w : ℂ)⁻¹) := by
      simp only [scal, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val]
    rw [mat_actL, mat_smul, e]
    have hc : star ((s w : ℂ)⁻¹) * (s w : ℂ)⁻¹ = (((‖(s w0 : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', norm_inv, hs w w0]
      push_cast
      ring
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.smul_apply, Pi.star_apply]
    rw [Complex.real_smul, ← hc]
    ring
  · refine ⟨1, one_pos, fun h => HS_ext fun w => absurd ⟨w⟩ hne⟩

end PositivityTheory.KB.WhittakerCocycle

end
end

section

noncomputable section

namespace PositivityTheory.KB.WhittakerCocycle

theorem ev_eq_lc {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F (Fin.partialProd g)) z := by
  unfold ev
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul]

private theorem partialProd_contractNth_mul_eq_succAbove {G : Type} [Group G] {k : ℕ} (g : Fin (k + 1) → G) (j l : Fin (k + 1)) :
    Fin.partialProd (Fin.contractNth j (· * ·) g) l = Fin.partialProd g (j.succ.succAbove l) := by
  induction l using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
    simp
  | succ l ih =>
    rw [Fin.partialProd_succ, ih]
    rcases lt_trichotomy (l : ℕ) j with h | h | h
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.castSucc.succ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_lt _ _ _ _ h]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.partialProd_succ g l.castSucc,
        Fin.contractNth_apply_of_eq _ _ _ _ h, mul_assoc]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.contractNth_apply_of_gt _ _ _ _ h]

theorem lc_dC {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ)
    (hb : Inv (MonoidHom.id G) b) :
    Finsupp.linearCombination ℝ (fun g : Fin (k + 1) → G => dC b (Fin.partialProd g)) =
      (Finsupp.linearCombination ℝ (fun g : Fin k → G => b (Fin.partialProd g))).comp (bd G k) := by
  unfold Inv at hb
  refine Finsupp.lhom_ext (fun g r => ?_)
  rw [LinearMap.comp_apply]
  have hs : Finsupp.single g r = r • Finsupp.single g (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, map_smul]
  congr 1
  rw [Finsupp.linearCombination_single, one_smul]
  unfold bd

  rw [Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum]
  simp only [map_smul, map_zsmul, Finsupp.linearCombination_single, one_smul, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold dC
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have h0 := hb (g 0) (Fin.partialProd fun i => g i.succ)
    simp only [MonoidHom.id_apply, smul_eq_mul] at h0
    rw [← h0]
    congr 1
    funext l
    exact Fin.partialProd_succ' g l
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ]
    simp only [one_mul]
    congr 2
    funext l
    exact (partialProd_contractNth_mul_eq_succAbove g j l).symm

theorem pEv {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ) (hb : Inv (MonoidHom.id G) b)
    (z : Chn G (k + 1)) (hz : IsCyc z) : ev (MonoidHom.id G) (dC b) 1 z = 0 := by
  rw [ev_eq_lc, lc_dC b hb, LinearMap.comp_apply]
  unfold IsCyc at hz
  rw [hz, map_zero]

end PositivityTheory.KB.WhittakerCocycle

end
end

section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem cons_mul (a γ : Γ) (σ : ℕ → Γ) :
    (fun n => a * cons γ σ n) = cons (a * γ) (fun n => a * σ n) := by
  funext n; cases n <;> rfl

theorem extDeriv_congr_nhds {n : ℕ} {ω₁ ω₂ : V → V [⋀^Fin n]→L[ℝ] ℝ} {x : V} (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ x = extDeriv ω₂ x := by
  simp only [extDeriv, h.fderiv_eq]

theorem kf_equiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ) (H : Hyp U A φ)
    {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V) (a : Γ)
    (hB : ∀ h ∈ U, B h ∈ U) (hψ : ∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h)
    (hβ : ∀ σ, ∀ h ∈ U, (β σ (B h)).compContinuousLinearMap B = β (fun n => a * σ n) h)
    (σ : ℕ → Γ) {h : V} (hh : h ∈ U) :
    (Kf A φ β σ (B h)).compContinuousLinearMap B = Kf A φ β (fun n => a * σ n) h := by
  obtain ⟨s, W, hW, -, hs⟩ := hL H (B h) (hB h hh)
  have hfin : Function.HasFiniteSupport
      (fun γ => psi A φ γ (B h) • β (cons γ σ) (B h)) := by
    refine s.finite_toSet.subset ?_
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs (B h) (mem_of_mem_nhds hW)]
  have key : ∀ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
      (psi A φ γ (B h) • β (cons γ σ) (B h))
        = psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := by
    intro γ
    rw [map_smul, ← cons_mul, ← hβ _ h hh, ← hψ γ h hh]
    rfl
  calc (Kf A φ β σ (B h)).compContinuousLinearMap B
      = ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (∑ᶠ γ, psi A φ γ (B h) • β (cons γ σ) (B h)) := rfl
    _ = ∑ᶠ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (psi A φ γ (B h) • β (cons γ σ) (B h)) := map_finsum _ hfin
    _ = ∑ᶠ γ, psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := finsum_congr key
    _ = Kf A φ β (fun n => a * σ n) h :=
      finsum_comp_equiv (Equiv.mulLeft a)
        (f := fun γ => psi A φ γ h • β (cons γ (fun n => a * σ n)) h)

theorem pEquiv (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) : PEquiv U A φ := by
  intro H k c hc B a hB hψ
  have hfd : ∀ x, fderiv ℝ B x = B := fun x => B.fderiv
  have he : ∀ j σ, ∀ h ∈ U, (eta A φ c j σ (B h)).compContinuousLinearMap B
      = eta A φ c j (fun n => a * σ n) h := by
    intro j
    induction j with
    | zero =>
      intro σ h hh
      rw [eta.eq_1, eta.eq_1]
      ext m
      simp [hc a (fun i => σ i)]
    | succ j ih =>
      intro σ h hh
      have hK : ∀ x ∈ U, (Kf A φ (eta A φ c j) σ (B x)).compContinuousLinearMap B
          = Kf A φ (eta A φ c j) (fun n => a * σ n) x :=
        fun x hx => kf_equiv hL H (eta A φ c j) B a hB hψ ih σ hx
      have hdiff : DifferentiableAt ℝ (Kf A φ (eta A φ c j) σ) (B h) :=
        ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds (hB h hh))).differentiableAt (by simp)
      have hpb := extDeriv_pullback (f := B) (x := h) (r := ⊤) hdiff B.contDiff.contDiffAt le_top
      simp only [hfd] at hpb
      rw [eta.eq_2, eta.eq_2, ← hpb]
      apply extDeriv_congr_nhds
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      exact hK x hx
  intro j σ h hh
  exact ⟨he j σ h hh, kf_equiv hL H (eta A φ c j) B a hB hψ (he j) σ hh⟩

end PositivityTheory.KB.WhittakerCocycle

end
end

section

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def Stk (U : Set V) : Prop := ∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U →
  ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) → dC' (intS' ω) y = intS' (extDeriv ω) y

def Wf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (eta A φ c j g) (fun l : Fin (j + 1) => A (g (k + 1 - j + l)) o)

def Bf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (Kf A φ (eta A φ c j) g) (fun l : Fin (j + 1) => A (g (k - j + l)) o)

theorem kf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ)
    (h : ∀ n, n + j + 1 ≤ k + 1 → σ n = σ' n) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ') (fun n hn => by
    cases n with
    | zero => rfl
    | succ m => exact h m (by omega))]

theorem eta_top (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (τ τ' : ℕ → Γ) (x : V) (hx : x ∈ U) :
    eta A φ c (k + 1) τ x = eta A φ c (k + 1) τ' x := by
  have h0 := hC H k c hc (k + 1) le_rfl (cons (τ 0) τ') x hx
  rw [Nat.sub_self] at h0
  have e1 : eta A φ c (k + 1) (skip 0 (cons (τ 0) τ')) = eta A φ c (k + 1) τ' := by
    congr 1
  have e2 : eta A φ c (k + 1) (skip 1 (cons (τ 0) τ')) = eta A φ c (k + 1) τ :=
    hD k c (k + 1) _ _ (fun n hn => by
      have : n = 0 := by omega
      subst this
      simp [skip, cons])
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, e1, e2] at h0
  simp at h0
  rw [add_neg_eq_zero] at h0
  exact h0.symm

private theorem neg_one_pow_add_one_add_eq_mul (a : ℕ) (m : ℕ) : (-1 : ℝ) ^ (a + 1 + m) = (-1) ^ a * (-1) ^ (m + 1) := by
  ring

theorem chain (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) {o : V}
    (ho : o ∈ U) (a j : ℕ) (hk : a + j = k) (g : ℕ → Γ) :
    ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) =
      Wf A φ c o j g + (-1) ^ a * Wf A φ c o (j + 1) g := by
  subst hk
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Kf A φ (eta A φ c j) g := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin (j + 2) → V, Y = fun l : Fin (j + 2) => A (g (a + (l : ℕ))) o := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin (j + 1) → V, Z = fun l : Fin (j + 1) => A (g (a + 1 + (l : ℕ))) o :=
    ⟨_, rfl⟩
  have hYU : ∀ l, Y l ∈ U := fun l => by rw [hY]; exact H.mapsTo _ _ ho
  have hZU : ∀ l, Z l ∈ U := fun l => by rw [hZ]; exact H.mapsTo _ _ ho
  have hcont : ∀ σ, ContinuousOn (Kf A φ (eta A φ c j) σ) U :=
    fun σ => ((hSm H (a + j) c j σ).2).continuousOn
  have hK : ∀ i, a + 1 ≤ i → Kf A φ (eta A φ c j) (skip i g) = ω := by
    intro i hi
    rw [hω]
    exact kf_dep hD c j _ _ (fun n hn => by simp only [skip]; rw [if_pos (by omega)])
  have hF2 : ∀ x ∈ U, (∑ i ∈ Finset.range (a + 2),
      ((-1 : ℝ) ^ i) • Kf A φ (eta A φ c j) (skip i g)) x = eta A φ c j g x := by
    intro x hx
    have h1 := hH H j a (eta A φ c j) g x hx
    have h0 : ∀ γ, psi A φ γ x • delG (a + 1) (eta A φ c j) (cons γ g) x = 0 := by
      intro γ
      have := hC H (a + j) c hc j (by omega) (cons γ g) x hx
      rw [show a + j + 1 - j = a + 1 by omega] at this
      rw [this, smul_zero]
    have h2 : Kf A φ (delG (a + 1) (eta A φ c j)) g x = 0 := by
      simp only [Kf, h0, finsum_zero]
    rw [h2, sub_zero] at h1
    rw [← h1]
    simp only [delG, Finset.sum_apply]
  have hWj : Wf A φ c o j g = ∑ i ∈ Finset.range (a + 2),
      (-1 : ℝ) ^ i * intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    rw [← intS'_sum H.convex _ _ _ (fun i _ => hcont _) hZU]
    rw [intS'_congr H.convex hF2 hZU]
    simp only [Wf, hZ]
    congr 1
    funext l
    rw [show a + j + 1 - j + ↑l = a + 1 + ↑l by omega]
  have hBA : ∀ i, i < a + 1 → Bf A φ c o j (skip i g) = intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    intro i hi
    simp only [Bf, hZ]
    congr 1
    funext l
    simp only [skip]
    rw [if_neg (by omega), show a + j - j + ↑l + 1 = a + 1 + ↑l by omega]
  have hBB : ∀ m : Fin (j + 1), Bf A φ c o j (skip (a + 1 + ↑m) g) =
      intS' ω (fun l => Y (m.succ.succAbove l)) := by
    intro m
    simp only [Bf, hY]
    rw [hK _ (by omega)]
    congr 1
    funext l
    simp only [skip, Fin.succAbove]
    split_ifs <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;>
      first | (exfalso; omega) | (congr 3; omega)
  have hExt : extDeriv ω = eta A φ c (j + 1) g := by rw [hω]; rfl
  have hSt := hS j ω (by
    rw [hω]
    exact ((hSm H (a + j) c j g).2).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) Y hYU
  rw [hExt] at hSt
  rw [dC', Fin.sum_univ_succ] at hSt
  have hW1 : Wf A φ c o (j + 1) g = intS' (eta A φ c (j + 1) g) Y := by
    simp only [Wf, hY]
    congr 1
    funext l
    rw [show a + j + 1 - (j + 1) + ↑l = a + ↑l by omega]
  have hY0 : (fun l => Y ((0 : Fin (j + 2)).succAbove l)) = Z := by
    funext l
    simp only [hY, hZ, Fin.succAbove_zero, Fin.val_succ]
    rw [show a + (↑l + 1) = a + 1 + ↑l by omega]
  rw [hY0] at hSt
  rw [show a + j + 2 = (a + 1) + (j + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hBA i (Finset.mem_range.mp hi)])]
  rw [Finset.sum_range (fun m => (-1 : ℝ) ^ (a + 1 + m) * Bf A φ c o j (skip (a + 1 + m) g))]
  simp only [hBB]
  rw [Finset.sum_range_succ, hK _ le_rfl] at hWj
  rw [hWj, hW1, ← hSt]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, neg_one_pow_add_one_add_eq_mul, mul_assoc]
  rw [mul_add, ← Finset.mul_sum]
  ring

end PositivityTheory.KB.WhittakerCocycle

end
end
