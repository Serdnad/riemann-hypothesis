module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem exists_analyticAt_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {f : E → F} {u : E} (hf : AnalyticAt ℂ f u)
    (hk : (fderiv ℂ f u : E →ₗ[ℂ] F).ker = ⊥) :
    ∃ Λ : F → E, AnalyticAt ℂ Λ (f u) ∧ ∀ᶠ v in 𝓝 u, Λ (f v) = v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  let L : F →L[ℂ] E := LinearMap.toContinuousLinearMap g
  have hLf : ∀ x, L (fderiv ℂ f u x) = x := fun x => by
    have := LinearMap.congr_fun hg x
    simpa [L] using this
  let h : E → E := fun v => L (f v)
  have hh : AnalyticAt ℂ h u := (L.analyticAt (f u)).comp hf
  have hd : fderiv ℂ h u = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := by
    have h1 : HasFDerivAt h (L.comp (fderiv ℂ f u)) u := L.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt
    rw [h1.fderiv]
    ext x
    simp [hLf]
  have hs : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) u := by
    have := hh.hasStrictFDerivAt
    rwa [hd] at this
  have hsrc : u ∈ (hs.toOpenPartialHomeomorph h).source := hs.mem_toOpenPartialHomeomorph_source
  have hcoe : ((hs.toOpenPartialHomeomorph h : OpenPartialHomeomorph E E) : E → E) = h :=
    hs.toOpenPartialHomeomorph_coe
  have han : AnalyticAt ℂ (hs.toOpenPartialHomeomorph h).symm (h u) := by
    have := (hs.toOpenPartialHomeomorph h).analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hsrc
      (by rw [hcoe]; exact hh) (by rw [hcoe]; exact hd)
    rwa [hcoe] at this
  refine ⟨fun y => (hs.toOpenPartialHomeomorph h).symm (L y), ?_, ?_⟩
  · exact AnalyticAt.comp (f := fun y => L y) (g := (hs.toOpenPartialHomeomorph h).symm) han (L.analyticAt (f u))
  · filter_upwards [(hs.toOpenPartialHomeomorph h).open_source.mem_nhds hsrc] with v hv
    have := (hs.toOpenPartialHomeomorph h).left_inv hv
    rwa [hcoe] at this

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_congr_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem OrbitChart.analyticAt_affCoord {P : Ideal (MRing ι)} {e : ℕ} (C : OrbitChart P e) {w : Fin e → ℂ}
    (hw : w ∈ C.D) (p : (k : K) → ι k) (hp : ∀ k, C.φ w ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun w' => affCoord p (C.φ w')) w := by
  rw [analyticAt_pi_iff]
  intro q
  exact (C.holo q w hw).div (C.holo ⟨q.1, p q.1⟩ w hw) (hp q.1)

end

theorem OrbitChart.analyticOnNhd_transition (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e) :
    AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  rintro w₀ ⟨hw₀, hO₀⟩
  obtain ⟨O', hO'o, hO'⟩ := C₂.O_open
  have hcont : ContinuousAt C₁.φ w₀ := continuousAt_pi.2 fun q => (C₁.holo q w₀ hw₀).continuousAt
  have hS : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O := by
    have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D := C₁.isOpen_D.mem_nhds hw₀
    have h2 : ∀ᶠ w in 𝓝 w₀, C₁.φ w ∈ O' :=
      hcont (hO'o.mem_nhds (by rw [hO'] at hO₀; exact hO₀.1))
    filter_upwards [h1, h2] with w a b
    exact ⟨a, by rw [hO']; exact ⟨b, C₁.mem w a⟩⟩
  have hTc : ContinuousAt (fun w => C₂.ρ (C₁.φ w)) w₀ := by
    have h1 : Tendsto C₁.φ (𝓝 w₀) (𝓝[C₂.O] (C₁.φ w₀)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, hS.mono fun _ h => h.2⟩
    exact (C₂.ρ_cont _ hO₀).tendsto.comp h1
  choose p hp using (C₁.mem w₀ hw₀).1
  have hu₀ : C₂.ρ (C₁.φ w₀) ∈ C₂.D := C₂.ρ_mem _ hO₀
  have horb := C₂.φ_ρ _ hO₀
  have hne : ∀ k, C₂.φ (C₂.ρ (C₁.φ w₀)) ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨c, hc, hz⟩ := horb
    intro k
    rw [hz]
    exact mul_ne_zero (hc k) (hp k)
  have hA₂ := C₂.analyticAt_affCoord hu₀ p hne
  have hA₁ := C₁.analyticAt_affCoord hw₀ p hp
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_analyticAt_leftInverse hA₂ (C₂.immersion _ hu₀ p hne)
  have hval : affCoord p (C₂.φ (C₂.ρ (C₁.φ w₀))) = affCoord p (C₁.φ w₀) := affCoord_congr_sameOrbit p horb
  have hΛ' : AnalyticAt ℂ Λ (affCoord p (C₁.φ w₀)) := by
    have := hΛ
    simp only [hval] at this
    exact this
  have hcomp : AnalyticAt ℂ (fun w => Λ (affCoord p (C₁.φ w))) w₀ :=
    AnalyticAt.comp (f := fun w => affCoord p (C₁.φ w)) (g := Λ) hΛ' hA₁
  refine hcomp.congr ?_
  filter_upwards [hS, hTc.eventually hΛl] with w hw hl
  rw [← hl, affCoord_congr_sameOrbit p (C₂.φ_ρ _ hw.2)]

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

section Minor

variable {N : ℕ}

theorem minorIJ_mul_one_add_single (H : Matrix (Fin N) (Fin N) ℂ) (I C : Finset (Fin N)) {ca cb : Fin N} (hlt : ca < cb)
    (hiff : ca ∈ C ↔ cb ∈ C) (t : ℂ) :
    minorIJ (H * (1 + Matrix.single cb ca t)) I C = minorIJ H I C := by
  have hne : ∀ x, ¬ (x = cb ∧ x = ca) := fun x hx => hlt.ne (hx.2.symm.trans hx.1)
  have hent : ∀ x y, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + (if x = cb ∧ y = ca then t else 0) := by
    intro x y
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]
  rw [minorIJ_mul_of_support H _ I C]
  · have h1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) C C = 1 := by
      rw [minorIJ_eq_det _ C C _ rfl rfl, Matrix.det_of_lowerTriangular]
      · refine Finset.prod_eq_one fun x _ => ?_
        rw [Matrix.submatrix_apply, hent, if_pos rfl, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        exact hne _ ⟨e1, e2⟩
      · intro x y hxy
        have hxy' : x < y := hxy
        have hs := (C.orderEmbOfFin rfl).strictMono hxy'
        rw [Matrix.submatrix_apply, hent, if_neg hs.ne, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        rw [e1, e2] at hs
        exact absurd hs (not_lt.mpr hlt.le)
    rw [h1, mul_one]
  · intro k c hc hk
    have hkc : k ≠ c := by
      rintro rfl
      exact hk hc
    rw [hent, if_neg hkc, if_neg, add_zero]
    rintro ⟨e1, e2⟩
    rw [e1] at hk
    rw [e2] at hc
    exact hk (hiff.mp hc)

theorem mem_stepCols_iff {j : ℕ} {a b ca cb i : Fin N} (hb : (b : ℕ) = a + 1) (h2 : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have h3 := i.2
  have h4 := b.2
  have h5 := ca.2
  have h6 := cb.2
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

end Minor

section Low

variable {Ψ : Type} {N j : ℕ}

theorem lowMat_isBlockDiag (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) := by
  intro x y hxy
  unfold lowMat
  rw [_root_.dite_eq_right (fun e => hxy e.2), if_neg]
  rintro rfl
  exact hxy Iff.rfl

theorem lowMat_det (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : (lowMat c τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_irrefl _ e.1), if_pos rfl]
  · intro x y hxy
    have hxy' : x < y := hxy
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_asymm hxy' e.1), if_neg hxy'.ne]

theorem analytic_wH {n e : ℕ} (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ)
    (r s : Fin N) (S : Set (Fin e → ℂ)) : AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) S := by
  have hl : ∀ x, AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' x s) S := by
    intro x
    unfold lowMat
    by_cases hh : s < x ∧ ((x : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · simp only [dif_pos hh, wL]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ)
        (ε (Sum.inr (Sum.inl ⟨(τ', x, s), hh⟩)))).analyticOnNhd _
    · simp only [_root_.dite_eq_right hh]
      exact analyticOnNhd_const
  have : (fun w => wH h ε τ' w r s) = fun w => ∑ x, h τ' r x * lowMat (wL ε w) τ' x s := by
    funext w
    simp only [wH, Matrix.mul_apply]
  rw [this]
  exact Finset.analyticOnNhd_fun_sum _ fun x _ => analyticOnNhd_const.mul (hl x)

end Low

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk}
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {H : Ψ → Matrix (Fin N) (Fin N) ℂ}

theorem flagZ_base (k : NonPluckerBlocks M.blk) (m : ι k.1) : flagZ M F zb H ⟨k.1, m⟩ = zb ⟨k, m⟩ := by
  unfold flagZ
  rw [_root_.dite_eq_right (fun e => by obtain ⟨p, hp⟩ := e; exact k.2 p hp)]

theorem flagZ_step {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagZ M F zb H ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (H p.1) I (stepCols N j p.2) := by
  have e : ∃ p, M.blk p = some k := ⟨p, hp⟩
  have hc : e.choose = p := M.blk_inj _ _ _ e.choose_spec hp
  unfold flagZ
  simp only [dif_pos e, hc]

variable {k₀ : K} {τ : Ψ} {ca cb : Fin N} {t : ℂ}

theorem fst_sqZ (k : K) (m : ι k) :
    fstPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := rfl

theorem snd_sqZ_ne {k : K} (hk : k ≠ k₀) (m : ι k) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k, m⟩) = _
  rw [v₁_ne (p := ⟨k, m⟩) hk]
  rfl

theorem snd_sqZ_self (m : ι k₀) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k₀, m⟩ =
      flagZ M F zb (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k₀, m⟩) = _
  rw [v₁_self]
  rfl

theorem basePart_fst : basePart M.blk (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  exact flagZ_base k m

theorem basePart_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) :
    basePart M.blk (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  have hne : k.1 ≠ k₀ := fun e => k.2 (τ, a) (by rw [hk₀, e])
  show sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k.1, m⟩ = _
  rw [snd_sqZ_ne hne]
  exact flagZ_base k m

theorem exact_fst (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (p : Ψ × Fin N) :
    M.ExactAt F p (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) (H p.1) := by
  refine ⟨fun k => by rw [basePart_fst]; exact hn k, fun k hk m => ?_⟩
  rw [fst_sqZ, flagZ_step hk, basePart_fst]

theorem exact_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) (hlt : ca < cb)
    (hiff : ∀ i, i ≠ a → (ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i))
    (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (τ' : Ψ) (i : Fin N) :
    M.ExactAt F (τ', i) (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t))
      (if τ' = τ then H τ * (1 + Matrix.single cb ca t) else H τ') := by
  refine ⟨fun k => by rw [basePart_snd hk₀]; exact hn k, fun k hk m => ?_⟩
  rw [basePart_snd hk₀]
  by_cases hkk : k = k₀
  · subst hkk
    have hp : (τ', i) = (τ, a) := M.blk_inj _ _ _ hk hk₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [snd_sqZ_self, flagZ_step hk₀, if_pos rfl, Function.update_self]
  · rw [snd_sqZ_ne hkk, flagZ_step hk]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hτ : τ' = τ
    · subst hτ
      have hia : i ≠ a := by
        rintro rfl
        exact hkk (Option.some_injective _ (hk.symm.trans hk₀))
      rw [if_pos rfl, minorIJ_mul_one_add_single _ _ _ hlt (hiff i hia)]
    · rw [if_neg hτ]

end Flag

theorem chart_exact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hb, h2, hk₀, hca, hcb, -, -, hB, -, -, hh⟩ := hW
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine ⟨fun τ' r s => analytic_wH h ε τ' r s _, fun w hw => ⟨fun τ' => ⟨?_, ?_⟩, ?_, fun τ' i => ⟨?_, ?_⟩⟩⟩
  · exact isBlockDiag_mul (hh τ').1 (lowMat_isBlockDiag _ _)
  · rw [wH, Matrix.det_mul, lowMat_det, mul_one]
    exact (hh τ').2
  · exact basePart_fst
  · exact exact_fst (H := fun τ' => wH h ε τ' w) ((hB.2.2.2.2 _ hw).2.1) (τ', i)
  · exact exact_snd (H := fun τ' => wH h ε τ' w) hk₀ hlt
      (fun i hi => mem_stepCols_iff hb h2 hca hcb hi) ((hB.2.2.2.2 _ hw).2.1) τ' i

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_self_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  have key : minorIJ X C C = minorIJ Xᵀ C C := by
    rw [minorIJ_eq_det X C C C.card rfl rfl, minorIJ_eq_det Xᵀ C C C.card rfl rfl,
      ← Matrix.transpose_submatrix, Matrix.det_transpose]
  rw [key, minorIJ_self_of_triangular Xᵀ (fun i j hij => by simpa [Matrix.transpose_apply] using hX.2 j i hij) C]
  exact Finset.prod_eq_one (fun c _ => hX.1 c)

theorem minorIJ_insert_erase_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) {C : Finset (Fin N)}
    {a' b' : Fin N} (hb : b' ∈ C) (hmax : ∀ c ∈ C, c ≤ b') (hlt : b' < a') :
    minorIJ X (insert a' (C.erase b')) C = X a' b' := by
  have ha : a' ∉ C := fun h => absurd (hmax a' h) (not_le.mpr hlt)
  obtain ⟨n, hn⟩ : ∃ n, C.card = n + 1 :=
    ⟨C.card - 1, by have := Finset.card_pos.mpr ⟨b', hb⟩; omega⟩
  have hR : (insert a' (C.erase b')).card = n + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hb, hn]
    rfl
  set eC := C.orderEmbOfFin hn with heC
  have hlast : eC (Fin.last n) = b' := by
    have hmem : b' ∈ Set.range eC := by rw [heC, Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨k, hk⟩ := hmem
    rcases (Fin.le_last k).lt_or_eq with h | h
    · have h1 : eC k < eC (Fin.last n) := eC.strictMono h
      have h2 : eC (Fin.last n) ∈ C := Finset.orderEmbOfFin_mem C hn _
      exact absurd (hmax _ h2) (not_le.mpr (hk ▸ h1))
    · rw [← h, hk]
  have hlt' : ∀ k : Fin (n + 1), k ≠ Fin.last n → eC k < b' := fun k hk =>
    hlast ▸ eC.strictMono (lt_of_le_of_ne (Fin.le_last k) hk)
  let f : Fin (n + 1) → Fin N := fun k => if k = Fin.last n then a' else eC k
  have hfmono : StrictMono f := by
    intro i j hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp only [f, if_neg hi]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]; exact (hlt' i hi).trans hlt
    · rw [if_neg hj]; exact eC.strictMono hij
  have hfmem : ∀ k, f k ∈ insert a' (C.erase b') := by
    intro k
    simp only [f]
    split_ifs with hk
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(hlt' k hk).ne, Finset.orderEmbOfFin_mem C hn k⟩)
  have hR' : ⇑((insert a' (C.erase b')).orderEmbOfFin hR) = f :=
    (Finset.orderEmbOfFin_unique hR hfmem hfmono).symm
  rw [minorIJ_eq_det X _ C (n + 1) hR hn, hR', Matrix.det_of_lowerTriangular]
  · have h1 : ∀ k : Fin n, X.submatrix f eC k.castSucc k.castSucc = 1 := by
      intro k
      show X (f k.castSucc) (eC k.castSucc) = 1
      simp only [f, if_neg (Fin.castSucc_lt_last k).ne]
      exact hX.1 _
    rw [Fin.prod_univ_castSucc, Finset.prod_eq_one (fun k _ => h1 k), one_mul]
    show X (if Fin.last n = Fin.last n then a' else eC (Fin.last n)) (eC (Fin.last n)) = X a' b'
    rw [if_pos rfl, hlast]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    simp only [Matrix.submatrix_apply, f, if_neg hi]
    exact hX.2 _ _ (eC.strictMono hij')

theorem mem_stepCols_stepOf (N j : ℕ) (c : Fin N) :
    c ∈ stepCols N j (stepOf N j c) ∧ ∀ x ∈ stepCols N j (stepOf N j c), x ≤ c := by
  have hc := c.isLt
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [stepCols, stepOf]
    split_ifs
    all_goals (try simp)
    all_goals omega
  · have hx' := x.isLt
    simp only [stepCols, stepOf] at hx
    rw [Fin.le_iff_val_le_val]
    split_ifs at hx
    all_goals (try simp at hx)
    all_goals omega

theorem minorIJ_stepCols_of_isLowerUni (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N) (_hj : j ≤ N)
    (_hd : IsBlockDiag j X) (hX : IsLowerUni X) (hlt : b' < a') (_hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) :
    minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧
      minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  obtain ⟨hb, hmax⟩ := mem_stepCols_stepOf N j b'
  exact ⟨minorIJ_self_of_isLowerUni hX _, minorIJ_insert_erase_of_isLowerUni hX hb hmax hlt⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.coordinate_ratio_value_at_point : ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k), z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 → y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.scaled_coordinates_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.local_section_vertical_factor : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo <;> assumption)
end
