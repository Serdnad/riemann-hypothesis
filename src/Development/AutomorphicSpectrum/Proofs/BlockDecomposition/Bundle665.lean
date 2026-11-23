module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_lineDer_of_growth (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : GlobalTheory.UAut.IsSm σ J φ) (hc : Continuous φ)
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {A : ℕ} {B : ℝ}
    (hB : ∀ g, ‖lineDer γ (lineDer γ φ) g‖ ≤ B * (height σ J g : ℝ) ^ A) : Continuous (lineDer γ φ) := by
  have hpos : ∀ g, 0 < (height σ J g : ℝ) := fun g =>
    zero_lt_one.trans_le (by exact_mod_cast GlobalTheory.AdelicU.one_le_height σ J g)
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (pow_pos (hpos 1) A)).1 ((norm_nonneg _).trans (hB 1))
  have hγc : Continuous γ := by
    obtain ⟨w, τ, Z, _, hy⟩ := hγ
    choose y hγ' hy using hy
    have hc : Continuous y := by
      rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
      have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
        funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
      rw [e]
      have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
        letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
        letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
        letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
        exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
    have : γ = fun t => embArch σ J w (y t) := funext hγ'
    rw [this]
    exact (continuous_embArch σ J w).comp hc
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp (GlobalTheory.AdelicU.continuous_height_GAd σ J)
  obtain ⟨c, hc'⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (hht.comp hγc)).bddAbove
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ g, ‖lineDer γ φ g - t⁻¹ • (φ (g * γ t) - φ g)‖ ≤
      B * ((height σ J g : ℝ) * c) ^ A * t := fun t t0 t1 g => by
    set q := t⁻¹ • (φ (g * γ t) - φ g) with hq
    have d1 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ g
    have d2 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := [γ]) (by simpa using hγ) hγ g
    simp only [List.foldr_cons, List.foldr_nil] at d1 d2
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun s => φ (g * γ s) - φ g - s • q)
      (f₁ := fun s => lineDer γ φ (g * γ s) - q) (f₂ := fun s => lineDer γ (lineDer γ φ) (g * γ s))
      (fun s => by simpa using ((d1 s).sub_const (φ g)).fun_sub ((hasDerivAt_id s).smul_const q))
      (fun s => (d2 s).sub_const q) t0.le (B := B * ((height σ J g : ℝ) * c) ^ A) fun s hs' => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _).le
          ((NNReal.coe_le_coe.2 (GlobalTheory.AdelicU.height_mul_le σ J _ _)).trans (by
            rw [NNReal.coe_mul]
            exact mul_le_mul_of_nonneg_left (hc' ⟨s, ⟨hs'.1, hs'.2.trans t1⟩, rfl⟩) (hpos g).le)) A) hB0)
    rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one, hq, smul_inv_smul₀ t0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ t] at this
    exact le_of_mul_le_mul_left this t0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g : GAd σ J => B * ((height σ J g : ℝ) * c) ^ A :=
    continuous_const.mul ((hht.mul continuous_const).pow A)
  obtain ⟨t, t0, t1, t2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := t))) (continuous_const (y := ε))).mem_nhds t2,
    fun g => t⁻¹ • (φ (g * γ t) - φ g),
    (((hc.comp (continuous_mul_const _)).sub hc).const_smul t⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key t t0 t1 y).trans_lt hy

theorem lineDer_mul_fin {φ : GAd σ J → ℂ} {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {k : GAd σ J} (hk : k ∈ finPts σ J)
    (e : ∀ g, φ (g * k) = φ g) (g : GAd σ J) : lineDer γ φ (g * k) = lineDer γ φ g := by
  have : (fun t => φ (g * k * γ t)) = fun t => φ (g * γ t) := funext fun t => by
    have hmem : γ t ∈ infPts σ J := by
      obtain ⟨w, τ, Z, -, ht⟩ := hγ
      obtain ⟨y, hy, -⟩ := ht t
      rw [hy]
      exact mem_infPts.2 (projFin_embArch σ J w y)
    have hc := GlobalTheory.CompanionTheory.SiegelAssemble.commute_of_mem hmem hk
    calc
      φ (g * k * γ t) = φ ((g * γ t) * k) := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
      _ = φ (g * γ t) := e _
  simp only [lineDer, this]

theorem isCuspidal_lineDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {φ : GAd σ J → ℂ} (hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ)
    (hc : Continuous φ) (hs : GlobalTheory.UAut.IsSm σ J φ) (hcu : IsCuspidal σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hc' : Continuous (lineDer γ φ)) : IsCuspidal σ J (lineDer γ φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 x
  have hI : GlobalTheory.UAut.IsIsoCols σ J C := hC.2
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hI
  have hco := GlobalTheory.UAut.cocompact_unipRad h hJ hI
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) (lineDer γ φ) := GlobalTheory.UAut.ConstAut.leftInv_foldr hl [γ]
  have h0 : ∀ y, GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J C) φ y = 0 := fun y =>
    (hco.constTermOn_eq_zero_iff h𝓕 hl y).2 (hcu r C hC μ 𝓕 hμ h𝓕 y)
  have hd := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco hl hc hl' hc'
    (by
      obtain ⟨w, τ, Z, _, hy⟩ := hγ
      choose y hγ' hy using hy
      have hc : Continuous y := by
        rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
        have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
          funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
        rw [e]
        have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
          letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
          letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
          letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
          exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
        exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
      have : γ = fun t => embArch σ J w (y t) := funext hγ'
      rw [this]
      exact (continuous_embArch σ J w).comp hc)
    (GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ) x
  simp only [h0] at hd
  rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one] at hd
  exact (hco.constTermOn_eq_zero_iff h𝓕 hl' x).1 (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem good_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  intro F E _ _ _ _ _ σ h n J hJ U A φ γ hφ hγ
  obtain ⟨B, hB⟩ := hφ.growth [γ, γ] (by simpa using hγ)
  have hcont : Continuous (lineDer γ φ) :=
    continuous_lineDer_of_growth h hφ.smooth hφ.cont hγ (A := A) (B := B) (by simpa using hB)
  refine ⟨GlobalTheory.UAut.ConstAut.leftInv_foldr hφ.left [γ], fun k hk hf => lineDer_mul_fin hγ hf (hφ.level k hk hf), hcont,
    GlobalTheory.UAut.isSm_lineDer hφ.smooth hγ, fun l hl => ?_,
    isCuspidal_lineDer h hJ hφ.left hφ.cont hφ.smooth hφ.cusp hγ hcont⟩
  have := hφ.growth (l ++ [γ]) (by
    intro δ hδ
    rcases List.mem_append.1 hδ with e | e
    · exact hl δ e
    · rw [List.mem_singleton.1 e]; exact hγ)
  simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {r : ℕ}

theorem cone_anti {c c' : ℝ} (hcc : c' ≤ c) {t : Fin r → ℝ} (ht : t ∈ cone r c) : t ∈ cone r c' :=
  ⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h),
    fun i h => hcc.trans (ht.2.2 i h)⟩

theorem cone_step {c : ℝ} (hc0 : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (d : ℕ) :
    ∀ a b : Fin r, b.val = a.val + d → c ^ d * t b ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have e : b = a := Fin.ext (by simpa using h)
    subst e
    simp
  | succ d ih =>
    intro a b h
    have hm : a.val + d < r := by
      have := b.2
      omega
    have h1 := ih a ⟨a.val + d, hm⟩ rfl
    have h2 := ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)
    calc c ^ (d + 1) * t b = c ^ d * (c * t b) := by ring
      _ ≤ c ^ d * t ⟨a.val + d, hm⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ t a := h1

theorem cone_pow_mul_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    {a b : Fin r} (hab : a ≤ b) : c ^ r * t b ≤ t a := by
  have hab' : a.val ≤ b.val := hab
  have h1 := cone_step hc0 ht (b.val - a.val) a b (by omega)
  have hle : c ^ r ≤ c ^ (b.val - a.val) :=
    pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)
  exact (mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1

theorem cone_pow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    (i : Fin r) : c ^ r ≤ t i := by
  have hi := i.2
  have hl : r - 1 < r := by omega
  have h1 := cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)
  have h2 := ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)
  calc c ^ r ≤ c ^ (r - 1 - i.val + 1) := pow_le_pow_of_le_one hc0.le hc1 (by omega)
    _ = c ^ (r - 1 - i.val) * c := pow_succ _ _
    _ ≤ c ^ (r - 1 - i.val) * t ⟨r - 1, hl⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ t i := h1

theorem weights_across_levels {e A T wa wb : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heA : e ≤ A) (heT : e ≤ T)
    (h : (e * A ≤ wa ∧ wb * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ wa * T ∧ e * A * wb ≤ 1) ∨ (e * A ≤ wa ∧ e * A * wb ≤ 1)) :
    wb * (e ^ 4 * A) ≤ T * wa := by
  have hA0 : 0 < A := he0.trans_le heA
  have hT0 : 0 < T := he0.trans_le heT
  have hee : e * e ^ 2 ≤ e ^ 2 := by
    have : 0 ≤ e ^ 2 := by positivity
    nlinarith
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e * (e * A) ≤ wa := by
      have : 0 ≤ e * A := by positivity
      nlinarith
    calc wb * (e ^ 4 * A) = (wb * e ^ 2) * (e * (e * A)) := by ring
      _ ≤ T * wa := mul_le_mul h2 h3 (by positivity) hT0.le
  · calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * e ^ 2 := mul_le_mul h2 hee (by positivity) zero_le_one
      _ = e ^ 2 := one_mul _
      _ ≤ wa * T := h1
      _ = T * wa := mul_comm _ _
  · have h3 : e * e ^ 2 ≤ T * wa := by
      calc e * e ^ 2 = e * (e * e) := by ring
        _ ≤ T * (e * A) := mul_le_mul heT (mul_le_mul_of_nonneg_left heA he0.le) (by positivity) hT0.le
        _ ≤ T * wa := mul_le_mul_of_nonneg_left h1 hT0.le
    calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * (e * e ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = e * e ^ 2 := one_mul _
      _ ≤ T * wa := h3

theorem frameWt_div_le_div_ratio : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c,
    ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  intro r c hc
  have hc0 : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  set c' := min c 1 with hc'
  set e := c' ^ r with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ hc0.le hc1
  refine ⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩
  have ht : t ∈ cone r c' := cone_anti (min_le_left _ _) ht0
  have hpos := ht.1
  have hge : ∀ i, e ≤ t i := cone_pow_le hc0 hc1 ht
  have hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a := fun h => cone_pow_mul_le hc0 hc1 ht h
  have hsq : e ^ 2 ≤ e := by nlinarith
  obtain ⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by
    by_cases h : s.val + 1 < r
    · refine ⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩
      have hb' : s.val < b.val := hb
      exact Fin.le_def.2 (by simp only []; omega)
    · refine ⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩
      have hb' : s.val < b.val := hb
      have := b.2
      omega
  have hT0 : 0 < T := he0.trans_le heT
  have lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simpa [frameWt] using hle ha
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
  have lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1 := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simp only [frameWt]
      rw [← div_eq_mul_inv]
      exact (div_le_one (hpos a)).2 (hle ha)
  have lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T := by
    intro γ h
    have key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T := fun b hb => by
      have h1 := hTb b hb
      have h2 := hge b
      constructor
      · rw [sq]
        exact mul_le_mul h2 heT he0.le (hpos b).le
      · have : 0 ≤ e * t b := (mul_pos he0 (hpos b)).le
        nlinarith
    rcases γ with _ | a | a
    · simp only [frameWt, one_mul]
      exact ⟨hsq.trans heT, hsq.trans heT⟩
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      simpa [frameWt] using key a ha
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      have h1 := hTb a ha
      have h2 := hge a
      simp only [frameWt]
      rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]
      constructor
      · have : 0 ≤ e * t a := (mul_pos he0 (hpos a)).le
        nlinarith
      · rw [sq]
        exact mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2 := by
    intro γ
    rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp
  have hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨
      (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨
      (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1) := by
    rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;>
      first
        | exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩
        | exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)
        | exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)
        | (exfalso; omega)
  have key := weights_across_levels he0 he1 (hge s) heT hcases
  have hwa : 0 < frameWt t α := frameWt_pos hpos α
  have hA0 : 0 < t s := hpos s
  have hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s) := by
    rw [hrat]
    field_simp
  rw [hK, div_le_div_iff₀ hwa (by positivity)]
  exact key

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitGram

variable {D : D7}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem gramQ_eq (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    gramQ V x = Formalism.UG.cT (sg D) x * (HSpace.gram V * x) := rfl

theorem gramQ_mul (V : HSp D) {r : ℕ} {δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hδ : Formalism.UG.cT (sg D) δ * HSpace.gram V * δ = HSpace.gram V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) : gramQ V (δ * x) = gramQ V x := by
  rw [gramQ_eq, gramQ_eq, Formalism.UG.cT_mul]
  calc Formalism.UG.cT (sg D) x * Formalism.UG.cT (sg D) δ * (HSpace.gram V * (δ * x))
      = Formalism.UG.cT (sg D) x * ((Formalism.UG.cT (sg D) δ * HSpace.gram V * δ) * x) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hδ]

theorem gramQ_herm (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ((gramQ V x).map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = gramQ V x := by
  have hJ : Formalism.UG.cT (sg D) (HSpace.gram V) = HSpace.gram V := Matrix.ext fun i j => (GlobalTheory.Doubling.isHermND_gram V).1 i j
  have hx : Formalism.UG.cT (sg D) (Formalism.UG.cT (sg D) x) = x := Matrix.ext fun i j => star_star (x i j)
  change Formalism.UG.cT (sg D) (gramQ V x) = gramQ V x
  rw [gramQ_eq, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hx, hJ, Matrix.mul_assoc]

theorem leftInv_subtypeSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (V : HSp D) {n : ℕ}
    (f : Mx D V.rank n → M) (p : Matrix (Fin V.rank) (Fin n) D.host.E → Prop)
    (hp : ∀ δ : GL (Fin V.rank) D.host.E, Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V →
      ∀ ξ, p ξ → p (δ.1 * ξ)) :
    LeftInv (GQ V) fun h => ∑' ξ : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ},
      f (GlobalTheory.SiegelFormula.invPt V h ξ.1) := by
  intro γ hγ h
  obtain ⟨δ, hU, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  have hU' : Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V := hU
  have hUi : Formalism.UG.cT (sg D) (δ⁻¹).1 * HSpace.gram V * (δ⁻¹).1 = HSpace.gram V :=
    (Formalism.UG.UJ (sg D) (HSpace.gram V)).inv_mem hU
  let e : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} ≃ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} :=
    ⟨fun ξ => ⟨δ.1 * ξ.1, hp δ hU' _ ξ.2⟩, fun ξ => ⟨(δ⁻¹).1 * ξ.1, hp δ⁻¹ hUi _ ξ.2⟩,
      fun ξ => Subtype.ext (by simp), fun ξ => Subtype.ext (by simp)⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (GlobalTheory.SiegelFormula.invPt V h ξ.1))
  simp only [GlobalTheory.SiegelFormula.invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

def fibreEquiv (V : HSp D) (r : ℕ) :
    (Σ β : HermE D r, {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1}) ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r} where
  toFun p := ⟨p.2.1, p.2.2.1⟩
  invFun x := ⟨⟨gramQ V x.1, gramQ_herm V x.1⟩, ⟨x.1, x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, x, hx, hg⟩
    change gramQ V x = b at hg
    subst hg
    rfl
  right_inv _ := rfl

theorem hasSum_IfrB : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ →
    ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r →
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ) := by
  intro D r V θ hθ ν hν φ hφ habs
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  haveI : Countable (HermE D r) :=
    inferInstanceAs (Countable {b : Matrix (Fin r) (Fin r) D.host.E // _})
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hA := leftInv_subtypeSum V (fun y => ‖φ y‖ₑ)
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r)
    (fun δ _ ξ h => (hrank δ ξ).trans h)
  have hfin : ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r},
      ‖φ (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := by
    refine (lintegral_mono fun q => ?_).trans_lt habs
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := GlobalTheory.CompanionTheory.ThetaOrbit.hasSum_average_descend (Γ := GQ V) (μ := ν) (fibreEquiv V r)
    (fun h x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun x => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    hA
    (fun β => leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  exact key

end GlobalTheory.CompanionTheory.SplitGram

end
end
