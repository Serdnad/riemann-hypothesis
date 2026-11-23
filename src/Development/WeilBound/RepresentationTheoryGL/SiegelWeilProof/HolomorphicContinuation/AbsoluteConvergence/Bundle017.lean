module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtEvalCurve
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
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

@[expose] public section

section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem lam_cont (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) {B : Set ℂ} (hB : IsOpen B) {w : ℂ} (hw : w ∈ B) (F : ℂ → G → ℂ)
    (hFc : ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ)) (hFh : ∀ g, DifferentiableOn ℂ (F · g) B)
    (hFi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) : ContinuousAt (fun z => l (F z)) w := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hFcont : ∀ z ∈ B, Continuous (F z) := by
    intro z hzB
    exact hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzB, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C B (fun z x => F z x) hB
    (hFc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hFh x)
  have hfeq : ∀ z ∈ B, l (F z) = L (Φ z) := by
    intro z hzB
    have hmem : F z ∈ invSub Γ := ⟨hFcont z hzB, hFi z hzB⟩
    rw [hL (F z) hmem (hFcont z hzB)]
    congr 1
    ext x
    rw [hΦ z hzB x]
    rfl
  have hd : DifferentiableOn ℂ (fun z => l (F z)) B :=
    (L.differentiable.comp_differentiableOn hΦd).congr hfeq
  exact (hd.differentiableAt (hB.mem_nhds hw)).continuousAt

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem scal_zero (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) : scal (aH X 0) y = y := by
  funext a j; simp [scal, aH]

theorem continuous_scal (α : Fin n → ℝ) : Continuous (scal (m := m) α) :=
  continuous_pi fun a => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs; fun_prop

theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) :=
  continuous_pi fun i => continuous_pi fun j => continuous_evX _

theorem prod_aH (X : Fin n → ℝ) (h : ℝ) :
    (∏ j, aH X h j ^ (2 * m) : ℝ) = Real.exp (2 * (h * ((m : ℝ) * ∑ j, X j))) := by
  simp only [aH, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem gaussPart : GaussPart := by
  intro m n ε c t hc X b hb Q
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  set E : (Fin m → Fin n → ℂ) → ℂ := fun y => Complex.exp (Complex.I * t * (b * gramX ε y).trace) with hEdef
  have hE : ∀ y, ‖E y‖ = 1 := fun y => norm_phase t _ (trace_im ε y hb)
  have hEc : Continuous E := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace
  set A : ℝ := (m : ℝ) * ∑ j, X j with hA
  set P' : PX m n := dil c X Q - ((m : ℂ) * ∑ j, (X j : ℂ)) • Q with hP'
  let φ : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  let φ' : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX P' (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  have hφc : ∀ (P : PX m n) (s : ℝ), Continuous fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y :=
    fun P s => (((continuous_evX P).comp (continuous_scal _)).mul ((continuous_gs c).comp (continuous_scal _))).mul hEc
  have hH : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun y : Fin m → Fin n → ℂ => (1 + ‖y‖) ^ (-r)) := by
    have : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ)) < r := by rw [hr]; linarith
    exact integrable_one_add_norm this
  have hdomI : ∀ (P : PX m n), ∃ K : ℝ, ∀ s : ℝ, |s| < 1 → ∀ y,
      ‖evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y‖ ≤ K * (1 + ‖y‖) ^ (-r) := by
    intro P
    obtain ⟨K, -, hK⟩ := dom_bound c hc X P
    exact ⟨K, fun s hs y => by rw [norm_mul, hE, mul_one]; exact hK s hs y⟩
  have hintP : ∀ (P : PX m n) (s : ℝ), |s| < 1 →
      Integrable fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y := by
    intro P s hs
    obtain ⟨K, hK⟩ := hdomI P
    exact Integrable.mono' (hint.const_mul K) (hφc P s).aestronglyMeasurable
      (Eventually.of_forall fun y => hK s hs y)

  have key : ∀ h : ℝ, Complex.exp (-((h * A : ℝ) : ℂ)) * secN ε c t Q (bS X h b) =
      Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := by
    intro h
    have hpos : ∀ j, 0 < aH X h j := fun j => Real.exp_pos _
    have h1 : secN ε c t Q (bS X h b) = ((∏ j, aH X h j ^ (2 * m) : ℝ) : ℂ) * ∫ y, φ h y := by
      unfold secN
      rw [integral_scal (aH X h) hpos]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [φ, hEdef, trace_scal]
    rw [h1, prod_aH, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hA]; push_cast; ring

  obtain ⟨K, hK⟩ := hdomI P'
  have hΨ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := φ) (F' := φ') (x₀ := (0 : ℝ))
    (bound := fun y => K * (1 + ‖y‖) ^ (-r)) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun s => (hφc Q s).aestronglyMeasurable)
    (hintP Q 0 (by simp)) ((hφc P' 0).aestronglyMeasurable)
    (Eventually.of_forall fun y s hs => hK s (by simpa [Real.dist_eq] using hs) y) (hint.const_mul K)
    (Eventually.of_forall fun y s _ => by
      have := (hasDerivAt_phi c X Q y s).mul_const (E y)
      refine this.congr_deriv ?_
      simp only [φ', hP', evX_eq, map_sub, smul_eval])

  have hexp : HasDerivAt (fun h : ℝ => Complex.exp (((h * A : ℝ) : ℂ))) (Complex.exp (((0 * A : ℝ) : ℂ)) * (A : ℂ)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const A).ofReal_comp).cexp.congr_deriv (by simp)
  have hF := hexp.mul hΨ.2
  have hfun : (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) =
      fun h => Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := funext key
  rw [hfun]
  refine hF.congr_deriv ?_

  have hφ0 : ∀ y, φ 0 y = evX Q y * gs c y * E y := fun y => by simp only [φ, scal_zero]
  have hφ'0 : ∀ y, φ' 0 y = evX P' y * gs c y * E y := fun y => by simp only [φ', scal_zero]
  have hI1 := hintP Q 0 (by simp)
  have hI2 := hintP P' 0 (by simp)
  simp only [scal_zero] at hI1 hI2
  have hdil : ∀ y, evX (dil c X Q) y * gs c y * E y =
      ((m : ℂ) * ∑ j, (X j : ℂ)) * (evX Q y * gs c y * E y) + evX P' y * gs c y * E y := by
    intro y
    simp only [hP', evX_eq, map_sub, smul_eval]
    ring
  unfold secN
  simp only [hφ0, hφ'0, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  rw [integral_congr_ae (Eventually.of_forall hdil), integral_add (hI1.const_mul _) hI2, integral_const_mul]
  simp only [hEdef, hA]
  push_cast
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section

namespace PositivityTheory.Rg.Sw.AbsSt

theorem thSph_of : KAK → Mult → DerivativeVacuumDilations → Sph → SecZero → HolParam → LC → NullIff → ThSph :=
  fun hKAK hMult hD hSph hSZ hHP hLC _ => thSph_of' helpA helpC hKAK hMult hD hSph hSZ hHP hLC

end PositivityTheory.Rg.Sw.AbsSt
end

section

namespace PositivityTheory.Rg.Sw.AbsSt

theorem tsGen : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → HolParam → LC → TSGen :=
  fun _ hD hK hM hS hDF hH hLC => tsGen_of hD hK hM hS hDF hH hLC tsbFacts

end PositivityTheory.Rg.Sw.AbsSt
end

section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem roots_bound (d : Polynomial ℂ) (hd : d ≠ 0) : ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, |r.re|, fun z hz h0 => ?_⟩
  have hm : z ∈ d.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr h0)
  have h1 : |z.re| ≤ ∑ r ∈ d.roots.toFinset, |r.re| :=
    Finset.single_le_sum (f := fun r : ℂ => |r.re|) (fun r _ => abs_nonneg _) hm
  linarith [le_abs_self z.re]

theorem top_E [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (hD : CayleyBlocksInvertible)
    (hHP : HolParam) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hczd : Differentiable ℂ cz)
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEr : ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) :
    ∀ z ∈ U, ∀ g, Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g := by
  have hsm : ∀ (c : ℂ) (F : G → ℂ) (g : G),
      Top μ ι p q e a b nb ψ (fun x => c * F x) g = c * Top μ ι p q e a b nb ψ F g := by
    intro c F g
    simp only [Top, mul_assoc c]
    simp_rw [integral_const_mul, mul_left_comm _ c, integral_const_mul]
  intro z hzU g
  have hdiff : DifferentiableOn ℂ
      (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g) U := by
    have h1 : DifferentiableOn ℂ (fun w => Top μ ι p q e a b nb ψ (E w) g) U :=
      top_hol (p := p) (q := q) (e := e) (a := a) (b := b) μ hD hHP hG.ιcont hnbc hψc hψs hUo E hEc hEh g
    have h2 : DifferentiableOn ℂ (fun w => cz (w - s₀)) U :=
      (hczd.comp (differentiable_id.sub_const s₀)).differentiableOn
    exact h1.sub (h2.mul (hEh g))
  have hVo : IsOpen (connectedComponentIn U z) := hUo.connectedComponentIn
  have hVU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
  have han := (hdiff.mono hVU).analyticOnNhd hVo
  have hray : (fun t : ℝ => z + (t : ℂ)) '' Ici 0 ⊆ connectedComponentIn U z := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ)).continuousOn
    · exact ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hUr.2 z hzU t ht
  have hT : (0 : ℝ) ≤ max 0 (σ - z.re) + 1 := by
    have := le_max_left 0 (σ - z.re)
    linarith
  have hw0 : z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ) ∈ connectedComponentIn U z := hray ⟨_, hT, rfl⟩
  have hre : σ < (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ)).re := by
    have := le_max_right 0 (σ - z.re)
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hev : (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g)
      =ᶠ[𝓝 (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ))] 0 := by
    have hopen : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hEw : E w = fun x => d.eval w * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x :=
      funext fun x => (hEr w hw).2 x
    have hs := top_sum μ hL hG hD hG.ιcont hnbc hψc hψs hceig w (hEr w hw).1 g
    simp only [Pi.zero_apply]
    rw [hEw, hsm (d.eval w) (fun x => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x), hs]
    ring
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
    hw0 hev (mem_connectedComponentIn hzU)
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end
