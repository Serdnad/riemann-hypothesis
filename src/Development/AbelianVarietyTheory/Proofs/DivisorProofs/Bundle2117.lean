module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic Topology

noncomputable section

namespace GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_one_entry {R : Type} [Ring R] (f : Ad E →+* R) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sub_one_entry_mem {w : Pl E} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E := by
  rw [mem_KGL_iff_val] at hg
  refine sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.1 i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _


omit [IsCMField E] in
theorem af_ext {a b : Af E} (h : ∀ u : Pl E, pLoc E u a = pLoc E u b) : a = b := Subtype.ext (funext h)

omit [IsCMField E] in
theorem pLoc_singleNU_self (w : Pl E) (y : w.adicCompletion E) : pLoc E w (GlobalTheory.GLTwoHecke.singleNU w y) = y :=
  GlobalTheory.AdelicU.evalV_singleFin_self w y

omit [IsCMField E] in
theorem pLoc_singleNU_ne {u w : Pl E} (h : u ≠ w) (y : w.adicCompletion E) :
    pLoc E u (GlobalTheory.GLTwoHecke.singleNU w y) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h y

theorem entry_eq_one_add {w : Pl E} {N N' : Set (Af E)} (h0 : (0 : Af E) ∈ N')
    (hadd : ∀ a ∈ N', ∀ b ∈ N', a + b ∈ N)
    (hw : ∀ y ∈ w.adicCompletionIntegers E, GlobalTheory.GLTwoHecke.singleNU w y ∈ N')
    (hc : ∀ y ∈ (conjSrc (conjE E) w).adicCompletionIntegers E,
      GlobalTheory.GLTwoHecke.singleNU (conjSrc (conjE E) w) y ∈ N')
    (z : UA E n) (hz : z ∈ locU n w) (hK : cLoc w z ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    ∃ a ∈ N, ((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + (show Ad E from ((0 : InfiniteAdeleRing E), a)) := by
  have hKc := integral_conjSrc z w hK
  have hfin : z ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 hz).1
  have hout : ∀ u : Pl E, u ≠ w → u ≠ conjSrc (conjE E) w → cLoc u z = 1 := by
    intro u huw huc
    have hne : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := fun h =>
      (eq_or_eq_conjSrc h).elim huw huc
    exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).2 u) hne)
  generalize conjSrc (conjE E) w = c at hc hKc hout
  refine ⟨GlobalTheory.GLTwoHecke.singleNU w ((cLoc w z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
    (if c = w then 0 else GlobalTheory.GLTwoHecke.singleNU c ((cLoc c z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j)),
    hadd _ (hw _ (sub_one_entry_mem hK i j)) _ ?_, ?_⟩
  · split_ifs
    · exact h0
    · exact hc _ (sub_one_entry_mem hKc i j)
  refine Prod.ext ?_ ?_
  · have h1 : GeneralLinearGroup.map (pInf E) (z : GA E n) = 1 := hfin
    have h2 : pInf E (((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
        pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
      rw [map_one_entry]
      have := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) h1
      simpa using this
    have h3 := (infEq E).symm.injective h2
    change _ = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 + 0
    rw [add_zero]
    exact h3
  · apply af_ext
    intro u
    change (cLoc u z).val i j = ((pLoc E u).comp (pFin E)) ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      (show Ad E from ((0 : InfiniteAdeleRing E), _)))
    rw [map_add (f := _), map_one_entry]
    change _ = _ + pLoc E u (GlobalTheory.GLTwoHecke.singleNU w _ + _)
    rw [map_add (f := _)]
    by_cases huw : u = w
    · subst huw
      rw [pLoc_singleNU_self]
      split_ifs with hcw
      · rw [map_zero]; abel
      · rw [pLoc_singleNU_ne (Ne.symm hcw)]; abel
    · rw [pLoc_singleNU_ne huw]
      by_cases huc : u = c
      · subst huc
        rw [if_neg huw, pLoc_singleNU_self]; abel
      · rw [hout u huw huc]
        split_ifs
        · simp
        · rw [pLoc_singleNU_ne huc]; simp

theorem eventually_locU_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))),
    IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) →
      ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  intro E _ _ _ n L hL
  have h1 : (L : Set (finU (E := E) (n := n))) ∈ 𝓝 (1 : finU (E := E) (n := n)) := hL.mem_nhds L.one_mem
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨V1, hV1, hV1L⟩ := h1
  rw [nhds_subtype, Filter.mem_comap] at hV1
  obtain ⟨V, hV, hVV1⟩ := hV1
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  let Φ : Af E → Ad E := fun a => show Ad E from ((0 : InfiniteAdeleRing E), a)
  have hΦ : Continuous Φ := continuous_const.prodMk continuous_id
  have hΦ0 : Φ 0 = 0 := rfl
  let ψ : (Bool × Fin n × Fin n → Af E) →
      Matrix (Fin n) (Fin n) (Ad E) × (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    fun y => (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (false, i, j)),
      MulOpposite.op (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (true, i, j))))
  have hψ : Continuous ψ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_) <;>
    exact continuous_pi fun i => continuous_pi fun j => continuous_const.add (hΦ.comp (continuous_apply _))
  have hψ0 : ψ 0 = Units.embedProduct _ (1 : GA E n) := by
    refine Prod.ext ?_ ?_
    · ext i j; simp [ψ, hΦ0]
    · refine MulOpposite.unop_injective ?_
      ext i j; simp [ψ, hΦ0]
  have hS : ψ ⁻¹' W ∈ 𝓝 (0 : Bool × Fin n × Fin n → Af E) :=
    hψ.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hS
  obtain ⟨I, t, ht, hIt⟩ := hS
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : Af E) := Filter.iInter_mem.2 ht
  obtain ⟨N', hN', hadd⟩ := exists_nhds_zero_half hN
  have h0 : (0 : Af E) ∈ N' := mem_of_mem_nhds hN'
  have hev := GlobalTheory.GLTwoHecke.eventually_singleNU_mem hN'
  have hev2 := (conjSrc_injective (conjE E)).tendsto_cofinite.eventually hev
  filter_upwards [hev, hev2] with w hw hw2 x hxw hxK hx
  have hxw' : x⁻¹ ∈ locU n w := inv_mem hxw
  have hxK' : cLoc w x⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := by rw [map_inv]; exact inv_mem hxK
  choose a ha hxa using entry_eq_one_add h0 hadd hw hw2 x hxw hxK
  choose b hb hxb using entry_eq_one_add h0 hadd hw hw2 x⁻¹ hxw' hxK'
  let y : Bool × Fin n × Fin n → Af E := fun p => if p.1 then b p.2.1 p.2.2 else a p.2.1 p.2.2
  have hy : y ∈ ψ ⁻¹' W := hIt fun p _ => by
    rcases p with ⟨_ | _, i, j⟩
    · exact Set.mem_iInter.1 (ha i j) _
    · exact Set.mem_iInter.1 (hb i j) _
  apply hV1L
  apply hVV1
  apply hWV
  have e : ψ y = Units.embedProduct _ ((x : GA E n)) := by
    refine Prod.ext ?_ ?_
    · ext i j
      exact (hxa i j).symm
    · refine MulOpposite.unop_injective ?_
      ext i j
      exact (hxb i j).symm
  show Units.embedProduct _ (x : GA E n) ∈ W
  rw [← e]
  exact hy

end GlobalTheory.BCT.GlobLev
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SubmeanChart

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem nd_eq_dimFl (X : Data E r) : nd X = dimFl E r := by
  unfold nd dimFl
  rw [Fintype.card_prod, card_strictLower, QuadraticCoefficientForms.card_Psi]

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ a b
  have h1 : mat (nmat X 0) τ = 1 := by
    ext i j
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    by_cases h : j < i
    · rw [dif_pos h, if_neg (ne_of_gt h)]
      rfl
    · rw [dif_neg h]
  show (mat x0 τ * mat (nmat X 0) τ) a b = x0 τ a b
  rw [h1, Matrix.mul_one]
  rfl

theorem differentiable_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro a
  rw [differentiable_pi]; intro b
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  refine Differentiable.fun_sum fun k _ => Differentiable.const_mul ?_ _
  by_cases h : b < k
  · simp only [nmat, dif_pos h]
    fun_prop
  · simp only [nmat, dif_neg h]
    exact differentiable_const _

theorem norm_dmin_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem nfac_of_orth (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : IsOrth X x) : X.nfac la x = 1 := by
  unfold Data.nfac
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
  rw [norm_div, norm_dmin_of_orth X hx, norm_dmin_of_orth X hx, div_one, Real.one_rpow]

theorem pnorm_eq (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem spread_nonneg (X : Data E r) (la : Wt X.Ψ r) (hr : 0 < r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  have i : Fin r := ⟨0, hr⟩
  have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
  have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
  linarith

theorem chartRad_pos (X : Data E r) (la : Wt X.Ψ r) {w : ℝ} (hr : 0 < r) (hw : (∑ τ, X.spread la τ) ≤ w) :
    0 < chartRad E r w := by
  have h0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la hr τ) hw
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast (QuadraticCoefficientForms.card_Psi X) ▸ QuadraticCoefficientForms.card_Psi_pos X
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold chartRad
  positivity

end

end GlobalTheory.SubmeanChart

namespace GlobalTheory.SubmeanChart
noncomputable section

theorem submean_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  intro E _ _ _ r X la w x P hr hx hw hP
  set ρ := chartRad E r w with hρdef
  have hρ : 0 < ρ := chartRad_pos X la hr hw
  have hch := GlobalTheory.T.normFactor_and_density_near_one_in_flagChart E r X la w x hr hx hw

  set φ : V (nd X) → ℂ := fun z => P (cpt X x z) with hφdef
  have hφ : DifferentiableOn ℂ φ (Metric.ball 0 ρ) :=
    hP.comp (differentiable_cpt X x).differentiableOn fun z hz =>
      (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub := GlobalTheory.enorm_pow_le_inv_measure_mul_lintegral_ball (volume : Measure (V (nd X))) (a := 0) hρ hφ 2
  have hne : ENNReal.ofReal (Real.pi ^ nd X * ρ ^ (2 * nd X) / ((nd X).factorial : ℝ)) =
      ENNReal.ofReal (Real.pi ^ dimFl E r * ρ ^ (2 * dimFl E r) / ((dimFl E r).factorial : ℝ)) := by
    rw [nd_eq_dimFl]
  rw [GlobalTheory.volume_ball_euclideanSpace_complex (0 : V (nd X)) hρ, Fintype.card_fin, hne] at hsub
  set D := dimFl E r with hD

  have h1 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ‖φ z‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (1 / 20)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨-, hn, -⟩ := hch z (le_of_lt (mem_ball_zero_iff.1 hz))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pnorm_eq, mul_pow]
    have he : 1 ≤ Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hn (Real.exp_pos (1 / 20)).le
      rwa [← Real.exp_add, show (1 / 20 : ℝ) + -(1 / 20) = 0 by norm_num, Real.exp_zero] at this
    calc ‖φ z‖ ^ 2 = ‖φ z‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖φ z‖ ^ 2 * (Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [hφdef]; ring

  have hμ : ENNReal.ofReal (Real.exp (-(1 / 10))) • (volume.restrict (Metric.ball (0 : V (nd X)) ρ)) ≤
      (muF X x).restrict (Metric.ball 0 ρ) := by
    have hb : Metric.ball (0 : V (nd X)) ρ ∩ OmF X x = Metric.ball 0 ρ :=
      Set.inter_eq_left.2 fun z hz => (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
    rw [muF, restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball, hb,
      ← withDensity_const]
    refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    exact ENNReal.ofReal_le_ofReal (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2
  have h2 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ≤
      ENNReal.ofReal (Real.exp (1 / 10)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
    have h3 := lintegral_mono' hμ (le_refl (fun z => ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)))
    rw [lintegral_smul_measure, smul_eq_mul] at h3
    calc _ = ENNReal.ofReal (Real.exp (1 / 10)) * (ENNReal.ofReal (Real.exp (-(1 / 10))) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show (1 / 10 : ℝ) + -(1 / 10) = 0 by norm_num, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr

  have h0 : ENNReal.ofReal (X.pnorm la P x ^ 2) = ‖φ 0‖ₑ ^ 2 := by
    rw [pnorm_eq, nfac_of_orth X la hx, mul_one, show φ 0 = P x by simp only [hφdef, cpt_zero], ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

  have hvol : (ENNReal.ofReal (Real.pi ^ D * ρ ^ (2 * D) / (D.factorial : ℝ)))⁻¹ =
      ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, mul_pow, ← pow_mul, mul_comm 2 D]
  have hexp : Real.exp (1 / 20) * Real.exp (1 / 10) ≤ 2 := by
    rw [← Real.exp_add]
    calc Real.exp (1 / 20 + 1 / 10) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log two_pos
  have hc : ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
      (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10))) ≤
      ENNReal.ofReal (2 * (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : 0 ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D := by positivity
    calc (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * (Real.exp (1 / 20) * Real.exp (1 / 10))
        ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * 2 := mul_le_mul_of_nonneg_left hexp hq
      _ = _ := by ring
  rw [h0]
  calc ‖φ 0‖ₑ ^ 2 ≤ _ := hsub
    _ ≤ ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * (ENNReal.ofReal (Real.exp (1 / 10)) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x))) := by
        rw [hvol]
        gcongr
        exact h1.trans (by gcongr)
    _ = (ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10)))) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
        ring
    _ ≤ _ := by gcongr

end
end GlobalTheory.SubmeanChart
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevGeo.Reps

theorem core (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) :
    ∃ (G : Matrix (Fin r) (Fin r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
      (g : Comp → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
      (Λk : Comp → Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (u : Comp → (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
      GlobalTheory.UCls.SelfDualLat G Λ ∧
      (∀ k, (X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧
        (Λk k : Set (Fin r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin r → D.host.E)) ∧
        (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin r → D.host.E)) = ⊤ ∧
        (∀ τ ∈ (X k).Ψ, gram τ G (u k τ) = G.map τ) ∧
        (∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) ∧
          ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
        ∀ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) →
          ∃ γ ∈ (X k).Γ, ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
      ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin r → D.host.E)) M (g k) (g k') → k = k' := by
  subst hr
  classical
  obtain ⟨x0, hx0, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx0 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  refine ⟨-(V.gram)ᵀ, GlobalTheory.Member.latC V, fun k => (finHom V (gA k)).1, Λk,
    fun k τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1, GlobalTheory.T.selfDualLattice_neg_transpose_gram D V, fun k => ?_, ?_⟩
  · refine ⟨hG k, GlobalTheory.T.finiteUnitaryPart_isInvertibleUnitaryAdelic D V (gA k), (hΛk k).1, (hΛk k).2.1, (hΛk k).2.2.1, ?_, ?_, ?_⟩
    · intro τ hτ
      simp only [dif_pos hτ]
      exact GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', h1, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      obtain ⟨γ, hγ, h2⟩ := GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' hγ'
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
  · exact GlobalTheory.T.componentRepresentatives_injective_doubleCoset D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])

end GlobalTheory.LevGeo.Reps

theorem GlobalTheory.LevGeo.Reps.components_double_cosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (g : (U σ).Comp → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (Λk : (U σ).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (u : (U σ).Comp → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ k, ((U σ).X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧ (Λk k : Set (Fin D.R.r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin D.R.r → D.host.E)) ∧ (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin D.R.r → D.host.E)) = ⊤ ∧ (∀ τ ∈ ((U σ).X k).Ψ, gram τ G (u k τ) = G.map τ) ∧ (∀ γ ∈ ((U σ).X k).Γ, ∃ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) ∧ ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) → ∃ γ ∈ ((U σ).X k).Γ, ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin D.R.r → D.host.E)) l.M (g k) (g k') → k = k' := by
  intro D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  exact GlobalTheory.LevGeo.Reps.core D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
end
end

section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.hyperbolic_pair_lattice_local_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  first
  | exact GlobalTheory.IwSplitLine.iwasawa_line_split F E σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  | exact GlobalTheory.IwSplitLine.iwasawa_line_split F E σ h n J hJ x y hxx hyy hxy hyx L hLat.toIsLattice v hv hL g
end
