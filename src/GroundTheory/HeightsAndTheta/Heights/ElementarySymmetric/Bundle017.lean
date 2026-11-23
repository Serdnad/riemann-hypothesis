module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle002
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GramMatrices.PGramAtPosDef
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle008

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

namespace MuLineNormEq


omit [Algebra ℚ Ω] in
theorem valAt_torusSmul {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y))
    {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hsw : torusSmul s w ∈ mcPts (mCoordIdeal y)) {a : Ω} {v : ℂ}
    (hv : IsValueAt y a w v) : valAt y a (torusSmul s w) = valAt y a w := by
  rw [LowerBoundFree.valAt_eq hw hv]
  exact LowerBoundFree.valAt_eq hsw
    (HermMetricEq.isValueAt_iff.2 ((HermMetricEq.isValueAt_iff.1 hv).smul s hs))


omit [Algebra ℚ Ω] in
theorem exists_unit_value {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y))
    {c : (k : K) → ι k} {f u : Ω} (hdom : InFrameDomain y c f w) (hu : IsUnitOn y c f u) :
    ∃ v, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y u w v ∧ v ≠ 0 := by
  obtain ⟨hc, v, hv, hv0⟩ := hdom
  have hf0 : f ≠ 0 := fun h0 => hv0 (isValueAt_zero hw (by rwa [h0] at hv))
  have hfi := HermMetricEq.regularAt_inv hf0 ⟨v, hv, hv0⟩
  have hreg : ∀ a : Ω, (∃ n : ℕ, f ^ n * a ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a w := by
    rintro a ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hw hc hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  obtain ⟨hu0, hu1, hu2⟩ := hu
  obtain ⟨vu, hvu⟩ := hreg _ hu1
  obtain ⟨vi, hvi⟩ := hreg _ hu2
  have h1 : vu * vi = 1 := IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hw (hvu.mul hvi)
    (by rw [mul_inv_cancel₀ hu0]; exact IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one)
  exact ⟨vu, hvu, left_ne_zero_of_mul_eq_one h1⟩

theorem gramAt_eq (D : ComponentData II Ψ K ι Ω E) (τ : Ψ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo)
    {b : Fin D.N → E τ} (l : Fin (D.h τ).m)
    (hd : InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z) {S : Matrix (Fin D.N) (Fin D.N) Ω}
    (hSe : ∀ q, b q = ∑ p, S p q • (D.h τ).b l p) {Sz : Matrix (Fin D.N) (Fin D.N) ℂ}
    (hSz : ∀ p q, IsValueAt D.y (S p q) z (Sz p q)) :
    LowerBoundFree.gramAt (D.h τ) b z = Szᴴ * (D.h τ).gram l z * Sz := by
  classical
  have hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hzP := hzX.1
  have hex : ∃ l, InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z := ⟨l, hd⟩
  have hd0 := hex.choose_spec
  obtain ⟨T, hT, hTe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame hex.choose) hzP hd0
    (HermMetricEq.isFrameAt_of_isFrameOver ((D.h τ).isFrame l) hzP hd).1
  have hTS : ∀ q, b q = ∑ p, (T * S) p q • (D.h τ).b hex.choose p := by
    intro q
    rw [hSe q]
    simp only [hTe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hS' : ∃ S' : Matrix (Fin D.N) (Fin D.N) Ω, ∀ q, b q = ∑ p, S' p q • (D.h τ).b hex.choose p :=
    ⟨T * S, hTS⟩
  have hchoose : hS'.choose = T * S := HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hTS q)
  have hTz : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (T p q) z (HermMetricEq.valM D.y T z p q) :=
    fun p q => (hT p q).isValueAt hzP
  have hTSz := HermMetricEq.isValueAt_mul hTz (fun p q => HermMetricEq.isValueAt_iff.1 (hSz p q))
  have hvals : (Matrix.of fun p q => valAt D.y (hS'.choose p q) z) = HermMetricEq.valM D.y T z * Sz := by
    ext p q
    rw [hchoose]
    exact LowerBoundFree.valAt_eq hzP (HermMetricEq.isValueAt_iff.2 (hTSz p q))
  have hcomp := (D.h τ).compat hex.choose l z hzX hd0 hd T hTe (HermMetricEq.valM D.y T z)
    (fun p q => HermMetricEq.isValueAt_iff.2 (hTz p q))
  rw [LowerBoundFree.gramAt, dite_eq_left hex, dite_eq_left hS', hvals, hcomp, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem gramAt_torusSmul (D : ComponentData II Ψ K ι Ω E) (τ : Ψ) {w : (Σ k, ι k) → ℂ} (hw : w ∈ D.Xo)
    {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hsw : torusSmul s w ∈ D.Xo) {c : (k : K) → ι k} {f : Ω}
    {b : Fin D.N → E τ} (hb : IsFrameOver D.y (D.W τ) c f b) (hdom : InFrameDomain D.y c f w) :
    LowerBoundFree.gramAt (D.h τ) b (torusSmul s w) = LowerBoundFree.gramAt (D.h τ) b w := by
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  obtain ⟨l, hl⟩ := (D.h τ).cover w hwX
  obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame l) hwX.1 hl
    (HermMetricEq.isFrameAt_of_isFrameOver hb hwX.1 hdom).1
  have hSw : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (S p q) w (HermMetricEq.valM D.y S w p q) :=
    fun p q => (hS p q).isValueAt hwX.1
  have hl' : InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) (torusSmul s w) :=
    HermMetricEq.inFrameDomain_smul s hs hl
  rw [gramAt_eq D τ hsw l hl' hSe (fun p q => HermMetricEq.isValueAt_iff.2 ((hSw p q).smul s hs)),
    gramAt_eq D τ hw l hl hSe (fun p q => HermMetricEq.isValueAt_iff.2 (hSw p q)),
    (D.h τ).torus l w hwX hl s hs]

theorem datum_norm_pos (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ D.Xo) (d : MuFrameAt H w) : 0 < d.norm := by
  classical
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  obtain ⟨vu, hvu, hvu0⟩ := exists_unit_value hwX.1 d.inDom d.unit
  have hval : valAt D.y d.u w = vu := LowerBoundFree.valAt_eq hwX.1 (HermMetricEq.isValueAt_iff.2 hvu)
  unfold MuFrameAt.norm
  refine mul_pos (mul_pos ?_ ?_) (Finset.prod_pos fun τ _ => Real.sqrt_pos.2 ?_)
  · rw [hval]
    exact norm_pos_iff.2 hvu0
  · exact Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  · have hP := GramAtPosDef.proof D τ w d.c d.f (d.b τ) hw (d.adapted τ).1 d.inDom
    have h1 := Complex.lt_def.1 hP.det_pos
    have h2 := Complex.lt_def.1
      (hP.submatrix (e := headIdx D.j_le_N) (Fin.castLE_injective D.j_le_N)).det_pos
    unfold quotNormSq
    exact div_pos (by simpa using h1.1) (by simpa using h2.1)

theorem exists_datum_smul (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) {w z : (Σ k, ι k) → ℂ}
    (hw : w ∈ D.Xo) {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hzs : z = torusSmul s w) (hz : z ∈ D.Xo)
    (d : MuFrameAt H z) : ∃ d' : MuFrameAt H w, d.norm = (∏ k, ‖s k‖ ^ H.aMu k) * d'.norm := by
  subst hzs
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  have hzX : torusSmul s w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hdom : InFrameDomain D.y d.c d.f w := by
    have h := HermMetricEq.inFrameDomain_smul (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k)) d.inDom
    convert h using 1
    funext p
    simp [torusSmul, inv_mul_cancel_left₀ (hs p.1)]
  refine ⟨⟨d.c, d.f, hdom, d.b, d.adapted, d.u, d.unit, d.eq⟩, ?_⟩
  obtain ⟨vu, hvu, -⟩ := exists_unit_value hwX.1 hdom d.unit
  have hval : valAt D.y d.u (torusSmul s w) = valAt D.y d.u w :=
    valAt_torusSmul hwX.1 hs hzX.1 (HermMetricEq.isValueAt_iff.2 hvu)
  have hprod : (∏ k, ‖torusSmul s w ⟨k, d.c k⟩‖ ^ H.aMu k) =
      (∏ k, ‖s k‖ ^ H.aMu k) * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ H.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [torusSmul, norm_mul, mul_zpow]
  have hg : ∀ τ, LowerBoundFree.gramAt (D.h τ) (d.b τ) (torusSmul s w) = LowerBoundFree.gramAt (D.h τ) (d.b τ) w :=
    fun τ => gramAt_torusSmul D τ hw hs hz (d.adapted τ).1 hdom
  show ‖valAt D.y d.u (torusSmul s w)‖ * (∏ k, ‖torusSmul s w ⟨k, d.c k⟩‖ ^ H.aMu k) *
      ∏ τ, Real.sqrt (quotNormSq D.j_le_N (LowerBoundFree.gramAt (D.h τ) (d.b τ) (torusSmul s w))) =
    (∏ k, ‖s k‖ ^ H.aMu k) * (‖valAt D.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ H.aMu k) *
      ∏ τ, Real.sqrt (quotNormSq D.j_le_N (LowerBoundFree.gramAt (D.h τ) (d.b τ) w)))
  simp only [hval, hprod, hg]
  ring

theorem proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (hI : MuFrameNormIndep.Statement D H) :
    MuLineNormEq.Statement D H := by
  intro z hz d
  obtain ⟨s, hs, hzs⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hwdef
  have hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hwP : w ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k)) hzX.1
    convert h using 1
    funext p
    rw [hzs]
    simp [torusSmul, inv_mul_cancel_left₀ (hs p.1)]
  have hw : w ∈ D.Xo := ⟨hwP, fun hB => hzX.2 (by rw [hzs]; exact D.bd_torus w hB s hs)⟩
  obtain ⟨d', hdd'⟩ := exists_datum_smul D H hw hs hzs hz d
  have hpos := datum_norm_pos D H hw d'
  have hM : muMetric H w = d'.norm := by
    rw [muMetric, dite_eq_left ⟨d'⟩]
    exact hI w hw _ d'
  have hR := refNorm_pos H.aMu hwP.1
  have hRz : refNorm H.aMu z = (∏ k, ‖s k‖ ^ H.aMu k) * refNorm H.aMu w := by
    rw [hzs]
    exact refNorm_smul _ s w
  show refNorm H.aMu z * Real.exp (Real.log (muMetric H w / refNorm H.aMu w)) = d.norm
  rw [hM, Real.exp_log (div_pos hpos hR), hRz, hdd']
  field_simp

end MuLineNormEq

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart FinHolAtlas)

theorem RefChartDisc.log_norm_eq_re {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ‖F s‖ = (L s).re := by
  refine ⟨fun s => Complex.log (F s / F 0) + (Real.log ‖F 0‖ : ℂ), ?_, ?_⟩
  · refine ((hF.div analyticAt_const h0).clog ?_).add analyticAt_const
    show F 0 / F 0 ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hF.continuousAt.eventually_ne h0] with s hs
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hs) (norm_ne_zero_iff.mpr h0)]
    ring

theorem RefChartDisc.analyticAt_comp {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {e : OpenPartialHomeomorph X (Fin n → ℂ)} (he : IsCompatChart A e) {y : ℂ → X}
    (hy : AnalyticAt ℂ (fun s => e (y s)) 0) (hys : ∀ᶠ s in 𝓝 (0 : ℂ), y s ∈ e.source)
    {V : Set X} {F : X → ℂ} (hF : A.HoloOn V F) (h0 : y 0 ∈ V) :
    AnalyticAt ℂ (fun s => F (y s)) 0 := by
  have h0s : y 0 ∈ e.source := hys.self_of_nhds
  have h1 : AnalyticAt ℂ (F ∘ e.symm) (e (y 0)) :=
    ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun he hF (e.map_source h0s) (by rwa [e.left_inv h0s])
  refine (h1.comp (f := fun s => e (y s)) hy).congr ?_
  filter_upwards [hys] with s hs
  simp [Function.comp, e.left_inv hs]

theorem RefChartDisc.proof (hProj : ProjChartHolo.Statement) : RefChartDisc.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S j γ hγ hmem hsrc
  set x := M.proj (γ 0) with hx
  set e := S.R.chart j with he_def
  have he : IsCompatChart M.atlas e := S.R.compat j
  have hφ : AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0 := hProj II Ψ K ι Ω E D M e he γ hγ hmem hsrc
  have hγ0 : γ 0 ∈ mcPts (mCoordIdeal D.y) := hmem.self_of_nhds
  have hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 x) :=
    (M.cont _ hγ0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγ.continuousAt.tendsto, hmem⟩)
  obtain ⟨U, hUo, hxU, hUsub, σ, hσ, hσh, G1, hG1, hG1eq⟩ := S.th_ref x x (S.R.th.mem_U x)
  obtain ⟨W, hWo, hxW, G2, hG2, hG2eq⟩ := S.R.q_th j x x ⟨S.R.th.mem_U x, hsrc⟩
  have hV : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ U ∩ W ∩ e.source :=
    hcont.eventually (((hUo.inter hWo).inter e.open_source).mem_nhds ⟨⟨hxU, hxW⟩, hsrc⟩)
  have hA : ∀ {V : Set M.Xc} {F : M.Xc → ℂ}, M.atlas.HoloOn V F → x ∈ V →
      AnalyticAt ℂ (fun s => F (M.proj (γ s))) 0 :=
    fun hF hxV => RefChartDisc.analyticAt_comp he hφ (hV.mono fun _ h => h.2) hF hxV

  choose i hi using (hσ x hxU).1.1
  set T : K → ℂ → ℂ := fun b s => γ s ⟨b, i b⟩ / σ (M.proj (γ s)) ⟨b, i b⟩ with hT_def
  have hden : ∀ b, AnalyticAt ℂ (fun s => σ (M.proj (γ s)) ⟨b, i b⟩) 0 := fun b => hA (hσh ⟨b, i b⟩) hxU
  have hT : ∀ b, AnalyticAt ℂ (T b) 0 := fun b =>
    (analyticAt_pi_iff.1 hγ ⟨b, i b⟩).div (hden b) (hi b)
  obtain ⟨c0, hc0, hγc0⟩ := (M.fibre _ (hσ x hxU).1 _ hγ0).1 (hσ x hxU).2
  have hT0 : ∀ b, T b 0 ≠ 0 := fun b => by
    have : γ 0 ⟨b, i b⟩ = c0 b * σ x ⟨b, i b⟩ := by rw [hγc0]; rfl
    simp only [hT_def, ← hx, this]
    exact div_ne_zero (mul_ne_zero (hc0 b) (hi b)) (hi b)
  choose L hL hLeq using fun b => RefChartDisc.log_norm_eq_re (hT b) (hT0 b)
  have hdenev : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ b, σ (M.proj (γ s)) ⟨b, i b⟩ ≠ 0 :=
    eventually_all.2 fun b => (hden b).continuousAt.eventually_ne (hi b)
  refine ⟨fun s => G1 (M.proj (γ s)) + G2 (M.proj (γ s)) - ∑ b, ((S.ref.a b : ℝ) : ℂ) * L b s, ?_, ?_⟩
  · refine ((hA hG1 hxU).add (hA hG2 hxW)).sub ?_
    have := Finset.analyticAt_sum (𝕜 := ℂ) Finset.univ fun b _ => (analyticAt_const (v := ((S.ref.a b : ℝ) : ℂ))).mul (hL b)
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp [Finset.sum_apply]
  filter_upwards [hV, hmem, hdenev, eventually_all.2 hLeq] with s hs hγs hds hLs
  obtain ⟨⟨hsU, hsW⟩, hssrc⟩ := hs
  set y := M.proj (γ s) with hy
  obtain ⟨hσy, hpσy⟩ := hσ y hsU
  obtain ⟨c, hc, hγc⟩ := (M.fibre _ hσy _ hγs).1 (by rw [hpσy])
  have hcT : ∀ b, c b = T b s := fun b => by
    have : γ s ⟨b, i b⟩ = c b * σ y ⟨b, i b⟩ := by rw [hγc]; rfl
    simp only [hT_def, ← hy, this]
    field_simp [hds b]
  have hmet : S.ref.h (γ s) = (∏ b, ‖c b‖ ^ S.ref.a b) * S.ref.h (σ y) := by
    rw [← S.ref.smul c (σ y) hc, hγc]; rfl
  have hpos : 0 < S.ref.h (σ y) := S.ref.pos _ hσy.1
  have hlog : Real.log (S.ref.h (γ s)) = ∑ b, (S.ref.a b : ℝ) * (L b s).re + Real.log (S.ref.h (σ y)) := by
    rw [hmet, Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))
      hpos.ne', Real.log_prod (fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.log_zpow, hcT b, hLs b]
  have h1 := hG1eq y hsU
  have h2 := hG2eq y ⟨⟨hsW, hUsub hsU⟩, hssrc⟩
  simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [hlog]
  linarith

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LiftGraphFactor.closed : LiftGraphFactor.Statement :=
  LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed

end GroundTheory.Heights₂.Heights.Targets
end
