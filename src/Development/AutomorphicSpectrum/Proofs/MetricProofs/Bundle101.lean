module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap

theorem orbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  show z' q = (c q.1)⁻¹ * (c q.1 * z' q)
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem orbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext q
  show c q.1 * (c' q.1 * z'' q) = c q.1 * c' q.1 * z'' q
  rw [mul_assoc]

theorem not_mem_mcPts_top {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h1 := (show (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ (⊤ : Ideal (MRing ι)), eval z (map (Int.castRingHom ℂ) f) = 0 from hz).2 1 Submodule.mem_top
  simp at h1

theorem factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (n e e' : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (pr : R.X → Rb.X) (prp : Rp.X → Rb.X) (h : R.X → Rp.X),
    (∀ x, SameOrbit (basePart M.blk (R.lift x x)) (Rb.lift (pr x) (pr x))) →
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x ∧
      SameOrbit (basePart M.blk z) (Rb.lift (prp x) (prp x))) →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x, prp (h x) = pr x) ∧ ∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) → h x = h x' := by
  intro K _ ι _ Φ _ y Ψ N j M p n e e' Rb R Rp pr prp hh H1 H2 H3
  have hnz : ∀ x k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hb : ∀ z w : (Σ k, ι k) → ℂ, SameOrbit (z ∘ stepV M p) (w ∘ stepV M p) →
      SameOrbit (basePart M.blk z) (basePart M.blk w) := by
    rintro z w ⟨c, hc, hzw⟩
    exact ⟨fun k => c ⟨k.1, Or.inl k.2⟩, fun k => hc _,
      funext fun q => congrFun hzw ⟨⟨q.1.1, Or.inl q.1.2⟩, q.2⟩⟩
  refine ⟨fun x => ?_, fun x x' hpr hsc => ?_⟩
  · obtain ⟨z, -, hz1, hz2⟩ := H2 (hh x)
    have o1 : SameOrbit (z ∘ stepV M p) (R.lift x x ∘ stepV M p) := by
      rw [hz1]
      exact H3 x
    exact Rb.inj _ _ (not_mem_mcPts_top _)
      (orbit_trans (orbit_trans (orbit_symm hz2) (hb _ _ o1)) (H1 x))
  · apply Rp.inj _ _ (not_mem_mcPts_top _)
    refine orbit_trans (H3 x) (orbit_trans ?_ (orbit_symm (H3 x')))
    have h1' := H1 x'
    rw [← hpr] at h1'
    obtain ⟨cb, hcb, hbeq⟩ := orbit_trans (H1 x) (orbit_symm h1')
    refine ⟨fun k => if hk : (∀ p', M.blk p' ≠ some k.1) then cb ⟨k.1, hk⟩
      else (hsc k.1 (k.2.resolve_left hk)).choose, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with hk
      · exact hcb _
      · intro h0
        obtain ⟨i, hi⟩ := hnz x k.1
        apply hi
        rw [(hsc k.1 (k.2.resolve_left hk)).choose_spec i, h0, zero_mul]
    · funext q
      show R.lift x x ⟨q.1.1, q.2⟩ = _ * R.lift x' x' ⟨q.1.1, q.2⟩
      dsimp only
      split_ifs with hk
      · exact congrFun hbeq ⟨⟨q.1.1, hk⟩, q.2⟩
      · exact (hsc q.1.1 (q.1.2.resolve_left hk)).choose_spec q.2

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

def SmMat (M : E → Matrix (Fin N) (Fin N) ℂ) (w : E) : Prop :=
  ∀ a b, ContDiffAt ℝ ∞ (fun u => M u a b) w

theorem SmMat.mul {M M' : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (h' : SmMat M' w) :
    SmMat (fun u => M u * M' u) w := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

theorem SmMat.conjTranspose {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) :
    SmMat (fun u => (M u)ᴴ) w := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp w (h b a)

theorem SmMat.minor {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (I J : Finset (Fin N)) :
    ContDiffAt ℝ ∞ (fun u => minorIJ (M u) I J) w := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun i _ => h _ _
  · simp only [dif_neg e]
    exact contDiffAt_const

theorem contDiffAt_blockPot (j : ℕ) (i : Fin N) {G h : E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hG : SmMat G w) (hh : SmMat h w) (hpos : (G w).PosDef) (hdet : (h w).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => blockPot j i (G u) (h u)) w := by
  have hre : ∀ {f : E → ℂ}, ContDiffAt ℝ ∞ f w → 0 < f w →
      ContDiffAt ℝ ∞ (fun u => Real.log (f u).re) w := fun hf h0 =>
    (Complex.reCLM.contDiff.contDiffAt.comp w hf).log (Complex.lt_def.1 h0).1.ne'
  have hfac : ContDiffAt ℝ ∞ (fun u => detFac j i (G u)) w := by
    unfold detFac
    refine ContDiffAt.mul ?_ ?_
    · by_cases c : j ≤ (i : ℕ) + 1
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
    · by_cases c : (i : ℕ) + 1 = N
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
  have hfac0 : 0 < detFac j i (G w) := by
    unfold detFac
    refine mul_pos ?_ ?_
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
  unfold blockPot
  refine (contDiffAt_const.mul (hre hfac hfac0)).add ?_
  by_cases c : IsProperStep N j i
  · simp only [if_pos c]
    refine contDiffAt_const.mul (hre ((hh.conjTranspose.mul hG).mul hh |>.minor _ _) ?_)
    have hu : IsUnit (h w) := (Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit
    exact GramPot.minor_pos
      (hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)) _
  · simp only [if_neg c]
    exact contDiffAt_const

end Calc

section Chart

variable {e n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contDiffAt_comp_holoMap {A : FinHolAtlas e X} {B : FinHolAtlas n Y} {pr : X → Y}
    (hp : HoloMap A B pr) {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : B.SmoothOn U f)
    (c : Fin A.n) {w : Fin e → ℂ} (hw : w ∈ (A.chart c).target)
    (hwU : pr ((A.chart c).symm w) ∈ U) :
    ContDiffAt ℝ ∞ (fun u => f (pr ((A.chart c).symm u))) w := by
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart c).symm w))
  have h1 : ContDiffAt ℝ ∞ (f ∘ (B.chart k).symm) (B.chart k (pr ((A.chart c).symm w))) := by
    refine (hf k).contDiffAt
      (((B.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨(B.chart k).map_source hk, ?_⟩)
    simpa [(B.chart k).left_inv hk] using hwU
  have h2 : ContDiffAt ℝ ∞ (B.chart k ∘ pr ∘ (A.chart c).symm) w :=
    (hp.2 c k w ⟨hw, hk⟩).contDiffAt.restrict_scalars ℝ
  refine (ContDiffAt.comp w h1 h2).congr_of_eventuallyEq ?_
  filter_upwards [((A.chart c).isOpen_inter_preimage_symm
    ((B.chart k).open_source.preimage hp.1)).mem_nhds ⟨hw, hk⟩] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem contDiffAt_of_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {w : E}
    (h1 : ContDiffAt ℝ ∞ (fun u => (g u).re) w) (h2 : ContDiffAt ℝ ∞ (fun u => (g u).im) w) :
    ContDiffAt ℝ ∞ g w := by
  have e : g = fun u => (((g u).re : ℝ) : ℂ) + (((g u).im : ℝ) : ℂ) * Complex.I := by
    funext u
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w h2).mul contDiffAt_const)

end Chart

theorem smoothOn_stepPh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS hP c w hw
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hwt, hwb⟩ := hw
  have hb : pr ((R.A.chart c).symm w) ∉ bdry BM.s := hwb
  obtain ⟨W, l, H, D, hWo, hyW, hWU, hWO, hH, hHd, hD, hD0, heq⟩ :=
    hS ((R.A.chart c).symm w) ((R.A.chart c).symm w) (R.mem_U _)
  have hcl : IsClosed (bdry BM.s) := isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  have hOo : IsOpen (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) := hWo.inter (hcl.isOpen_compl.preimage hp.1)
  have hnhd : (R.A.chart c).target ∩ (R.A.chart c).symm ⁻¹' (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) ∈ 𝓝 w :=
    ((R.A.chart c).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hwt, hyW, hb⟩
  have hOb : IsOpen (BM.O l \ bdry BM.s) := (BM.O_open l).sdiff hcl
  have hmemO : pr ((R.A.chart c).symm w) ∈ BM.O l \ bdry BM.s := ⟨hWO _ hyW, hb⟩
  have hG : SmMat (fun u => BM.G l p.1 (pr ((R.A.chart c).symm u))) w := fun a b =>
    contDiffAt_of_re_im
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).1 c hwt hmemO)
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).2 c hwt hmemO)
  have hHm : SmMat (fun u => H ((R.A.chart c).symm u)) w := fun a b =>
    (hH a b c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hDm : ContDiffAt ℝ ∞ (fun u => D ((R.A.chart c).symm u)) w :=
    (hD c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hD1 : D ((R.A.chart c).symm w) ≠ 0 := hD0 _ hyW
  have hbp := contDiffAt_blockPot j p.2 hG hHm (BM.G_pos l p.1 _ hmemO).2 (hHd _ hyW).2
  have hlog : ContDiffAt ℝ ∞ (fun u => Real.log ‖D ((R.A.chart c).symm u)‖) w :=
    (hDm.norm ℝ hD1).log (norm_ne_zero_iff.2 hD1)
  have hpot : ContDiffAt ℝ ∞ (fun u => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h
      (R.lift ((R.A.chart c).symm w) ((R.A.chart c).symm u)))) w :=
    (hP.1 ((R.A.chart c).symm w) c).contDiffAt
      (((R.A.chart c).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hwt, R.mem_U _⟩)
  refine ((hbp.add hlog).sub hpot).congr_of_eventuallyEq ?_
  filter_upwards [hnhd] with u hu
  have := heq _ hu.2.1 hu.2.2
  simp only [Function.comp_apply]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_inv {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hs' : RegAt x (mCoordIdeal z) s⁻¹) :
    valAt x s⁻¹ z = (valAt x s z)⁻¹ ∧ valAt x s z ≠ 0 := by
  obtain ⟨-, -, -, h1, hm⟩ := ValRing.regAt_valAt_ring K ι Ω x z hz
  have h := (hm s s⁻¹ hs hs').2.2.1
  rw [mul_inv_cancel₀ h0, h1] at h
  have hne : valAt x s z ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact ⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩

theorem coord_ne_zero {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 :=
  fun h0 => h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀)) := BM.good l x₀ hx.1
  have hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  obtain ⟨c, hc, hzc⟩ := id hso

  have hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
    rw [hzc]; exact TorusAct.mCoordIdeal_torus c hc _
  have hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [hzc]
    exact ((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1
  have hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z)) := by rw [hI]; exact hgood
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k => coord_ne_zero (hgood'.1 k)

  let t : K → ℂ := fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1
  have htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1 := fun k h => dif_neg h
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [htb ⟨k, h⟩]; exact inv_ne_zero (hne _)
    · rw [ht1 k h]; exact one_ne_zero
  let z₁ : (Σ k, ι k) → ℂ := fun q => t q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((TorusAct.main _ _ _ y z t ht).2 hz).1
  have hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q := rfl
  have hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z) := by
    rw [hb₁]
    exact ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _
  have hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀) :=
    ⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by
      rw [hb₁, hzc]; funext q; exact (mul_assoc _ _ _).symm⟩
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hb₁]
    show t k.1 * _ = 1
    rw [htb k]
    exact inv_mul_cancel₀ (hne k)
  have hind := (BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp
  rw [hval] at hind

  have hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z := by
    have := (BM.hom p).smul t z ht
    rw [BM.hom_deg] at this
    exact this
  have hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹ := by
    have e := Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k)
      (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))
    rw [← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1)
      (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹
    rw [htb k, norm_inv, norm_zpow, _root_.inv_zpow]

  obtain ⟨hu0, hu1, hu2⟩ := hgood'.2.2 p hp
  obtain ⟨hinv, hv0⟩ := valAt_inv hzb hu0 hu1 hu2
  have hmono : baseMono M (BM.F l) p z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hpos : 0 < (BM.hom p).h z := (BM.hom p).pos z hz.1
  rw [hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv] at hind
  rw [hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)),
    Real.log_inv]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def flagAt {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (ca cb : Fin N) (t : ℂ) (w : Fin d → ℂ)
    (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  if τ' = τ then H τ w * (1 + Matrix.single cb ca t) else H τ' w

def IsFibreData {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) : Prop :=
  (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀ (flagAt H τ ca cb (z 0) (Fin.tail z) τ')) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem isFibreChart_iff {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N)
    (ca cb : Fin N) {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ))
    (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) :
    IsFibreChart FA τ a ca cb q Un Gn ΦYn ΦWn ↔ ∃ l H bp, IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp :=
  Iff.rfl

def upsVal {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℂ :=
  valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b)

def upsLogAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℝ :=
  if M.blk p = none then Real.log ‖upsVal BM l p b‖ else 0

def potAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X)
    (hf : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  blockPot j p.2 (BM.G l p.1 b) hf - upsLogAt BM l p b

def alphaOf {M : FlagModel y Ψ N j} {n d : ℕ} (BM : BaseMetric M n) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) (p : Ψ × Fin N) (w : Fin d → ℂ) : ℝ :=
  potAt BM l p (bp w) (H p.1 w)

def facOf (N j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
    else minorIJ h (omIdx N j) (omIdx N j)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.regularized_weight_tendsto_C2 : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => S.regWeight t ∘ (M.atlas.chart j).symm) (S.R.ph ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied | exact GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied <;> assumption)
end
