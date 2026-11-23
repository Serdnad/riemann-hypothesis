module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.CurvePointsFinite

theorem degC_pos_of_isArithVar_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) : 0 < degC W := by
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  rw [hdeg]
  exact Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩

theorem ZhangLowerX.proof (h : SuccessiveMinimaLowerBound) : ZhangLowerX.Statement := by
  intro K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh
  refine h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_
  have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
  have h1 := hh W hW hPW
  rwa [IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd] at h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem leadMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    f (leadMinor M a) = leadMinor (f.mapMatrix M) a := by
  unfold leadMinor pivotMinor
  rw [RingHom.map_det]
  rfl

theorem leadMinor_one {R : Type} [CommRing R] {n : ℕ} (a : Fin (n - 1)) :
    leadMinor (1 : Matrix (Fin n) (Fin n) R) a = 1 := by
  unfold leadMinor pivotMinor
  have h : (1 : Matrix (Fin n) (Fin n) R).submatrix (Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega))
      (pivotCols a (Fin.castLE (Nat.sub_le n 1) a)) = (1 : Matrix (Fin ((a : ℕ) + 1)) (Fin ((a : ℕ) + 1)) R) := by
    ext i j
    have hj : pivotCols a (Fin.castLE (Nat.sub_le n 1) a) j = Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega) j := by
      unfold pivotCols
      split_ifs with hlt
      · rfl
      · ext
        simp only [Fin.val_castLE]
        have := j.2
        omega
    rw [Matrix.submatrix_apply, hj, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castLE_inj]
  rw [h, Matrix.det_one]

theorem genMatFr_eq_map (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    genMatFr F Ψ n τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext i j
  simp [genMatFr]

theorem GenLeadMinorNeZero.full : GenLeadMinorNeZero.Statement := by
  intro F _ Ψ n τ a
  rw [genMatFr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinor0NeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMat0Fr F Ψ n j τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagRatioFieldEq.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c) =
      IntermediateField.adjoin Ω (Set.range (flagMinorRatio0 Ω Ψ D.N D.j))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

theorem ProjSmoothAlong.proof (hO : HoloInjDerivInj.Statement) (hL : LocalOrbitChart.Statement) :
    ProjSmoothAlong.Statement := by
  intro II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀
  set S := mcPts (mCoordIdeal D.y) with hS
  set x₀ := M.proj z₀ with hx₀
  obtain ⟨j, hj⟩ := M.atlas.cover x₀
  set e := M.atlas.chart j with he
  obtain ⟨W, hWo, hxW, s, hs, hsh⟩ := M.sections x₀
  obtain ⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀
  set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ
  set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf
  set u₀ := e x₀ with hu₀
  set T := e.target ∩ e.symm ⁻¹' W with hT
  have hTo : IsOpen T := e.isOpen_inter_preimage_symm hWo
  have hσa : AnalyticOnNhd ℂ σ T := fun u hu => AnalyticAt.pi fun p => hsh p j u hu
  have hu₀t : u₀ ∈ e.target := e.map_source hj
  have hsymm₀ : e.symm u₀ = x₀ := e.left_inv hj
  have hu₀T : u₀ ∈ T := ⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩

  have hσ₀ : σ u₀ = s x₀ := by simp only [hσ, hsymm₀]
  obtain ⟨hsx₀S, hsx₀p⟩ := hs x₀ hxW
  obtain ⟨c₀, hc₀, hc₀e⟩ := (M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm
  have hsx₀N : s x₀ ∈ N := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1
  have hκs₀ : κ (s x₀) = κ z₀ := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2

  set T' := T ∩ σ ⁻¹' N with hT'
  have hT'o : IsOpen T' := hσa.continuousOn.isOpen_inter_preimage hTo hNo
  have hu₀T' : u₀ ∈ T' := ⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩
  have hfa : AnalyticOnNhd ℂ f T' := fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)
  have hinj : Set.InjOn f T' := by
    intro u hu u' hu' hfu
    obtain ⟨hmS, hmp⟩ := hs (e.symm u) hu.1.2
    obtain ⟨hmS', hmp'⟩ := hs (e.symm u') hu'.1.2
    obtain ⟨c, hc, hce⟩ := hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu
    have hpe : M.proj (σ u) = M.proj (σ u') := (M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩
    have h2 : e.symm u = e.symm u' := by
      simp only [hσ] at hpe
      rw [← hmp, ← hmp', hpe]
    rw [← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]

  have hDinj : Function.Injective (fderiv ℂ f u₀) := hO D.n f T' hT'o hfa hinj u₀ hu₀T'
  set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv
    with hLc
  have hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀ := by
    have hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀ := by
      ext v; rfl
    rw [hcoe]
    exact (hfa u₀ hu₀T').differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω f u₀ := (hfa u₀ hu₀T').contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set linv := hcd.localInverse hFD hn with hlinv
  have hlinv_cd : ContDiffAt ℂ ω linv (f u₀) := hcd.to_localInverse hFD hn
  have hlinv₀ : linv (f u₀) = u₀ := hcd.localInverse_apply_image hFD hn
  have hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u := (hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse
  have hfu₀ : f u₀ = κ z₀ := by simp only [hf, hσ₀, hκs₀]

  set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ
  have hΦcd : ContDiffAt ℂ ω Φ z₀ := by
    have h1 : ContDiffAt ℂ ω linv (κ z₀) := hfu₀ ▸ hlinv_cd
    exact h1.comp z₀ (hκa z₀ hzN).contDiffAt
  have hΦ₀ : Φ z₀ = u₀ := by simp only [hΦ, ← hfu₀, hlinv₀]
  obtain ⟨V₁, hV₁, hΦV₁⟩ := hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)
  have hΦV₁R : ContDiffOn ℝ ∞ Φ V₁ := hΦV₁.restrict_scalars ℝ
  set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂
  have hV₂n : V₂ ∈ 𝓝 z₀ :=
    inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))
  have hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target := by
    have := hg j
    simpa [ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn] using this
  have hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂ :=
    hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)

  have hcont : ContinuousWithinAt M.proj S z₀ := M.cont z₀ hz₀
  have htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀) :=
    (e.continuousAt hj).tendsto.comp hcont.tendsto
  have hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W :=
    hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)
  have hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w) := htend.eventually hleft
  have hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N := nhdsWithin_le_nhds (hNo.mem_nhds hzN)
  have hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N :=
    (hev1.and hev2).and hev3
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N},
    inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩
  rintro w ⟨⟨-, hw⟩, hwS⟩
  obtain ⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩ := hw hwS
  obtain ⟨hsS, hsp⟩ := hs (M.proj w) hxW'
  obtain ⟨c, hc, hce⟩ := (M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm
  have hfe : f (e (M.proj w)) = κ w := by
    simp only [hf, hσ, e.left_inv hxe]
    rw [hce]
    exact (hκt w hwN c hc).2
  have hΦw : Φ w = e (M.proj w) := by
    simp only [hΦ]
    rw [← hfe, hli]
  simp only [hΦw, e.left_inv hxe]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ModelFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (modelQ M Ψ ⁻¹' {y} \ modelCrit M Ψ).Finite

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem HodgeFlagArith.proof (hNe : HodgeFlagNeZero.Statement) (hTr : HodgeFlagRatioTrdeg.Statement) :
    HodgeFlagArith.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  choose cX hcX using D.arith.2.1.2.2
  choose cP hcP using hNe II Ψ K ι Ω E D Pl H B
  let c : ∀ k, Pl.ιY k := fun
    | Sum.inl k => cX k
    | Sum.inr q => cP q.1 q.2
  have hc : ∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0 := by
    rintro (k | q)
    · intro h
      have h0 : D.y ⟨k, cX k⟩ = 0 := by
        have h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0 := h
        have h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0 :=
          IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')
        exact C_injective _ _ (h2.trans C_0.symm)
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    · exact hcP q.1 q.2
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : CharZero Pl.ΩY :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)
  have hhor : IsHorizontal (Pl.flagPrime B) := horizontal (Pl.flagGenericPoint B)
  refine ⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (Pl.flagGenericPoint B),
    relevant (Pl.flagGenericPoint B) c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ Pl.ιY (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (Pl.flagGenericPoint B) c) (ratioPtL (Pl.flagGenericPoint B) c)
    (birational (Pl.flagGenericPoint B) c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (Pl.flagGenericPoint B) c) = ((D.n + D.flagDim0 : ℕ) : Cardinal) := by
    rw [← hTr II Ψ K ι Ω E D Pl H B c hc]
    have hsub : (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (Pl.flagGenericPoint B) c).toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      simp only [IntermediateField.adjoin_toSubfield]
      refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
        (Subfield.closure_mono Set.subset_union_right)
      rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    rw [← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]
    exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv
  rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc, hL] at htr
  have : (mCoordIdeal (Pl.flagGenericPoint B)).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) (algebraMap_injective _ hhor)
  show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) = _
  rw [hA, htr]
  rw [← Nat.cast_add, Cardinal.toENat_nat,
    show D.n + 1 + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) =
      D.n + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushDown.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hArith : HodgeFlagArith.Statement) : PushDown.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep
  have hY := hArith II Ψ K ι Ω E D Pl H B
  have hX : IsArithVar (imageZ Pl.xV (Pl.flagPrime B)) (D.n + 1) := by
    rw [Pl.imageZ_forget_flagPrime]
    exact D.arith
  refine ⟨fun G J L L' N hJ hL hL' hN => ?_, fun d r L L' N hdr hd hL hL' hN => ?_⟩
  · have h := hPF II hII.1 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) D.flagDim0
      G J L L' N Pl.isBlockMap_xV hY hX hJ hL hL' hN
    rwa [Pl.imageZ_forget_flagPrime] at h
  · exact hII.2.2.2 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) d r L L' N
      Pl.isBlockMap_xV (by rw [hdr]; exact hY) hX hd hL hL' hN

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
