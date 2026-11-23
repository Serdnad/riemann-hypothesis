module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle599
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle587
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle020
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open GlobalTheory.PrincCong (congSub mem_congSub_iff isOpen_congSub exists_mat_subset)
open GlobalTheory.LFun.ConjPlace (invT invT_val mem_iff_invT map_mem_Ov_iff)
open GlobalTheory.ThetaSatake (cw cloc)
open GlobalTheory.CompanionTheory.ThetaSatPair (embT_cw invT_symm)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KExLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le_KGL (w : Pl E) (n k : ℕ) : congSub w n k ≤ KGL w (n := n) :=
  fun g hg => ((mem_congSub_iff w n k g).1 hg).1

theorem eventually_congSub_le (w : Pl E) (a : ℕ) (U : Subgroup (GLw a w)) (hU : IsOpen (U : Set (GLw a w))) :
    ∀ᶠ k in atTop, congSub w a k ≤ U := by
  have hVn : (U : Set (GLw a w)) ∈ 𝓝 (1 : GLw a w) := hU.mem_nhds U.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hVn
  obtain ⟨t, htn, htV⟩ := Filter.mem_comap.1 hVn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 htn
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨N₀, hN₀⟩ := exists_mat_subset w a (Filter.inter_mem hA hB')
  filter_upwards [eventually_ge_atTop N₀] with m hm γ hγ
  have a1 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 hγ).2
  have a2 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 (inv_mem hγ)).2
  exact htV (hAB ⟨a1.1, a2.2⟩)

theorem continuous_detGL (w : Pl E) (a : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw a w → (w.adicCompletion E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · have e : (fun g : GLw a w => (((GeneralLinearGroup.det g)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
        fun g => ((g⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) _).det := by
      funext g
      rw [← map_inv]
      rfl
    exact e ▸ Continuous.matrix_det (Units.continuous_val.comp continuous_inv)

theorem eventually_det (w : Pl E) (a : ℕ) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) :
    ∀ᶠ k in atTop, ∀ g ∈ congSub w a k, μ (GeneralLinearGroup.det g) = 1 := by
  have hU : IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw a w)) : Set (GLw a w)) :=
    hμ.preimage (continuous_detGL w a)
  filter_upwards [eventually_congSub_le w a _ hU] with k hk g hg
  exact hk hg

theorem isCompact_congSub (w : Pl E) (n k : ℕ) : IsCompact (congSub w n k : Set (GLw n w)) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w n k)) (congSub_le_KGL w n k)

theorem blocks_mem_congSub {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) {k : ℕ} (hg : blk h w m X ∈ congSub w n k) :
    m.1 ∈ congSub w a k ∧ m.2 ∈ congSub w b k := by
  obtain ⟨hK, hc⟩ := (mem_congSub_iff w n k _).1 hg
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have v := GlobalTheory.CompanionTheory.CtS.blk_val_eq h w m X
  have iv := GlobalTheory.CompanionTheory.CtS.blk_inv_val h w m X
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have v11 : ∀ i j, (blk h w m X).val (e (Sum.inl i)) (e (Sum.inl j)) = m.1.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have v22 : ∀ i j, (blk h w m X).val (e (Sum.inr i)) (e (Sum.inr j)) = m.2.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have i11 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inl i)) (e (Sum.inl j)) = (m.1⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have i22 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inr i)) (e (Sum.inr j)) = (m.2⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have o11 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inl i)) (e (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  have o22 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inr i)) (e (Sum.inr j)) =
      (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(mem_congSub_iff w a k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩,
    (mem_congSub_iff w b k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩⟩
  · rw [← v11]; exact h1 _ _
  · rw [← i11]; exact h2 _ _
  · rw [← v11, ← o11]; exact hc _ _
  · rw [← v22]; exact h1 _ _
  · rw [← i22]; exact h2 _ _
  · rw [← v22, ← o22]; exact hc _ _

theorem conj_mem_congSub (w : Pl E) (n k : ℕ) {x g : GLw n w} (hx : x ∈ KGL w (n := n)) (hg : g ∈ congSub w n k) :
    x * g * x⁻¹ ∈ congSub w n k := by
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y * z⁻¹, (MonoidHom.normal_ker _).conj_mem y hy z, by simp only [map_mul, map_inv]⟩

theorem invT_mem_congSub {u w : Pl E} (c : u.adicCompletion E ≃+* w.adicCompletion E)
    (hc : ∀ x, Valued.v (c x) = Valued.v x) (a k : ℕ) {g : GLw a u} (hg : g ∈ congSub u a k) :
    invT c a g ∈ congSub w a k := by
  have h1 := (mem_congSub_iff u a k _).1 hg
  have h2 := (mem_congSub_iff u a k _).1 (inv_mem hg)
  refine (mem_congSub_iff w a k _).2 ⟨(mem_iff_invT c (map_mem_Ov_iff c hc) g).1 h1.1, fun i j => ?_⟩
  have e : (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      c ((1 : Matrix (Fin a) (Fin a) (u.adicCompletion E)) j i) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  rw [invT_val, e, ← map_sub, hc]
  exact h2.2 j i

theorem under_cw (w : Pl E) :
    (cw w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) (cw w) w).2
    (Or.inr (conjPl_conjSrc _ w))).symm

end GlobalTheory.CompanionTheory.KExLevel

namespace GlobalTheory.CompanionTheory.KExLevel

theorem kEx : KEx := by
  intro E _ _ _ n Sec _ R _ μ hμ L hL
  let T : Finset (Pl E) := R ∪ R.image cw
  have A : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ R, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k → m ∈ L a w := by
    intro a ha w hw
    obtain ⟨L₁, L₂, e, l1, l2⟩ := hL a (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)) w hw
    filter_upwards [eventually_congSub_le w a L₁ l1.1, eventually_congSub_le w (n - a) L₂ l2.1] with k h1 h2 m m1 m2
    rw [e]
    exact ⟨h1 m1, h2 m2⟩
  have B : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ T, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k →
        μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 := by
    intro a _ w _
    filter_upwards [eventually_det w a (μ w) (hμ w), eventually_det w (n - a) (μ w) (hμ w)] with k h1 h2 m m1 m2
    rw [map_mul, map_pow, map_pow, h1 _ m1, h2 _ m2, one_pow, one_pow, one_mul]
  obtain ⟨M, hA, hB⟩ := (((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (A a ha)).and ((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (B a ha))).exists
  have hT : ∀ w, w ∈ T → (if w ∈ T then congSub w n M else KGL w (n := n)) = congSub w n M := fun w hw => if_pos hw
  refine ⟨fun w => if w ∈ T then congSub w n M else KGL w (n := n), ⟨fun w => ?_, ?_⟩, fun w => ?_, fun w hw => ?_,
    fun a ha w hw m X hm => ?_, fun a ha w hw hs u hc m X hm => ?_⟩
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isOpen_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
  · refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    refine hw ?_
    have h' : w ∉ T := h
    simp only [if_neg h']
    exact le_rfl
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isCompact_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  · refine if_neg fun h => ?_
    rcases Finset.mem_union.1 h with h | h
    · exact hw w h rfl
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact hw r hr (under_cw r).symm
  · have hwT : w ∈ T := Finset.mem_union_left _ hw
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos hwT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ w m X hm
    exact ⟨hA a ha' w hw m b1 b2, hB a ha' w hwT m b1 b2⟩
  · have hu : u = cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
    have huT : u ∈ T := Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, hu.symm⟩)
    have hw' : w = cw u := by rw [hu]; exact (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos huT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ u m X hm
    clear hu hc
    subst hw'
    have hv : ∀ x, Valued.v ((cloc u).symm x) = Valued.v x := fun x => by
      have := (GlobalTheory.CuspRep.conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 ((cloc u).symm x)
      have e : GlobalTheory.CuspRep.conjLoc (IsCMField.complexConj E).toRingEquiv u ((cloc u).symm x) = x :=
        (cloc u).apply_symm_apply x
      rw [e] at this
      exact this.symm
    let p : ∀ c : ℕ, GLw c u → GLw c (cw u) := fun c g =>
      (invT (cloc u) c).symm ((PhiU c (u.adicCompletion E))⁻¹ * g * PhiU c (u.adicCompletion E))
    have hp : ∀ c (g : GLw c u), g ∈ congSub u c M → p c g ∈ congSub (cw u) c M := fun c g hg => by
      have hk : (PhiU c (u.adicCompletion E))⁻¹ ∈ KGL u (n := c) := inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ c)
      have h1 := conj_mem_congSub u c M hk hg
      rw [inv_inv] at h1
      change (invT (cloc u) c).symm _ ∈ _
      rw [invT_symm]
      exact invT_mem_congSub (cloc u).symm hv c M h1
    have he : ∀ c (g : GLw c u), embW c u g = embT c (cw u) (p c g) := fun c g => by
      rw [embT_cw]
      simp only [p, MulEquiv.apply_symm_apply]
      congr 1
      group
    exact ⟨hB a ha' u huT m b1 b2, (p a m.1, p (n - a) m.2), hA a ha' (cw u) hw _ (hp _ _ b1) (hp _ _ b2),
      he _ _, he _ _⟩

end GlobalTheory.CompanionTheory.KExLevel

end
end

section

open Filter Topology Set
open PositivityTheory.Rg.SwEis

namespace GlobalTheory.CompanionTheory.PolyDenominator

theorem exists_pow_mul (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) (a : ℂ) :
    ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ 0 ∧ ∀ z, B z = (z - a) ^ k * v z :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundFirst.main B hB hz a

theorem finite_zeros (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    {z | z ∈ Q ∧ B z = 0}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hz
  have han : AnalyticOnNhd ℂ B univ := fun x _ => hB.analyticAt x
  by_contra hinf
  have hinf' : ({z | z ∈ Q ∧ B z = 0} : Set ℂ).Infinite := hinf
  obtain ⟨x, hxQ, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hQ (fun z hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, B z = 0 :=
    (accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2
  exact hz₀ (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ x) hfreq (mem_univ z₀))

theorem factor_of_finset {Q : Set ℂ} (F : Finset ℂ) :
    ∀ B : ℂ → ℂ, Differentiable ℂ B → (∃ z, B z ≠ 0) → (∀ z ∈ Q, B z = 0 → z ∈ F) →
      ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
        (∀ z, B z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro B hB _ hF
    refine ⟨1, B, one_ne_zero, hB, fun z => by simp, fun z hz h0 => ?_⟩
    simpa using hF z hz h0
  | insert a F _ ih =>
    intro B hB hz hF
    obtain ⟨k, v, hv, hva, hBv⟩ := exists_pow_mul B hB hz a
    obtain ⟨d, u, hd, hu, hvu, huQ⟩ := ih v hv ⟨a, hva⟩ (by
      intro z hzQ h0
      have hza : z ≠ a := fun h => hva (h ▸ h0)
      have hBz : B z = 0 := by rw [hBv, h0, mul_zero]
      exact (Finset.mem_insert.1 (hF z hzQ hBz)).resolve_left hza)
    refine ⟨(Polynomial.X - Polynomial.C a) ^ k * d, u,
      mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hd, hu, fun z => ?_, huQ⟩
    rw [hBv, hvu]
    simp [mul_assoc]

theorem exists_poly_factor (A : ℂ → ℂ) (hA : Differentiable ℂ A) (hz : ∃ z, A z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
      (∀ z, A z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 :=
  factor_of_finset (finite_zeros A hA hz hQ).toFinset A hA hz fun z hzQ h0 => by simpa using And.intro hzQ h0

theorem glue : Glue := by
  classical
  intro X I _ T e H A R hA hAne hHd hHc hHe hed hec heT s₀
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min s₀.re R - 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = s₀.im := ⟨_, rfl⟩
  have hQ : IsCompact (Icc a (R + 1) ×ℂ Icc (c - 1) (c + 1)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨d, u, hd, hu, hAu, huQ⟩ := exists_poly_factor A hA hAne hQ
  let P : Set ℂ := {z | R < z.re}
  let W : Set ℂ := {z | a < z.re ∧ z.re < R + 1 ∧ c - 1 < z.im ∧ z.im < c + 1}
  let U : Set ℂ := P ∪ {z | a < z.re ∧ c - 1 < z.im ∧ z.im < c + 1}
  have hPo : IsOpen P := isOpen_lt continuous_const Complex.continuous_re
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hUo : IsOpen U := hPo.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))
  have hWQ : ∀ z ∈ W, u z ≠ 0 := fun z hz => huQ z (Complex.mem_reProdIm.2
    ⟨⟨hz.1.le, hz.2.1.le⟩, ⟨hz.2.2.1.le, hz.2.2.2.le⟩⟩)
  have hUPW : ∀ z ∈ U, z ∈ P ∨ z ∈ W := by
    rintro z (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · by_cases h : R < z.re
      · exact Or.inl h
      · exact Or.inr ⟨h1, by linarith [not_lt.1 h], h2, h3⟩
  let E : ℂ → X → ℂ := fun z x => if R < z.re then d.eval z * e z x else H z x / u z
  have hEP : ∀ z, R < z.re → ∀ x, E z x = d.eval z * e z x := fun z h x => by simp [E, h]
  have hEW : ∀ z ∈ W, ∀ x, E z x = H z x / u z := by
    intro z hz x
    by_cases h : R < z.re
    · have h0 := hWQ z hz
      rw [hEP z h, hHe z h, hAu z]
      field_simp
    · simp [E, h]
  have hHT : ∀ i x z, H z (T i x) = H z x := by
    intro i x z
    have h1 : AnalyticOnNhd ℂ (H · (T i x)) univ := fun w _ => (hHd (T i x)).analyticAt w
    have h2 : AnalyticOnNhd ℂ (H · x) univ := fun w _ => (hHd x).analyticAt w
    have hmem : ((R + 1 : ℝ) : ℂ) ∈ P := by simp [P]
    have h3 : (H · (T i x)) =ᶠ[𝓝 ((R + 1 : ℝ) : ℂ)] (H · x) := by
      filter_upwards [hPo.mem_nhds hmem] with w hw
      rw [hHe w hw, hHe w hw, heT]
    exact congrFun (h1.eq_of_eventuallyEq h2 h3) z
  refine ⟨U, d, E, hUo, ⟨⟨R, subset_union_left⟩, ?_⟩, ?_, hd, ?_, ?_, ?_, fun z hz x => hEP z hz x⟩
  · rintro s (h | ⟨h1, h2, h3⟩) t ht
    · left
      simp only [P, mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
      exact lt_add_of_lt_of_nonneg h ht
    · right
      simp only [mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      exact ⟨lt_add_of_lt_of_nonneg h1 ht, h2, h3⟩
  · by_cases h : R < s₀.re
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · have := min_le_left s₀.re R
        rw [ha]; linarith
      · rw [hc]; linarith
      · rw [hc]; linarith
  · intro x z hz
    rcases hUPW z hz with h | h
    · have h1 : DifferentiableAt ℂ (fun w => d.eval w * e w x) z :=
        (d.differentiable z).mul ((hed x z h).differentiableAt (hPo.mem_nhds h))
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hPo.mem_nhds h] with w hw using hEP w hw x
    · have h1 : DifferentiableAt ℂ (fun w => H w x / u w) z := (hHd x z).div (hu z) (hWQ z h)
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hWo.mem_nhds h] with w hw using hEW w hw x
  · have hc1 : ContinuousOn (fun y : ℂ × X => d.eval y.1 * e y.1 y.2) (P ×ˢ univ) :=
      (d.continuous.comp continuous_fst).continuousOn.mul hec
    have hc2 : ContinuousOn (fun y : ℂ × X => H y.1 y.2 / u y.1) (W ×ˢ univ) :=
      hHc.continuousOn.div (hu.continuous.comp continuous_fst).continuousOn fun y hy => hWQ y.1 hy.1
    rintro ⟨z, x⟩ ⟨hz, -⟩
    rcases hUPW z hz with h | h
    · have ho : IsOpen (P ×ˢ (univ : Set X)) := hPo.prod isOpen_univ
      have hmem : (z, x) ∈ P ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (P ×ˢ univ) :=
        hc1.congr fun y hy => hEP y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
    · have ho : IsOpen (W ×ˢ (univ : Set X)) := hWo.prod isOpen_univ
      have hmem : (z, x) ∈ W ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (W ×ˢ univ) :=
        hc2.congr fun y hy => hEW y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
  · intro z hz i x
    rcases hUPW z hz with h | h
    · rw [hEP z h, hEP z h, heT]
    · rw [hEW z h, hEW z h, hHT]

end GlobalTheory.CompanionTheory.PolyDenominator
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeSmooth

theorem exists_open_unit_subgroup_ker : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧
      (∀ x ∈ U, IsUnitAt w x) ∧ ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  intro E _ _ χ w
  have hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ) := GlobalTheory.HeckeComp.smooth_loc χ w
  let V : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {x | Valued.v (x : w.adicCompletion E) = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hV : IsOpen (V : Set (w.adicCompletion E)ˣ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx1 : Valued.v (x : w.adicCompletion E) = 1 := hx
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by rw [hx1]; exact one_ne_zero
    have h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹'
        {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x :=
      Units.continuous_val.continuousAt (Valued.locally_const hx0)
    refine Filter.mem_of_superset h2 ?_
    intro y hy
    have hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E) := hy
    show Valued.v (y : w.adicCompletion E) = 1
    rw [hy', hx1]
  refine ⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hker.inter hV
  · intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro x hx
    exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1

end GlobalTheory.CompanionTheory.HeckeSmooth
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.adelic_haar_splits_as_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple <;> assumption)
end
