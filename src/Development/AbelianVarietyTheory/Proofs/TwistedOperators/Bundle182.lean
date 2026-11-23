module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle167
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Finset
open GlobalTheory.SignedHC

namespace GlobalTheory.PiCounts

variable {G : GridData}

theorem a_injective (hg : 0 < G.ga) : Function.Injective G.a := by
  intro i j h
  have e := G.a_sub_a i j
  rw [h, sub_self] at e
  have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have : ((j : ℚ) - i) = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact h
    · exact absurd h hg'
  have : (j : ℚ) = i := by linarith
  exact_mod_cast this.symm

theorem a_anti {i j : ℕ} (h : i ≤ j) : G.a j ≤ G.a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ G.ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h]

theorem card_tops (hg : 0 < G.ga) : G.tops.card = G.m + 1 := by
  rw [GridData.tops, card_image_of_injective _ (a_injective hg), card_range]

theorem card_cloudHalf : G.cloudHalf.card = G.k - 1 := by
  rw [GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : G.v i = G.v j := by
      have : (G.v i : ℚ) = G.v j := by simp only [GridData.vHalf] at h; linarith
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e (G.v_anti i j hi.1 h' hj.2).ne'
    · exact h'
    · exact absurd e (G.v_anti j i hj.1 h' hi.2).ne

theorem card_Cs' (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card = i * (G.s - 1) := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc (G.m - i + 1) G.m, (G.blockC' u).card = G.s - 1 := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  · intro u hu v hv huv
    have hu := mem_Icc.1 (mem_coe.1 hu)
    have hv := mem_Icc.1 (mem_coe.1 hv)
    refine disjoint_left.2 fun x h1 h2 => ?_
    have b1 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h1
    have b2 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hv.2 h2
    rcases lt_or_gt_of_ne huv with h | h <;>
      linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]

theorem card_entries_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (GlobalTheory.SignedHC.entries (G.parPi i)).card = G.rankP i := by
  have hg0 : 0 < G.ga := by omega
  have d1 : Disjoint G.tops G.cloudHalf := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨l, hl, rfl⟩ := GridData.mem_tops.1 h1
    linarith [GlobalTheory.ChiGrid.cloudHalf_lt h2, a_anti (G := G) hl]
  have d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc (G.m - i + 1) G.m).biUnion G.blockC') :=
    disjoint_left.2 fun x h1 h2 => by
      obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
      have hu := mem_Icc.1 hu
      have b := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h2
      rcases mem_union.1 h1 with h1 | h1
      · obtain ⟨l, -, rfl⟩ := GridData.mem_tops.1 h1
        rcases lt_or_ge l u with h | h
        · linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b.2]
        · linarith [a_anti (G := G) h, b.1]
      · linarith [GlobalTheory.ChiGrid.cloudHalf_lt h1, a_anti (G := G) hu.2, b.1]
  have := G.two_le_k
  rw [GridData.entries_parPi, GridData.entries_lam, card_union_of_disjoint d2, card_union_of_disjoint d1,
    card_tops hg0, card_cloudHalf, card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem card_parPi_le {i : ℕ} (hg : 0 < G.ga) : (G.parPi i).card ≤ (G.m + 1) + (G.k - 1) +
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card := by
  rw [GridData.parPi]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact card_image_le.trans (card_range _).le
  · exact card_image_le.trans card_cloudHalf.le
  · exact card_image_le

theorem card_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (G.parPi i).card = G.rankP i := by
  refine le_antisymm ?_ ((card_entries_parPi hm hs hg hi).symm.le.trans card_image_le)
  have := G.two_le_k
  refine (card_parPi_le (by omega)).trans ?_
  rw [card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem isRegular_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    IsRegular (G.parPi i) :=
  isRegular_iff_card.2 ((card_entries_parPi hm hs hg hi).trans (card_parPi hm hs hg hi).symm)

theorem nMinus_parPi (hg : 0 < G.ga) (i : ℕ) : nMinus (G.parPi i) = (G.m - i + 1) / 2 := by
  have : (G.parPi i).filter (fun x => x.2 = false) =
      (range ((G.m - i + 1) / 2)).image fun c => (G.a (G.m - i - 1 - 2 * c), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parPi, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨l, h1, h2, h3⟩ | ⟨-, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · have h5 : ¬ (G.m - i ≤ l ∨ Even (G.m - i - l)) := by simpa using h3.symm
        rw [Nat.even_iff] at h5
        refine ⟨(G.m - i - l - 1) / 2, by omega, ?_, rfl⟩
        rw [show G.m - i - 1 - 2 * ((G.m - i - l - 1) / 2) = l by omega, h2]
      · simp at h
      · simp at h
    · rintro ⟨c, hc, rfl, rfl⟩
      refine ⟨Or.inl ⟨G.m - i - 1 - 2 * c, by omega, rfl, ?_⟩, rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro c hc c' hc' h
  simp only [coe_range, Set.mem_Iio] at hc hc'
  have h1 := a_injective hg (congrArg Prod.fst h)
  omega

end GlobalTheory.PiCounts

namespace GlobalTheory.Grid

theorem parPi_counts : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m →
    GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧
      GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  intro D _ τ i hi
  have hg : (grid D τ).s < (grid D τ).ga := by
    have := (isLeast_gap D).1.2.1
    show sLen D < gap D
    omega
  have hs : 1 ≤ (grid D τ).s := by show 1 ≤ D.R.r + 6; omega
  have hm := grid_nearMid D τ
  have hi' : i ≤ (grid D τ).m := hi
  refine ⟨GlobalTheory.PiCounts.isRegular_parPi hm hs hg hi', ?_, GlobalTheory.PiCounts.nMinus_parPi (by omega) i⟩
  exact (GlobalTheory.PiCounts.card_parPi hm hs hg hi').trans rfl

end GlobalTheory.Grid
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open Filter Topology

theorem tendsto_sum_placeIdem {F : Type} [Field F] [NumberField F]
    (α : HeightOneSpectrum (𝓞 F) → GlobalTheoryTheory.GenusMassVolumes.Af F) (h1 : ∀ v, evalV F v (α v) = 1)
    (h0 : ∀ v v', v' ≠ v → evalV F v' (α v) = 0) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ s, α v) atTop (𝓝 1) := by
  classical
  have hv : ∀ (s : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)),
      evalV F w (1 - ∑ v ∈ s, α v) = if w ∈ s then 0 else 1 := by
    intro s w

    rw [map_sub, map_one, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw (fun v _ hvw => h0 v w (Ne.symm hvw)), h1, sub_self]
    · rw [Finset.sum_eq_zero (fun v hvs => h0 v w (by rintro rfl; exact hw hvs)), sub_zero]

  let y : Finset (HeightOneSpectrum (𝓞 F)) → (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun s w => if w ∈ s then 0 else 1
  have hy : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with s hs
    have hws : w ∈ s := Finset.singleton_subset_iff.mp hs
    simp [y, hws]
  let g : ((w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F) → GlobalTheoryTheory.GenusMassVolumes.Af F :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite
  have hg : Continuous g := RestrictedProduct.isEmbedding_structureMap.continuous
  have hgy : ∀ s, g (y s) = 1 - ∑ v ∈ s, α v := by
    intro s
    refine FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => ?_)
    have e1 : (g (y s)) w = ((y s w : w.adicCompletionIntegers F) : w.adicCompletion F) := rfl
    have e2 : (1 - ∑ v ∈ s, α v) w = evalV F w (1 - ∑ v ∈ s, α v) := rfl
    rw [e1, e2, hv]
    by_cases hw : w ∈ s <;> simp [y, hw]
  have hg0 : g 0 = 0 := FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => rfl)
  have hlim : Tendsto (fun s => 1 - ∑ v ∈ s, α v) atTop (𝓝 (0 : GlobalTheoryTheory.GenusMassVolumes.Af F)) := by
    have h := (hg.tendsto 0).comp hy
    rw [hg0] at h
    exact h.congr (fun s => hgy s)
  simpa using (tendsto_const_nhds (x := (1 : GlobalTheoryTheory.GenusMassVolumes.Af F))).sub hlim

theorem tendsto_truncation : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  intro D ε hε a ha
  simp only [IsPlaceIdem] at hε
  choose α hαε hα1 hα0 using hε
  have hsum : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ∑ v ∈ s, ε v = pairA D.host.F 0 (∑ v ∈ s, α v) := by
    intro s
    simp only [hαε]
    exact (map_sum (AddMonoidHom.inr (InfiniteAdeleRing D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) α s).symm
  have hpair : Continuous (pairA D.host.F 0) := by
    show Continuous fun y : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => ((0 : InfiniteAdeleRing D.host.F), y)
    exact continuous_const.prodMk continuous_id
  have hlimF : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => ∑ v ∈ s, ε v) atTop
      (𝓝 (pairA D.host.F 0 1)) := by
    simp_rw [hsum]
    exact (hpair.tendsto 1).comp (tendsto_sum_placeIdem α hα1 hα0)

  have hidem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * a = a := by
    have hsplit : pairA D.host.F 0 1 = 1 - pairA D.host.F 1 0 := by
      rw [eq_sub_iff_add_eq]
      show ((0 + 1, 1 + 0) : InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F) = 1
      rw [zero_add, add_zero]
      rfl
    have hr : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) = GlobalTheory.SplitScalar.realIdem D := by
      rw [GlobalTheory.SplitScalar.realIdem, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsplit, map_sub, map_one, hr, sub_mul, one_mul, GlobalTheory.SplitScalar.realIdem_mul_of_fin ha, sub_zero]
  have hT := hlimF.smul_const a
  rw [Algebra.smul_def, hidem] at hT
  exact hT.congr (fun s => Algebra.smul_def _ _)

end GlobalTheory.VecInv

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem adjoint_apply_of_orthogonal_ker {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℂ}
    (hu : u ∈ (LinearMap.ker T)ᗮ) (h : T (LinearMap.adjoint T (T u)) = l • T u) : LinearMap.adjoint T (T u) = l • u := by
  have hk : LinearMap.adjoint T (T u) - l • u ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, map_smul, h, sub_self]
  have hr : LinearMap.adjoint T (T u) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk'
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hk', inner_zero_left]
  have ho : LinearMap.adjoint T (T u) - l • u ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hr (Submodule.smul_mem _ l hu)
  have hz := Submodule.inner_right_of_mem_orthogonal hk ho
  rwa [inner_self_eq_zero, sub_eq_zero] at hz

theorem inner_apply_of_adjoint_eq {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℝ}
    (h : LinearMap.adjoint T (T u) = (l : ℂ) • u) (w : H) : ⟪T u, T w⟫_ℂ = (l : ℂ) * ⟪u, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]

theorem conj_csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    starRingEnd ℂ (GlobalTheory.LiftLower.csumAt S ((starRingEnd ℂ).comp σ) f g) = GlobalTheory.LiftLower.csumAt S σ f g := by
  unfold GlobalTheory.LiftLower.csumAt

  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, RingHom.comp_apply, map_sum, map_mul,
  Complex.star_def, Complex.conj_conj]

end GlobalTheory.ConjScalar
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem vacuum_unique_of_selfDual {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (Λ : Submodule R X)
    (hΛ : SelfDual γ Λ) (s : M) (hs : s ≠ 0) (hfix : Fixes W Λ s)
    (hspan : Submodule.span ℂ (Set.range fun x => W x s) = ⊤) (v : M) (hv : Fixes W Λ v) : ∃ c : ℂ, v = c • s := by
  have key : ∀ z : X, W z s = (γ (w • (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) : X))
      (z - Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)))⁻¹ • W (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)) s := by
    intro z
    set t : X := Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) with ht
    have hmem : z - t ∈ Λ := by
      rw [← Submodule.Quotient.eq]
      exact (Quotient.out_eq (Submodule.Quotient.mk z : X ⧸ Λ)).symm
    have h1 := h.comp t (z - t) s
    rw [hfix _ hmem, add_sub_cancel] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]
  have hli : LinearIndependent ℂ (fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    refine linearIndependent_of_simultaneous_eigen _ (fun q (a : Λ) => γ a (Quotient.out q)) (fun a : Λ => W a) ?_ ?_ ?_
    · intro q q' hq
      have hm : (Quotient.out q : X) - Quotient.out q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (Quotient.out q) = γ a (Quotient.out q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← Submodule.Quotient.eq] at hm
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      have e2 : (Submodule.Quotient.mk (Quotient.out q') : X ⧸ Λ) = q' := Quotient.out_eq q'
      rw [← e1, ← e2, hm]
    · intro a q
      rw [h.comm, hfix a a.2]
    · intro q h0
      have h1 := h.neg_comp (Quotient.out q) s
      rw [h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [key z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ q, b q = W (Quotient.out q) s := fun q => Module.Basis.mk_apply hli hsp q
  have hcoord : ∀ a ∈ Λ, ∀ q x, b.coord q (W a x) = γ a (Quotient.out q) * b.coord q x := by
    intro a ha q x
    have e : (b.coord q).comp (W a) = γ a (Quotient.out q) • b.coord q := by
      refine b.ext fun q' => ?_
      rw [LinearMap.comp_apply, hb, h.comm, hfix a ha, ← hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hq
      · rw [hq]
      · simp
    exact LinearMap.congr_fun e x
  have h0 : (Quotient.out (0 : X ⧸ Λ) : X) ∈ Λ :=
    (Submodule.Quotient.mk_eq_zero Λ).1 (Quotient.out_eq (0 : X ⧸ Λ))
  have hb0 : b 0 = s := by rw [hb, hfix _ h0]
  have hvan : ∀ q : X ⧸ Λ, q ≠ 0 → b.repr v q = 0 := by
    intro q hq
    have hn : (Quotient.out q : X) ∉ Λ := fun hm => hq (by
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      rw [← e1]; exact (Submodule.Quotient.mk_eq_zero Λ).2 hm)
    rw [hΛ] at hn
    push_neg at hn
    obtain ⟨a, ha, hne⟩ := hn
    have hne' : γ a (Quotient.out q) ≠ 1 := fun e => hne (h.swap_eq_one e)
    have e := hcoord a ha q v
    rw [hv a ha, Module.Basis.coord_apply] at e
    have e2 : (γ a (Quotient.out q) - 1) * b.repr v q = 0 := by rw [sub_mul, ← e]; ring
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne')
  refine ⟨b.repr v 0, b.ext_elem fun q => ?_⟩
  rw [map_smul, ← hb0, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hq : (0 : X ⧸ Λ) = q
  · subst hq; simp
  · rw [if_neg hq, mul_zero, hvan q (Ne.symm hq)]

end GlobalTheory.SphTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

end GlobalTheory.KFinCuspAvgType
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_linear_thetaFunctions : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.term_linear | exact GlobalTheory.MixedTerm.term_linear | (intros; apply GlobalTheory.MixedTerm.term_linear <;> assumption)
end
