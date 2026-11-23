module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle235
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle237
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle233
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle202
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rd_iter_pow (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (M : ℕ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
      ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr M
  obtain ⟨Θ, hΘ, hid⟩ := hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  induction M with
  | zero =>
    intro F F' hF hF'
    obtain ⟨_, _, -, hFc, -⟩ := hF
    obtain ⟨_, _, -, hFc', -⟩ := hF'
    obtain ⟨K, hK⟩ := radial_boundedness P.k P.r Wp Wq D F F' hFc hFc'
    exact ⟨K, fun s => by simpa using hK s⟩
  | succ M ih =>
    intro F F' hF hF'
    obtain ⟨K1, hK1⟩ := ih (Θ 1 F) (Θ 0 F') (hΘ 1 F hF) (hΘ 0 F' hF')
    obtain ⟨K2, hK2⟩ := ih (Θ 3 F) (Θ 2 F') (hΘ 3 F hF) (hΘ 2 F' hF')
    refine ⟨K1 + K2, fun s => ?_⟩
    have e := hid s F F' hF hF'
    calc ‖s‖ ^ (M + 1) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        = ‖s‖ ^ M * ‖s * B.beta D (wvG D.z D.z' s F) F'‖ := by rw [norm_mul, pow_succ]; ring
      _ = ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') -
            B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖ := by rw [e]
      _ ≤ ‖s‖ ^ M * (‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F')‖ +
            ‖B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ K1 + K2 := by rw [mul_add]; exact add_le_add (hK1 s) (hK2 s)

theorem rd_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx N])
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem rd_decay (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' → ∀ n : ℕ,
      ∃ C : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3)) := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr F F' hF hF' n
  have hp := rd_iter_pow hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨K0, hK0⟩ := hp 0 F F' hF hF'
  obtain ⟨KN, hKN⟩ := hp (n + 3) F F' hF hF'
  refine ⟨2 ^ (n + 3) * (K0 + KN), fun s => ?_⟩
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hb : 0 ≤ ‖B.beta D (wvG D.z D.z' s F) F'‖ := norm_nonneg _
  have hb0 : ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K0 := by simpa using hK0 s
  have hbN := hKN s
  have hpos : 0 < 1 + ‖s‖ := by linarith
  have main : (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ 2 ^ (n + 3) * (K0 + KN) := by
    calc (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        ≤ 2 ^ (n + 3) * (1 + ‖s‖ ^ (n + 3)) * ‖B.beta D (wvG D.z D.z' s F) F'‖ :=
          mul_le_mul_of_nonneg_right (rd_pow_le _ hx _) hb
      _ = 2 ^ (n + 3) * (‖B.beta D (wvG D.z D.z' s F) F'‖ +
            ‖s‖ ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖) := by ring
      _ ≤ 2 ^ (n + 3) * (K0 + KN) := mul_le_mul_of_nonneg_left (add_le_add hb0 hbN) (by positivity)
  have hr' : (1 + ‖s‖) ^ (-((n : ℝ) + 3)) = ((1 + ‖s‖) ^ (n + 3))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hr', ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [main]

theorem radDecay_of_cut (hI : RDIdent) : RadDecay := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε G H hε hG hH Φ Ψ hΦ hΨ
    c hc n
  have hr : 0 < P.r := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  obtain ⟨C', hC'⟩ := rd_decay hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr G H
    ⟨ε, hε, hG⟩ ⟨ε, hε, hH⟩ n
  subst hz hz' hπ hπ'
  obtain ⟨C1, -, hC1⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  refine ⟨‖C1‖ * C', fun s Wv hW => ?_⟩
  have hwv := radial_wave_identity P.k P.r Wp Wq D hr ε s G
  have hΦ' : ∀ y ∈ DomR P.k P.r D.z D.z', ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 := by
    intro y hy
    rw [hW Φ y.1 y.2, hΦ y hy, hwv.2 y hy, hl']
  rw [hl0, hC1 (wvG D.z D.z' s G) H (Wv Φ) Ψ (hwv.1 hG).2.1 hH.2.1 hΦ' hΨ c, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC' s) (norm_nonneg _)

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem germ_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vec : C.LPt → H) (b s : ℕ) (hs : 2 ≤ s) (hbs : b + s - 1 = S.G.r + 1) (h : C.LPt)
    (x D : ℂ) (hD : D ≠ 0) :
    utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
        mainD s (betaL S) 1 (fun z => (fun _ => (1 : ℂ)) z • btOf s (KB.dlB S b s) Vec h z) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s D), coJ S b s x j • Vec (ptJ s h x D j) := by
  rw [Finset.sum_insertNone, hbs, sub_eq_add_neg]
  have hz : ∀ z ∈ G.rootSet s D, z ≠ 0 := by
    intro z hz h0
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [h0, zero_pow (by omega)] at hz
    exact hD hz.symm
  congr 1
  · simp only [utOf, vOf, ptX, coJ, ptJ, smul_smul, List.append_assoc, List.singleton_append]
    push_cast
    rfl
  · unfold mainD
    rw [one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hzm => ?_
    simp only [btOf, if_neg (hz z hzm), one_smul, coJ, ptJ, smul_smul, neg_smul, one_mul]

end

end Formalism.FourierDecayAlt.P.GermRateSplit

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Formalism.FourierDecayAlt.P.GermRateSplit Finset
open scoped ComplexConjugate InnerProductSpace

theorem germ_rate_top_bound : Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB := by
  intro hA Cb
  obtain ⟨c1, hc1⟩ := GermFibreKernels.cutSeq_cpt Cb
  refine ⟨c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hF := hc1 c1 le_rfl E Wp Wq S p f χ A₀ hB n
  intro ε hε b s hb hs hbs a ha H _ _ _ Vec hVec
  refine ⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩
  intro h hsz K hK hK0
  have hbs' : b + s = S.G.r + 2 := hbs
  have hb1 : b + s - 1 = S.G.r + 1 := by omega
  obtain ⟨I, hI, c, Fi, L, hc, hFi, hgram⟩ :=
    gN_top_gram hB (PBASM.cutSeq S p f χ n) (fun v ε hε => hF v ε hε) v ε hε a ha
  choose Ci hCi using fun i => top_core hB v (Fi i) (hFi i) a.length b s hb hs hbs' h hsz K hK hK0
  refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  rw [germ_sum (PBL.setC S p (PBASM.cutSeq S p f χ n)) Vec b s hs hb1 h x D hD0]
  have hk : ∀ j ∈ Finset.insertNone (G.rootSet s D), ∀ l ∈ Finset.insertNone (G.rootSet s D),
      KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a (ptJ s h x D j) (ptJ s h x D l) =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length (ptJ s h x D l) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D l))),
          (omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))⟫_ℂ := by
    intro j _ l _
    rw [hb1]
    exact hgram _ _
  have h2 := norm_sum_le_of_gram (fun P Q => KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a P Q)
    Vec hVec c hc (fun i P => (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P)))
    (Finset.insertNone (G.rootSet s D)) (ptJ s h x D) hk (coJ S b s x)
  refine h2.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∑ j ∈ Finset.insertNone (G.rootSet s D), conj (coJ S b s x j) •
        ((omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))) =
      L i (∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) •
        (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul]
  rw [e]
  have h3 := hCi i x hx D hD
  have hsq := Real.sqrt_nonneg (c i)
  calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))‖
      ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
    _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
    _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring

end Formalism.FourierDecayAlt.P
end
