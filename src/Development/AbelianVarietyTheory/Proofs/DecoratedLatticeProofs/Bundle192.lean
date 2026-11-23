module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle170
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB


theorem _root_.GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ k : GA D S, mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ) → ∃ h : GA D A, k = o.emb (h, 1) := by
  first | exact @GlobalTheory.exists_emb_of_fixes_lineVec | exact GlobalTheory.exists_emb_of_fixes_lineVec | (intros; apply GlobalTheory.exists_emb_of_fixes_lineVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_flagUnipotent_coordinate_measurableEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d, ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  first | exact @GlobalTheory.Unf.flagCoord_measEquiv | exact GlobalTheory.Unf.flagCoord_measEquiv | (intros; apply GlobalTheory.Unf.flagCoord_measEquiv <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_toCompl_tmul_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (b : Fv D.host.F v) (o m : D.host.E) :
    secW hw h (toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m) =
      pairA D.host.F 0 (singleFin v b) ⊗ₜ[D.host.F] (o * m) := by
  have e : toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m =
      toCompl h (b ⊗ₜ[D.host.F] (o * m)) := by
    rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
  have e2 : toCompl h (b ⊗ₜ[D.host.F] (o * m)) = GlobalTheory.LFun.InertChart.complEquiv hw h (b ⊗ₜ[D.host.F] (o * m)) := rfl
  rw [e, e2]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) = _
  rw [RingEquiv.symm_apply_apply, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]

theorem secW_rank_one_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ frameLat S)
    {t : Fin T.rank → D.host.E} (ht : t ∈ frameLat T) {z : w.adicCompletion D.host.E} (hz : z ∈ Ov D.host.E w) :
    (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E)
      (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  obtain ⟨y, rfl⟩ := GlobalTheory.LFun.InertChart.toCompl_surjective h z
  have hy := (GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h y).2 hz
  refine intLoc_induction (p := fun y => (Matrix.of fun i j => secW hw h (toCompl h y *
      algebraMap D.host.E (w.adicCompletion D.host.E) (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v)) (fun b hb o => ?_) ?_ (fun y y' h1 h2 => ?_)
      (fun y h1 => ?_) hy
  · refine AddSubgroup.subset_closure ⟨singleFin v b, fun u => ?_, fun u hu => evalV_singleFin_ne hu _, a, ha, s, hs,
      o • t, Submodule.smul_mem _ o ht, ?_⟩
    · by_cases e : u = v
      · subst e; rw [evalV_singleFin_self]; exact hb
      · rw [evalV_singleFin_ne e]; exact zero_mem _
    · ext i j
      rw [Matrix.of_apply, Matrix.of_apply, secW_toCompl_tmul_mul]
      congr 1
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  · convert add_mem h1 h2 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, map_add (f := _), add_mul]
  · convert neg_mem h1 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, map_neg, neg_mul]

theorem secW_span_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : IsConjAt D.sp.cm.sig h c) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {p : Fin T.rank → w.adicCompletion D.host.E} (hp : p ∈ latAt w (frameLat T))
    {y : Fin S.rank → w.adicCompletion D.host.E} (hy : y ∈ latAt w (frameLat S)) :
    ∀ z ∈ Ov D.host.E w, (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E) a * p i *
      ∑ k, c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  have hst : ∀ x : D.host.E, star x = D.sp.cm.sig x := fun _ => rfl
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t, ht, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      intro z hz
      convert secW_rank_one_mem hw h ha hs ht hz using 1
      ext i j

      simp only [Matrix.of_apply, GlobalTheory.LFun.InertChart.conj_algebraMap hc, map_mul, map_sum, hst]
      ring_nf
    | zero =>
      intro z hz
      convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
      ext i j
      simp
    | add y y' _ _ h1 h2 =>
      intro z hz
      convert add_mem (h1 z hz) (h2 z hz) using 1
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
    | smul o y _ h1 =>
      intro z hz
      convert h1 (z * c o) (mul_mem hz (GlobalTheory.LFun.InertChart.conj_mem hw hc o.2)) using 1
      ext i j
      have e : ∀ k, c ((o • y) k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j) =
          c o * (c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) := fun k => by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, mul_assoc]
      simp only [Matrix.of_apply, e, ← Finset.mul_sum]
      congr 1
      ring
  | zero =>
    intro z hz
    convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  | add p p' _ _ h1 h2 =>
    intro z hz
    convert add_mem (h1 z hz) (h2 z hz) using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, mul_add]
  | smul o p _ h1 =>
    intro z hz
    convert h1 (z * o) (mul_mem hz o.2) using 1
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    congr 1
    ring

theorem uPt_mem_latO : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  intro D v w hw h S T k aS aT hk haS haT x hx
  obtain ⟨-, ⟨a₀, ha₀, rfl⟩, -⟩ := hk
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt D.sp.cm.sig hw h
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt_host D) hw hc
  have hcc : ∀ z, c (c z) = z := hU.1
  set ι := algebraMap D.host.E (w.adicCompletion D.host.E) with hι
  set Gw := S.gram.map ι with hGw
  set Gi := (S.gram⁻¹).map ι with hGi
  have hGG : Gi * Gw = 1 := by
    rw [hGi, hGw, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  set N := (aS⁻¹).1 * Gi with hN
  have hG : ∀ l i, c (ι (S.gram l i)) = ι (S.gram i l) := fun l i => by
    rw [GlobalTheory.LFun.InertChart.conj_algebraMap hc, (GlobalTheory.Doubling.isHermND_gram S).1 i l]
  have hY : ∀ j, (fun l => c (N j l)) ∈ latAt w (frameLat S) := by
    intro j
    rw [GlobalTheory.LFun.InertChart.mem_latAt_iff hw hc (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)]
    intro y hy
    have hu := (haS ((aS⁻¹).1 *ᵥ y)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) j
    have e : Formalism.UG.hform c (S.gram.map ι) y (fun l => c (N j l)) = c ((N *ᵥ (Gw *ᵥ y)) j) := by

      simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hG, hGw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, hGG, Matrix.mul_one]
    exact GlobalTheory.LFun.InertChart.conj_mem hw hc hu
  have hcol : ∀ j l, ∑ m, c (c (N j m)) * ι (S.gram m l) = (aS⁻¹).1 j l := fun j l => by
    simp only [hcc]
    have := congrFun (congrFun (show N * Gw = (aS⁻¹).1 by rw [hN, Matrix.mul_assoc, hGG, Matrix.mul_one]) j) l
    rw [← this, Matrix.mul_apply]
    rfl
  have hT : ∀ i, (fun r => aT.1 r i) ∈ latAt w (frameLat T) := fun i => by
    have := (haT (Pi.single i 1)).1 fun m => by
      by_cases e : m = i
      · subst e; simp
      · simp [e]
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdec : uPt hw h (ι a₀) aS aT x = ∑ i, ∑ j, (Matrix.of fun r l => secW hw h (x i j * ι a₀ * aT.1 r i *
      ∑ m, c (c (N j m)) * ι (S.gram m l)) : WO S T) := by
    ext r l
    simp only [uPt, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply, hcol]

    rw [show ∀ f : Fin T.rank → Fin S.rank → w.adicCompletion D.host.E, ∑ i, ∑ j, secW hw h (f i j) =
      secW hw h (∑ i, ∑ j, f i j) from fun f => by simp only [map_sum]]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdec]
  exact sum_mem fun i _ => sum_mem fun j _ => secW_span_mem hw h hc ha₀ (hT i) (hY j) (x i j) (hx i j)

end GlobalTheory.InertFrameLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX * b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' * (gA S * c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  let c : Mx D S.rank ρ := d.jX * b
  change adj c' * (gA S * c) = ε • (1 : Mx D ρ ρ) at hcc
  have hcc0 : adj c * (gA S * c) = 0 := by
    dsimp only [c]
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b,
      ← Matrix.mul_assoc (adj d.jX), d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  have hcc' : adj c * (gA S * c') = ε • (1 : Mx D ρ ρ) := by
    have h := congrArg adj hcc
    rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at h
  let H : Mx D ρ ρ := adj c' * (gA S * c')
  have hHint (i j : Fin ρ) : H i j ∈ intAt D (· = v) := by
    have hgram : H i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
      simp only [H, hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, mul_assoc]
    rw [hgram]
    exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by
    dsimp only [H]
    rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]
  let K : Mx D ρ ρ := w • H
  have hKint (m i : Fin ρ) : K m i ∈ intAt D (· = v) := by
    change (w • H) m i ∈ intAt D (· = v)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.IwaPlace.DualIso.intAt_mul_mem hw (hHint m i)
  let c'' : Mx D S.rank ρ := c' - c * K
  have hpair : adj c'' * (gA S * c) = ε • (1 : Mx D ρ ρ) := by
    dsimp only [c'']
    rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero,
      sub_zero, hcc]
  refine ⟨c'', ?_, hpair, ?_⟩
  · intro i
    have hcol : (fun k => (c * K) k i) = ∑ m, K m i • (fun k => c k m) := by
      funext k
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    change (fun k => c' k i) - (fun k => (c * K) k i) ∈ M
    rw [hcol]
    exact sub_mem (hc' i) (AddSubgroup.sum_mem _ fun m _ =>
      GlobalTheory.IwaPlace.DualIso.smul_mem_of_isSDAt hM (hKint m i) (hc m))
  · have hleft : adj c'' * (gA S * c') = H - (ε * cA D w) • H := by
      dsimp only [c'']
      rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']
      change H - adj (w • H) * (ε • (1 : Mx D ρ ρ)) = _
      rw [adj_smul, hadjH, mul_smul_comm, mul_one, smul_smul]
    have hsum : ε * cA D w + ε * w = ε := by
      rw [← mul_add, add_comm, hwc, hεε]
    calc
      adj c'' * (gA S * c'') =
          adj c'' * (gA S * c') - (adj c'' * (gA S * c)) * K := by
        change adj c'' * (gA S * (c' - c * K)) = _
        rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
          ← Matrix.mul_assoc (adj c'') (gA S * c) K]
      _ = H - (ε * cA D w) • H - (ε * w) • H := by
        rw [hleft, hpair]
        change H - (ε * cA D w) • H - (ε • (1 : Mx D ρ ρ)) * (w • H) = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      _ = 0 := by rw [sub_sub, ← add_smul, hsum, hεH, sub_self]
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField GlobalTheory.FinPl.FrameLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.IwaPlace.LocSD

variable {D : D7}

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) → ε * a = a := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_,
    ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩,
    fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩
  change pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _
  rw [map_one]

variable {S : HSp D}

theorem hermAt_mul_inc (y : Fin S.rank → AE D) (a : AE D) (s : Fin S.rank → D.host.E) :
    hermAt S y (fun i => a * incA D (s i)) = cA D a * pairing S s y := by
  unfold hermAt pairing FrameLat.row
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]
  ring

theorem hermAt_sum_right {m : ℕ} (y : Fin S.rank → AE D) (x : Fin m → Fin S.rank → AE D) :
    hermAt S y (fun i => ∑ l, x l i) = ∑ l, hermAt S y (x l) := by
  unfold hermAt

  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hermAt_mem_idAt {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D P)
    (x : Fin S.rank → AE D) : hermAt S y x ∈ idAt D P :=
  Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

variable {L : Lat S}

theorem exists_mul_mem (hL : IsSelfDualC S L) (v : Pl D) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ latV S L (· = v) := by
  have hfull : Submodule.IsFullLattice D.host.E L := by
    haveI : Submodule.IsLattice D.host.E L := hL.1
    refine ⟨?_⟩
    obtain ⟨m, s, s', hs, _, hd⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
    apply eq_top_iff.mpr
    intro y _
    have hy : y = ∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) • s l := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have heq : (∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) * s l a) =
          ∑ b, ∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
      rw [heq]
      have hterm : ∀ b, (∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a) =
          (if a = b then 1 else 0) * y b := by
        intro b
        calc
          _ = ∑ l, (s l a * ∑ k, star (s' l k) * S.gram k b) * y b := by
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
          _ = _ := by rw [← Finset.sum_mul, hd]
      simp_rw [hterm]
      simp
    rw [hy]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs l))
  obtain ⟨N, hN, -, h⟩ := GlobalTheory.LatAlmostStd.exists_commensurable L hfull
  refine ⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩
  have h1 : (N : AE D) • y ∈ latV S L (· = v) := by
    have e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) :
        Fin S.rank → D.host.E) k) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one,
          zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      · intro i _ hi
        rw [Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e]
    exact sum_mem fun i _ => int_mul_mem (hy i) (h i 1)
  rcases Int.natAbs_eq N with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have e' : ((N.natAbs : ℕ) : ℤ) = -N := by omega
    rw [← Int.cast_natCast, e', Int.cast_neg, neg_smul]; exact neg_mem h1

theorem isSDAt_latV : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  intro D S L v hL
  refine ⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩
  · refine ⟨hermAt_mem_idAt hy x, ?_⟩
    obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
    have e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i := funext fun i => hd x i

    rw [e, hermAt_sum_right, map_sum]
    refine sum_mem fun l _ => ?_
    rw [hermAt_mul_inc, RingHom.map_mul]
    exact mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)
  · obtain ⟨ε, hc, hε, hact⟩ := exists_idem v
    refine mem_of_pairing hL hy fun s hs => ?_
    have h1 := (h _ (int_mul_mem hε hs)).2
    rwa [hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))] at h1

end GlobalTheory.IwaPlace.LocSD

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realRepresentation_moves_rieszVector_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  first | exact @GlobalTheory.Core.Mi.piU_rieszJ | exact GlobalTheory.Core.Mi.piU_rieszJ | (intros; apply GlobalTheory.Core.Mi.piU_rieszJ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.secondModel_finitePart_frameActionMatrix : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), _root_.GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  first | exact @GlobalTheory.Core.Mi.FinFrame.repM_toH | exact GlobalTheory.Core.Mi.FinFrame.repM_toH | (intros; apply GlobalTheory.Core.Mi.FinFrame.repM_toH <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  first | exact @GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | exact GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | (intros; apply GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt <;> assumption)
end
