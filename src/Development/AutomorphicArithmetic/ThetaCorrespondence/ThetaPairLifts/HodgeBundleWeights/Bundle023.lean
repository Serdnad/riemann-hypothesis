module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAbsEntrySumNonneg
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle021
public import Development.WeilBound.CoreStatements.NefModelVolumes.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325

@[expose] public section

section

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
namespace GlobalTheory.FlatCore.Bdry
theorem nval_evI_eq_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp
end GlobalTheory.FlatCore.Bdry
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | exact _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | (intros; apply _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt <;> assumption)
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefWt
theorem weight_line_bundle_isNef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  intro hPr hNN hSA E _ _ _ H Dw l Xo c TF Z hF la hla
  letI := algebraΓOfHom (str₀ TF.X Z)
  classical
  obtain ⟨-, hproj, -⟩ := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hproj
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (C.isLB a) = φ a := fun _ => rfl
  have nef0 : ∀ a, φ a = 0 → IsNef c.F (L₀ TF.X Z a) := fun a h =>
    (isNef_triv c.F _).of_cls_eq (C.isLB a) (by rw [hφ, h]; rfl)
  by_cases hN : 0 < Dw.p + Dw.q
  swap
  · refine nef0 la ?_
    have : la = 0 := funext fun τ => funext fun i => absurd i.2 (by omega)
    rw [this, map_zero]
  have key : la = _ := decomp la hla hN
  let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
  let W : (Psi H × ℕ) ⊕ (Psi H × Bool) → AllWt.Weight Dw := Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
    (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1))
  have hP : ∀ x, IsNef c.F (L₀ TF.X Z (W x)) := by
    rintro (⟨τ, k⟩ | ⟨τ, b⟩)
    · show IsNef c.F (L₀ TF.X Z (piece Dw τ k))
      unfold piece
      split_ifs with h1 h2
      · exact _root_.GlobalTheory.T.hodgeBundle_headWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k h2
      · exact _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k (not_lt.1 h2) h1
      · exact nef0 0 (map_zero φ)
    · cases b
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).2
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).1
  refine IsNef.of_cls_eq_sum ((Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum Finset.univ) hP
    (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
      (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat)) hA (C.isLB la) ?_
  rw [hφ]
  conv_lhs => rw [key]

  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_nsmul]
  rcases x with ⟨τ, k⟩ | ⟨τ, b⟩ <;> rfl
end GlobalTheory.NefWt
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.base_weight_line_bundle_is_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  first | exact @_root_.GlobalTheory.NefWt.weight_line_bundle_isNef | exact _root_.GlobalTheory.NefWt.weight_line_bundle_isNef | (intros; apply _root_.GlobalTheory.NefWt.weight_line_bundle_isNef <;> assumption)
end
end

section

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
theorem height_add_log_nonneg (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hG : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0)) (hd : 0 < Y.dg u1 Z) :
    0 ≤ Y.ht u1 Z + Real.log abelian₂ := by
  haveI hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hd' : 0 < compDeg Y.U Z (wtOf (dat p i) u1 0) := by exact_mod_cast hd
  exact _root_.GlobalTheory.ImageHeightNonneg.imageHeight_nonneg_of_divisor hP _ _ _ _ _ _ _ _ w abelian₂ hG.1 (fun σ f => petOn_conj _ _ _ _ Z _ σ f) hG.2.2 hw hd'
theorem slope_le_height (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hGo : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
    (hBir : GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0))
    (hdel : (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1) (hρ : rhoB (dat p i) u1 < 1) (hd : 0 < Y.dg u1 Z)
    {cc B s cs : ℝ} (hM : Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc)
    (hcc : 0 ≤ cc) (hh : 0 ≤ htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) (hcs : Real.log abelian₂ ≤ cs)
    (hnn : 0 ≤ Y.ht u1 Z + cs)
    (hs : (s : EReal) ≤ compVolSlope Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) Z (uPrime (dat p i) u1)) :
    (1 - rhoB (dat p i) u1) * max 0 (s + cs) ≤ Y.ht u1 Z + cs + (cc + htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) := by
  have h1ρ : 0 < 1 - rhoB (dat p i) u1 := by linarith
  have hdelpos : 0 < topDeg Y.U Z (uPrime (dat p i) u1) :=
    lt_of_lt_of_le (mul_pos h1ρ hd) hdel
  have hf := two_lt_half_finrank D
  set hc := htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1) with hhc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA := (le_compVolSlope_iff Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) hdelpos s).1 hs cs
  have hB := GlobalTheory.CovHtCmp.compVol_le_volL_deep D p.T.toCore ((i : ℕ) + 1) Y e o hY hf hHT Z u1 (uPrime (dat p i) u1) cc B cs ε hM hε
  have hC := _root_.SelfIntersectionVolumeEstimates.VolUpG.volume_line_bundle_le hPX hP D p.T.toCore ((i : ℕ) + 1) Y e o hY hf Z u1 n w abelian₂ (cs + cc + hc + ε) hGo hBir hM.1 hd hw
    (by linarith)
  have hABC := hA.trans (hB.trans hC)
  have hpos : 0 ≤ Y.dg u1 Z * (Y.ht u1 Z + (cs + cc + hc + ε)) := mul_nonneg hd.le (by linarith)
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at hABC
  change delPrime Y.U Z u1 * (s + cs) ≤ _ at hABC
  have key : (1 - rhoB (dat p i) u1) * max 0 (s + cs) * Y.dg u1 Z ≤ (Y.ht u1 Z + cs + (cc + hc) + ε) * Y.dg u1 Z := by
    rcases le_total (s + cs) 0 with h | h
    · rw [max_eq_left h, mul_zero, zero_mul]
      exact mul_nonneg (by linarith) hd.le
    · rw [max_eq_right h]
      calc (1 - rhoB (dat p i) u1) * (s + cs) * Y.dg u1 Z = ((1 - rhoB (dat p i) u1) * Y.dg u1 Z) * (s + cs) := by ring
        _ ≤ delPrime Y.U Z u1 * (s + cs) := mul_le_mul_of_nonneg_right hdel h
        _ ≤ _ := hABC
        _ = _ := by ring
  exact le_of_mul_le_mul_right key hd
theorem heightAt_eq_of_cover (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {C0 Cs Cm Cb PP : ℝ} (h0 : 0 ≤ C0) (hs0 : 0 ≤ Cs) (hm0 : 0 ≤ Cm) (hb0 : 0 ≤ Cb) (hU : 0 ≤ unitE p)
    (hmean : MeanAll Y.U (xiR D) (ell D) C0) (hne : Nonempty (Comp Y.d.Xo₂ Y.d.c₂)) {u1 : AllWt.Weight (dat p i)}
    (hρ : rhoB (dat p i) u1 < 1) (hDeg : DegAt p i Y u1) (hS : ShortAt p i Y PP Cs u1) (hGe : GeomAt p i Y u1)
    (hM : MultAt p i Y PP Cm u1) (hB : BudgetAt p i Y PP Cb u1) :
    HeightAt p i Y PP (Cs + Cm + Cb + C0 * Cb) u1 := by
  obtain ⟨abelian₂, hLam, hSb⟩ := hS
  obtain ⟨cc, hcc, hccb, hMZ⟩ := hM
  obtain ⟨-, g, hgap, herr0, herrb, hht0, hhtb⟩ := hB
  obtain ⟨sl, hsl, hX⟩ := hmean (uPrime (dat p i) u1) g hgap
  obtain ⟨δ, hδ, hδZ⟩ := hDeg
  have hdg : ∀ Z, 0 < Y.dg u1 Z := fun Z => lt_of_lt_of_le hδ (hδZ Z).1
  have hLam1 : 1 ≤ abelian₂ := by
    obtain ⟨Z⟩ := hne
    obtain ⟨n, w, hw⟩ := hLam Z
    exact hw.one_le
  have hcs : 0 ≤ Real.log abelian₂ := Real.log_nonneg hLam1
  have hl1 : 0 ≤ l1 (uPrime (dat p i) u1) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hhc : 0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1) := mul_nonneg hht0 hl1
  have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
  have hnn : ∀ Z, 0 ≤ Y.ht u1 Z + Real.log abelian₂ := fun Z => by
    obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.height_add_log_nonneg hP hw (hGe Z).1 (hdg Z)
  have e1 : 0 ≤ Cs * unitE p := mul_nonneg hs0 hU
  have e2 : 0 ≤ Cm * unitE p := mul_nonneg hm0 hU
  have e3 : 0 ≤ Cb * unitE p := mul_nonneg hb0 hU
  have e4 : 0 ≤ C0 * Cb * unitE p := mul_nonneg (mul_nonneg h0 hb0) hU
  refine ⟨Real.log abelian₂, cc + htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1),
    C0 * errX (ell D) (uPrime (dat p i) u1) g, sl, hcs, add_nonneg hcc hhc, mul_nonneg h0 herr0, hnn, fun Z => ?_, hX,
    ?_, ?_, ?_⟩
  · obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.slope_le_height hPX hP hY hHT hw (hGe Z).1 (hGe Z).2.1 (hGe Z).2.2 hρ (hdg Z) (hMZ Z) hcc hhc le_rfl (hnn Z) (hsl Z)
  · have : (lenT p i PP : ℝ) * (C0 * errX (ell D) (uPrime (dat p i) u1) g) ≤ C0 * Cb * unitE p := by
      rw [mul_left_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left herrb h0
    linarith
  · rw [mul_add]
    linarith
  · linarith
end Point
end GlobalTheory.CovHt.HtTopG
end
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive
theorem logCanonical_refl_of_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m
  have hoff : ∀ z, z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off ↔ z ∈ U₀ TF.X Z := fun z => by
    rw [Modif.off_eq]; rfl
  haveI : IsReduced (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := isReduced_Y₀ TF.X Z
  have hdense : Dense ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off : Set (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) := by
    rw [Modif.off_eq]; exact (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).dense
  have hpole : SimplePoleAlong (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs) ω₀.ω := by
    intro y hy
    have hy' : y ∉ U₀ TF.X Z := fun h => hy ((hoff y).2 h)
    obtain ⟨V, hyV, t, h1, h2⟩ := _root_.GlobalTheory.T.boundary_divisor_has_reduced_equation hP E H Dw l Xo c TF Z hF hV y hy'
    obtain ⟨V', hyV', hle, i, j, u, hi, hj, hu, hpl⟩ :=
      _root_.GlobalTheory.T.exists_simple_log_pole_along_boundary hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ y hy' V hyV t h1 h2
    refine ⟨V', hyV', (i, j), fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      fun z hz => (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz),
      fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      resG _ hle t, u, fun z hz => ?_, hu, fun W hW f hf z hz => ?_, fun z hz ho => ?_⟩
    · erw [ger_resG, hoff]; exact h1 z (hle hz)
    · erw [ger_resG]
      exact h2 W (hW.trans hle) f (fun z hz hz' => hf z hz fun h => hz' ((hoff z).1 h)) z hz
    · erw [ger_resG]; exact hpl z hz ho _
  refine ⟨fun ⟨g, hg, e⟩ => ?_, fun ⟨G, hG⟩ => ?_⟩
  · obtain ⟨G, hG'⟩ := GlobalTheory.T.exists_extend_mul_simplePole_of_vanishing hdense _ ω₀.ω hpole (H0.pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top g) (fun y hy i hi => by
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top i y (memTop y) hi g
      rw [e]
      have h := hg y (fun h => hy ((hoff y).2 h)) (i PUnit.unit) (mem_pull.1 hi)
      exact map_nonunit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ.stalkMap y).hom _ h)
    refine ⟨G, hG'.trans ?_⟩
    subst e
    congr 1
    exact (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).trans (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).symm
  · obtain ⟨g', hv, hr⟩ := GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends hdense _ ω₀.ω hpole G ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) hG
    haveI : IsOpenImmersion (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ := inferInstanceAs (IsOpenImmersion (𝟙 _))
    obtain ⟨g, rfl⟩ := ((isoOver_of_isOpenImmersion (O := ⊤) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ (fun x _ => ⟨x, rfl⟩)).bijective_pull
      (p := str₀ TF.X Z) (isLB_L₀ TF.X Z s) (W := ⊤) le_top le_top).2 g'
    refine ⟨g, fun y hy i hi => ?_, ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).bijective_pullOff (isLB_L₀ TF.X Z s)).1 ?_⟩
    · have h := hv y (fun h => hy ((hoff y).1 h)) (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) (mem_pIdx.2 hi)
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) y (memTop y) (mem_pIdx.2 hi) g
      erw [e] at h
      intro hu
      exact h (hu.map _)
    · rw [← hr]
      exact (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).trans (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).symm
end GlobalTheory.LogCanonicalReflexive
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.logCanonical_divisor_refl : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  first | exact @_root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary | exact _root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary | (intros; apply _root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary <;> assumption)
end
end
