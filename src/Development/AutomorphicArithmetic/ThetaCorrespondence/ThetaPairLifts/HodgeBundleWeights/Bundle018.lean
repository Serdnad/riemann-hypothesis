module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle013
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

section

section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw
namespace GlobalTheory.FlatSplit
section Congr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}
end Congr
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)
end Weights
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem flat_at_of_split_covering (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems)
    (hDG : DeepGoodAt p i Y)
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧
      FlatExists Y.U (xiR D) ∧
      (∀ τ, |c1 Y.U (xiR D) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord D L p.Del p.h0).logOm| ≤
        3 * (dat p i).q * L.sc.L) ∧
      logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * L.sc.L)
    {CA PP PP' A : ℝ} (hA : AnchorAt p i CA) (hW : WtNum p i PP) (hH : HostNum D L PP' A 0) :
    FlatAt p i Y (11 * CA + 83) := by
  obtain ⟨hcx, hgood, hflat, hc1, hlog⟩ := hc
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have hUn := _root_.GlobalTheory.T.unramified_points_of_deep_cover hP D p.T ((i : ℕ) + 1) Y _ _ p.fw.laws hj hY.1
  have hrank : 1 ≤ (dat p i).p + (dat p i).q := Inhab.rank_pos p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) hj
  have hev : Even (p.κ i).n := hW.dom.2
  have hFL := ((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D p.T.Q.H (dat p i) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (fun _ => D.sp.W ((i : ℕ) + 1))
    Y.dict hcx hY.1.geo hrank hgood hflat hUn (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1))
    ((p.κ i).n / 2)).2 (uM p i) 0).2 hDG.2.2.2.1
  obtain ⟨-, hrk, hdeg⟩ := hFL
  have hex : exZ (dat p i) (Gs p i (-(cZero D ((i : ℕ) + 1)))) = exZ (dat p i)
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := by
    have := exZ_shift_neg (dat p i) (wtA (p.κ i)) ((p.κ i).n / 2) (D.R.k - 1) (cZero D ((i : ℕ) + 1))
    rwa [Nat.two_mul_div_two_of_even hev] at this
  have hcg := congr_exZ Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict hY.1.unf hex
  have hR0 := hDG.2.2.2.2.1
  unfold FlatAt
  have e1 : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) = slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := hcg.2.2
  have e2 : Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1)))) = rankW Y.U (wtOf (dat p i) (uM p i) 0) := hcg.2.1.trans hrk
  have hR : (0 : ℝ) < (rankW Y.U (wtOf (dat p i) (uM p i) 0) : ℝ) := by rw [← e2]; exact_mod_cast hR0
  rw [degW_eq, degW_eq, hrk] at hdeg
  rw [e1]
  have hb1 : 1 ≤ L.sc.b := by have := hH.room; rwa [Real.rpow_zero] at this
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL := hH.big.2.1
  have hll := hH.big.2.2.2
  have k1 : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
  have k2 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L := by nlinarith
  have k3 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by nlinarith
  have k4 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.b * Real.log (Real.log L.sc.x) := by nlinarith
  have hbE : L.sc.b ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k3 (by linarith : (0 : ℝ) ≤ L.sc.b)]
  have hLE : L.sc.L ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k4 (by linarith : (0 : ℝ) ≤ L.sc.L)]
  have hfr : (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) = (D.R.f : ℝ) * D.R.r := by
    rw [hH.deg, hW.sig.2.2, Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring
  have hm : 2 * ((((p.κ i).n / 2 : ℕ) : ℝ)) ≤ (D.R.nV : ℝ) := by
    have := Nat.mul_div_le (p.κ i).n 2
    rw [hW.cols] at this
    rw [hW.cols]; exact_mod_cast (by omega : 2 * (D.R.nV / 2) ≤ D.R.nV)
  have num := twice_twist_ge (fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)) (c1 Y.U (xiR D))
    (((dat p i).p : ℝ) - (dat p i).q) ((dat p i).q : ℝ) (ofRecord D L p.Del p.h0).logOm L.sc.L L.sc.b (unitE p) (mainT p i) CA
    (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E) ((((p.κ i).n / 2 : ℕ) : ℝ))
    (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) (D.R.nV : ℝ)
    (logSum (badPrimes p.T.Q.H Y.d.l₂)) hc1 hA.1 hA.2.1 (Nat.cast_nonneg _) (lrd_le hH) hL hm (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by rw [hfr]; exact hA.2.2) hbE hLE hlog
  rw [← mul_add] at hdeg
  have key := le_of_mul_le_mul_left hdeg hR
  show slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict (wtOf (dat p i) (uM p i) 0) - mainT p i -
    (11 * CA + 83) * unitE p ≤ _
  linarith
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
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

namespace GlobalTheory.KeyInvInt
open GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FlatLine

theorem exists_inverse_integral_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  intro _hP D T j Y e o hY _hE
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨K, hK, hKv⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ _ _ _ _ _ _ g ee hpq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ _ _ _ _ _ _ g ee _ _ (Y.U _) K hσ
    (hY.unf _ hσ) hY.geo hpq hK hKv
  choose a ha hZ using hρ
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hKint : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 Y.d.c₂.F)),
      ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) w, 0 ≤ v (K : Rul Y.d.Xo₂ Y.d.c₂) := by
    by_cases hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p
    · exact fun w v hv => (GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr _ _ _ _ _ _ g ee K hpq hg hK hKv w v hv).1
    · exact GlobalTheory.T.thetaKeyRule_valuation_nonneg_integral_framed_point κ hkr _ _ _ _ _ _ g ee K hpq hK hKv
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.exists_constant_smul_integral_of_fourth_power _ _ _ _ _ _ (K : Rul Y.d.Xo₂ Y.d.c₂) (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂) a ha hZ hKint
  have hwt : ∀ (m : ℤ) (τ : D.host.E →+* ℂ) (i : ℕ), i < (T.Q.Dw j).mult τ → (wtOf (T.Q.Dw j) 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst _ _ (T.Q.Dw j)
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1 = -keyEx (T.Q.Dw j) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [GlobalTheory.AllWt.exOf, exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  refine ⟨((ρ.ρ⁻¹ : (Rul Y.d.Xo₂ Y.d.c₂)ˣ) : Rul Y.d.Xo₂ Y.d.c₂), t • (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂), t, ?_, ht, ?_, hint⟩
  · rw [hex]
    exact GlobalTheory.AllWt.inv_mem_secZ ρ.mem
  · rw [mul_smul_comm, Units.inv_mul]
end GlobalTheory.KeyInvInt
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


theorem _root_.GlobalTheory.T.inverse_invariant_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @_root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | exact _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | (intros; apply _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant <;> assumption)
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogPole
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_log_pole_along_boundary (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z)
    (V : (Y₀ TF.X Z).Opens) (hy : y ∈ V) :
    ∃ (W : (Y₀ TF.X Z).Opens) (_ : y ∈ W) (_ : W ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι)
      (k : TF.X.F.J) (δ u : Γ(Y₀ TF.X Z, W)),
      W ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧ IsUnit u ∧
      (∀ z (hz : z ∈ W), IsUnit (ger z hz δ) ↔ z ∈ U₀ TF.X Z) ∧
      (∀ (W' : (Y₀ TF.X Z).Opens) (hW' : W' ≤ W) (f : Γ(Y₀ TF.X Z, W')), (∀ z (hz : z ∈ W'), z ∉ U₀ TF.X Z →
        ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) →
        ∀ z (hz : z ∈ W'), ger z (hW' hz) δ ∣ ger z hz f) ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) ho hi,
        ev z W hz δ * H0.val (B := LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle
          ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) z
          (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k) ho hi ω₀.ω = ev z W hz u := by
  obtain ⟨i, hi⟩ := exists_chart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB y
  obtain ⟨U, n, e₀, v, hyU, hv₀⟩ := GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point E H Dw l Xo c TF Z hF y
  obtain ⟨e, W, k, L, N, hv, hyW, hWV, hc⟩ := GlobalTheory.T.exists_bigCell_chartFrame_eigenbasis E H Dw l Xo c TF Z U n e₀ v hv₀ y hyU V hy
  obtain ⟨ε, b, hb⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v _ hv.1 hv.2.1 hv.2.2
  obtain ⟨x, U', hU', hyU', hx, hbd⟩ := GlobalTheory.T.exists_coordinates_logVectorFields_determinant E H Dw l Xo c TF U b _ hyU
  have het := GlobalTheory.T.etale_bigCellCoordinates_flagSpace E H Dw l Xo c TF Z hF U n e v hv W k L N hc
  obtain ⟨s, hs, hcmp⟩ := _root_.GlobalTheory.T.kodaira_spencer_comparison_along_boundary hP E H Dw l Xo c TF
  let o : Fin Dw.dim ≃ HIx Dw (psiSet H) :=
    (Fintype.equivFinOfCardEq (FlagTan.card_HIx (FlagTan.isHalf_psiSet H))).symm
  obtain ⟨a, ha, hhor⟩ := GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal E H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨W', hW'a, hyW', hW'⟩ := Opens.isBasis_iff_nbhd.1 (Y₀ TF.X Z).isBasis_affineOpens
    (show y ∈ W ⊓ (toBase TF Z ⁻¹ᵁ U'.1 ⊓ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i) from ⟨hyW, hyU', hi⟩)
  have hW'W : W' ≤ W := hW'.trans inf_le_left
  have hW'U : W' ≤ toBase TF Z ⁻¹ᵁ U'.1 := hW'.trans (inf_le_right.trans inf_le_left)
  have hW'i : W' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i := hW'.trans (inf_le_right.trans inf_le_right)
  let O := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let G : Fin Dw.dim ⊕ VIx Dw → Γ(Y₀ TF.X Z, W) :=
    Sum.elim (fun i => ((toBase TF Z).appLE U.1 W hc.2.1).hom (x i)) (cellCoord N)
  let g : Fin (FlagTan.dimFlag Dw) → Γ(Y₀ TF.X Z, W') := fun a => resG _ hW'W (G (O a))
  have hfr := GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale c.F TF.Y.X (Y₀ TF.X Z) TF.Y.s (toBase TF Z) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) Dw.dim (FlagTan.dimFlag Dw) TF.smooth (VIx Dw) O U.1 U'.1 hU'
    U.2 W W' hW'W hc.1 hW'a hc.2.1 hW'U (cellCoord N) het x hx
  have hJ : IsUnit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g) :=
    ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isUnit_jacobian_iff i hW'a hW'i g).2 hfr
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : IsLocallyNoetherian TF.Y.X := LocallyOfFiniteType.isLocallyNoetherian TF.Y.s
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing TF.Y.X (Y₀ TF.X Z) (toBase TF Z) (VIx Dw) (LogKS.interior TF.Y) U U' hU' W hc.1 hc.2.1
    (cellCoord N) het _ hbd
  let ac : Γ(Y₀ TF.X Z, W') := algX (str₀ TF.X Z) W' (a : c.F)
  have hac : IsUnit ac := (Ne.isUnit (Rat.cast_ne_zero.2 ha)).map _
  refine ⟨W', hyW', hW'W.trans hWV, i, k,
    resG _ hW'W (((toBase TF Z).appLE U.1 W hc.2.1).hom (logDet (fun j => (b j).1) x)),
    ac * resG _ hW'W (diagUnit L hc.2.2.2.2.1).val * (show Γ(Y₀ TF.X Z, W') from
      (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g), hW'i, hW'W.trans hc.2.2.1,
    (hac.mul ((Units.isUnit _).map _)).mul hJ, fun z hz => ?_, fun W'' hW'' f hf z hz => ?_, fun K _ z hz ho hi => ?_⟩
  · rw [ger_resG]
    exact r₁ z (hW'W hz) (hW'U hz)
  · rw [ger_resG]
    exact r₂ W'' (hW''.trans hW'W) (hW''.trans hW'U) f hf z hz
  have eM : toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = inc₀ TF.X Z := Category.id_comp _
  have hzW := FlagMod.le_preimage_mono hW'W hz
  have hU₀ : ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z := fun p hp => by
    have := ho hp
    rw [Modif.off_eq] at this
    exact this
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_map _ hc.2.2.1 hzW
  obtain ⟨_, hch⟩ := exists_chartFr (z ≫ inc₀ TF.X Z) hU₀
  obtain ⟨Q, hQ⟩ := hch k hk
  obtain ⟨P₀, P, t, hU, hQP, ht, hP₀, hB⟩ := GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW hk Q hQ
  have ez : z ≫ inc₀ TF.X Z = TF.X.ptY P := FlagMod.FlagCover.eq_ptY (hQ.lies.frBor hQP)
  obtain ⟨w, hw⟩ := (hKS K P).exists_isTanFrame
  have ezM : z ≫ toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = z ≫ inc₀ TF.X Z := by rw [eM]
  choose zw hzw hzO using fun b => exists_tanLift (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) (hw.isDef b)
    (ezM.trans ez) ho
  have hzw' : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ inc₀ TF.X Z = TF.X.ptY (w b) := fun b => by
    exact (congrArg (zw b ≫ ·) eM).symm.trans (hzw b)
  have hkM := ezM ▸ hk
  have key := ω₀.isKS K P Q t w z zw i k W' hW'i g hz (fun b => hzO b W' hz) hkM ho hi (chartFr_congr ezM.symm hkM hQ)
    hQP hw hzw
  obtain ⟨v₁, v₂⟩ := GlobalTheory.T.vertical_tangentFrame_jacobian_det_one E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW P₀ P hU ez hP₀ hB (fun b => w (.inr b))
    (fun b => zw (.inr b)) (fun b => hzO _ W hzW) hw.2 (fun b => hzw' _)
  have eb : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ toBase TF Z = frX (w b) ≫ TF.Y.j := fun b => by
    rw [← Category.assoc, hzw', (TF.X.lies_ptY _).1]
  have hwU : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1 := fun b =>
    eb b ▸ FlagMod.le_preimage_map _ hc.2.1 (hzO b W hzW)
  have hdet : ∀ σ, ((N σ).map (ev z W hzW)).det = 1 := fun σ => by
    rw [Matrix.det_of_upperTriangular fun i j hij => by rw [Matrix.map_apply, hc.2.2.2.2.2.1 σ i j hij, map_zero]]
    simp [hc.2.2.2.2.2.2.1]
  have hh := hhor x K P₀ P hU _ hdet hP₀ hB (fun b => w (.inl b)) (fun b => hwU _) hw.1
  have eP : z ≫ toBase TF Z = frX P₀ ≫ TF.Y.j := by
    rw [← Category.assoc, ez, (TF.X.lies_ptY _).1,
      FlagMod.eq_frX P₀ ((FlagMod.frX_fst P).trans hP₀.1) (FlagMod.frX_snd P)]
  have hblock := det_block o (fun a b => (ev (zw b) W (hzO b W hzW) (G a)).snd) (fun i b => v₂ b _) v₁
  have e₁ : (Matrix.of fun a b => (TangentOrigin.evalPt (zw (tanOrd Dw b)) W' (hzO _ W' hz) (g a)).snd) =
      Matrix.of fun a b => (ev (zw (tanOrd Dw b)) W (hzO _ W hzW) (G (O a))).snd := by
    ext a b
    exact congrArg TrivSqZeroExt.snd (FlagMod.ev_res _ hW'W _ _ _)
  have e₂ : (Matrix.of fun i j => (ev (zw (.inl (o j))) W (hzO _ W hzW) (G (.inl i))).snd) =
      Matrix.of fun i j => (ev (frX (w (.inl (o j))) ≫ TF.Y.j) U.1 (hwU _) (x i)).snd := by
    ext i j
    exact congrArg TrivSqZeroExt.snd ((FlagMod.ev_appLE _ _ hc.2.1 _ (eb _ ▸ hwU _) _).trans
      (congrArg (· (x i)) (FlagMod.ev_congr (eb _) _ _ _)))
  rw [e₁, hblock, e₂, map_diagUnit (ev z W hzW) L hc.2.2.2.2.1 t ht] at key
  have hca : ev z W' hz ac = (a : K) := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
    exact map_ratCast ((ev z W' hz).comp (algX (str₀ TF.X Z) W')) a
  rw [FlagMod.ev_res _ hW'W hz hzW, FlagMod.ev_appLE _ _ hc.2.1 _ (eP ▸ hU), FlagMod.ev_congr eP _ _ hU, hh,
    map_mul, map_mul, hca, FlagMod.ev_res _ hW'W hz hzW, mul_assoc, mul_assoc]
  exact congrArg _ ((mul_comm _ _).trans key)
section Main
open ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem log_pole_along_boundary_is_simple : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ y _ V hy t ht₁ ht₂
  obtain ⟨W, hyW, hWV, i, k, δ, u, hi, hk, hu, h₁, h₂, h₃⟩ := _root_.GlobalTheory.LogPole.exists_log_pole_along_boundary hP TF Z hF hKS hV ω₀ y V hy
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) :=
    haveI := (TF.X.normal (inc₀ TF.X Z y)).1
    MulEquiv.isDomain _ (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  obtain ⟨V', hyV', hV', b, hb, e⟩ := exists_unit_mul y hyW (resG _ hWV t) δ
    (by rw [ger_resG]; exact ger_ne_zero (dense_U₀ TF.X Z) t (fun z hz h => (ht₁ z hz).2 h) y _)
    (by rw [ger_resG]; exact ht₂ W hWV δ (fun z hz h hu => h ((h₁ z hz).1 hu)) y hyW)
    (h₂ W le_rfl _ (fun z hz h hu => h ((ht₁ z (hWV hz)).1 (by rwa [ger_resG] at hu))) y hyW)
  refine ⟨V', hyV', hV'.trans hWV, i, k, b * resG _ hV' u, hV'.trans hi, hV'.trans hk, fun z hz => ?_,
    fun z hz ho hc => ?_⟩
  · rw [map_mul]
    exact (hb z hz).mul ((hu.map _).map _)
  let O : (Y₀ TF.X Z).Opens := ksOpen (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) i k
  let ω : Γ(Y₀ TF.X Z, O) := ω₀.ω.loc (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k)
  have e₁ : resG _ (inf_le_left : W ⊓ O ≤ W) δ * resG _ inf_le_right ω = resG _ inf_le_left u := by
    refine FlagMod.ext_ev_field fun K _ p hp => ?_
    have a₁ := FlagMod.le_preimage_mono inf_le_left hp
    have a₂ := FlagMod.le_preimage_mono inf_le_right hp
    rw [map_mul, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₂]
    exact h₃ K p a₁ (FlagMod.le_preimage_mono inf_le_left a₂) (FlagMod.le_preimage_mono inf_le_right a₂)
  have hzO : z ∈ O := ⟨ho, hc⟩
  have hm : z ∈ W ⊓ O := ⟨hV' hz, hzO⟩
  have e₂ := congrArg (ger z hm) e₁
  have e₃ := congrArg (ger z hz) e
  simp only [map_mul, ger_resG] at e₂ e₃
  change ger (Y := Y₀ TF.X Z) z _ t * ger (Y := Y₀ TF.X Z) z hzO ω = ger (Y := Y₀ TF.X Z) z hz _
  rw [map_mul, ger_resG, e₃, mul_assoc, e₂]
end Main
end GlobalTheory.LogPole
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

theorem _root_.GlobalTheory.T.exists_simple_log_pole_along_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  first | exact @_root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple | exact _root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple | (intros; apply _root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple <;> assumption)
end
end
