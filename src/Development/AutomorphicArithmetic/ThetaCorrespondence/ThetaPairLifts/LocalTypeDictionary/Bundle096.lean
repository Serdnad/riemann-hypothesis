module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle669
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle094
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle095
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage1
theorem stage1_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PGUnit F ∧ R.PGEquiv F ∧ (R.toCx3 F).zs.InBlock ∧ R.PThmA ∧ R.PThmB := by
  intro P D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  obtain ⟨_hGiven, _hGS, _hCD, hLI, hTR, _hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  have hOk := GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed R F hT.char hT.junk
  have hGU : R.PGUnit F := GlobalTheory.gUnit_of_models R F hT.char.base.models
  have hGE : R.PGEquiv F := GlobalTheory.GEquivCx.pGEquiv_of_baseW P.q2 R F hT.char.base hT.ex
  have hBlk : (R.toCx3 F).zs.InBlock := GlobalTheory.Hk3.inBlock_of_cuspRapidDecay P.q2 R F hLI hT.ok hT.char hT.ex hGE
  have hA : R.PThmA := GlobalTheory.T.thetaLift_theoremA_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hJ
  have hB : R.PThmB := GlobalTheory.T.thetaLift_theoremB_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ
  exact ⟨hOk, hGU, hGE, hBlk, hA, hB⟩
end GlobalTheory.Stage1
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PGUnit F ∧ R.PGEquiv F ∧ (R.toCx3 F).zs.InBlock ∧ R.PThmA ∧ R.PThmB := by
  first | exact @_root_.GlobalTheory.Stage1.stage1_alt | exact _root_.GlobalTheory.Stage1.stage1_alt | (intros; apply _root_.GlobalTheory.Stage1.stage1_alt <;> assumption)
end
end

section

section
noncomputable section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
namespace GlobalTheory.NormRatio
section General
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end General
section Translates
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)
end Translates
section Exact
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
end Exact
section Fock
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}
end Fock
section Norm
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
theorem theta_lift_petersson_norm_eq_rallis_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (hX : IsDict P X)
    {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))} {μ₀ : Measure (GA D X.B)} (hK : IsMaxLevel X.toFrame K₀ μ₀)
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ} (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o)
    (ho : o + P.a ≤ P.d) (ha : 1 ≤ P.a) (had : P.a < P.d) (hu : GlobalTheory.LFun.UnrOff X.χB (Sf : Set (FinPl D))) (Λ : ℂ → ℂ)
    (hΛ : ∀ s, GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL X.χB⁻¹ (Sf : Set (FinPl D))) s (Λ s)) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) =
      mass D P.d * mass D P.a * ((∏ i ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - i)) /
        GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) P.a P.d (((P.d - P.a : ℕ) : ℂ) / 2)) *
        (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) *
          ((locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ))) := by
  refine (GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan P X hX ha had).elim fun cA h1 => h1.elim fun a h2 => h2.elim fun ν h3 => h3.elim fun 𝓕 hPair => ?_
  have hfd := finite_data hI h hm hstd ho
  refine hfd.1.elim fun LB hLB => ?_
  have hn := (hfd.2 ν 𝓕 hPair.covol).1
  have hs := (hfd.2 ν 𝓕 hPair.covol).2
  have hlev := fun x => GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)
  have hsph : IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf (X.fock T) := isSphOff_pure hX.2.inf hLB.2 _ _ _ _ _
  have hU : GlobalTheory.Core.Rk.IP.Unram X.ψ X.A X.B X.χB (stdLat X.A) LB Sf (X.fock T) (X.fock T) :=
    ⟨(hlev 1).1, hLB.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2, hu, hsph, hsph⟩
  have hint := GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact P X hX (hlev 1).1 (fun x => (hlev x).2) a ν 𝓕 hPair.maj Sf (X.fock T)
    (ip X.A X.B ν 𝓕 (X.fock T) (X.fock T))
    (fun x hx k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (by rw [hX.2.fixA x hx T]))
    (fun x hx hx' k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (ip_fock_zero hX hPair.covol T (h.std.ptA x).1 (hs x hx hx')))
  refine hK.meas.elim fun 𝓕₀ h𝓕₀ => hX.1.measA.elim fun 𝓕A h𝓕A => ?_
  haveI := hX.1.haarA
  haveI : μ₀.IsHaarMeasure := h𝓕₀.1.1
  have hA : GlobalTheory.Cusp.wittIndex X.A = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramA)
  have hB : GlobalTheory.Cusp.wittIndex X.B = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramB)
  have key := _root_.GlobalTheory.BottomRallis.rallis_inner_product_bottom_norm_eq hP hPair hA hB (isFockVec_fock hX T) hU X.m μ₀
    ⟨((P.d - P.a : ℕ) : ℝ) / 2 - 1, by linarith, hint.1 _⟩
    (fun i => Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (X.A.rank : ℂ) / 2 - i)) fun i _ => hΛ _
  have vA := volQ_eq_mass X.A P.a X.ιA X.KA X.m 𝓕A hX.1.defA hX.1.injA hX.1.rangeA hX.1.ratA hX.1.levA hX.1.levA_iff h𝓕A
  have vB := volQ_eq_mass X.B P.d X.ιB K₀ μ₀ 𝓕₀ hX.1.defB hX.1.injB hX.1.rangeB hX.1.ratB hK.lev hK.mem_iff h𝓕₀
  have e1 := hint.2.trans ((ip_fock hX hPair.covol T).trans (congrArg _ hn))
  refine key.trans ?_
  rw [vA, vB, e1, X.rkA, X.rkB]
theorem petersson_norm_bottom_theta_lift_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) {T : Type}
    {L : LevCh D T} {sc : Consts} {μ : T} (hL : L.Is μ) (G : GridData L sc) {t : T} {i j : Fin D.R.m}
    {P' : Pair D ⊤ δ t0 Q} (hb : IsBottom G t i j (modT G t) P P') {Λ : ℂ → ℂ} (hΛ : GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ) :
    (P.norm : ℂ) = normFactor D δ t0 P.a P.d P.n *
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  have hm := goodMod_modT hL (GlobalTheory.SqTop.BotT.pde_ne_q hR).1 (GlobalTheory.SqTop.BotT.pde_ne_q hR).2 G t
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hdict := exact_dictionary P hI (isCongLevel_of_isBlockLevel hm.1 hb.lev.1)
  refine hdict.2.1.elim fun X h1 => h1.elim fun r h2 => h2.elim fun K₀ h3 => h3.elim fun μ₀ h4 => ?_
  have h5 := hdict.2.2 X r K₀ μ₀ h4.1 h4.2
  have hX := h5.1.1
  have hχ := GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse X.χB P.W.chV' P.W.ep' (nuH G t i j) hX.2.weil.hecT h4.1.chB hb.chars.2
  have hl := GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive hL hR.hF G t i j X.χB hχ
  have hT := _root_.GlobalTheory.NormRatio.theta_lift_petersson_norm_eq_rallis_integral hP hI h4.1 hX h4.2 hm hb.std (by rw [zero_add]; exact P.a_le) (by omega) (by omega) hl.1 Λ
    (hl.2 Λ hΛ)
  have hidx : ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = locIdx D (modT G t) P.a (P.d - P.a) :=
    GlobalTheory.StdLoc.relIndex_blockLevel P (modT G t) P.a hm.1 hm.2.1 P.a_le (hPa.symm ▸ hb.lev.1)
  have hidx' : ((P.J.relIndex (intG D P.d) : ℕ) : ℂ) = (locIdx D (modT G t) P.a (P.d - P.a) : ℂ) := by
    rw [← hidx]; rfl
  have hd := GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial D (modT G t) (sfB G t) hm P.a (P.d - P.a) (by omega)
  rw [Nat.add_sub_cancel' P.a_le] at hd
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hprod : ∏ k ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - k) =
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
    obtain ⟨u, hu⟩ := hrk.2.2.1
    have e1 : P.d = 2 * GlobalTheory.SqTop.h0 D i j := by unfold GlobalTheory.SqTop.h0; omega
    rw [← GlobalTheory.BottomRallis.prod_range_sub_eq_prod_Icc (fun s => Λ s) P.a (GlobalTheory.SqTop.h0 D i j) (GlobalTheory.SqTop.e0 D i j)
      (by unfold GlobalTheory.SqTop.h0 GlobalTheory.SqTop.e0; omega)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    rw [Nat.cast_sub P.a_le, e1]
    push_cast
    ring
  refine h5.2.2.2.2.trans ?_
  rw [Finset.sum_congr rfl fun T _ => hT T, ← Finset.mul_sum, ← Finset.sum_mul, hidx', hprod]
  exact collect hd (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
end Norm
theorem big_theta_petersson_norm_ratio_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  intro hP hI _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 i j t t' Q Q' P P' P₁ P₁' Λ Λ' hb hb' hΛ hΛ'
  have h1 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb hΛ
  have h2 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb' hΛ'
  have h3 := (GlobalTheory.BottomReal.bottom_real_eq G hL hb hb').1
  have h4 : normFactor D δ t0 P.a P.d P.n = normFactor D δ t0 P₁.a P₁.d P₁.n :=
    congr (congr (congrArg (normFactor D δ t0) h3.1) h3.2.1) h3.2.2.1
  rw [h1, h2, h4]
  ring
end GlobalTheory.NormRatio
end
end

section
open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  first | exact @_root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | exact _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | (intros; apply _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
namespace GlobalTheory.RallisBottom
theorem big_theta_norm_eq_rallis_inner_product : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, ∃ (P : PolF D WW.rank A.rank) (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)) (c : ℂ), c ≠ 0 ∧ ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s := by
  intro hPr
  obtain ⟨CF0, h⟩ := GlobalTheory.T.exists_innerProductFormula_data_definite_bottom
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have hX₁ := isBottomTri_posSig hX
  obtain ⟨χA, χB, sA, sB, cA, a, νW, 𝓕W, LA, LB, Sf, par, κ, P, hP, hw, hF, hU, h1, hpar, hsph, hκ, hdS, hL, hloc⟩ :=
    h C hC D large₂ he hx hR T Lc μ₀ hμ G W i j (posSig A) A' WW (Tri.posSig X) hX₁ (sigOK_posSig hX) t
  obtain ⟨ν, 𝓕, hν, h𝓕, hvol⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero W i j (posSig A) A' WW (Tri.posSig X) hX₁
  obtain ⟨m, hm, hdict⟩ := GlobalTheory.T.definiteBottom_thetaIntegral_normSq_eq_petersson W i j (posSig A) A' WW (Tri.posSig X) hX₁ t P ν 𝓕 hν h𝓕
  obtain ⟨hs₁, hZ⟩ := hloc m hm
  obtain ⟨-, -, -, hH⟩ := _root_.GlobalTheory.T.rallis_bottom_hecke_form_anisotropic hPr D W.ψ W.θ (GlobalTheory.Grid.neg (posSig A)) WW χA χB sA sB A'.rank cA a _ νW 𝓕W hP hw LA LB Sf _ _ hF hF hU
    m ν hm hν _ h1 _ h1 par hpar hsph hs₁
  refine ⟨P, ν, 𝓕, volQ WW ν * κ * _,
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hvol) hκ) hZ, hν, h𝓕, fun Λ hΛ => ?_⟩
  show ((∫ h in 𝓕, ‖(Tri.posSig X).I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = _
  rw [hdict, hH _ (hL Λ hΛ), mul_right_comm κ, mul_div_cancel_right₀ _ hdS]
  ring
end GlobalTheory.RallisBottom
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rallis_inner_product_big_theta_lift : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, ∃ (P : PolF D WW.rank A.rank) (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)) (c : ℂ), c ≠ 0 ∧ ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s := by
  first | exact @_root_.GlobalTheory.RallisBottom.big_theta_norm_eq_rallis_inner_product | exact _root_.GlobalTheory.RallisBottom.big_theta_norm_eq_rallis_inner_product | (intros; apply _root_.GlobalTheory.RallisBottom.big_theta_norm_eq_rallis_inner_product <;> assumption)
end
end
