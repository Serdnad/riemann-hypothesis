module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle383
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle817
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle639
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle427
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MidVacLat
variable {D : D7}
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j hj d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sd0 : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j (by omega))
  have sd1 : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) hj)
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd0).1 (f.g.b j)
  obtain ⟨M', hM', hmv'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd1).1 (f.g.b (j + 1))
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hvth := hd₀.2.1.2.theta
  have hvlat := hd₀.2.1.2.lat
  exact ⟨M, M', hM, hM', hmv _, hmv' _, hWe.om_pres _ _ hvth,
    isLatVac_move hWe sd0 hM sd1 hM' (hmv _) (hmv' _) hvth hvlat⟩
end GlobalTheory.MidVacLat
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.TupRoot
variable {D : D7}
end GlobalTheory.TupRoot
open GlobalTheory.TupRoot in
theorem GlobalTheory.TupRoot.weil_tuple_root_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP _hR t
  have hc := hP.bot.hyp.2.2.2.1
  have hL := hc.lev
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have hxi : ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) ((_root_.GlobalTheory.Fam.pk_z W).xiH t) := hL.xi t
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have hstep : ∀ k, Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta k =
      ((Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).1 * (_root_.GlobalTheory.Fam.pk_z W).xi t,
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).2 * (_root_.GlobalTheory.Fam.pk_z W).xi t) := by
    intro k
    unfold Lift.chrStep
    split_ifs <;> simp [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_right_comm]
  have hpow : ∀ x, (_root_.GlobalTheory.Fam.pk_z W).xi t x ^ n = 1 := pow_eq_one_of_chrEq hxi hn
  have hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (_root_.GlobalTheory.Fam.pk_z W).xi t x = 1 := eq_one_of_finPart hxi hn0 hn
  choose xr hxr using fun k => GlobalTheory.RecDict.exists_isDetRoot D (Yc D k) (f.g.b k)
  obtain ⟨xT, hxT⟩ := GlobalTheory.RecDict.exists_isDetRoot D D.sp.X' f.g.bT
  let w : ℕ → Circle := fun k => if k + 1 < D.R.m then ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (xr (k + 1))
    else ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT
  refine ⟨fun k => (w k : ℂ), ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨n, hn0, ?_⟩
    have h1 : w k ^ n = 1 := by
      simp only [w]
      split_ifs <;> rw [mul_pow, inv_pow, hpow, hpow, inv_one, one_mul]
    have := congrArg (fun z : Circle => (z : ℂ)) h1
    simpa using this
  · intro j hj _ _ a ha a' ha' g hg
    have hW0 := hc.chain.ωY W.P.A3.A.μ0 j hj
    have hWt := hc.chain.ωY t j hj
    rw [hstep] at hWt
    obtain ⟨z, hz⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D j) a
    obtain ⟨y, hy1, hy⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a ha z hz
    obtain ⟨z', hz'⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D (j + 1)) a'
    obtain ⟨y', hy1', hy'⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a' ha' z' hz'
    rw [twist_eq hW0 hWt (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy (hxr j))
      (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy' (hxr (j + 1))) hg]
    have e : ((_root_.GlobalTheory.Fam.pk_z W).xi t (y * xr j))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (y' * xr (j + 1)) = w j := by
      simp only [w, if_pos hj, map_mul, hinf _ hy1, hinf _ hy1', one_mul]
    rw [e]
  · intro j h g hg
    have hW0 := isWeil_rec (idx_top h) _ (hc.chain.ωX W.P.A3.A.μ0)
    have hWt := isWeil_rec (idx_top h) _ (hc.chain.ωX t)
    rw [hstep] at hWt
    have e := twist_eq hW0 hWt (hxr (j + 1)) hxT hg
    have hw : w (j + 1) = ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr (j + 1)))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT := by
      simp only [w]
      rw [if_neg (by omega)]
    show _ = ((w (j + 1) : Circle) : ℂ) • _
    rw [hw]
    exact e
  · intro j
    refine ⟨n, hn0, ?_⟩
    have hν : (_root_.GlobalTheory.Fam.pk_z W).xi t ^ n = 1 := MonoidHom.ext fun x => by simpa using hpow x
    simp only [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_one, mul_pow, hν]
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem lastStep_integrableOn_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv F Q x g
  have hC := hP.bot.hyp.2.2.2.1
  have hω : IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' _ _ (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) :=
    weil_transport ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) (hC.chain.ωX W.P.A3.A.μ0) (j + 1) (idx_top h)
  obtain ⟨c1, hc1⟩ := hC.lev.βY (j + 1) (by omega)
  obtain ⟨c2, hc2⟩ := hC.lev.βX
  have hv' : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' v :=
    (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc1) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc2) hc1.1 hc2.1 hv
  have hf := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hC.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) hv' Q
  have hν := hC.models.νX W.P.A3.A.μ0
  have key := GlobalTheory.Hk3.StepX.integ_X hω hf (F.1 x)
    (multT_apply_continuous _ _ _ _ F.1 F.2 x) (multT_apply_left _ _ _ _ F.1 F.2 x) _ hν.1.1 _ hν.2 g 1
  simpa only [mul_one] using key
end GlobalTheory.BaseChain
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepLevelP.IoLevPf
end GlobalTheory.StepLevelP.IoLevPf
namespace GlobalTheory.StepLevelP

theorem io_levChi_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ F : (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1), F.1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) (g * κ) = levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) g := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF κ hκ φ x g
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).Is W.P.A3.A.μ0 := hC.lev
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have hio := hC.chain.ioY t j (by omega)
  have hκG : κ ∈ GfC (Yc D j) := hκ.1
  have hκP : Lev.finE (Yc D j) κ ∈ parLev D.sp.cm (Yc D j).gram ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) := hκ.2.1
  have hκH : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ) ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := hκ.2.2
  have hκl : IsLevelLift (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)
      (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ)) κ := ⟨hκG, hκP, rfl⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain (_root_.GlobalTheory.Fam.pk_z W) hL t (j + 1) hj
    (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ))
  have hj' : j < D.R.m := by omega
  have hlaw := GlobalTheory.StepLaw.step_law (_root_.GlobalTheory.Fam.pk_z W).toLevCh hL t j (j + 1) rfl hj' hθ (D.sp.Y_sig _) (D.sp.Y_sig _) (r_le_Y _) (r_le_Y _)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY j hj') (hL.βY (j + 1) hj)
    (hC.chain.ωY t j hj) (hC.chain.vY t j hj) _ κ κ' hκl hκ'
  have hsS : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' ≠ 0 :=
    levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ)⁻¹ •
      (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).vY t j := hlaw
  have hv : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ *
        (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) •
        (_root_.GlobalTheory.Fam.pk_z W).vY t j := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) hθ (hC.chain.ωY t j hj)
    _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vY t j) (hC.chain.ptY t j hj) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (hC.chain.ωY t j hj)
    ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) (hC.chain.ptY t j hj φ)
  have hκ'H : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D (j + 1)) κ') ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := by
    rw [hκ'.2.2]; exact hκH
  have hκ'P : κ' ∈ levS (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) := ⟨hκ'.1, hκ'.2.1, hκ'H⟩
  have e1 : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hsub : (⟨_, hκ'H⟩ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H) = ⟨_, hκH⟩ := Subtype.ext hκ'.2.2
  have e2 : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ' =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) *
        levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκ'H, Units.val_mul, hsub]
    rfl
  have hfd : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have := hC.models.νY t (j + 1) h
      exact ⟨this.1.1, this.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      rw [e]
      have := hC.models.νY' t
      exact ⟨this.1.1, this.2⟩
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Yc D (j + 1))
  have htg : IsTopologicalGroup (GA D (Yc D (j + 1))) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Yc D (j + 1)).gram))
  haveI := hfd.1
  haveI hR : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) = (_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) := map_mul_right_eq_self _ κ'
  have hFv := fun v => GlobalTheory.StepLevelP.IoLevPf.multT_val (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) _ _ F.1 hF v
  have hpt' : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) = (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) • (_root_.GlobalTheory.Fam.pk_z W).ptY t j φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1))
    ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) hfd.2 κ' hmap
    (fun h => thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D j)).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, (hFv x).1 γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) (h * κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x (h * κ') =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ * levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ') * (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h) := fun h => by
    rw [hth, (hFv x).2 κ' hκ'P]; ring
  rw [← hio.eq F φ x (g * κ), ← hio.eq F φ x g]
  unfold Lift.liftInt
  rw [← hint.2]
  simp only [hpw]
  rw [integral_const_mul, e1, e2]
  field_simp
end GlobalTheory.StepLevelP
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopLevelP
section Package
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Package
theorem vector_of_mem_cxp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  exact mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W) hC.grp.red_R hC.models.jX hC.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
    (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩ ((hP.hTop t).le ⟨_, rfl⟩)
end GlobalTheory.TopLevelP
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepMove
section Lattices
open GlobalTheory.FinPl hiding Pl
variable {D : D7}
end Lattices
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
end Gen
theorem fock_vac_moved_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))) ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j hj g g' hg hg' M M' hM hM' hm hm'
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sd : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((_root_.GlobalTheory.Fam.pk_z W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  exact gen (W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj) (sd j (by omega)) hM (sd (j + 1) hj) hM' hg hg' (hm _) (hm' _) _ _
    (W.Q.charW.base.chain.vY W.P.A3.A.μ0 j hj).1
end GlobalTheory.StepMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopMove
section Package
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Package
theorem fock_vac_moved_top_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (_root_.GlobalTheory.Fam.pk_z W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))) ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (θ := (_root_.GlobalTheory.Fam.pk_z W).θ)
    (sS := cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (sT := cart (_root_.GlobalTheory.Fam.pk_z W).MX) (weil_omT (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (isVacO_vacT (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1
end GlobalTheory.TopMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.PlaceSep
variable {D : D7}
end GlobalTheory.Fam.PlaceSep
open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ PP PP' : Pl D.host.E, (PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP) → (PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have mixed : ∀ A B : Pl D.host.E, A ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → _root_.GlobalTheory.Fam.QAllAlt W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopConv
variable {D : D7}
end GlobalTheory.TopConv
end
noncomputable section
namespace GlobalTheory.TopConv

theorem top_comb_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv
  have hLev := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hbY⟩ := hLev.βY (j + 1) (by omega)
  obtain ⟨cX', hbX⟩ := hLev.βX
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have hr : (Yc D (j + 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY n) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY n) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 n (_root_.GlobalTheory.Fam.pk_z W).triv) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m)
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (_root_.GlobalTheory.Fam.pk_z W).vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact W.Q.charW.base.chain.vX _
  have hX := key (j + 1) (idx_top h)
  obtain ⟨d₁, hd₁, e₁⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hX
  obtain ⟨d₂, hd₂, e₂⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hv
  have hv0 : v ≠ 0 := (GlobalTheory.Chain.StepVac.stepVec_vac sdY sdX hr hv).2.1
  have hspan := comb_mem_span (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₂) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)
  rw [← e₂] at hspan
  have hvac := GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hv.1 sdY sdX hspan hv0
  obtain ⟨b, hb, hbv⟩ := exists_finComb_of_mem_span _ hvac
  obtain ⟨c, hc, hcc⟩ := isFinComb_comp (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₁) hb
  refine ⟨c, hc, ?_⟩
  rw [hcc, hbv]
  exact e₁.symm
end GlobalTheory.TopConv
end
end
end

end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattices_consecutive_step_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))) ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) 1) ≠ 0 := by
  first | exact @_root_.GlobalTheory.StepMove.fock_vac_moved_alt | exact _root_.GlobalTheory.StepMove.fock_vac_moved_alt | (intros; apply _root_.GlobalTheory.StepMove.fock_vac_moved_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattices_top_step_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (_root_.GlobalTheory.Fam.pk_z W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))) ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) 1) ≠ 0 := by
  first | exact @_root_.GlobalTheory.TopMove.fock_vac_moved_top_alt | exact _root_.GlobalTheory.TopMove.fock_vac_moved_top_alt | (intros; apply _root_.GlobalTheory.TopMove.fock_vac_moved_top_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_data_step_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  first | exact @_root_.GlobalTheory.MidVacLat.main_alt_alt | exact _root_.GlobalTheory.MidVacLat.main_alt_alt | (intros; apply _root_.GlobalTheory.MidVacLat.main_alt_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_place_eq_of_under_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ PP PP' : Pl D.host.E, (PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP) → (PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  first | exact @_root_.GlobalTheory.Fam.pg_qAll_under_inj_alt | exact _root_.GlobalTheory.Fam.pg_qAll_under_inj_alt | (intros; apply _root_.GlobalTheory.Fam.pg_qAll_under_inj_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.root_of_unity_theta_twist_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  first | exact @_root_.GlobalTheory.TupRoot.weil_tuple_root_alt | exact _root_.GlobalTheory.TupRoot.weil_tuple_root_alt | (intros; apply _root_.GlobalTheory.TupRoot.weil_tuple_root_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chain_projection_level_character_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ F : (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1), F.1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) (g * κ) = levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) g := by
  first | exact @_root_.GlobalTheory.StepLevelP.io_levChi_alt | exact _root_.GlobalTheory.StepLevelP.io_levChi_alt | (intros; apply _root_.GlobalTheory.StepLevelP.io_levChi_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.top_step_vector_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  first | exact @_root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | exact _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | (intros; apply _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.top_step_vector_theta_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  first | exact @_root_.GlobalTheory.TopConv.top_comb_alt | exact _root_.GlobalTheory.TopConv.top_comb_alt | (intros; apply _root_.GlobalTheory.TopConv.top_comb_alt <;> assumption)
end

end
end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vector_of_mem_extra_projection : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  first | exact @_root_.GlobalTheory.TopLevelP.vector_of_mem_cxp | exact _root_.GlobalTheory.TopLevelP.vector_of_mem_cxp | (intros; apply _root_.GlobalTheory.TopLevelP.vector_of_mem_cxp <;> assumption)
end

end
end
