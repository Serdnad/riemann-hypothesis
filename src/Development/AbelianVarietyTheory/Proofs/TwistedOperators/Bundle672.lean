module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle049
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle622
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle575
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle665
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle666
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle517
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobiStep_basePoint_jacobiFunction_unfolded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ ∀ y : WO J.W₀ B.L → ℂ, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) Ψ, IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (rat x₀) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
  first | exact @GlobalTheory.Asc.fb_base_th_fl | exact GlobalTheory.Asc.fb_base_th_fl | (intros; apply GlobalTheory.Asc.fb_base_th_fl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel



theorem thP_vec_eq_translate : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (hn : T.rank ≤ S.rank) (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ f₀ f, IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → ∃ (Lv : SW.Level C.X) (M : ℕ) (f' : WO S T → ℂ) (k₀ : GA D S), IdemTwo Lv.w ∧ 0 < M ∧ (M : 𝓞 D.host.E) ∈ Lv.𝔪 ∧ C.IsBase Lv B f' ∧ k₀ ∈ GfC S ∧ f = om (k₀, 1) (C.uVec Lv hn f') ∧ C.IsTh (C.uVec Lv hn f') ∧ C.IsFock B (C.uVec Lv hn f') ∧ C.uVec Lv hn f' ≠ 0 ∧ ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C om hom hn B hB ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd f₀ f hf
  have hf0 : f ≠ 0 := GlobalTheory.T.theta_kernel_finite_vector_ne_zero D S T C hn B hB ΛT hsd βS βT hβS hβT Pg Q ξ f₀ f hf
  have hfc := hf
  obtain ⟨hvac, e, he, hθ⟩ := hf
  obtain ⟨Lv, k₀, Λ', L, hw2, hmP, hJ, hk₀, hmov, hfin, hA, hB', hC, hD, hE, hF⟩ :=
    GlobalTheory.T.thetaLift_level_datum_sum_of_translates D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd e he
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hfT : f = Tm (thPDatum S T βS βT Pg Q ξ e) := hall Tm hTm
  obtain ⟨hSB, hTh, hFock, hLat⟩ := GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum D S T C B hB ΛT hsd (Pg ∪ Q) e he f₀ hvac Tm hTm L hA hB' hC
  have hLat'' := hLat _ hD
  haveI := Fintype.ofFinite (LvCls C Lv)
  set f'' := Tm (indL L) with hf''
  have hee : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : ∀ w : WO S T, IsHalf (cA D e) (partAt (cA D e) w) := fun w i j => by
    simp only [partAt, Matrix.map_apply]
    rw [← mul_assoc, hee]
  set t : LvCls C Lv → WO S T := fun c =>
    partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) with ht
  have hfsum : f = ∑ c : LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) •
      heisO C.ψ S T (t c) f'' := by
    rw [hfT]
    have hΦ : thPDatum S T βS βT Pg Q ξ e = ∑ c : LvCls C Lv,
        Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) • fun x => indL L (x + t c) := by
      funext x
      rw [hF x, finsum_eq_sum_of_fintype, Finset.sum_apply]
      rfl

    rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hTm.trans _ hSB _ (hhalf _)]
  set f' := om (k₀⁻¹, 1) f'' with hf'
  have hinv : ∀ g : GA D S, ∀ x, om (g, 1) (om (g⁻¹, 1) x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    exact congrArg (fun E : Module.End ℂ (WO S T → ℂ) => E x) om.map_one
  have hinv' : ∀ g : GA D S, ∀ x, om (g⁻¹, 1) (om (g, 1) x) = x := fun g x => by
    simpa using hinv g⁻¹ x
  have hom1 : om (k₀, 1) f' = f'' := hinv k₀ f''
  have hTh' : C.IsTh f' := hom.om_pres _ _ hTh
  have hu : om (k₀, 1) (C.uVec Lv hn f') = f := by

    rw [hfsum, Ctx.uVec, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
    congr 1
    rw [Ctx.rho, hom.om_heis _ _ _ _ hTh', hom1]
    obtain ⟨v, hv, hv1, hv2⟩ := hE _ (c.out).2
    have h2 : heisO C.ψ S T (2 • v) f'' = f'' := hLat''.1 v hv
    have h3 := GlobalTheory.FinTranslate.heisO_heisO S T C.ψ (t c) (2 • v) f''
    rw [h2, show C.ψ (symplOH S T (t c) (2 • v)) = 1 from hv2, one_smul] at h3
    calc heisO C.ψ S T (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) f''
        = heisO C.ψ S T (t c + 2 • v) f'' := congrArg (fun w => heisO C.ψ S T w f'') hv1
      _ = heisO C.ψ S T (t c) f'' := h3.symm
  have hmt1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have hmvB : C.mvB 1 B = B := by
    funext τ
    simp [Ctx.mvB, hmt1, compAt]
  have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  have hne' : f' ≠ 0 := by
    intro h0
    apply hf0
    have : f'' = 0 := by rw [← hom1, h0, map_zero]
    rw [hfsum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [this]
    have : heisO C.ψ S T (t c) (0 : WO S T → ℂ) = 0 := by
      funext w
      simp [heisO]
    rw [this, smul_zero]
  have hFock' : C.IsFock B f' := by
    have := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f'' hTh).2 B hB).1 hFock)
    rwa [hmvB] at this
  have hlat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))) f' :=
    (GlobalTheory.TensLatMove.hatA_move D S T C k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmov hmov1).2
      om hom f'' hTh hLat''
  have hbase : C.IsBase Lv B f' := ⟨hTh', hne', hFock', hlat'⟩
  have hu1 : C.IsTh (C.uVec Lv hn f') := GlobalTheory.Ker.KernelCompare.isTh_uVec C Lv hn hTh'
  have hfth : C.IsTh f := hu ▸ hom.om_pres _ _ hu1
  have hfF : C.IsFock B f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_thPVec C.ψ C.θ S T _ _ _ _ βS βT Pg Q ξ f₀ f hfc hfth τ
  have hu2 : C.IsFock B (C.uVec Lv hn f') := by
    have h := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f hfth).2 B hB).1 hfF)
    rw [hmvB, ← hu, hinv'] at h
    exact h
  have hu3 : C.uVec Lv hn f' ≠ 0 := fun h0 => hf0 (by rw [← hu, h0, map_zero])
  refine ⟨Lv, Ideal.absNorm Lv.𝔪, f', k₀, hw2, ?_, Ideal.absNorm_mem Lv.𝔪, hbase, hk₀, hu.symm, hu1, hu2, hu3,
    GlobalTheory.T.hermitianThetaLevelGroup_stabilizes_selfDualLatticeFrame D S T C Lv ΛT hsd hAA βT hβT Pg hmP hJ⟩
  exact Nat.pos_of_ne_zero fun h => Lv.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

end GlobalTheory.LiftLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.EvenOnto.upNe_of_heckeForm | exact GlobalTheory.EvenOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.EvenOnto.upNe_of_heckeForm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  first | exact @GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | exact GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | (intros; apply GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  first | exact @GlobalTheory.AscFin.ShiftVal.val_le_cosExp | exact GlobalTheory.AscFin.ShiftVal.val_le_cosExp | (intros; apply GlobalTheory.AscFin.ShiftVal.val_le_cosExp <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftInt

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem upSum_single {ρ : ℕ} {i j : Fin ρ} (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (Matrix.single i j c : Mx D ρ ρ) = c := by
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hj, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mxAt_single {P : GlobalTheory.FinPl.Pl D → Prop} {ρ : ℕ} (i j : Fin ρ) {c : AE D} (hc : c ∈ idAt D P) :
    MxAt P (Matrix.single i j c : Mx D ρ ρ) := by
  intro a b
  rw [Matrix.single_apply]
  split_ifs
  · exact hc
  · exact zero_mem _

theorem mul_single_mulVec {m ρ : ℕ} (x : Mx D m ρ) (i j : Fin ρ) (c : AE D) (z : Fin ρ → AE D) :
    (x ⬝ (Matrix.single i j c : Mx D ρ ρ)) *ᵥ z = GlobalTheory.FinPl.colMul x i (c * z j) := by
  funext k
  rw [← Matrix.mulVec_mulVec, Matrix.single_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [GlobalTheory.FinPl.colMul, mul_comm]
  · intro b _ hb
    simp [Function.update_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ _) h



theorem shift_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) → mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ _ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t htd ht hsh i j hj
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨h1, -, -⟩ := GlobalTheory.FinPl.InvStep.diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.InvStep.levi_sub_one_mem dW ht i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.ColonInt.colon_int D V V₀ ρ dV LV LV₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdV hG.monoV i j _ hti ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * t.1 i i) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, GlobalTheory.FinPl.colMul dV.jX j a ∈ latV V LV (· = v) →
      GlobalTheory.FinPl.colMul dV.jX i (r * o * a) ∈ latV V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hN : (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ) = t.1 ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    conv_rhs => rw [h1]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.single_apply]
    split_ifs with h
    · rw [← h.1]; ring
    · rw [mul_zero]
  have hmove : mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ (Matrix.single i j (r * t.1 i i * o) : Mx D ρ ρ)) =
      xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) := by
    rw [hN, xZero, ← map_inv, ← Matrix.mul_assoc, HypDec.levi_jX, Matrix.mul_assoc, ← Matrix.mul_assoc (t⁻¹).1,
      show (t⁻¹).1 ⬝ t.1 = 1 from t.inv_mul, Matrix.one_mul]
  have hx : MxAt (· = v) (xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ)) := by
    intro a b
    have := GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ 1 (mxAt_single i j hro) a b
    rwa [Matrix.mul_one] at this
  have hA : xZero dW ⬝ (Matrix.single i j (r * o) : Mx D ρ ρ) ∈ p.A₁ := by
    refine (hS.a _ hx).2 ((GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hG.sdV hG.sdW _ _).2 ⟨?_, fun y hy => ?_⟩)
    · rw [HypDec.extX_apply]
      exact fun a b => GlobalTheory.FinPl.InvStep.mat_mem_idAt (xZero dW) _ dV.pX (mxAt_single i j hro) a b
    · have h2 := (hG.cols i _ (Ideal.mul_mem_right _ _ hro)).1 (hRo _ (((hG.monoV y).1 hy).1 j))
      rw [← mul_single_mulVec, Matrix.mulVec_mulVec] at h2
      rw [HypDec.extX_apply]
      exact h2
  have h3 := hsh (Matrix.single i j (r * t.1 i i * o))
    (mxAt_single i j (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hr)))
    (fun a b hab => by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd hlt (not_lt.2 hab))
    (by rw [hmove]; exact hA)
  rwa [upSum_single hj] at h3

end GlobalTheory.AscFin.ShiftInt

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.FinPl.PtInv

variable {D : D7}

theorem pairS_jX_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (N : Mx D ρ ρ) (i : Fin ρ) (b : AE D) :
    pairS W (dW.jX ⬝ N) (dW.jY ⬝ Matrix.single i i b) = cA D b * N i i := by
  rw [pairS, adj_mul, GlobalTheory.FinPl.InvStep.adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W),
    ← Matrix.mul_assoc (adj dW.jY), HypDec.gram_YX, Matrix.one_mul, GlobalTheory.FinPl.InvStep.trace_single_mul]

theorem pairS_add_left {W : HSp D} {ρ : ℕ} (x x' y : Mx D W.rank ρ) :
    pairS W (x + x') y = pairS W x y + pairS W x' y := by
  simp only [pairS, Matrix.mul_add, Matrix.trace_add]

theorem symplO_off {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) {v : Pl D} {M : Mx D W.rank ρ}
    (hM : GlobalTheory.AscFin.MxOff (· = v) M) (y : Mx D W.rank ρ) (hy : MxAt (· = v) (dV.extY W y)) :
    symplO V W (dV.extX W M) (dV.extY W y) = 0 := by
  have hfix : SelfDualAt.cP (· = v) • dV.extY W y = dV.extY W y := by
    ext k l
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact SuppShift.eps_mul (hy k l)
  have h0 : SelfDualAt.cP (· = v) • dV.extX W M = dV.extX W 0 := by
    ext k l
    rw [map_zero, Matrix.zero_apply, Matrix.smul_apply, Algebra.smul_def, HypDec.extX_apply, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    have h : M k m * algebraMap (AF D.host.F) (AE D) (SelfDualAt.cP (· = v)) = 0 :=
      GlobalTheory.DisjComb.mul_eq_zero_of_off (hM k m) (SuppShift.eps_idAt v)
    rw [← mul_assoc, mul_comm (algebraMap _ _ _), h, zero_mul]
  rw [← hfix, SelfDualAt.symplO_smul_swap, h0, InvStep.symplO_extX_extY]
  simp [pairS]



theorem inv_int_of_pt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∃ u : UX D ρ, ∃ a ∈ p.A₁, GlobalTheory.AscFin.MxOff (· = v) (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a)) → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t htd ht hpt i
  obtain ⟨-, h2, -⟩ := InvStep.diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := InvStep.levi_sub_one_mem dW (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  obtain ⟨u, a, ha, hoff⟩ := hpt
  obtain ⟨b₀, hab, hb₀⟩ := hS.a' a ha
  have hlev : mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) = dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1) := by
    rw [← map_inv dW.levi t, ← Matrix.mul_assoc, xZero, HypDec.levi_jX, Matrix.mul_assoc]
  have hu1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
  have hdiag : ((t⁻¹).1 ⬝ u.1.1) i i = (t⁻¹).1 i i := by
    conv_lhs => rw [h2]
    rw [diagonal_mul, hu1, mul_one]
  have hsum : dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1) = (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) + (a - b₀) + b₀ + dW.jX ⬝ (1 : Mx D ρ ρ) := by
    rw [hlev, Matrix.mul_one, xZero]
    abel
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v (GlobalTheory.T.isTameFinitePlaceHermitian_all D v) hG.sdV hG.sdW hG.monoV hG.monoW
    hG.cols i _ hc1 ?_
  intro b hb hY
  have hYm : MxAt (· = v) (dV.extY W (dW.jY ⬝ Matrix.single i i b)) := LatMem.latO_mxAt hY
  have hτ : ∀ M : Mx D W.rank ρ, ψ (symplO V W (dV.extX W M) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W M (dW.jY ⬝ Matrix.single i i b))) := fun M => by
    rw [InvStep.symplO_extX_extY]
  have e : cA D b * (t⁻¹).1 i i = pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b) + pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b) + pairS W b₀ (dW.jY ⬝ Matrix.single i i b) +
      pairS W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b) := by
    calc cA D b * (t⁻¹).1 i i = pairS W (dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1)) (dW.jY ⬝ Matrix.single i i b) := by rw [pairS_jX_single, hdiag]
      _ = pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b) + pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b) + pairS W b₀ (dW.jY ⬝ Matrix.single i i b) + pairS W (dW.jX ⬝ (1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b) := by
        rw [hsum, pairS_add_left, pairS_add_left, pairS_add_left]
      _ = _ := by
        rw [pairS_jX_single dW (1 : Mx D ρ ρ), pairS_jX_single dW ((Matrix.single i i 1 : Mx D ρ ρ)), Matrix.one_apply_eq, Matrix.single_apply_same]
  have k1 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ, symplO_off dV hoff _ hYm, AddChar.map_zero_eq_one]
  have k2 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ, symplO_off dV hab _ hYm, AddChar.map_zero_eq_one]
  have k3 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W b₀ (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ]
    exact (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V W LV LW hG.sdV hG.sdW (· = v) _ (LatMem.latO_mxAt hb₀)).1 hb₀ _ hY
  have hlat : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V W LV LW hG.sdV hG.sdW (· = v) _).2 ⟨fun k l => ?_, fun y hy => ?_⟩
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (SuppShift.eps_idAt v)
    · have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) =
          SuppShift.eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      have ha' : SuppShift.eps v * (dV.pX *ᵥ y) i ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (SuppShift.eps_idAt v)
      have hV' : colMul dV.jX i (SuppShift.eps v * (dV.pX *ᵥ y) i) ∈ latV V LV (· = v) := by
        rw [SuppShift.colMul_mul]
        exact SuppShift.smul_latV (SuppShift.eps_int v) (((hG.monoV y).1 hy).1 i)
      have hA := (hG.cols i _ ha').1 hV'
      change (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ))) *ᵥ y ∈ _
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, SuppShift.single_mulVec', one_mul,
        ← SuppShift.colMul_mul]
      exact hA
  have k4 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    have hfix : SelfDualAt.cP (· = v) • dV.extY W (dW.jY ⬝ Matrix.single i i b) = dV.extY W (dW.jY ⬝ Matrix.single i i b) := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact SuppShift.eps_mul (hYm k l)
    rw [← hτ, ← hfix, SelfDualAt.symplO_smul_swap]
    exact (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V W LV LW hG.sdV hG.sdW (· = v) _ (LatMem.latO_mxAt hlat)).1 hlat _ hY
  have hadd : ∀ x y : AE D, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (x + y))) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * x)) *
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * y)) := fun x y => by
    rw [mul_add, map_add (f := _), AddChar.map_add_eq_mul]
  rw [hτ, pairS_jX_single, Matrix.single_apply_same, e, hadd, hadd, hadd, k1, k2, k3, k4, one_mul, one_mul, one_mul]

end GlobalTheory.FinPl.PtInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.base_point_character_trivial_on_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h))) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.pcBF_xZero_char | exact GlobalTheory.AscFin.pcBF_xZero_char | (intros; apply GlobalTheory.AscFin.pcBF_xZero_char <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.idempotent_smul_mem_hat_lattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) → v ∈ latBig G i → ∀ e : AE D, IsIdemSum e G.pl.W0 → e • v ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  first | exact @GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | exact GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig | (intros; apply GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig <;> assumption)
end
