module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle583
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle634
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.tame_functional_vacuum_irreducibility : ∀ D : D7, Irr D := by
  first | exact @GlobalTheory.Irr.irr | exact GlobalTheory.Irr.irr | (intros; apply GlobalTheory.Irr.irr <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

theorem resEta_one_of_step {μ : ℕ → ((AE D)ˣ →* Circle)} {η : (AE D)ˣ →* Circle} {n a b : ℕ}
    (h1 : ResEta D (Lift.chrStep μ η n).1 a) (h2 : ResEta D (Lift.chrStep μ η n).2 b) (hab : (a + b) % 2 = 1 % 2) :
    ResEta D η 1 := by
  unfold Lift.chrStep at h1 h2
  split_ifs at h1 h2
  · have h := resEta_parity (resEta_mul (resEta_inv h1) h2) hab
    rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h
  · have h := resEta_parity (resEta_mul h1 (resEta_inv h2)) hab
    rwa [mul_inv, inv_inv, mul_inv_cancel_left] at h

theorem levChi_flag_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    levChi V β (flagL (datY V.rank r t j hr Pg Q P χ ξ Frm.B)) κ =
      ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (redFn β PP (finE V κ))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, ((ξ PP (dBlk (blk2 r) 1 (redFn β PP (finE V κ))) : ℂˣ) : ℂ)⁻¹ := by
  have h := subgroupCharExtension_one_apply (N := ℂˣ) (⊤ : Subgroup (G0 Pg r)) (rTup β (datY V.rank r t j hr Pg Q P χ ξ Frm.B) (finE V κ))
  unfold levChi levFn
  rw [Units.val_mul, Units.val_mul]
  refine congrArg₂ _ ((congrArg₂ _ (congrArg Units.val h) rfl).trans ?_) ?_
  · rw [Units.val_one, one_mul]; rfl
  · rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun PP _ => ?_
    exact Units.val_inv_eq_inv_val _

theorem vacScal_resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (hd : Disjoint L.Pg (L.Q t)) {S T : HSp D}
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (g : GA D S) (h : GA D T) :
    vacScal βS βT P (resChr L t n) (resChr L t n) g h =
      (∏ PP ∈ L.Pg, (((L.chi n PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ((L.chi n PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹)) *
      ∏ PP ∈ L.Q t, (((L.xiR t PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
        ((L.xiR t PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) := by
  have e : P = L.Pg.disjUnion (L.Q t) hd := Finset.ext fun PP => (hP PP).trans Finset.mem_disjUnion.symm
  unfold vacScal
  rw [e, Finset.prod_disjUnion]
  refine congrArg₂ _ (Finset.prod_congr rfl fun PP hPP => ?_) (Finset.prod_congr rfl fun PP hPP => ?_)
  · simp only [resChr, if_pos hPP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · simp only [resChr, if_neg (Finset.disjoint_right.1 hd hPP)]

theorem regroup (A B G q q' H : ℂ) : A * B⁻¹ * G * (q * q' * H) = A * q * ((B * q'⁻¹)⁻¹ * (G * H)) := by
  rw [mul_inv, inv_inv]; ring

theorem step_law {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (j n : ℕ) (hn : n = j + 1) (hj : j < D.R.m)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (hS : S.SigOK) (hT : T.SigOK)
    (ha : D.R.r ≤ S.rank) (hb : D.R.r ≤ T.rank) (ea : S.rank = D.R.r + j * D.R.t) (eb : T.rank = D.R.r + n * D.R.t)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hsS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hsT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {NS NT : ℕ}
    (hβS : IsSDFrame S βS ΛS NS) (hβT : IsSDFrame T βT ΛT NT)
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T (Lift.chrStep (L.mu t) L.eta n).1 (Lift.chrStep (L.mu t) L.eta n).2 om)
    {f₀ f : WO S T → ℂ}
    (hf : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT
      (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) (L.chi n) (L.Q t) (L.xiR t) f₀ f)
    (g0 : G0 L.Pg D.R.r) (κ : GA D S) (κ' : GA D T)
    (hκ : IsLevelLift S βS (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) g0 κ)
    (hκ' : IsLevelLift T βT (datY T.rank D.R.r D.R.t n hb L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) g0 κ') :
    (levChi S βS (flagL (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ)⁻¹ • om (κ, κ') f =
      (levChi T βT (flagL (datY T.rank D.R.r D.R.t n hb L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ')⁻¹ • f := by
  classical
  subst hn
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := hf
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have dS := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D S βS ΛS NS hβS
  have dT := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D T βT ΛT NT hβT
  obtain ⟨cS, fS, -⟩ := hβS
  obtain ⟨cT, fT, -⟩ := hβT
  obtain ⟨hd, htame⟩ := GlobalTheory.T.stepSplittingCharacters_tame_levelResidue D T0 L μ0 hL t ⟨j, hj⟩
  obtain ⟨t1, t2⟩ := htame e P hP he
  have tS : TameOn (Lift.chrStep (L.mu t) L.eta (j + 1)).1 e P (resChr L t (j + 1)) := by
    unfold Lift.chrStep; split_ifs
    · exact t2
    · exact t1
  have tT : TameOn (Lift.chrStep (L.mu t) L.eta (j + 1)).2 e P (resChr L t (j + 1)) := by
    unfold Lift.chrStep; split_ifs
    · exact t1
    · exact t2
  have hη : ResEta D L.eta 1 := resEta_one_of_step hW.resS hW.resT (by
    obtain ⟨c, hc⟩ := D.R.t_odd
    rw [ea, eb, add_mul, one_mul]
    generalize j * D.R.t = w
    omega)
  have kS := parLev_St hκ.2.1
  have kT := parLev_St hκ'.2.1
  have hvac := GlobalTheory.T.weilAction_vacuum_eq_residueDetChar_of_frameStabilizer D ψ S T _ _ om θ sS sT ΛS ΛT βS βT e _ _ _ f₀ hW hθ hS hT hsS hsT dS dT fS fT he tS tT
    (GlobalTheory.T.vacuum_fixed_nonsplit_place_of_characterFrame D L.C L.eta hL.eta hη ψ S T _ _ om ΛS ΛT hW dS dT) hv κ hκ.1 κ' hκ'.1 kS kT
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (GlobalTheory.ProjXCols.selfDual_isFullLattice S ΛS dS) (GlobalTheory.ProjXCols.selfDual_isFullLattice T ΛT dT) βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) (L.chi (j + 1)) y *
        omegaQ (L.Q t) D.R.r (L.xiR t) 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  have hsch := GlobalTheory.T.weilRep_schrodingerModel_half_substitution D ψ S T _ _ om ΛS ΛT e f₀ Tm hW dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) hinf hv.2.theta hTm
    κ κ' _ (GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action D S T ΛS ΛT βS βT dS.1 dT.1 fS fT κ κ' kS kT _) hvac _ hSB
  have hfe := hall Tm hTm
  have hne := levChi_ne_zero (β := βS)
    (flagL (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ
  rw [hfe]
  refine (congrArg _ hsch).trans ?_
  rw [smul_smul, ← map_smul, ← map_smul]
  congr 1
  funext x
  obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reduction D S T βS βT κ κ' kS kT x
  have i3 : IsHalf e (actO S T κ⁻¹ κ'⁻¹ x) ↔ IsHalf e x := by
    refine ⟨fun h => ?_, fun h => GlobalTheory.SplitHecke.isHalf_actO _ _ h⟩
    have := GlobalTheory.SplitHecke.isHalf_actO κ κ' h
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hx, if_pos ⟨i3.2 hx.1, i1.2 hx.2⟩]
    have a1 := GlobalTheory.T.typePlaces_localDatum_blockTriangular_law D _ _ D.R.r D.R.t j ha hb ea eb L.Pg (L.Q t) L.chi (L.xiR t)
      (fun PP => redFn βS PP (finE S κ)) (fun PP => redFn βT PP (finE T κ')) _ _
      (fun PP hP => parLev_g hκ.2.1 hP) (fun PP hP => parLev_g hκ'.2.1 hP)
      (fun PP hP => (congrFun hκ.2.2 ⟨PP, hP⟩).trans (congrFun hκ'.2.2 ⟨PP, hP⟩).symm) (fun PP _ => i2 hx.2 PP)
    have a2 := GlobalTheory.T.twistPlaces_localDatum_blockTriangular_law D _ _ D.R.r ha hb (L.Q t) (L.xiR t) 1
      (fun PP => redFn βS PP (finE S κ)) (fun PP => redFn βT PP (finE T κ')) _ _
      (fun PP hP => parLev_q hκ.2.1 hP) (fun PP hP => parLev_q hκ'.2.1 hP) (fun PP _ => i2 hx.2 PP)
    rw [zpow_one, zpow_one, Finset.prod_mul_distrib (s := L.Q t)
      (f := fun PP => ((L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn βS PP (finE S κ))) : ℂˣ) : ℂ)⁻¹)] at a2
    rw [vacScal_resChr L t (j + 1) hd βS βT P hP, mul_assoc, mul_mul_mul_comm,
      inv_mul_eq_iff_eq_mul₀ hne]
    refine (congrArg₂ _ a1 a2).trans ?_
    rw [levChi_flag_datY, levChi_flag_datY, Finset.prod_inv_distrib (s := L.Q t)
      (f := fun PP => ((L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn βT PP (finE T κ'))) : ℂˣ) : ℂ))]
    exact regroup _ _ _ _ _ _
  · rw [if_neg hx, if_neg fun h => hx ⟨i3.1 h.1, i1.1 h.2⟩, mul_zero, mul_zero]

theorem last_step_law : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωX → R.chain_vX → ∀ t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) g0 κ → IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ' → (levChi _ (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ • R.ωX t (κ, κ') (R.vX t) = (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ hω hv t g0 κ κ' hκ hκ'
  have hm := D.R.two_le_m
  exact step_law R.toLevCh hL t (D.R.m - 1) D.R.m (by omega) (by omega) hθ (D.sp.Y_sig _) D.sp.X'_sig (r_le_Y _) r_le_X
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl) D.sp.X'_rank
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY _ (by omega)) hL.βX (hω t) (hv t)
    g0 κ κ' hκ hκ'

end GlobalTheory.StepLaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

variable {D : D7}

theorem row_mat {S T : HSp D} (hS : S.gram = 1) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a e : AE D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjA S T βS βT a (partAt (cA D e) (finW S T y)) = Matrix.of fun i j => rowAdj T βT a e (y i) 0 j := by
  have hb : βS.val * (βS⁻¹).val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hg : (S.gram⁻¹).map (incA D) = 1 := by rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjA frMapAdj rowAdj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, hg, Matrix.one_mul]
  ext i j

  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
  partAt, finW, smul_eq_mul, Fin.sum_univ_one, map_sum]

theorem rowRed_zero (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) :
    rowRed T βT a e PP 0 = 0 := by
  funext j
  have h0 : rowAdj T βT a e 0 = 0 := by
    unfold rowAdj; ext i k; simp [Matrix.mul_apply, Matrix.smul_apply]
  have h1 : ∀ h, Formalism.L2.DIV.resS D.host.F PP (⟨0, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 :=
    fun _ => map_zero _
  simp [rowRed, redM, h0, h1]

theorem full_std (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem full_smul {r : ℕ} (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (L : Lt D.host.E r) (hL : L.FG)
    (hLs : Submodule.span D.host.E (L : Set (Fin r → D.host.E)) = ⊤) :
    (I • L).FG ∧ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) = ⊤ := by
  refine ⟨hL.smul (IsNoetherian.noetherian I), ?_⟩
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have htE : (t : D.host.E) ≠ 0 := fun h => ht0 (RingOfIntegers.ext (h.trans rfl))
  rw [eq_top_iff, ← hLs, Submodule.span_le]
  intro u hu
  have hu' : (t : D.host.E) • u ∈ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul ht hu)
  have := Submodule.smul_mem _ ((t : D.host.E)⁻¹) hu'
  rwa [smul_smul, inv_mul_cancel₀ htE, one_smul] at this

end GlobalTheory.LiftDat.RowKer

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

theorem rowRed_eq_zero_iff : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, ((∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftDat.rowRed T βT a e PP v = 0) ↔ v ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ _ _ e he a k₀ _ _ hgen h1 h2 h3 _ v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
    have hv0 : v = 0 := funext fun j => isEmptyElim j
    constructor
    · intro _; rw [hv0]; exact zero_mem _
    · intro _ PP _; funext j; exact isEmptyElim j
  let i0 : Fin S.rank := ⟨0, lt_of_lt_of_le hpos hn⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := Matrix.of fun i => if i = i0 then v else 0
  have hyrow : ∀ i, y i = if i = i0 then v else 0 := fun i => rfl
  have hy0 : y i0 = v := by rw [hyrow, if_pos rfl]
  have hy : ∀ L : Lt D.host.E T.rank, v ∈ L → y ∈ tens (stdL D.host.E S.rank) L := fun L hvL =>
    (GlobalTheory.SW.TensLat.mem_tens_stdL L y).2 fun k => by
      rw [hyrow]
      split_ifs
      · exact hvL
      · exact zero_mem _
  have hAo : ∀ L : Lt D.host.E T.rank, ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) L,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) L :=
    fun L o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hce : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
      rw [← map_mul, ← map_mul, hee])
  have hfinW : ∀ (L : Lt D.host.E T.rank) (z : Matrix (Fin S.rank) (Fin T.rank) D.host.E),
      z ∈ tens (stdL D.host.E S.rank) L → finW S T z ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L z hz => by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hz
  have hxL : ∀ L : Lt D.host.E T.rank, v ∈ L →
      partAt (cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L hvL => by
    have : partAt (cA D e) (finW S T y) = cA D e • finW S T y := by ext i j; rfl
    rw [this]; exact smul_mem_hatA_of_int (hAo L) hce (hfinW L y (hy L hvL))
  have hhalf : IsHalf (cA D e) (partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [partAt, Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
  obtain ⟨hc1, hc2⟩ := hgen _ hhalf
  have hred : ∀ PP, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) =
      fun i j => rowRed T βT a e PP (y i) j := by
    intro PP; rw [row_mat C.m.gS βS βT a e y]; rfl
  constructor
  · intro hR
    have hint := hc1.2 (hxL _ hv)
    have hall : ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) = 0 := by
      intro PP hPP
      rw [hred]
      funext i j
      rw [hyrow]
      split_ifs
      · exact congrFun (hR PP hPP) j
      · exact congrFun (rowRed_zero T βT a e PP) j
    have hxI := hc2.1 ⟨hint, hall⟩

    have hm : liftI Pg Q ⊔ conjI (liftI Pg Q) = ⊤ := Ideal.isCoprime_iff_sup_eq.1 h3
    have h1' : (1 : 𝓞 D.host.E) ∈ liftI Pg Q ⊔ conjI (liftI Pg Q) := by rw [hm]; exact Submodule.mem_top
    obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1'
    have hcP : ∀ PP ∈ Pg ∪ Q, conjI (liftI Pg Q) ≤ PP.asIdeal := by
      intro PP hPP x hx
      have h2' := mem_of_mem_conjI hx
      rw [liftI] at h2'
      have h3' : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
        hPP (Ideal.prod_le_inf h2')
      have h4' := mem_of_mem_conjI h3'
      have h5' : stO (stO x) = x := RingOfIntegers.ext (star_star _)
      rwa [h5'] at h4'
    have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
      intro PP hPP htm
      have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
    have hPQ : (Pg ∪ Q).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply h1
      rw [liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
    have ht0 : (t : D.host.E) ≠ 0 := by
      obtain ⟨PP, hPP⟩ := hPQ
      intro h
      apply htP PP hPP
      have : t = 0 := RingOfIntegers.ext (h.trans rfl)
      rw [this]; exact zero_mem _
    have htL : ∀ u ∈ C.X.Λ, t • u ∈ liftI Pg Q • C.X.Λ := fun u hu => Submodule.smul_mem_smul ht hu
    have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) := smul_mem_tens t htL (hy _ hv)
    have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
      GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
    have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
      have e2 : finW S T ((t : D.host.E) • y) =
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
          Matrix.transpose_smul]
      have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
      rw [e2, smul_smul, mul_assoc]
      have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
      rw [e4, mul_smul, ← e3]
      ext i j; rfl
    have hpe : partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [e1]; exact smul_mem_hatA_of_int (hAo _) hz1 (hfinW _ _ hty)

    have hpo := GlobalTheory.T.offIdempotent_finitePoint_mem_completedTensorLattice D S T Pg Q e he C.X.Λ y (hy _ hv)
    have hsum : finW S T y = partAt (cA D e) (finW S T y) + partAt e (finW S T y) +
        partAt (1 - e - cA D e) (finW S T y) := by
      ext i j; simp only [partAt, Matrix.add_apply, Matrix.map_apply]; ring
    have hfI : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [hsum]; exact add_mem (add_mem hxI hpe) hpo
    have hyI := ((GlobalTheory.Ker.HatLat.hatA_tens D S T C (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) (full_std _)
      (full_smul _ h2 C.X.Λ C.X.Λ_fg C.X.Λ_span)).2.1 y).1 hfI
    have := (GlobalTheory.SW.TensLat.mem_tens_stdL _ y).1 hyI i0
    rwa [hy0] at this
  · intro hvI PP hPP
    have h6 := (hc2.2 (hxL _ hvI)).2 PP hPP
    rw [hred] at h6
    funext j
    have h7 := congrFun (congrFun h6 i0) j
    rw [hy0] at h7
    exact h7

end GlobalTheory.LiftDat.RowKer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

theorem _root_.GlobalTheory.T.weilLatticeVacuum_eq_prod_splitPlace_factors : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsWeilDatumO ψ S T χS χT om →
    ∀ {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Pl D.host.E)), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w) →
    Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (P : Set (Pl D.host.E)) →
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ P, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f →
    om (g, h) f = (∏ w ∈ P, ((splitFacO χS χT (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) : Circle) : ℂ)) • f := by
  first | exact @GlobalTheory.LatStabScalar.om_eq_prod_splitFac | exact GlobalTheory.LatStabScalar.om_eq_prod_splitFac | (intros; apply GlobalTheory.LatStabScalar.om_eq_prod_splitFac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  first | exact @GlobalTheory.FockTransl.Jet.jet_eq_fock | exact GlobalTheory.FockTransl.Jet.jet_eq_fock | (intros; apply GlobalTheory.FockTransl.Jet.jet_eq_fock <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  first | exact @GlobalTheory.RowTest.realPts_ontoUni_haar_unique | exact GlobalTheory.RowTest.realPts_ontoUni_haar_unique | (intros; apply GlobalTheory.RowTest.realPts_ontoUni_haar_unique <;> assumption)
end
