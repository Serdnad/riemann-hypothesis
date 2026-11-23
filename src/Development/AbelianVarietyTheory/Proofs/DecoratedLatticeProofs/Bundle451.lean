module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle369
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle421
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle428
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecLawBoth



open Classical in
theorem stepLevLawT (D : D7) (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D) (hs : s.Is c k)
    (hs' : s'.Is c (k + 1)) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (hW : IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : WO s.V s'.V → ℂ)
    (hv : IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) :
    ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ω (1, κ) f = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ • f := by
  intro κ hκ
  obtain ⟨hr, ξ1, hL⟩ := hs.lev
  obtain ⟨hr', ξ2, hL'⟩ := hs'.lev
  rw [hL] at hv
  rw [hL'] at hκ ⊢
  have ea : s.V.rank = D.R.r + k * D.R.t := hs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hs'.rank
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← Finset.union_empty c.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k hk
  have hlev : Lev.finE s'.V κ ∈ lev D.sp.cm s'.V.gram s'.β
      (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B) := hκ.2
  have sg : Lev.finE s.V 1 ∈ St s.β := by rw [map_one]; exact Subgroup.one_mem _
  have sh : Lev.finE s'.V κ ∈ St s'.β := parLev_St hlev.1
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) hs.selfDual hs'.selfDual hs.frame hs'.frame hf he'
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT (Subgroup.one_mem _) hκ.1 sg sh
  set H : ∀ PP : Pl D.host.E, GL (Fin s'.V.rank) (kP PP) := fun PP => redFn s'.β PP (Lev.finE s'.V κ) with hH
  have hPeq : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P = c.P := by simp [Lev.datY]
  have hcg : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).cg = c.chi := by simp [Lev.datY]
  have hP : (fun PP : ↥c.Pg => upperLeftBlock hr' (H PP.1)) ∈ c.P.H := by
    have := hlev.2
    rw [hPeq] at this
    exact this
  have hBT : ∀ PP ∈ c.Pg, H PP ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hPP => parLev_g hlev.1 hPP
  have h1' : ω (1, κ) f₀ = ((∏ PP ∈ c.Pg, (c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)))⁻¹ : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_one, one_mul, hH]
  have hoT := GlobalTheory.T.levelPlacesDatum_inv_left_mul_target_level D s.V.rank s'.V.rank D.R.r D.R.t k hr hr' ea eb c.Pg c.P c.chi ξ1 H hBT hP
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ 1 κ
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame 1 κ sg sh) _
    ((((c.P.chi ⟨_, hP⟩ * ∏ PP ∈ c.Pg, ∏ i ∈ Finset.range (k + 1),
        c.chi (i + 1) PP (dBlk (blkOf D.R.r D.R.t) (i + 1) (H PP)))⁻¹ *
      ∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ)) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β 1 κ sg sh x
      have i0 : IsHalf e (actO s.V s'.V 1⁻¹ κ⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V 1 κ x ▸ GlobalTheory.SplitHecke.isHalf_actO 1 κ H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), StepLevLaw.omegaQ_empty, StepLevLaw.omegaQ_empty,
          mul_one, mul_one]
        simp only [map_one, redFn_one, Units.val_one, Matrix.mul_one]
        exact hoT (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2]
  congr 1
  have hchi : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P.chi ⟨_, hlev.2⟩ =
      c.P.chi ⟨_, hP⟩ := rfl
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hlev.2, hchi]
  simp only [Lev.datY, ↓reduceIte, Finset.prod_empty, mul_one]
  rw [Finset.prod_inv_distrib, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [mul_comm _ (∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP))), inv_mul_cancel_left]

theorem vecLaw : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L)
    (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  refine ⟨fun κ hκ => (StepLevLaw.stepLevLaw D c hc ⟨k, hk⟩ s s' hs hs' p.ω hp.weil ξ f₀ p.f hv κ hκ).2, ?_⟩
  exact stepLevLawT D c hc k hk s s' hs hs' p.ω hp.weil ξ f₀ p.f hv

end GlobalTheory.ChainOnto.StepVecLawBoth

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverSwap

variable {D : D7}

theorem eq_zero_of_two {v v' : Pl D} (hne : v ≠ v') {z : AE D} (h : z ∈ idAt D (· = v))
    (h' : z ∈ idAt D (· = v')) : z = 0 := by
  have hc : compAt D v z = 0 := by
    unfold idAt at h'
    exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h').2 ⟨v, hne⟩
  rw [GlobalTheory.FinPl.Model.eq_single h, hc]
  exact (GlobalTheory.AdelicU.Supp.singleTens D.host.E v).map_zero'

theorem cA_mem_idAt {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem symplO_eq_zero_of_ne {v v' : Pl D} (hne : v ≠ v') {S T : HSp D} {x y : WO S T} (hx : MxAt (· = v) x)
    (hy : MxAt (· = v') y) : symplO S T x y = 0 := by
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 :=
      eq_zero_of_two hne (Ideal.mul_mem_left _ _ (hx d a)) (Ideal.mul_mem_right _ _ (cA_mem_idAt (hy c b)))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem comb_comm {v v' : Pl D} (hne : v ≠ v') (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {c c' : WO S T →₀ ℂ}
    (hc : CombAt (· = v) c) (hc' : CombAt (· = v') c') (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f) = GlobalTheory.SeeSaw.comb ψ S T c' (GlobalTheory.SeeSaw.comb ψ S T c f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.1 c c' (fun x hx y hy => symplO_eq_zero_of_ne hne (hc x hx) (hc' y hy)) f

end GlobalTheory.FinPl.OverSwap

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.OverSwap in
theorem overSwap : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  intro D k _ _ _ _ p p' n n' m m' _ _ _ _ _ _ _ _ ψ hψ hp hp' hne S T α β α' β' LS LT f₀ g h Ψ Ψ' hv' hO1 hO2
  obtain ⟨hLS, hLT, hf₀, hΨ, -⟩ := id hO1
  obtain ⟨-, -, hg, hΨ', -⟩ := id hO2
  obtain ⟨c, hc, hcO⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hψ hp S T α β LS LS LT LT hLS hLT hLS hLT).2 Ψ hΨ
  obtain ⟨c', hc', hcO'⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p' m m' ψ hψ hp' S T α' β' LS LS LT LT hLS hLT hLS hLT).2 Ψ' hΨ'
  have eg : g = GlobalTheory.SeeSaw.comb ψ S T c f₀ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β LS LT hLS hLT f₀ hf₀).1 Ψ hΨ).unique hO1 (hcO f₀ hf₀)
  have eh : h = GlobalTheory.SeeSaw.comb ψ S T c' g :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT g hg).1 Ψ' hΨ').unique hO2 (hcO' g hg)
  have hO3 := hcO' f₀ hv'
  have hvac : Vac ψ S T LS LT (· = p.v) (GlobalTheory.SeeSaw.comb ψ S T c' f₀) :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT f₀ hv').2.1 Ψ' _ hO3).2 LS LT (· = p.v)
      (fun e => hne e.symm) hf₀
  refine ⟨_, hO3, ?_⟩
  have e : h = GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f₀) := by
    rw [eh, eg, comb_comm hne ψ hc hc']
  rw [e]
  exact hcO _ hvac

end GlobalTheory.FinPl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRebase

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem zero_placeModel {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 0 0 := by
  refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?_⟩
  · funext w; simp [heisO]
  · funext w; simp [heisO]
  · simp

theorem local_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (p : GlobalTheory.FinPl.Pl D)
    (hsp : ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (hu1 : ∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧
      incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p))
    (hu2 : ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) :
    ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧ (f ≠ 0 → comb ψ S T c f ≠ 0) := by
  obtain ⟨e, ε, he, hε, hs⟩ := hsp
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D p e ε he hε hs
  have hU : q.UnitAA := by
    unfold GlobalTheory.FinPl.SplitPt.UnitAA
    rw [hq]
    exact ⟨hu1, hu2⟩
  rw [← hq]
  obtain ⟨glS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q S (Fin S.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  obtain ⟨glT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q T (Fin T.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  let α : GlobalTheory.FinPl.Frame q S (Fin S.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T (Fin T.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glT, hT1, hT2⟩
  obtain ⟨ΛS, hl1, hαN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α N hN
  obtain ⟨ΛT, hl2, hβN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β N' hN'
  obtain ⟨ΛSm, hl3, hαM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α M hM
  obtain ⟨ΛTm, hl4, hβM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β M' hM'
  haveI : ΛS.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α N hN ΛS hαN
  haveI : ΛT.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β N' hN' ΛT hβN
  haveI : ΛSm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α M hM ΛSm hαM
  haveI : ΛTm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β M' hM' ΛTm hβM
  have R := GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D _ q (Fin T.rank) (Fin S.rank) ψ hψ hU S T α β M N M' N' hM hM' hN hN'
  obtain ⟨c, hc, hov⟩ := R.2 (GlobalTheory.LatPair.latInd ΛS ΛT) (GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hO := hov f hf
  have h1 := R.1 ΛS ΛT hαN hβN f _ hO
  refine ⟨h1.1, fun hf0 hg => hf0 ?_⟩
  obtain ⟨⟨Tm, hTm⟩, -⟩ := hO.2.2.2.2
  have hOf : GlobalTheory.FinPl.Over ψ α β M M' f (GlobalTheory.LatPair.latInd ΛSm ΛTm) f := by
    refine ⟨hM, hM', hf, GlobalTheory.LatPair.latInd_mem_SB _ _, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    rw [GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D _ q _ _ S T α β M M' hM hM' hU ΛSm ΛTm hαM hβM]
    have hv := hT'.vac
    rw [one_smul] at hv
    exact hv.symm
  have hN0 := h1.2 _ _ hOf
  rw [hg] at hN0
  have := hN0.2.2.2.2.2 0 (zero_placeModel ψ S T _ _)
  simpa using this

end GlobalTheory.VacRebase

namespace GlobalTheory.VacRebase

theorem idAt_mono' {D : D7} {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) :
    GlobalTheory.FinPl.idAt D P ≤ GlobalTheory.FinPl.idAt D P' := by
  unfold GlobalTheory.FinPl.idAt
  exact inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hp => w.2 (h _ hp)⟩ le_rfl)

theorem foldr_vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) (X : GlobalTheory.FinPl.Pl D → Prop) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p)) → (∀ p ∈ l, ¬ X p) → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT X f → GlobalTheory.FinPl.Vac ψ S T LS LT X (l.foldr (fun p g => comb ψ S T (c p) g) f) := by
  intro l
  induction l with
  | nil => intro _ _ f hf; exact hf
  | cons p l ih =>
    intro hc hX f hf
    rw [List.foldr_cons]
    have hd : ∀ x, x = p → ¬ X x := fun x hx => hx ▸ hX p List.mem_cons_self
    exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = p) X hd).2.1 (c p) (hc p List.mem_cons_self)).2 LS LT _
      (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun x hx => hX x (List.mem_cons_of_mem _ hx)) f hf)

theorem foldr_vac_on {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), l.Nodup → (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p) ∧ ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T (c p) f) ∧
        (f ≠ 0 → comb ψ S T (c p) f ≠ 0)) → ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ l) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ l) (l.foldr (fun p g => comb ψ S T (c p) g) f) ∧
        (f ≠ 0 → l.foldr (fun p g => comb ψ S T (c p) g) f ≠ 0) := by
  intro l
  induction l with
  | nil =>
    intro _ _ f hf
    refine ⟨⟨hf.1, ?_⟩, fun h => h⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => absurd hx List.not_mem_nil)]
    exact hf.2
  | cons p l ih =>
    intro hnd hc f hf
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hd : ∀ x, x = p → ¬ x ∈ l := fun x hx => hx ▸ hpl
    have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· = p) (· ∈ l) hd
    have hfun : (fun x => x ∈ p :: l) = fun x => x = p ∨ x ∈ l := by
      funext x; exact propext List.mem_cons
    rw [hfun] at hf ⊢
    have hf2 := (DC.2.2.2.2 M M' f hM hM').1 hf
    obtain ⟨ihv, ihn⟩ := ih (List.nodup_cons.1 hnd).2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) f hf2.2
    have hgp := foldr_vac_off hψ c (· = p) M M' l (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
      (fun x hx hxp => hpl (hxp ▸ hx)) f hf2.1
    obtain ⟨hcp, hloc⟩ := hc p List.mem_cons_self
    obtain ⟨hv1, hn1⟩ := hloc _ hgp
    rw [List.foldr_cons]
    refine ⟨(DC.2.2.2.2 N N' _ hN hN').2 ⟨hv1, (DC.2.1 (c p) hcp).2 N N' _ ihv⟩, fun h0 => hn1 (ihn h0)⟩

end GlobalTheory.VacRebase

theorem GlobalTheory.VacRebase.rebase_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  intro D ψ hψ S T M N M' N' Q hM hN hM' hN' hQ hoff
  have hc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ (p ∈ Q → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧
        (f ≠ 0 → comb ψ S T c f ≠ 0)) := by
    intro p
    by_cases hp : p ∈ Q
    · obtain ⟨h1, h2, h3⟩ := hQ p hp
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.VacRebase.local_step hψ hM hN hM' hN' p h1 h2 h3
      exact ⟨c, hc1, fun _ => hc2⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hp⟩
  choose c hc1 hc2 using hc
  let l := Q.toList
  have hmem : ∀ p, p ∈ l ↔ p ∈ Q := fun p => Finset.mem_toList
  refine ⟨convList ψ S T (l.map c), ?_, fun f hf => ?_⟩
  · refine support_convList (p := GlobalTheory.FinPl.MxAt (· ∈ Q)) (fun i j => Ideal.zero_mem _)
      (fun x y hx hy i j => by rw [Matrix.add_apply]; exact Ideal.add_mem _ (hx i j) (hy i j)) ?_
    intro c' hc' x hx i j
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    exact GlobalTheory.VacRebase.idAt_mono' (fun v hv => hv ▸ (hmem p).1 hp) (hc1 p x hx i j)
  rw [comb_convList]
  have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· ∈ l) (· ∉ l) (fun x h1 h2 => h2 h1)
  have hfun : (fun x => x ∈ l ∨ x ∉ l) = fun _ => True := by
    funext x; exact propext ⟨fun _ => trivial, fun _ => em _⟩
  have hf' : GlobalTheory.FinPl.Vac ψ S T M M' (fun x => x ∈ l ∨ x ∉ l) f := by rw [hfun]; exact hf
  obtain ⟨hin, hout⟩ := (DC.2.2.2.2 M M' f hM hM').1 hf'
  obtain ⟨v1, n1⟩ := GlobalTheory.VacRebase.foldr_vac_on hψ hM hN hM' hN' c l (Finset.nodup_toList Q)
    (fun p hp => ⟨hc1 p, hc2 p ((hmem p).1 hp)⟩) f hin
  have hout' : GlobalTheory.FinPl.Vac ψ S T N N' (· ∉ l) f := by
    refine ⟨hout.1, ?_⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => by
      obtain ⟨a, b⟩ := hoff x (fun h => hx ((hmem x).2 h)); exact ⟨a.symm, b.symm⟩)]
    exact hout.2
  have v2 := GlobalTheory.VacRebase.foldr_vac_off hψ c (· ∉ l) N N' l (fun p _ => hc1 p) (fun p hp h => h hp) f hout'
  refine ⟨?_, n1⟩
  rw [← hfun]
  exact (DC.2.2.2.2 N N' _ hN hN').2 ⟨v1, v2⟩
end

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

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

theorem fock_vac_moved_top : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (weil_omT (pk W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (isVacO_vacT (pk W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1

end GlobalTheory.TopMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_places_finite : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Set.Finite {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} := by
  first | exact @GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | exact GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | (intros; apply GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattice_frame_chain : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((pk W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := by
  first | exact @GlobalTheory.Fam.sdY_frames | exact GlobalTheory.Fam.sdY_frames | (intros; apply GlobalTheory.Fam.sdY_frames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  first | exact @GlobalTheory.LocMod.indicator_vac | exact GlobalTheory.LocMod.indicator_vac | (intros; apply GlobalTheory.LocMod.indicator_vac <;> assumption)
end
