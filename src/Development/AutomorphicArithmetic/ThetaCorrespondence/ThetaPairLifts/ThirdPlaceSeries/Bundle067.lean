module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle063
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Formalism.LocalToGlobal.Divisibility.Bundle004
public import Formalism.LocalToGlobal.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle852
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle935
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle768
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle928
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle048
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle001
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho


theorem readTw_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (a : (withLoc b.L).nd.Loc) :
    ReadTw (withLoc b.L) a := by
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  refine ⟨(castQ hpq).symm.toRingHom.comp (((withLoc b.L).naut.iotaQ a).comp
      (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))),
    (castQ hpq).trans ((withLoc b.L).naut.iotaQC a), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  · intro x
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
        ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
        (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
      fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
        (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  · intro y
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y))))) = _
    rw [RingEquiv.apply_symm_apply, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    rfl
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho


theorem sideB_built_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (ψ : D'.nd.Loc → NC.HC D'.host.E) (hψ : ∀ a, NC.ReadC D'.nd.plOm.1 (D'.ntw.psiL a) (NC.iotaC D' a) (ψ a) 0)
    (cf : CharFrame D') (hcf : HEq cf (cfL b.L b.cf))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host) (hPq : HEq Pq b.Pq)
    (S : RatDat D'.ntw) (hS : HEq S (ratL b.L b.S))
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S.WL j)) (hhL : HEq hL' b.hL)
    (eig : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (heig : HEq eig b.eig)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq θ b.θ) :
    ∃ Rw : RowSide D', HEq Rw.locR b.A.row.locR ∧ Nonempty (SideB D' cf Rw b.low Pq S hL' eig θ) ∧
      (∀ a σ v, IsSplitPl D'.host v → D'.naut.locW a σ v = Rw.locR σ v) := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hPq
  obtain rfl := eq_of_heq hS
  obtain rfl : hL0 = hL' := (eq_of_heq hhL).symm
  obtain rfl : eig0 = eig := (eq_of_heq heig).symm
  obtain rfl : θ0 = θ := (eq_of_heq hθ).symm
  obtain ⟨Rw, hRw, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf0 A.row low Pq S0 hL0 eig0 θ0 Bs L ψ hψ
  refine ⟨Rw, hRw, ⟨Bs'⟩, fun a σ v _ => ?_⟩
  have e : Rw.locR = A.row.locR := eq_of_heq hRw
  rw [e]
  exact Au.locW a σ v

theorem isKsForm_of_built_heq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (S : RatDat D'.ntw)
    (hS : HEq (ratL b.L b.S) S) (h : ∀ j, 1 ≤ j → j ≤ b.D.R.m → (b.S.A j).IsKsForm) :
    ∀ j, 1 ≤ j → j ≤ D'.R.m → (S.A j).IsKsForm := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hS
  exact h
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
end GlobalTheory.RowTriple.Lay
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top4
open Formalism.L2.Top3
section StageB
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel} {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP}
def kernelChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel :=
  fun Fm hc x hx h i => by
    exact { Ks := (selB Fm hc x hx h i).T.Q.c.F }
def indefiniteRealisationChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) :=
  fun Fm hc x hx h i => (selB Fm hc x hx h i).Q
def SingleMapCondition (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x)
    (i : Fm.Ix x) : Prop :=
  let B := selB Fm hc x hx h i
  letI := B.alg
  ∀ j, Formalism.IndefR.FWT.OneMapRowR B.T B.Q.Rl.toRealDat B.κ B.v₀ B.O (Formalism.IndefR.phEff B.Q.Rl) j
end StageB
section TwPl
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem real_t_tw_pl_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.twPl = P.S0.Tw :=
  tw_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tie_tw_rec_of_real_rec {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
    (hs : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) : TieTwRec L P.S0.Tw := by
  intro y hy
  rw [← _root_.Formalism.L2.Top4.real_t_tw_pl_eq Q] at hy
  have h := (Qr.tw_iff (D.plEq.symm y)).1 (by simpa using hy)
  exact ⟨hs _ h, h⟩
end TwPl
end Formalism.L2.Top4
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowCuspFromLift
theorem exists_isCuspParam_of_liftAt_good_index : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa →
    D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  intro D Rw hP j σ π μ Pa hL hR hB hm hg
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := hP.tie0.1
  have hAut : SumRepresentations.At.TieAut D.nd D.naut := hP.tie0.2.1
  have hC := hP.cancel
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain ⟨hB1, -, hB3, hB4, hB5, hB6⟩ := hB
  have hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩
  have hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r := by
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    have hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV := by
      rw [← hB3]; unfold rankIso; exact ((hperm.map _).sum_eq).symm
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hloc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have e1 := hB4 w hw
    rw [hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append,
      (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)
        (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w)
        (D.naut.locG_dim _ w)).1] at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]
      exact GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3,
      (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]
  obtain ⟨π', hπ'⟩ := GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc
  obtain ⟨q, hLq, hq⟩ := List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')
  obtain ⟨a, ρ, d⟩ := q
  simp only [Formalism.BasicNotions.Part.mk.injEq] at hq
  obtain ⟨rfl, h2, rfl⟩ := hq
  have h2' := eq_of_heq h2
  subst h2'
  have hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂ := hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)
  have hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have hs := hloc w hw
    rw [hπ', SphericalInertData.isoLoc_single] at hs
    exact hs
  have hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧
      D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun z => -z) := by
    intro τ
    have eA := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)
    have eB := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).1] at eA
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).2] at eB
    have fA := add_right_cancel eA
    have fB := add_right_cancel eB
    rw [hLq, isoInf_one] at fA fB
    have gA := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)
    have gB := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)
    rw [D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]
    simp [Multiset.map_map, Function.comp_def]
  refine ⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit,
    fun w hw => ?_, fun w hw hw' => ?_, hinf⟩
  · have hu := (hB5 w hw).1
    rw [GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq,
      SphericalInertData.isoLoc_single] at hu
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)
  · rw [hsplit w hw]
    exact (hR w hw hw').1
end GlobalTheory.RowCuspFromLift
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
theorem part_norm_o_alt (D : D7) (ht : SumRepresentations.tie0 D) (hT : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) {j : ℕ} {π : D.nbc.AU j}
    {Pa : List (Part D.naut.CG)} (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa)
    (w : PlE D.host) (hu : D.naut.unr (D.naut.locG p.π w)) :
    ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro α hα
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤
      D.nbc.infW j (D.nbc.wtAU j π) τ := fun τ => by
    rw [← hB.2.2.2.2.2 τ]; exact mem_isoInf D Pa p hp hd1 τ
  have hW := fun τ => D.nbc.infW_alg j (D.nbc.wtAU j π) τ
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
theorem split_step_o_alt (D : D7) (Rw : RowSide D) (hL : _root_.GlobalTheory.HeightCounting.Up.ParityLaws D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j)
    (μ : D.naut.CG 1) (Pa : List (Part D.naut.CG)) (hA : LiftAt D Rw j σ π μ) (hR : RowLoc D Rw σ)
    (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hg : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k))
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG μ w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := by
  have hT := hL.tie0
  have hLP := hT.1
  have hAut := hT.2.1
  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  obtain ⟨m, hm⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmt := (_root_.UpperTheory.GalN.tempo' hL.temp 1 μ le_rfl hA.csd (mu_ralg D Rw j σ π μ hA) w).1 rfl
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 hmt m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp
  have hV := hA.loc w hs
  have hiso := GlobalTheory.MuBlock.frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.nbc.locAU j π w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.nbc.locAU j π w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) := by
    rw [hV, (hLP w (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w))
      (Rw.locR σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (Rw.locR σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := GlobalTheory.MuBlock.frobEig_spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w hμ
  dsimp only at hmu
  have hVe : D.naut.frobEig (D.nbc.locAU j π w) =
      (D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add (f := _)]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := UpperTheory.GalN.string_count (Formalism.ConjugateSelfDual.normV w) D.R.t
    (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := (hR w hs hg).2 α hα
      rwa [GlobalTheory.MuBlock.absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have k := _root_.GlobalTheory.MuBlockLoc.part_norm_o_alt D hT hL.temp hB p hp w (hPa p hp)
      refine ⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα =>
        (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩
end GlobalTheory.MuBlockLoc
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.HeightCounting.Up.ParCopy

theorem parIn_of_nTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (_root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

theorem exists_mtInput_of_nTrue {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩
end GlobalTheory.HeightCounting.Up.ParCopy
namespace GlobalTheory.HeightCounting.Up
end GlobalTheory.HeightCounting.Up
end
end
