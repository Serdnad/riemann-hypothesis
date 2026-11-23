module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle149
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulEqOfUnif
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle134
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle083
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle151
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle120
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle105
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.LvT.Built.Assemble

theorem sharpBound_stability_latticeColumnChain : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u),
    (∀ i, i ≤ D.R.m → Nonempty (Split (B.J.A i) B.J.T)) → B.Sees →
    (∀ i, i < D.R.m → ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧ Built.Dat.KerBar k ∧
      Built.Dat.KerP k) →
    Module.finrank ℚ B.E * D.R.N D.R.m + 1 < B.J.T → TwColumn.WtSigns B.ch → Conclusion5Sharp B.ch ∧ FormsStable B.ch := by
  intro D u B hsp hsee hker hT hW

  have hM : ∀ i (h : i ≤ D.R.m), ∃ M : PtModel B.ch i, Nonempty (B.Real i (hsp i h).some M) :=
    fun i h => GlobalTheory.T.exists_levelPrimePointModel_realisation D u B i (hsp i h).some
  let Lv : LevTie B.ch := fun i h => (hM i h).choose
  have hR : ∀ i (h : i ≤ D.R.m), B.Real i (hsp i h).some (Lv i h) := fun i h => (hM i h).choose_spec.some

  have hC : ∀ i (h : i ≤ D.R.m), ∃ Co : (Lv i h).Coord, Co.Ok ∧ (hR i h).ValIs Co :=
    fun i h => GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices D u B i (hsp i h).some (Lv i h) (hR i h) h hsee
  let Vt : ValTie Lv := fun i h => ⟨(hC i h).choose, (hC i h).choose_spec.1⟩

  have hk : ∀ i (h : i < D.R.m), ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧
      Built.Dat.KerBar k ∧ Built.Dat.KerP k := hker

  have hK : ∀ i (h : i < D.R.m), ∃ K : KerPt (Lv i h.le) (Lv (i + 1) h),
      K.TgtEq ∧ Built.Dat.KerIs (hR i h.le) (hR (i + 1) h) K (hk i h).choose :=
    fun i h => GlobalTheory.T.exists_pointKernel_realised_models D u B i (hsp i h.le).some (hsp (i + 1) h).some (Lv i h.le) (Lv (i + 1) h)
      (hR i h.le) (hR (i + 1) h) _ (hk i h).choose_spec.1
  let Kt : KerTie Lv := fun i h => (hK i h).choose
  have laws : KerLaws Vt Kt :=
    { tgt := fun i h => (hK i h).choose_spec.1
      dil := fun i h => GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.1
      uk := fun i h => GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.2.1
      bar := fun i h => GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.1
      intP := fun i h => IntPPass.intP_of_kerP D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.2 }
  have hF : FormsStable B.ch := formsStable_of_tgtEq D u B.ch Lv Kt laws.tgt
  have h4 : LevelChainUOperatorCommutation B.ch := levelChainUOperatorCommutation_of_pointPairLaw D u B.ch Lv Kt laws.tgt laws.uk
  have hst : StabUnit B.ch := StabOrder.stabUnit_of_chainIn B.ch B.I B.emb D.what₂.embLL B.hI rfl hT
  have hWb : WtBounds B.ch := wtBounds_of_nonneg D u B.ch hW.1 hW.2
  exact ⟨levelChainSharpColumnValuation_of_stability D u B.ch hF h4 (UKS.ukSharp D u B.ch Lv Vt Kt laws hst hWb) hWb, hF⟩

end GlobalTheory.LvT.Built.Assemble
end

section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

instance datNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

theorem kmap_dat : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

local instance representativeDatNumberField {B : Base} {X : PreX B.toPre} (I : TC B X)
    (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE


theorem _root_.GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

theorem kerP : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJet hKnown B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro w hw hs b b' d d' F hF
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := isTerm h u a hi b b' d d'
  rw [hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩]
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w
  have eA := AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hal := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hrat : GlobalTheory.KerT.RatTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ColIn.A I) u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (ColIn.A I) u i hX hPr
    h.sel_ok (h.T_mem u) (GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
      (B.R.m - 2) u i (ColIn.A I) hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi)
  rw [ColIn.A, eA] at hrat
  have hseen : Formalism.L2.Col.seenC (B.primes X) u ((I.rec7 l Z).plEq w) := @of_decide_eq_true _ (Classical.propDecidable _) hs
  have hPT : GlobalTheory.KerT.PTerm B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) ((I.rec7 l Z).plEq w) :=
    GlobalTheory.KerT.PAll.pTerm_of_std I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hrat _
    (GlobalTheory.KerT.PStd.pTerm_std hJet hKnown I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hal _ hseen)
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have e := hw
    unfold OverT at e
    rw [e] at h1
    exact h1
  letI : StarRing B.fields.E := B.fields.starE
  have key := hPT d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hT) F hF
  rw [ColIn.A, eA]
  have eS : ∀ τ, (dat I l Z u a).ch.C.sDiv i τ = -((B.wts.lamTrue u (i + 1) τ).detShift) := fun τ => by
    have e1 := (KMap.sSharp_eq (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi τ).2
    have e2 := GlobalTheory.GO.ChSrc.trueWt_detShift_succ (X := B.fields) (B.wts.hc u) hi τ
    have e3 := congrFun (GlobalTheory.GO.ChSrc.trueWt_eq B.wts u (i + 1)) τ
    refine e1.trans ?_
    rw [← e3, e2, neg_neg]
  have eE : (((I.rec7 l Z).R.f * (I.rec7 l Z).R.N i : ℕ) : ℤ) + ∑ τ, (dat I l Z u a).ch.C.sDiv i τ =
      ((B.fields.f * B.R.N i : ℕ) : ℤ) - ∑ τ, (B.wts.lamTrue u (i + 1) τ).detShift := by
    rw [Finset.sum_congr rfl (fun τ _ => eS τ), Finset.sum_neg_distrib, B.fields_f, sub_eq_add_neg]
    rfl
  rw [eE]
  exact key

end GlobalTheory.LvT.Built.TrueLaws
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localBasisRepLattice_integralCoords_spec : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl), Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) (GlobalTheory.PerQ.Co.bP I u a w c) ∧ (∀ x, iniH (N_m_succ B.R) (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) = ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧ (∀ x, (I.perIn u a).tz * (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) = x (Br.iL (N_m_succ B.R))) ∧ Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) (GlobalTheory.PerQ.Co.bM I u a w c) := by
  first | exact @GlobalTheory.PerQ.Co.usage₉ | exact GlobalTheory.PerQ.Co.usage₉ | (intros; apply GlobalTheory.PerQ.Co.usage₉ <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

theorem mem_infSpan (φ : UA E n → ℂ) (k : infU E n) : RU E n k φ ∈ infSpan φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem infSpan_stable (φ : UA E n → ℂ) (k : infU E n) : ∀ ψ ∈ infSpan φ, RU E n k ψ ∈ infSpan φ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, rfl⟩ := h
    rw [RU_RU]
    exact mem_infSpan φ (k * l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  | smul c _ _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

def finStab (φ : UA E n → ℂ) : Subgroup (finU (E := E) (n := n)) where
  carrier := {k | RU E n k φ = φ}
  one_mem' := by
    change RU E n 1 φ = φ
    rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb => by
    change RU E n (a.1 * b.1) φ = φ
    rw [← RU_RU, show RU E n b φ = φ from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change RU E n (a.1)⁻¹ φ = φ
    conv_lhs => rw [← show RU E n a φ = φ from ha]
    rw [RU_RU, inv_mul_cancel, map_one]; rfl

theorem isAutFormU_of_mem (hc : ∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (ψ : UA E n → ℂ) (hψ : ψ ∈ infSpan φ) : IsAutFormU ψ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      exact hφ.cont.comp (continuous_mul_const l.1)
    | zero => exact continuous_const
    | add _ _ _ _ h₁ h₂ => exact h₁.add h₂
    | smul c _ _ h => exact h.const_smul c
  · intro γ hγ g
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      change φ (γ * g * l) = φ (g * l)
      rw [mul_assoc, hφ.left γ hγ]
    | zero => rfl
    | add _ _ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]
    | smul c _ _ h => simp only [Pi.smul_apply, h]
  · refine Subgroup.isOpen_mono (H₁ := finStab φ) (H₂ := finStab ψ) (fun k hk => ?_) hφ.level
    change RU E n k ψ = ψ
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [RU_RU, ← hc l k.1 k.2, ← RU_RU, show RU E n k φ = φ from hk]
    | zero => rw [map_zero]
    | add _ _ _ _ h₁ h₂ => rw [map_add (f := _), h₁, h₂]
    | smul c _ _ h => rw [map_smul, h]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := infSpan φ) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact infSpan_stable φ k ψ hψ

def coeff (φ : UA E n → ℂ) (l : infSpan φ →ₗ[ℂ] ℂ) : infSpan φ →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun k => l.comp ((RU E n k).restrict (infSpan_stable φ k))

theorem continuous_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    Continuous fun k : infU E n => l ⟨RU E n k φ, mem_infSpan φ k⟩ := by
  have := hφ.kfin
  refine l.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun g => ?_) _)
  exact hφ.cont.comp (continuous_const.mul continuous_subtype_val)

theorem finite_coeff {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (l : infSpan φ →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n =>
      l ⟨RU E n (x * k : infU E n) φ, mem_infSpan φ (x * k)⟩)) := by
  have := hφ.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coeff φ l)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨_, mem_infSpan φ k⟩, funext fun x => congrArg l (Subtype.ext ?_)⟩
  exact RU_RU x.1 k.1 φ

theorem exists_poly_mul_autForm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ)
    (hφ : IsAutFormU φ) : ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ),
      (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}
        ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  have := hφ.kfin
  let b := Module.finBasis ℂ (infSpan φ)
  refine ⟨_, fun i k => b.coord i ⟨RU E n k φ, mem_infSpan φ k⟩, fun i => (b i).1, fun i => ⟨?_, ?_⟩, fun k g => ?_⟩
  · exact GlobalTheory.UnitaryBC.rightFinite_mem_poly E n _ (continuous_coeff hφ _) (finite_coeff hφ _)
  · exact isAutFormU_of_mem (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.1 hφ _ (b i).2
  · have h := congrArg (fun v : infSpan φ => v.1 g) (b.sum_repr ⟨RU E n k φ, mem_infSpan φ k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

end GlobalTheory.UnitaryDecomp

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU (E := E) (n := n) → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU (E := E) (n := n)), IsOpen (V : Set (finU (E := E) (n := n))) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU (E := E) (n := n) | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  choose V hVo hV using he
  have haf : ∀ g : finU (E := E) (n := n), a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU (E := E) (n := n), b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k : finU (E := E) (n := n) | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
end
