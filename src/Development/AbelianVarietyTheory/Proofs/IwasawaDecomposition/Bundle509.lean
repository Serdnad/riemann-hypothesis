module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle280
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle308
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle504
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem exists_lvTied_of_std {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type)
    (chOf : (I.stp u a i).Cl → Ch)
    (lat' : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hlat : lat' = I.latAt u a i)
    (res' : ∀ v : (I.atT l u a).vT, 𝓞 B.host.E →+* (I.atT l u a).Fv v) (hres : res' = I.resT l u a)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (lat' c.1)))
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi)
    (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal})
    (hK : ∃ k, I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hY : ∀ y, (eY y).1 = y.1) (hV : ∀ v, (eV v).1 = v.1.under (𝓞 B.host.F))
    (hkill : ∀ β, FunKilled (K β).lev (X.piT u)) :
    ∃ L : LevelCompatibleLattices (D := I.rec7 l Z) (I.fm l u a) (B.T u) res' i hi (fun c => latCrd (I.rec7 l Z) i hi (lat' c)),
      ((∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.N), L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
        ∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.dnN v), L.prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
      (∃ fMe, FvTieG L eV K fMe) ∧ UpNatTieG L eY eV K ∧ DnNatTieG L eY eV K := by
  subst hlat hres
  obtain ⟨L, hL⟩ := GlobalTheory.Mem.Col2.TC.exists_level_projections I hOk hP l Z u a i hi
  have hK' : I.ReadsK l Z u a i hi chOf K := hK
  obtain ⟨fMe, hf, -⟩ := GlobalTheory.Mem.Col2.LevFun.fvTieG I hOk hP l Z u a i hi bad Ch chOf K eV L hK' hV hL
    (fun β v h t t' e => hkill β v h t t' e)
  exact ⟨L, hL, ⟨fMe, hf⟩, GlobalTheory.Mem.Col2.UpChart.upNatTie I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK' hY hV hL,
    GlobalTheory.DnMove.dnNatTieG_cols I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK' hY hV hL⟩



noncomputable def lvSameMu0 {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l)
    (u : B.Word) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m)
    (a : TwAtT (I.tw l l0 Z) u (I.rec7 l Z).what₂.mu0) (hV : a.eVT = Equiv.refl _)
    (hR : ∀ v r, (a.eFv v).symm (I.resT l u I.mu0 (a.eVT v) r) = I.resT l u I.mu0 v r) :
    LvSame a i (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i) (Formalism.L2.Herm.yCast (I.rec7 l Z) u i) ((I.tw l l0 Z).eMu0 u i hi) := by
  obtain ⟨eVT, eFv, psiT, rhoT, Mu0, duStar, Dstar, GamP, tauOf, seenP⟩ := a
  dsimp only at hV hR
  subst hV
  have hE : ∀ v x, eFv v x = x := by
    intro v x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (congrArg (eFv v) (hR v r)).symm.trans ((eFv v).apply_symm_apply _)
  exact
    { eLv := fun v c => AddEquiv.refl _
      eLv_smul := fun v c r x => by rw [hE]; rfl
      fv := fun v c x => by rw [hE]; rfl
      up := fun v c x _ => rfl
      upT := fun v c x _ h y => rfl
      eLk := fun v c => AddEquiv.refl _
      eLk_smul := fun v c r x => by rw [hE]; rfl
      te := fun v c => rfl
      dn := fun v c g g' hg _ => by
        obtain rfl : g = g' := LinearMap.ext fun x => (hE v (g x)).symm.trans (hg x)
        rfl
      dnT := fun v c g g' hg _ h y => by
        obtain rfl : g = g' := LinearMap.ext fun x => (hE v (g x)).symm.trans (hg x)
        rfl
      dil := fun v r c => by
        have key : ∀ q : (((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v)ˣ, (q : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) = (r : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) →
            ((I.tw l l0 Z).fm u (I.rec7 l Z).what₂.mu0).dil i v r (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i c) =
              Formalism.L2.Herm.clsCast (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dil i v q c) := by
          intro q hq
          obtain rfl : q = r := Units.ext hq
          rfl
        refine key _ ?_
        exact hE v _
      dilT := fun v r c h y => by
        have key : ∀ q : (((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v)ˣ, (q : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) = (r : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) →
            ((I.tw l l0 Z).fm u (I.rec7 l Z).what₂.mu0).dilT i v r (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i c)
              (fun z => h ((Formalism.L2.Herm.yCast (I.rec7 l Z) u i).symm z)) (Formalism.L2.Herm.yCast (I.rec7 l Z) u i y) =
              ((I.rec7 l Z).fm u).dilT i v q c h y := by
          intro q hq
          obtain rfl : q = r := Units.ext hq
          rfl
        refine key _ ?_
        exact hE v _
      bw := fun w _ _ v x => Iff.rfl }



theorem tw_lv_tied_and_same : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → (∃ Lv : SymmetricTwistedLevelData W, I.StdLv l Z l0 Lv) ∧ Nonempty (TwLvSameS W) := by
  intro B X I hOk hP l Z l0 inQ H F T J W hF hW
  have hY : ∀ u μ i hm y, (twYS T F u μ i hm y).1 = y.1 := by
    intro u μ i hm y
    unfold twYS
    rw [hW.eY u μ i hm]
    simp only [Equiv.trans_apply, Equiv.refl_symm, Equiv.refl_apply]
    unfold eYS
    split_ifs with h
    · exact (hF u).1.eY i hm h y
    · have e : (I.rec7 l Z).R.m = B.R.m := rfl
      exact (hF u).1.eYC i (by omega) (by omega) y
  have hV : ∀ u μ v, ((W.atT u μ).eV (F u).atT v).1 = v.1.under (𝓞 B.host.F) := by
    intro u μ v
    unfold TwAtT.eV
    rw [hW.eVT u μ]
    exact (hF u).1.eV v
  have hres : ∀ u μ, (W.atT u μ).res (F u).atT = I.resT l u μ := fun u μ =>
    funext fun v => RingHom.ext fun r => hW.eFv u μ v r
  have key := fun u μ (hμ : μ ≠ (I.rec7 l Z).what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) =>
    exists_lvTied_of_std I hOk hP l Z u μ i hm _ _ (T.chOf u μ i) (T.lat u μ i) (hW.lat u μ i) ((W.atT u μ).res (F u).atT) (hres u μ)
      (W.ch u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (hW.reads u μ hμ i h1 hm) (hY u μ i hm) (hV u μ)
      (hW.killed u μ hμ i h1 hm)
  choose L hL using key
  refine ⟨⟨⟨L, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.1.choose, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.1.choose_spec,
    fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.2.1, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.2.2, ?_⟩,
    fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).1⟩, ⟨⟨?_, ?_⟩⟩⟩
  · intro u μ hμ i h1 hm
    rw [hres u μ, hW.lat u μ i]
    exact GlobalTheory.Mem.Col2.TC.bw_tie I hOk hP l Z u μ i hm (twYS T F u μ i hm) (hY u μ i hm)
  · intro u μ
    rw [hW.eCls0 u μ, hW.eY u μ 0 (Nat.zero_le _)]
    refine (GlobalTheory.Mem.Col2.TC.StepZero.lvSame_zero I hOk hP l Z l0 u μ (W.atT u μ) (hW.eVT u μ) fun v r => ?_).some
    have h := hW.eFv u μ v r
    simp only [TwAtT.res, RingHom.comp_apply, (hF u).1.res] at h
    exact h
  · intro u i hi
    refine lvSameMu0 I l Z l0 u i hi (W.atT u _) (hW.eVT u _) fun v r => ?_
    have h := hW.eFv u (I.rec7 l Z).what₂.mu0 v r
    simp only [TwAtT.res, RingHom.comp_apply, (hF u).1.res] at h
    exact h

end GlobalTheory.Mem.Col2.TC
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

abbrev refUp (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : Refill Z :=
  { Refill.ofDiv Z N h with S := S' }


open Formalism.BasicNotions.DivX (md) in

def divBack {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (X : DivX (w.D (SRe.upL Z S' N h))) : DivX (w.D Z) :=
  { X with md := fun S κ p _ la z => { md X S κ p la z with } }



theorem grpAt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GrpAt (w.st Z) w.I) : GrpAt (w.st (SRe.upL Z S' N h)) w.I :=
  ⟨(by with_unfolding_all exact (x.pl :)), (by with_unfolding_all exact (x.idem :)), (by with_unfolding_all exact (x.cen :))⟩



theorem muIsW_up {Z : w.Lt} {Wt : Set B.places.Pl} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (x : V4.MuIsW (w.st Z) f T Wt w.I.xi) : V4.MuIsW (w.st (SRe.upL Z S' N h)) f T Wt w.I.xi := by
  exact
    { inj := by with_unfolding_all exact (x.inj :)
      range := by with_unfolding_all exact (x.range :)
      mu0 := by with_unfolding_all exact (x.mu0 :)
      star := by with_unfolding_all exact (x.star :)
      star' := by with_unfolding_all exact (x.star' :)
      tw := by with_unfolding_all exact (x.tw :)
      on := by with_unfolding_all exact (x.on :)
      off := by with_unfolding_all exact (x.off :)
      sub := by with_unfolding_all exact (x.sub :)
      supp := by with_unfolding_all exact (x.supp :) }



theorem rowInt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GlobalTheory.PerQ.RowInt w.I w.l Z) : GlobalTheory.PerQ.RowInt w.I w.l (SRe.upL Z S' N h) :=
  ⟨(by with_unfolding_all exact (x.ref :)), (by with_unfolding_all exact (x.tw :))⟩



theorem idxDefs_up {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (Y : DivX (w.D (SRe.upL Z S' N h))) (hI : IdxDefs (w.D Z) (divBack Y)) : IdxDefs (w.D (SRe.upL Z S' N h)) Y :=
  ⟨(by with_unfolding_all exact (hI.Ij_def :)), (by with_unfolding_all exact (hI.jw_def :))⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.L2.Forms Formalism.L2.G Formalism.UG Matrix
open scoped TensorProduct

section Hyp

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}



theorem stab_iff_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β))
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β)
      (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Hyp

section Main



theorem stepTiesD_mid : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ u v hg i hi hi2
  have h1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  let F := t.C.forms u
  let dt : GlobalTheory.Port.MemDt F :=
    ⟨fun j hj _ => GlobalTheory.Port.detTieOf t.full.1.base _, fun j _ _ β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hB : GlobalTheory.Port.BaseEx t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) := by
    obtain ⟨Cm, hC1, hC2, -⟩ := F.deC (i + 1) h1 hi2
    exact GlobalTheory.Port.baseEx_of t.g.herm u v hg _ Cm hC1 hC2 (GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dt i hi v hg)
  have hrat : ∀ β, Formalism.L2.G.Cmp.ChiRatAll ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev (w.D Z).what₂.embLL := by
    rw [GlobalTheory.Port.formsInMem_mid F dt i hi hi2]
    intro β
    obtain ⟨k, hR⟩ := (t.std u).mid (i + 1) h1 hi2
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i + 1) (le_of_succ_m hi2) _ _ _ rfl
      (F.ch (i + 1) h1 hi2) k hR
      (fun β => GlobalTheory.Port.chi_fin_of_glevH (F.glevC (i + 1) h1 hi2 β) fun a => ((w.D Z).host.g_prime a).ne_zero) β
  have hψ : GlobalTheory.Port.PsiEx (GlobalTheory.Port.formsInMem F dt i hi) (t.cmp.embW u v hg) :=
    GlobalTheory.Port.psiEx_of _ (t.cmp.embW u v hg) (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O hrat
      (GlobalTheory.Port.finMem_of F dt i hi)
  haveI : ∀ j, Finite (t.C.herm.base.Ch u j) := fun j => t.C.herm.base.ChFin u j
  let S : StepD t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) :=
    ⟨hB.choose, hB.choose_spec.2, fun β => (hψ β).choose, fun β => GlobalTheory.Port.fin_of _ β _⟩
  refine ⟨GlobalTheory.Port.formsInMem F dt i hi, GlobalTheory.Port.formsInMem_fin F dt i hi, S, ?_⟩
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ (GlobalTheory.Port.formsInMem F dt i hi).T := by
    rw [GlobalTheory.Port.memberChainForms_levelPrime_eq_member]; exact hg.2.2.2.2.2
  have hbad : ∀ w' ∈ (GlobalTheory.Port.formsInMem F dt i hi).bad,
      (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
    rw [GlobalTheory.Port.formsInMem_bad]; exact Formalism.L2.G.bad_notOver u v hg
  have hre := fun β w' => GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram
    (gramN (w.D Z) (i + 1) hi) (gramN_apply (w.D Z) (i + 1) hi) ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev w'
  refine ⟨fun β w' h x hx ha hb => ?_, fun β w' h x hx => ?_, hbad, hB.choose_spec.1, fun β => (hψ β).choose_spec,
    GlobalTheory.Port.chRat_mem (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 F dt i hi,
    GlobalTheory.Port.formsInMem_ok F dt i hi v, hT⟩
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    exact (hre β w').2.2 (fun hb' => hbad w' hb' h) hTw
      ((stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hx).2 ⟨ha, hb⟩)
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    have hl := (hre β w').1 hx
    exact (stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hl.1).1 hl

end Main

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.twisted_chain_chart_level_characters_rational : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  first | exact @GlobalTheory.ChiRatStd.chiRatAll_twChart | exact GlobalTheory.ChiRatStd.chiRatAll_twChart | (intros; apply GlobalTheory.ChiRatStd.chiRatAll_twChart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem finite_T_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) : Finite a.x.T := by
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hfin



end GlobalTheory.Mem.Top.Bl

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  first | exact @GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | exact GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | (intros; apply GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  first | exact @GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | exact GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | (intros; apply GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie <;> assumption)
end
