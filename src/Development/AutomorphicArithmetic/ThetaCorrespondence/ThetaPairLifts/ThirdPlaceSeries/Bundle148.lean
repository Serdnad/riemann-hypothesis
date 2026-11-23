module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle487
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle116
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd.Bwd
section Dense
open Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col GlobalTheory.RootEx GlobalTheory.TwBridge ValuativeRel
end Dense
section Rat
open _root_.Formalism.L2.Col Formalism.UG
attribute [local instance] GlobalTheory.Mem.Col2.starE
end Rat

theorem onePlace_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (i : Fin J.r), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v), _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i n hn hphi
  have hs := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  obtain ⟨gl, hglc, hgl, hglu⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by omega))
  have hAt : ∀ y, gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun y =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1 _ rfl
  have hund : (J.G i).q.v = ((J.P i).1).under (𝓞 B.host.F) := by
    rw [hJ.eq i]; exact (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i
  have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hW.tr.pins.some l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨e, he, heβ⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := hs; exact Nat.le_succ_of_le this)
  let K := (GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).comap gl
  have hKo : IsOpen (K : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) :=
    (GlobalTheory.ClassSumLevel.isOpen_levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).preimage hglc
  have hle : _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ K := by
    refine prX_le_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep K hKo (fun e' he' y hy => ?_)
    refine Subgroup.mem_comap.2 ((GlobalTheory.ClassSumLevel.mem_levG_iff _ _ _ _).2 ?_)
    refine mem_lev_of_rat I hI l Z u _ J.A hJ.is j hj (J.ι j α) (hJ.std j (by omega) _) (J.P i) (hJ.tw i).nmem _
      (eU ▸ GlobalTheory.AdForm.Model.finGL_mem _ (rankN (I.rec7 l Z) j hj') _) (fun v' hv' => ?_) y hy (fun r s => ?_)
    · refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ _ _ _ fun w hw r s => ?_
      refine (GlobalTheory.FinMComp.adAt_finM_eq_one (I.rec7 l Z) _ (rankN (I.rec7 l Z) j hj') _ _ (hAt _) w
        (fun h => hv' (hw.symm.trans (h.trans hund))) r s).trans ?_
      rfl
    · obtain ⟨r, rfl⟩ := e'.surjective r
      obtain ⟨s, rfl⟩ := e'.surjective s
      have ee : ∀ c, (finCongr (rankN (I.rec7 l Z) j hj')).symm (e' c) = e c := fun c => Fin.ext ((he' c).trans (he c).symm)
      have h1 := entry_of_std _ e heβ _ _ (hgl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y)).2 r s
      refine adAt_eq_of_pr (J.G i).q (J.P i).1 hidem
        (mt _ (gl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y))
          ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' r)) ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' s))) _ ?_
      rw [ee, ee]
      exact h1
  have hn' : n = gl (_root_.GlobalTheory.LevProd.localHomProduct J j hj n i) :=
    hglu n _ ((GlobalTheory.LocGl.supp_iff _ _).2 hn) ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
  have hK : gl (_root_.GlobalTheory.LevProd.localHomProduct J j hj n i) ∈ GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj')
    (J.A.K j hj' (J.ι j α)).lev := hle hphi
  rw [← hn'] at hK
  exact (hJ.is.U j hj' _ n).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hn, hK⟩
theorem mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J), (∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α n hn hphi
  classical
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image (fun i => (J.G i).q.v)
  have key : ∀ S : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)), S ⊆ Q → ∀ n ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S),
      (∀ i, (J.G i).q.v ∈ S → _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ n hn _
      rw [grpAt_empty _ (fun w h => by simp at h) n hn]
      exact one_mem _
    | insert v S hvS ih =>
      intro hsub n hn hphi
      obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 (hsub (Finset.mem_insert_self v S))
      obtain ⟨x, hx, y, hy, rfl⟩ := ((GlobalTheory.FinPl.localComponents _ (fun w => w = v)).2 _).1 n
      have hxS : x ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) :=
        grpAt_le_of _ (fun w hw => by rw [hw]; exact Finset.mem_insert_self v S) hx
      have hyS : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S) := by
        have h1 : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) := by
          have : y = x⁻¹ * (x * y) := by group
          rw [this]; exact mul_mem (inv_mem hxS) hn
        rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at h1 ⊢
        rw [GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts] at hy
        refine fun a b => ⟨(h1 a b).1, fun w hw => ?_⟩
        by_cases hwv : w = v
        · exact hy a b w hwv
        · exact (h1 a b).2 w (fun hm => (Finset.mem_insert.1 hm).elim hwv hw)
      have hyv : _root_.GlobalTheory.LevProd.localHomProduct J j hj y i0 = 1 := by
        show GlobalTheory.LevIdx.locHom (J.G i0).q _ _ y = 1
        apply locHom_one_of_off
        rw [hi0]; exact hy
      have hxU : x ∈ J.A.U j (J.ι j α) := by
        refine _root_.GlobalTheory.LevProd.Bwd.onePlace_alt W hW u a ha hTr j hj t J hJ α i0 x (by rw [hi0]; exact hx) ?_
        have := hphi i0 (by rw [hi0]; exact Finset.mem_insert_self v S)
        rwa [map_mul, Pi.mul_apply, hyv, mul_one] at this
      have hyU : y ∈ J.A.U j (J.ι j α) := by
        refine ih (fun w hw => hsub (Finset.mem_insert_of_mem hw)) y hyS (fun i hi => ?_)
        have hxi : _root_.GlobalTheory.LevProd.localHomProduct J j hj x i = 1 := by
          show GlobalTheory.LevIdx.locHom (J.G i).q _ _ x = 1
          apply locHom_one_of_off
          exact GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ _ _
            (fun p hp hp' => hvS (by rw [← hp, hp']; exact hi)) hx
        have := hphi i (Finset.mem_insert_of_mem hi)
        rwa [map_mul, Pi.mul_apply, hxi, one_mul] at this
      exact mul_mem hxU hyU
  refine key Q subset_rfl n (grpAt_le_of _ (fun w hw => ?_) hn) (fun i _ => hphi i)
  obtain ⟨i, hi⟩ := hw
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
end GlobalTheory.LevProd.Bwd
end
end
end

section



section
noncomputable section


namespace GlobalTheory.LineIdeal
section Loc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
end Loc
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
section Word
variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}
end Word
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem single_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : _root_.GlobalTheory.MiTop.PlacedConditions f B) (a₀ a₁ : GA D (D.sp.X 0)) (x : GlobalTheory.FinPl.Pl D)
    (hg : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ x) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal) {α cc : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ *ᵥ (a •
      (((cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) *
        incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) •
      ratV fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) ∈ latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = x) ↔
      a ∈ intAt D (· = x) := by
  intro a ha
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, -, ht, sh, -, -, hb, hp⟩ := hP
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hI := all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 (fun e => hx ((ht.tP x).1 e)) hα hψ 0 D.R.rS h₀ (D.R.rS - 1) r (by have := r.2; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hm := ht.moves 0 (by omega) (· = x) fun p hp e => by
    obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 e
    exact hg PP h1 (h2.symm.trans hp)
  have hx1 := xu_fixes (h := W.Q.instEq) (u := u) hW.bot.idE r
  rw [← mul_assoc (α * α), ← mul_assoc (cc ^ _)] at hI
  generalize cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (D.sp.Y 0).rank → D.host.E,
      (fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) = ε := ⟨_, rfl⟩
  have he' : ∀ k, B.d.e k r = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) * ε k := fun k => by rw [he, ← hε]
  rw [hε] at hx1 ⊢
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    funext k
    change a * (_ * incA D (ε k)) = _ * incA D (B.d.e k r)
    have : D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k = lam * -s * B.d.e k r := by
      rw [he']
      linear_combination ((W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * n1 + (lam * μ * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * hss
    have h2 := congrArg (incA D) this
    rw [map_mul, map_mul (incA D) (lam * -s), map_mul (incA D) lam] at h2
    linear_combination (a * K) * h2
  have hfix : mt (D.sp.Y 0) ((show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹) *ᵥ
      (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    have e : (show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ =
        embA B.d B.o (a₀ * a₁)⁻¹ * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      unfold _root_.GlobalTheory.MiTop.translationElement
      rw [map_inv, _root_.mul_inv_rev, mul_inv_cancel_left, _root_.mul_inv_rev, inv_inv]
    rw [e, GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec, mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), hx1, hy]
    generalize (K : AE D) * incA D lam * (incA D (-s) * a) = t
    have e1 : colMul B.d.jX r t = B.d.jX *ᵥ Pi.single r t := by
      rw [mulVec_single]; funext k; exact mul_comm _ _
    rw [e1, mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX]
  have hsup : ∀ i, (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) i ∈
      idAt D (· = x) := fun i => Ideal.mul_mem_right _ _ ha
  rw [GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec] at hfix
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI ((K : AE D) * incA D lam * (incA D (-s) * a)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))
  rw [← inU_val lam hlam, ← Units.val_mul, Units.inv_mul_cancel_left, Units.val_mul, inU_val, ← hj] at h1
  refine (hm _ (GlobalTheory.FinPl.KOpen.supp_mulVec (D.sp.Y 0) _ _ hsup)).trans
    ((iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hfix)).trans (h1.trans ?_))
  rcases hs with rfl | rfl
  · rw [map_neg, map_one, neg_one_mul, int_neg]
  · rw [neg_neg, map_one, one_mul]
theorem common_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hg hu hu'
  have hstd : IsStdChar D W.Q.Rl.ψ (-1) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, -⟩ := hP
    exact hc.std
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hstd
  have hψ : ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = v) := fun s hs => by
    rw [(hα v).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have hfg : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := (_root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 (by have := D.R.two_le_m; omega)).1.1.fg
  exact ⟨_, fun c => ⟨line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f B hP a₀ a v hg hu (hα v).1 hψ) c,
    line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f' B' hP' a₀' a' v hg hu' (hα v).1 hψ) c⟩⟩
end GlobalTheory.LineIdeal
end
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory
theorem baseLat_line_offT_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP x hxg hxt u'' hxu c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hc0, hv0, hvt, hso, hgp, hgr, hbt, hpt⟩ := hP
  have hm : 0 < D.R.m := by unfold Ranks.rS at hr; omega
  have hxg' : x ∉ v'.gP := by
    intro h
    obtain ⟨PP, hPP, hPx⟩ := (hvt.gP x).1 h
    exact hxg PP hPP hPx.symm
  have hmv := hvt.moves 0 hm (· = x) (by rintro p rfl; exact hxg')
  set b : GA D (D.sp.Y 0) := f.g.b 0 with hb
  set w : Fin (D.sp.Y 0).rank → AE D := fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hw
  have hy : ∀ i, (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) i ∈ idAt D (· = x) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mul_mem_right _ _ hc
  have key : (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w ∈ latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = x) ↔
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) ∈ latV (D.sp.Y 0) (v'.N 0) (· = x)) :=
    hmv _ hy
  have hinv : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) = w := by
    rw [Matrix.mulVec_mulVec]
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [hinv] at key
  refine key.trans ?_
  exact _root_.GlobalTheory.T.smul_frameVector_mem_latV_iff_mem_intAt W hW hr u f B k ι v' o n G pl hc0 hv0 hvt hso hgp hgr hbt hpt x hxg'
    (fun h => hxt ((hvt.tP x).1 h)) u'' hxu c hc
end GlobalTheory
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLev
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
def relaxedLevelSubgroup (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj)
def baseLevelSubgroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) then
    _root_.GlobalTheory.PenLev.relaxedLevelSubgroup h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥
theorem relax_le_gfc (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ≤ GfC _ :=
  fun _ hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
theorem base_level_subgroup_le_gfc (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 1 = B.R.m) : _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj ≤ GfC _ := by
  unfold _root_.GlobalTheory.PenLev.baseLevelSubgroup
  split_ifs
  · exact _root_.GlobalTheory.PenLev.relax_le_gfc _ _ _ _
  · exact bot_le
theorem mem_relax_iff' (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ↔ g ∈ J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) ∧ g ∈ GfC _ ∧
      ∀ i, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  simp only [_root_.GlobalTheory.PenLev.relaxedLevelSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, and_assoc]
theorem base_level_subgroup_eq_relax (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (hJ : J.Reads) (α : J.Ch j) :
    ∃ (t₀ : W.P.T) (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀) (α₀ : J₀.Ch j), J₀.Reads ∧ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj = _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J₀ j hj α₀ := by
  have h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2.some, h.choose_spec.choose_spec.1, ?_⟩
  unfold _root_.GlobalTheory.PenLev.baseLevelSubgroup
  rw [dite_eq_left h]
end GlobalTheory.PenLev
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem loc_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i
  have hs := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj
  have hjm : j < B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  have hle : _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ :=
    prX_le_KO_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep (hL.int _ _ _)
  have hreg := (J.E i).reg
  have hJo : IsOpen ((((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
      (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k)) :=
    (hreg.2.2 _ _ _).1
  set g₀ := (J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' hs) (α i) with hg₀
  have hOo : IsOpen {w : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin ((J.G i).s - j + 1)) (J.G i).k |
      g₀⁻¹ * w * g₀ ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1)
        (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J} :=
    hJo.preimage (by fun_prop)
  have hpo : IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := by
    refine GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [one_mem]) ?_
    intro z hz hzO
    exact GlobalTheory.StepData.mem_Cgrp.2 ⟨hz, hzO⟩
  haveI : BorelSpace (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    _root_.GlobalTheory.SplitFlip.borel_GL
  refine ⟨hle, hpo.measurableSet, ?_⟩
  have hc := GlobalTheory.SplitFlip.isCompact_KO (k := (J.G i).k) (n := XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
  haveI : CompactSpace (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) := isCompact_iff_compactSpace.1 hc
  have ho' : IsOpen (((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _) : Subgroup _) : Set (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j))) :=
    hpo.preimage continuous_subtype_val
  haveI : Finite (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ⧸ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)) :=
    ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).quotient_finite_of_isOpen ho'
  haveI : ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).subgroupOf (KO (J.G i).k _)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero
end GlobalTheory.LevProd
end
end
end
