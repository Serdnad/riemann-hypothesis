module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrMemOfMemLatV
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Formalism.LocalRingCardinality.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle416

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.FinData
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ s j α γ hj
  refine ⟨?_, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atG j).2.1, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atT j).1⟩
  unfold _root_.GlobalTheory.Fam.QuadraticExtensionData.dQ
  refine isFinComb_smul _ _ (isFinComb_smul _ _ (GlobalTheory.QPl.ThetaPin.isFinComb_aconv _ fun e he => ?_))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨ε, hε, hsum⟩ := (J.G i).q.above
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  refine GlobalTheory.QPl.ThetaPin.isFinComb_of_half hε _ fun w hw => hsum ▸ ?_
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  rcases Nat.lt_or_ge j (J.G i).s with h1 | h1
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = (J.G i).s := ⟨(J.G i).s - j - 1, by omega⟩
    exact ((J.E i).dL_mid j d hd (α i) (γ i)).1 w hw
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      exact ((J.E i).dL_pen (α i) (γ i)).1 w hw
    · obtain rfl : j = (J.G i).s + 1 := by omega
      exact ((J.E i).dL_top (α i) (γ i)).1 w hw
end GlobalTheory.Fam.FinData
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.TopFrame

theorem baseFr_top_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i (hm : (J.G i).s + 1 + 1 ≤ B.R.m) (γ : J.Ch₀ ((J.G i).s + 1 + 1)) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((J.G i).s + 1)) (Fin B.R.t) ((J.G i).s + 2) ⊕ Unit ≃ Fin (B.R.N ((J.G i).s + 1 + 1))), GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e → ∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b)) = (J.G i).FM.β r b := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hiA t J hJ i hm γ e he r b
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have key : ∀ j (h : j = (I.rec7 l Z).R.m), (∀ r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0) ∧
      ∀ r, vecB (a.g.oT j h) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro j h
    subst h
    exact ⟨hiA, fun r => hat.z0 r⟩
  obtain ⟨hA, hz⟩ := key _ (J.G i).hs
  obtain ⟨-, ⟨e', he', hT'⟩, hz0⟩ := ha.stdQ (J.pl i) ⟨t, J.mem i⟩
  let ι : (I.rec7 l Z).host.E →+* (J.G i).k := (J.G i).q.pr.comp (incA (I.rec7 l Z))
  have hL := frsF_top J.A hJ.is hW.tr.ok (J.P i) (hJ.tw i).nmem _ hs γ (finCongr (rankN (I.rec7 l Z) _ hm) r) (e b)
  have hL' : baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b) =
      if r.val = (e b).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := hL
  have hN : B.R.N ((J.G i).s + 1 + 1) = B.R.N B.R.m := congrArg _ hs
  refine (congrArg _ hL').trans (Eq.trans ?_ (congrFun (congrFun (J.G i).last r) b).symm)
  rcases b with b | b
  · have hb : (e (Sum.inl b)).val = (e' b).val := (he _).trans (he' b).symm
    have hb2 : (e (Sum.inl b)).val + 1 ≠ B.R.N B.R.m := by
      intro h
      have h2 : (e (Sum.inr ())).val = B.R.N B.R.m - 1 := he _
      have h3 : e (Sum.inl b) = e (Sum.inr ()) := Fin.ext (by omega)
      exact Sum.inl_ne_inr (e.injective h3)
    have h5 : (if r.val = (e (Sum.inl b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        (a.g.oT _ (J.G i).hs).iA r (e' b) := by
      refine Eq.trans ?_ (hA r (e' b)).symm
      rw [← hb]
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb2
      · rfl
      · rfl
    refine (congrArg _ h5).trans ?_
    show _ = ∑ c, ι ((a.g.oT _ (J.G i).hs).iA r c) * (J.G i).FT.β c b
    have h6 : ∀ c, (J.G i).FT.β c b = if c = e' b then 1 else 0 := fun c => (congrFun (congrFun hT' c) b).trans Matrix.one_apply
    refine Eq.symm ((Finset.sum_congr rfl fun c _ => congrArg _ (h6 c)).trans ?_)
    refine (Finset.sum_eq_single (e' b) (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · exact (congrArg _ (if_neg hc)).trans (mul_zero _)
    · exact (congrArg _ (if_pos rfl)).trans (mul_one _)
  · have h2 : (e (Sum.inr b)).val = B.R.N B.R.m - 1 := he _
    have h3 := (e (Sum.inr b)).2
    have h4 : (if r.val = (e (Sum.inr b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        vecB (a.g.oT _ (J.G i).hs) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r := by
      rw [hz]
      split_ifs with h5 h6 h7
      · rfl
      · omega
      · omega
      · rfl
    refine (congrArg _ h4).trans ?_
    show ι (∑ c, (a.g.oT _ (J.G i).hs).iB r c * (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) c) = ∑ c, ι ((a.g.oT _ (J.G i).hs).iB r c) * (J.G i).z₀ c
    exact (map_sum ι _ _).trans (Finset.sum_congr rfl fun c _ => (map_mul ι _ _).trans (congrArg _ (congrFun hz0 c).symm))
end GlobalTheory.Fam.TopFrame
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm
end GlobalTheory.Fam.MovedJoin
namespace GlobalTheory.Fam
open GlobalTheory.AdForm GlobalTheory.Fam.MovedJoin

theorem QuadraticExtensionData.Reads.movedAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha t J hJ i
  refine { toReadsAt := ⟨hJ.eq i, hJ.tw i, hJ.M i, hJ.rep i⟩, rk := fun _ => rfl, low := ?_, pen := ?_ }
  · intro k hk hm β e he r b
    have hs : (a.Q (J.pl i) ⟨t, J.mem i⟩).s + 1 + 1 = B.R.m := (a.Q (J.pl i) ⟨t, J.mem i⟩).hs
    have hstd := hJ.std k (by omega) β
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 k (Nat.le_succ_of_le hk)
    rw [hF]
    have key : ∀ r' b' : Fin (B.R.N k), Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 k β).1.1 (J.P i) (Pi.single b' 1) r' =
        if r' = b' then (1 : B.host.E) else 0 := by
      intro r' b'
      apply (algebraMap B.host.E ((J.P i).1.adicCompletion B.host.E)).injective
      rw [← adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn k hm β r' b', hstd, adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ r' b']
    unfold _root_.GlobalTheory.QTw.baseFr
    refine (congrArg _ (key _ _)).trans ?_
    have hiff : ((finCongr (rankN (I.rec7 l Z) k hm)) (Fin.cast rfl r) = e b) ↔ (r = e' b) := by
      constructor
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he b).trans (he' b).symm))
      · intro h
        exact Fin.ext ((congrArg Fin.val h).trans ((he' b).trans (he b).symm))
    have hR : ∀ x : (a.Q (J.pl i) ⟨t, J.mem i⟩).k, x = (if r = e' b then 1 else 0) →
        x = Matrix.submatrix (1 : Matrix (Fin ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).X k).rank) (Fin ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).X k).rank) (a.Q (J.pl i) ⟨t, J.mem i⟩).k) id e' r b := by
      intro x hx
      rw [hx]
      rfl
    apply hR
    split_ifs with h1 h2 h2
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_one _)).trans (map_one _)
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · simp only [GlobalTheory.LocMod.Place.pr]
      exact (congrArg _ (map_zero _)).trans (map_zero _)
  · intro hm β e he
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
    have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
    obtain ⟨k₀, h, hk₀, hfin, hkA, hh, hg⟩ := hJ.pen ((J.G i).s + 1) (by omega) β
    obtain ⟨g, hgJ, hgm⟩ := hg i rfl
    obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
    have hkb := (hJ.is.kA ((J.G i).s + 1) hm β).2.1
    have hent : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin ((I.rec7 l Z).sp.X ((J.G i).s + 1)).rank),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c)
          (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d) = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y c d) := by
      intro y c d
      simp [finM, Matrix.reindex_apply]
    have hent' : ∀ (y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1))) (c d : Fin (B.R.N ((J.G i).s + 1))),
        finM _ (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) y c d = toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ y
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm c) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm d)) := by
      intro y c d
      rfl
    have hk0 : (Formalism.L2.Theta.mt _ k₀).map (J.G i).q.pr = 1 := by
      refine map_eq_one_of_pr _ _ fun c d => GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ ?_
      have h1 := congrFun (congrFun hfin (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c))
        (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d)
      rw [hent] at h1
      refine (congrArg (adAt B.host.F (J.P i).1) h1).trans ((adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ _ _).trans ?_)
      have hite : (if finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) c = finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm) d
          then (1 : B.host.E) else 0) = if c = d then 1 else 0 := by
        by_cases hcd : c = d
        · subst hcd
          simp
        · rw [if_neg (fun h' => hcd ((finCongr _).injective h')), if_neg hcd]
      exact congrArg _ hite
    have hkAm : (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ := by
      rw [hkA, GlobalTheory.AdForm.CongAtIdem.mt_mul', Matrix.map_mul, hk0, Matrix.one_mul]
      exact hgm
    have hentry : ∀ (x : Fin (B.R.N ((J.G i).s + 1))) (b : StepData.XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1)),
        (ofSplit (J.G i).q).pr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) =
          (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) b := by
      intro x b
      have h1 := adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn _ hm β x (e b)
      rw [← hkb] at h1
      have h2 : adAt B.host.F (J.P i).1 (toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b)))) =
          algebraMap B.host.E _ (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single (e b) 1) x) := by
        have h5 := hent' (J.A.kA ((J.G i).s + 1) β) x (e b)
        exact (congrArg (adAt B.host.F (J.P i).1) h5).symm.trans h1
      have h3 := GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq _ _ hidem _ _ h2
      have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e b) = e' b := Fin.ext ((he b).trans (he' b).symm)
      refine h3.symm.trans ?_
      refine (congrArg (fun c => (J.G i).q.pr (Formalism.L2.Theta.mt _ (J.A.kA ((J.G i).s + 1) β)
          ((finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm x) c)) h4).trans ?_
      refine (congrFun (congrFun hkAm _) (e' b)).trans ?_
      exact mul_frameγ_std _ e' hF _ _ _
    refine ⟨g, hgJ, fun r b => hentry _ b, ?_⟩
    refine (hJ.cos i β e he).trans (congrArg _ ?_)
    funext r
    have hexp := map_eq_sum_frame ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i))
      (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) (e r)
    refine hexp.trans ?_
    refine (Equiv.sum_comp e (fun c => ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i) (Pi.single c 1) (e r)) *
      ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)).symm
        (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2) c))).symm.trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    have h4 : (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm)).symm (e r) = e' r := Fin.ext ((he r).trans (he' r).symm)
    have H := (hentry (e r) b).trans ((congrArg (fun c => (((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁) c b) h4).trans
      (frameβ_mul_std _ e' hF _ r b))
    exact congrArg₂ (· * ·) H rfl
end GlobalTheory.Fam
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem lattice_eq_base_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ p, p ∉ a.v.tP → GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) (a.g.x 0).L (· = p) = GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft (I.rec7 l Z).host.E (I.rec7 l Z).host.E (finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 (I.rec7 l Z).host.E))) (· = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr row col hc p hp
  obtain ⟨hs⟩ := hW.tr.std
  obtain ⟨k, hk⟩ := (hs u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hx := (hTr.pinX.xs 0 (Nat.zero_le _)).2.2
  have hlb := hk.lb ()
  have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
  have hd : ((B.T u : ℕ) : ℤ) ≠ 0 := fun h => hTp (by rw [h]; simp)
  have h1 : ((1 : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    rw [Int.cast_one]; exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set e := finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) with he
  have hpi : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := by
    refine ⟨⟨B.host.conj (X.piT u : B.host.E), map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2⟩, ?_⟩
    apply RingOfIntegers.ext
    have := X.piT_norm u
    push_cast
    exact this.symm
  refine le_antisymm (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ ((B.T u : ℕ) : ℤ) hd ?_ p hTp)
    (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ 1 one_ne_zero ?_ p h1)
  · intro y hy
    have hyi : ∀ j, IsIntegral ℤ (y j) := (hx y).1 hy
    refine Submodule.mem_map.2 ⟨fun j => (((B.T u : ℕ) : ℤ) • y) (e.symm j), (hlb _).2 fun j => ?_, ?_⟩
    · refine ⟨((B.T u : ℕ) : 𝓞 B.host.E) * ⟨y (e.symm j), hyi _⟩, ?_, fun _ => dvd_mul_of_dvd_left hpi _⟩
      show (((B.T u : ℕ) : ℤ) • y) (e.symm j) = _
      rw [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    · funext i
      show (((B.T u : ℕ) : ℤ) • y) (e.symm (e i)) = _
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hxm, rfl⟩
    rw [one_smul]
    refine (hx _).2 fun j => ?_
    obtain ⟨r, hr, -⟩ := (hlb x).1 hxm (e j)
    show IsIntegral ℤ (x (e j))
    rw [hr]; exact r.2
end GlobalTheory.Fam
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.DisjProof
theorem vT_disjoint_vGs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.Fam
inductive TruePackAlt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}, _root_.GlobalTheory.MiS.RealPackAlt ex → Prop
  | mk {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
      {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
      {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
      _root_.GlobalTheory.Fam.AllFamilyConditions W → TruePackAlt W
def RealPackageCondition {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE
end GlobalTheory.Fam
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevPrimeData
open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.LevPrimeData
theorem GlobalTheory.LevPrimeData.data_preT_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (g : GlobalTheory.Fam.Geo (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (c₀ : ℕ → ℂ) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)) (ζ₀ : Fin g.Lz.rank → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E), GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ g.x g.vac c₀ → v.NT = (_root_.GlobalTheory.Fam.pk_z W).ΛX → (∀ p, p ∈ v.tP ↔ ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → IsLineVec g.Lz ζ₀ → (∀ r, vecB (g.oT B.R.m rfl) ζ₀ r = (show Fin (B.R.N B.R.m) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) _ le_rfl) r)) → GlobalTheory.AdForm.IsEmbTop (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (∀ x : GlobalTheory.FinPl.Pl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G), ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ x.asIdeal → ∃ LZ : GlobalTheory.FinPl.Lat g.Lz, GlobalTheory.FinPl.OrthAt (g.oT B.R.m rfl) (g.x B.R.m).L (_root_.GlobalTheory.Fam.pk_z W).ΛX LZ x) → (∀ j h, (v.τ j h)ᴴ * ((g.bes j 0 h).L.gram * v.τ j h) = (-((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0 * star (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) • g.Lz.gram ∧ v.τ j h *ᵥ ζ₀ = (-(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0 ^ (B.R.m / 2)) • (g.bes j 0 h).ζ) → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι), PreT v o ∧ o.ζ₀ = ζ₀ ∧ GlobalTheory.AdForm.StdT I l Z u o.p o.β o.Q fun j => (g.x j).L := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u g c₀ v ζ₀ hPin hNT htP hline hz hemb hort htau
  obtain ⟨pins⟩ := hW.tr.pins
  obtain ⟨k, _, _, _, _, ι, p, J, q, χ, β, Q, hPl, hch, -, hval, hpl, hb, hStd⟩ :=
    GlobalTheory.T.standardPairs_exist_at_levelPrime I hW.tr.ok pins l Z u (_root_.GlobalTheory.Fam.pk_z W).ψ hPin.std (fun j => (g.x j).L) (fun j hj z => (hPin.xs j hj).2.2 z)
  have hG : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => hW.tr.ok.gram_X j
  have hz' : ∀ r : Fin ((I.rec7 l Z).sp.X B.R.m).rank, vecB (g.oT B.R.m rfl) ζ₀ r =
      if r.1 + 1 = ((I.rec7 l Z).sp.X B.R.m).rank then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro r
    rw [hz r]
    have e : ((I.rec7 l Z).sp.X B.R.m).rank = B.R.N B.R.m := Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl
    show (if r.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) = _
    rw [← e]
  have hpos : 0 < ((I.rec7 l Z).sp.X B.R.m).rank := by
    have h1 := (g.oT B.R.m rfl).rank_add
    have h2 : g.Lz.rank = 1 := hline.1
    change 0 < ((GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X B.R.m).rank
    omega
  have htop := fun i => GlobalTheory.StdPairTop.ker_stdPair _ k (p i) q _ _ _ (g.oT B.R.m rfl) (hG _) ζ₀ hline (X.piT u) _ hz' (hval i).1 (hval i).2
    (g.x B.R.m).L v.NT (fun z => (hPin.xs _ le_rfl).2.2 z)
    (by obtain ⟨LZ, h⟩ := hort (p i).v ((hpl _).1 ⟨i, rfl⟩); exact ⟨LZ, hNT ▸ h⟩)
    (β B.R.m i) (Q B.R.m i) (hb _ _) ((hStd.2 _ le_rfl).2 i).1 ((hStd.2 _ le_rfl).2 i).2
  choose γ γ₀ hγ using htop
  have hcore : ∀ j ρ h i, Nonempty (GlobalTheory.FinPl.Frame (p i) (g.bes j ρ h).V₀ (Fin ((I.rec7 l Z).sp.X j).rank ⊕ Fin 1)) := by
    intro j ρ h i
    obtain ⟨γ', -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 (g.bes j ρ h).V₀ (Fin (g.bes j ρ h).V₀.rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨α, -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨β₀, -⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame (g.bes j ρ h).o (g.bes j ρ h).line α γ'
    exact ⟨β₀⟩
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ι,
    ⟨p, J, q, χ, fun i => (hch i).1, β, Q, fun j ρ h i => (hcore j ρ h i).some, fun _ _ _ => ⊥, ζ₀, γ,
      fun n h i => h ▸ γ₀ i⟩, ?_, rfl, hStd⟩
  refine ⟨hPl.nodup, hPl.all, hPl.inj, fun x => (htP x).trans (hpl x).symm, fun i => ⟨(hch i).2, hPl.unit i⟩,
    fun j hj i => ((hStd.2 j hj).2 i).1, hline, fun j h => (htau j h).1,
    fun j h => ⟨_, (htau j h).2, fun i => GlobalTheory.LevPrimeData.splitPlace_valuation_neg_cmGenerator_pow_eq_one (p i) (hPl.unit i) _⟩,
    fun i => GlobalTheory.MiStar.normLast_valuation _ k (p i) q _ _ _ (g.oT B.R.m rfl) hpos (hG _) ζ₀ _ hz' (hval i).1 (hval i).2, fun n h i => ?_⟩
  subst h
  obtain ⟨h1, Λ, s, h2, h3, h4⟩ := hγ i
  exact ⟨h1, Λ, s, hNT ▸ h2, h3, h4⟩
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.VacTheta
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha hTr j hj
  have hv := hTr.pinX.vc j (by omega)
  refine ⟨hv.2.theta, hv.2.lat, ?_⟩
  exact (GlobalTheory.HeisComb.main _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _).2.2.1 (a.v.dT j) (a.g.vac j) hv.2.theta
    (isFinComb_of_combAt (ha.vis.atT j).1) hv.1
end GlobalTheory.Fam.VacTheta
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem volLev_top_ne_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho
end GlobalTheory.TopVol
end
end
end
