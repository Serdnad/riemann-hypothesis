module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle441
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle096
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

@[expose] public section

section



section
noncomputable section
section Loc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.TopCongr GlobalTheory.LocMod
namespace GlobalTheory.Fam.TopFrames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.Fam.TopFrames
end Loc
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix
open GlobalTheory.SeeSaw.BaseFrame GlobalTheory.TopStep
namespace GlobalTheory.Fam.TopFrames
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
end GlobalTheory.Fam.TopFrames
end Gen
section World
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
namespace GlobalTheory.Fam.TopFrames
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
section Tw
variable {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀}
end Tw
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}

theorem valuation_frs_sub_kronecker_lt_one (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads) (P : BadPr I (W.P.I.tup t))
    (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : J.Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  have hm : j ≤ B.R.m := by omega
  obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj β
  have h4 : ¬ ∃ i, (J.G i).q.v = P.1.under (𝓞 B.host.F) := by
    rintro ⟨i, hi⟩
    rw [(GlobalTheory.LocMod.PinEx.place_facts _ (J.G i).idem).1] at hi
    have h5 := ((TwistPrimes.twist_primes_away I hW.tr.ok).2 u (W.P.I.tup t) (J.pl i) ((hW.tq.Q t _).1 (J.mem i))).1
    rcases (under_eq_iff B.host (J.pl i) P.1).1 hi.symm with h6 | h6
    · exact h5.2.1 (h6 ▸ hP)
    · exact h5.2.2.2.1 (h6 ▸ hP)
  have h5 := finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 h4
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 (P.1.under (𝓞 B.host.F))
    fun hT => Formalism.L2.Col.rls_T_notUnder l.pr u _ hT ⟨P.1, hP, rfl⟩
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (J.A.kb j β) = 1 := by
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm β).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j β).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] (P.1.under (𝓞 B.host.F)).adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have h9 := (hJ.is.base j hm β).1
  rw [e]
  exact GlobalTheory.SeeSaw.BaseFrame.lift_near_one (y := 1) (by rw [one_mul]; exact h9) (by rw [one_mul]; exact h9) h9 (hJ.is.base j hm β).2
    ⟨P.1, hP⟩ hk (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hP⟩) r c

theorem fm_beta_eq {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (hIs : a.Is) (hTr : a.True) (hA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0)
    (n : Fin a.n) (r) : (∀ c, (a.G n).FM.β r (Sum.inl c) = if r.val = GlobalTheory.SymBridge.zPos c then 1 else 0) ∧
      (a.G n).FM.β r (Sum.inr ()) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) := by
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have hA' : ∀ j (h : j = (I.rec7 l Z).R.m) r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0 := by
    rintro _ rfl
    exact hA
  have hB' : ∀ j (h : j = (I.rec7 l Z).R.m) r, ((a.g.oT j h).iB *ᵥ a.o.ζ₀) r =
      if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    rintro _ rfl r
    exact hTr.z0 r
  obtain ⟨-, ⟨e, he, hT⟩, hz⟩ := hIs.stdG n
  rw [(a.G n).last]
  refine ⟨fun c => ?_, ?_⟩
  · rw [fromCols_apply_inl, hT, Matrix.mul_apply, Finset.sum_eq_single (e c)]
    · rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, ← he c]
      refine (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hA' _ _ r (e c))).trans ?_
      split_ifs
      exacts [map_one _, map_zero _]
    · intro b _ hb
      rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [fromCols_apply_inr, hz]
    refine Eq.trans ?_ (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hB' _ (a.G n).hs r))
    refine Eq.trans ?_ (map_sum (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (fun b => (a.g.oT _ (a.G n).hs).iB r b * a.o.ζ₀ b) Finset.univ).symm
    show ∑ b, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((a.g.oT _ (a.G n).hs).iB r b) * _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (a.o.ζ₀ b) = _
    exact Finset.sum_congr rfl fun b _ => (map_mul (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) _ _).symm

theorem xiStd_eq_const_mul_locXi_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch ((a.G n).s + 1)) (γ : J.Ch ((a.G n).s + 1 + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ C : ℂ,
  (∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
     GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
     ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y')) →
  ∀ (hj : (a.G n).s + 1 + 1 ≤ B.R.m) z, _root_.GlobalTheory.Fam.TopLoc.standardXi a n z =
    C * B.embLL (GlobalTheory.QTw.locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (GlobalTheory.QTw.homOf I l Z ((a.G n).s + 1) hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hA n t J hJ α γ P hP C hC hj z
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt P.1 x := by
    have hR := (hIs.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hm : (a.G n).s + 1 ≤ B.R.m := Nat.le_of_succ_le hj
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hlt := GlobalTheory.SeeSaw.LevelData.val_lt_one_iff hint
  obtain ⟨e', he'⟩ := exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨e, he⟩ := exists_topOrd B.R (a.G n).s hs
  have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv hs (J.ι _ α)
  have hF' := top_near hW.tr.ok hJ.is P hPv hs (J.ι _ γ)
  have hq := intAt_q_mul (A := J.A) P hPv hs (J.ι _ α)
  have hco := hJ.cosG n α e' he'
  have hx : locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (homOf I l Z ((a.G n).s + 1) hj z) =
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P
        (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P) (homOf I l Z ((a.G n).s + 1) hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2)) := by
    unfold locXi
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dif_pos hs]
    rfl
  rw [hx]
  clear hx
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P = f at hF hq ⊢
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P = f' at hF' ⊢
  generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g10⟩ := id (GlobalTheory.SeeSaw.LevelData.type_prime hPv)
  have hqv : HeightOneSpectrum.valuation B.fields.E P.1 (Formalism.L2.Col.qOf P.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hPv
    exact GlobalTheory.AtTypeExists.valuation_norm P.1 (g1 ▸ g4)
  let Jx := XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1)
  have hy : (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)) :
      (Jx → (a.G n).k) ⧸ _root_.GlobalTheory.StepData.box Jx (1 : (a.G n).kˣ)) =
      Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f.symm y (e' r)) := by
    refine GlobalTheory.SeeSaw.StdMatch.mk_eq_mk_of_int fun c => ?_
    have h1 := (hint _).2 (intAt_sub_of_near hqv hF hq (e' c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e' c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco c
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  refine Eq.trans ?_ (hC e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r) _ _ hq)
  refine Eq.trans ?_ (congrArg (fun w => ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) w _) hy)
  have e1 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (rankN (I.rec7 l Z) _ hm) (rankN (I.rec7 l Z) _ hj) f f' e' e
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f (Pi.single (e' c) 1) (finCongr (rankN (I.rec7 l Z) _ hm) r)))
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e c) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)))
    (fun _ _ => rfl) (fun _ _ => rfl) z
  refine xiTop_frames (a.G n).unitVol (a.G n).S (Fin B.R.t) ((a.G n).FX _ le_rfl) (a.G n).FM
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hm).2.2) ((a.G n).latX _ le_rfl))
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hj).2.2) (a.G n).latM) (fun r c => ?_) (fun r c => ?_) _ e1
  · obtain ⟨e₁, h1, h2⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
    have h3 := (hlt _).2 (hF (finCongr (rankN (I.rec7 l Z) _ hm) r) (e' c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, (he' c).trans (h1 c).symm] at h3
    have h4 : ((a.G n).FX ((a.G n).s + 1) le_rfl).β r c = if r.val = (e₁ c).val then 1 else 0 :=
      (congrFun (congrFun h2 r) c).trans (Matrix.one_apply.trans (if_congr Fin.ext_iff rfl rfl))
    exact (congrArg (fun w => valuation (a.G n).k (_ - w)) h4).trans_lt h3
  · have h3 := (hlt _).2 (hF' (finCongr (rankN (I.rec7 l Z) _ hj) r) (e c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, he c] at h3
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Fam.TopFrames.fm_beta_eq hIs hTr hA n r
    show valuation (a.G n).k (_ - (a.G n).FM.β r c) < 1
    rcases c with c | c
    · exact (congrArg (fun w => valuation (a.G n).k (_ - w)) (h1 c)).trans_lt h3
    · refine (congrArg (fun w => valuation (a.G n).k (_ - w)) h2).trans_lt ?_
      have h4 := (hlt ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E)).2 ((P.1.valuation_lt_one_iff_mem _).2 (g10 u))
      have h5 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u : 𝓞 B.host.E) : B.host.E) - 1 :=
        ((_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_sub ((X.piT u : 𝓞 B.host.E) : B.host.E) 1).trans (congrArg _ (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_one)
      rw [h5] at h4
      replace h3 : valuation (a.G n).k (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e (Sum.inr c)) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)) -
          if (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 then 1 else 0) < 1 := h3
      have h6 : 0 < B.R.N B.R.m := by
        have := (e (Sum.inr c)).2
        rw [← hs]
        omega
      by_cases hr : r.val + 1 = B.R.N B.R.m
      · rw [if_pos (show (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from Nat.eq_sub_of_add_eq hr)] at h3
        rw [if_pos hr]
        have h7 := Valuation.map_sub_lt _ h3 h4
        rwa [sub_sub_sub_cancel_right] at h7
      · rw [if_neg (show ¬ (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from fun h => hr (by
          have h8 : r.val = B.R.N B.R.m - 1 := h
          omega))] at h3
        rw [if_neg hr, map_zero]
        exact h3
end GlobalTheory.Fam.TopFrames
end World
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_twist_scalar_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' a.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX
    (_root_.GlobalTheory.Fam.pk_z W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.r = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have hs : (a.Q PP ⟨t, hP⟩).s + 1 + 1 =
        (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m :=
      (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg,
      PP'.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠
        PP.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    intro PP' hPP' e
    have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.pk.bot.hyp.2.2.2.1.lev
    have hApart := GlobalTheory.StepLifts.places_apart _ hl t
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with hEq | hConj
    · exact Finset.disjoint_left.1 hApart.2 hPP' (hEq ▸ hP)
    · exact hApart.1 PP' hPP' PP (Or.inr hP) (GlobalTheory.GoodPrimes.isConjPl_iff.2 hConj)
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.Fam.pk_z W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E, PP'.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠ PP.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) →
        Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP' (Lev.finE (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (Lev.finE (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (_root_.GlobalTheory.Fam.pk_z W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
noncomputable section
namespace GlobalTheory.QLevMid

theorem level_at_place_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.pk.bot.hyp.2.2.2.1.lev
  obtain ⟨N, hSD⟩ : ∃ N, IsSDFrame (Yc _ j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) N := ⟨_, hl.βY j hj⟩
  have hPg : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg,
      PP'.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ≠
        PP.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    intro PP' hPP' e
    have hApart := GlobalTheory.StepLifts.places_apart _ hl t
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with hEq | hConj
    · exact Finset.disjoint_left.1 hApart.2 hPP' (hEq ▸ hP)
    · exact hApart.1 PP' hPP' PP (Or.inr hP) (GlobalTheory.GoodPrimes.isConjPl_iff.2 hConj)
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK
  have hQ : ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))
end GlobalTheory.QLevMid
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_row_pair_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i (hm : (J.G i).s + 1 + 1 ≤ B.R.m) (γ : J.Ch₀ ((J.G i).s + 1 + 1)) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((J.G i).s + 1)) (Fin B.R.t) ((J.G i).s + 2) ⊕ Unit ≃ Fin (B.R.N ((J.G i).s + 1 + 1))), GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e → ∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b)) = (J.G i).FM.β r b := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hiA t J hJ i hm γ e he r b
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have key : ∀ j (h : j = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m), (∀ r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0) ∧
      ∀ r, vecB (a.g.oT j h) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro j h
    subst h
    exact ⟨hiA, fun r => hat.z0 r⟩
  obtain ⟨hA, hz⟩ := key _ (J.G i).hs
  obtain ⟨-, ⟨e', he', hT'⟩, hz0⟩ := ha.stdQ (J.pl i) ⟨t, J.mem i⟩
  let ι : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (J.G i).k := (J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
  have hL' : baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b) =
      if r.val = (e b).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := by
    exact GlobalTheory.Fam.TopFrame.frsF_top J.A hJ.is hW.tr.ok (J.P i) (hJ.tw i).nmem _ hs γ
      (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) _ hm) r) (e b)
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
    · exact (congrArg _ (ite_eq_right hc)).trans (mul_zero _)
    · exact (congrArg _ (ite_eq_left rfl)).trans (mul_one _)
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
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem xi_eq_xiOff_mul_join_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ j hj α γ z
  rw [(GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is).1 j hj (J.ι j α) (J.ι (j + 1) γ) z]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => J.P i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hJ.eq i]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.disjoint_left.1 ((_root_.GlobalTheory.PkPlaces.pk_places_alt W hW.pk).2 t).1 ((hW.lev.2.1 _).2 h) (J.mem i)
  · intro i₁ _ i₂ _ h
    exact hJ.inj (((hJ.eq i₁).symm.trans (congrArg Subtype.val h)).trans (hJ.eq i₂))
  · intro P hP
    have hv : P.1 ∉ (B.primes X).vGs := (Finset.mem_filter.1 hP).2
    have hq : P.1 ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact absurd h hv
      · exact h
    obtain ⟨i, hi⟩ := hJ.surj _ ((hW.tq.Q t P.1).2 hq)
    exact ⟨i, Finset.mem_univ _, Subtype.ext ((hJ.eq i).trans hi)⟩
  · intro i _
    rfl
end GlobalTheory.Fam
end
end
