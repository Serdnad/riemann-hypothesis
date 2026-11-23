module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle498
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle302
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem star_character_eq_prod_additive_characters_root : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) :=
  by
  intro D X h hE hg
  obtain ⟨ψ', hψ, hchar⟩ := GlobalTheory.T.finiteAddChar_conj_eq_prod_placeResidueChars D X h hE hg
  refine ⟨ψ', fun kv i j => if GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j +
      GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j = 1 then 1 else -1, hψ, ?_⟩
  intro k hk Ns hM hU
  have hK : k ∈ X.B.I.Kset := hk.1
  rw [GlobalTheory.Mem.SymChar.otherInstanceCharacter_eq_psi_symmetricArgument, hchar _ _ _ (fun kv => GlobalTheory.T.heckeArgument_residue_eq_weighted_symmetricFrameSum D X h hE hg kv k hK _ (hM kv))
    (fun kv => GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum D X h hE hg kv k hK (Ns kv) (hM kv) (hU kv))]
  refine Finset.prod_congr rfl fun kv _ => ?_
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases he : symEdge D.R.rS D.R.k i j
  · simp only [if_pos he]
    rw [← add_mul, ← Int.cast_add]
    rcases GlobalTheory.Mem.SymChar.wt_add D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j with h2 | h2
    · rw [h2]; simp
    · rw [h2]; simp
  · simp only [if_neg he, add_zero]

end GlobalTheory.Mem.SymChar
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.twisted_chart_levels_determinant_maps_values : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∃ dt : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.DetTie (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev,
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) β cl, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r =
        (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).tw β).ch
          (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).K β).y cl) : ℂ) := by
  first | exact @GlobalTheory.Mem.Top.KerTwDet.detTie_vals | exact GlobalTheory.Mem.Top.KerTwDet.detTie_vals | (intros; apply GlobalTheory.Mem.Top.KerTwDet.detTie_vals <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

noncomputable section

namespace GlobalTheory.ChiRatStd

open GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT



theorem chiRatAll_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (L : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hL : L = I.latAt u a i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (L c.1)))
    (k : Ch → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) (β : Ch) :
    Formalism.L2.G.Cmp.ChiRatAll (K β).lev B.embLL := by
  subst hL
  obtain ⟨c, rfl⟩ := hR.onto β
  intro κ
  have hF : ChiFin I l Z (K (chOf c)).lev := by
    obtain ⟨n, hn, h⟩ := hfin (chOf c)
    exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨x, hx, ⟨q, hq⟩, -⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hP l Z u a i hi bad Ch chOf K k hR c hF κ
  obtain ⟨κ', hg, hq', -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hc := hR.chr c x κ' hg (by rw [hq']; exact hq)
  exact ⟨_, by rw [← hx]; exact hc.symm⟩



theorem chiRatAll_twChart : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  intro K B f T w _ _ _ Z t Wt nch n _ tt hstd u μ hμ j hj β
  obtain ⟨k, hR⟩ := hstd.1.reads u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  exact chiRatAll_of_reads w.I w.ok w.pins w.l Z u μ (j + 1) hj _ _ _ (hstd.1.lat u μ (j + 1))
    (fun β => tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) k hR
    (fun β => tt.forms.chi_fin u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) β

end GlobalTheory.ChiRatStd
end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem multR_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    MultR R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; MultR (real (reL a Z) R) (face (reL a Z) F)) :)) := by
  set_option backward.isDefEq.lazyWhnfCore false in
    with_unfolding_all
      have h := congrArg (fun (m : type_of% (@Mult a.D)) ↦ m R.θ (R.MY 0) (JR R F) (chiR R F))
        (mult_eq (reL a Z) a)
      exact h



theorem mvSee : MvSee := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h t hs
  obtain ⟨h1, h2, σ, red, hA, ⟨hr, hB⟩, hC⟩ := hs
  have hB' := cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) => ∀ k ∈ X.B.I.Kset, ∀ T ∈ E, ∀ (v : (MP R).Vec)
    (g : GA a.D (Yc a.D 0)), (T : MMap (MP R)) v (g * kap X h t k) =
      actL (Yc a.D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) ((T : MMap (MP R)) v) g) (multR_eq_reL a Z R F)) hB
  -- Reduce projections through the relabelling before comparing their parent records.
  set_option backward.isDefEq.lazyWhnfCore false in
    with_unfolding_all
      refine @SeeAt.mk _ _ _ _ _ _ _ _ _ _ (alg (reL a Z) iK) _ _ _ _ _ ?_ ?_ ?_
      · exact h1
      · exact h2
      · refine ⟨σ, red, ?_, ⟨?_, ?_⟩, ?_⟩
        · exact hA
        · exact hr
        · exact hB'
        · exact hC

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem mvRowJ : MvRowJ := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R X h G t eE j hj
  exact (by with_unfolding_all exact (hj :))

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem ep_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    EP R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; EP (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrFun (eeat_eq (reL a Z) R) (R.levR F true))



theorem mvEv_holds : MvEv := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h G t c hj
  exact (by with_unfolding_all exact ((cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) =>
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c) (ep_eq_reL a Z R F)) hj) :))

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), EntC q.x.ker → ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t ∧ GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O t ∧ GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z t := by
  intro 𝒮 K q hE
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
  simp only [ofObj, extraObj] at ker_eq
  cases ker_eq
  obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
    ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
      nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
    kT.unf kT.ok kT.served
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep w.I w.ok w.l Z t1 ((StdModel.stdKer_iff w.I w.l Z t1).2 s1)
  have ha : t.Adapted := by
    unfold Formalism.L2.Ker.KerEntTied.Adapted at a1 ⊢
    rw [o, e]
    exact a1
  have hc : GlobalTheory.Pdv.IsEntC t := by
    unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o1, e1]
    exact hE
  exact ⟨t, ⟨s, o.trans o1, heq_of_eq (e.trans e1), ha, p⟩, ⟨w.ok, w.pins, pin.isTw, pin.jets, rfl, s, hc, ha, p⟩, r⟩
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)



theorem rMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (t : TupU I U) (t' : TupU I U')
    (h : t.1 = t'.1) :
    rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ t = rMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ ⟨τ, hτ⟩)) :))



theorem lMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (i : Fin X.toD7.R.m)
    (t : TupU I U) (t' : TupU I U') (h : t.1 = t'.1) :
    lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i t = lMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ i t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i ⟨τ, hτ⟩)) :))



theorem mAU_mLU_ixOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  intro X px I hX U Xg tr t
  refine ⟨fun b => ?_, fun i => ?_⟩
  · cases b
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev1 I) (chr1 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
  · have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ X.toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dite_eq_left hi]
    exact lMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) i (tAll I (ixOf I U t)) t (tup_ixOf I t)

end GlobalTheory.Mem.R3.Rw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem hd_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (y : Hd R), ∃ y' : HdB b R, Same b y y' := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R y
  letI := alg b iK
  let y' : HdB b R :=
    { tup := (by with_unfolding_all exact (y.tup :))
      tupT := (by with_unfolding_all exact (y.tupT :))
      tupT_tup := (by with_unfolding_all exact (y.tupT_tup :))
      tup0 := (by with_unfolding_all exact (y.tup0 :))
      hm := (by with_unfolding_all exact (y.hm :))
      hTop := topMult_tr b y.hTop
      hinj := inj_tr b y.hinj
      PY := (by with_unfolding_all exact ((rowPsi b y.PY) :))
      PW := fun i => (by with_unfolding_all exact ((rowPsi b (y.PW i)) :))
      ιW := (by with_unfolding_all exact (y.ιW :))
      isomFin := fun i => ⟨(by with_unfolding_all exact ((y.isomFin i).bij :)), (by with_unfolding_all exact ((y.isomFin i).conj :)), (by with_unfolding_all exact ((y.isomFin i).lat :))⟩
      frameMatch := (by with_unfolding_all exact (y.frameMatch :))
      hF := (by with_unfolding_all exact (y.hF :))
      stdPsi := (by with_unfolding_all exact (y.stdPsi :)) }
  exact ⟨y', ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact ((HEq.refl y.PY.ψ) :)), (by with_unfolding_all exact ((HEq.refl fun i => (y.PW i).ψ) :))⟩⟩

end GlobalTheory.Mem.R3.Rw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Tr

theorem rowPsi_eq_of_psi {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

theorem reps_parts_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs
  letI := alg b iK
  have hY0 : (rowPsi a y'.PY).ψ = y.PY.ψ := (by with_unfolding_all exact ((eq_of_heq hs.PY) :))
  have hY : rowPsi a y'.PY = y.PY := rowPsi_eq_of_psi _ _ hY0
  have hW0 : (fun i => (rowPsi a (y'.PW i)).ψ) = (fun i => (y.PW i).ψ) := (by with_unfolding_all exact ((eq_of_heq hs.PW) :))
  have hW : ∀ i, rowPsi a (y'.PW i) = y.PW i := fun i => rowPsi_eq_of_psi _ _ (congrFun hW0 i)
  have hocc : HEq (y'.occ (face b F)) (y.occ F) := by
    unfold Hd.occ principalLevelFrame.OccRows principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.occ F)) :))
  have e : y'.occ (face b F) = y.occ F := (by with_unfolding_all exact ((eq_of_heq hocc) :))
  refine ⟨?_, ?_, ?_⟩
  · intro Φ rep h
    exact ⟨h.fin, fun π => by rw [e]; exact h.mem π, fun π π' hi => h.inj π π' hi, fun ρ hρ => h.all ρ (by rw [e] at hρ; exact hρ)⟩
  · intro bb π
    unfold Hd.prtE principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtE F bb π)) :))
  · intro i π
    unfold Hd.prtW
    rw [isotL_eq a b]
    delta isotLB
    rw [hW i]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtW F i π)) :))

end GlobalTheory.Mem.R3.Tr

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.field_datum_size_log_discriminant : RayField → ∀ (P : Pre) (δ : FieldDat P), Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  first | exact @GlobalTheory.Mem.Fld.TorsionSize.sz_discField | exact GlobalTheory.Mem.Fld.TorsionSize.sz_discField | (intros; apply GlobalTheory.Mem.Fld.TorsionSize.sz_discField <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chart_localGroup_le_baseLattice_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | exact GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | (intros; apply GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base <;> assumption)
end
