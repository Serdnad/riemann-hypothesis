module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle283
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle153
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle293
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.Pdv

theorem stabStd_eq_stabSet {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun γ => (fun v => γ.1 v) '' ((I.stp u a i).rep c).1.2 = ((I.stp u a i).rep c).1.2) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hs : _ = _ := s.2
    refine ⟨s.1, congrArg (fun p => p.1.1) hs, congrArg (fun p => p.1.2) hs, ?_⟩
    refine Prod.ext ?_ rfl
    exact GlobalTheory.KerJ.ufGL_val s.1.1
  · rintro ⟨b, hb, hq, rfl⟩
    refine ⟨⟨b, Subtype.ext (Prod.ext hb hq)⟩, ?_⟩
    refine Prod.ext ?_ rfl
    exact (GlobalTheory.KerJ.ufGL_val b.1).symm

theorem rep_coset_empty {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m)
    (c : (I.stp u a i).Cl) : ((I.stp u a i).rep c).1.2 = ∅ := by
  have key : ∀ y : Ys B.fields (B.R.N i), y = Ys.triv _ _ → ∀ s N, s ∈ y.ys N → s = ∅ := by
    rintro y rfl s N hs
    exact hs
  exact key _ (by unfold ysAt; exact if_neg hi) _ _ ((I.stp u a i).rep c).2

theorem stabStd_eq_stabSet_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun _ => True) := by
  rw [stabStd_eq_stabSet, rep_coset_empty I u a i hi c]
  congr 1
  funext γ
  simp

theorem stab_pin : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I hI hP l Z L hT Gi Gl K Y cX ex t hN hK hR u a
  change B.Word at u
  change I.ι at a
  obtain ⟨cc, cc_rec, cc_ok, δ', δ_ok, B', χ, χ_ok, idl, idl_ok, χ_rec, cD, X', seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S', word,
    T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf,
    kf_un, served⟩ := t
  obtain ⟨hX, hseam, hPr, hCh, hsel, hS, hword, htup, hcst, hidx, hm2, -, -, -, -⟩ := hK
  subst hX
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hCh
  obtain rfl := eq_of_heq hsel
  subst hS
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hidx
  subst hm2
  obtain ⟨r, hr, hrs⟩ := hR u a
  obtain rfl := eq_of_heq hr
  unfold GlobalTheory.KerJ.StabPin
  dsimp only
  have hm : B.R.m = B.R.m - 2 + 2 := (hI.idx_ok a).hm
  have h1 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  obtain ⟨hXo, hPro, -⟩ := base_fields_primes_ok B X
  have hG : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get h) := by
    intro j b h
    unfold levGAt
    rw [← Idx.some_get b h]
    rfl
  have hQ : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levQ j (b.get h) := by
    intro j b h
    unfold levQAt
    rw [← Idx.some_get b h]
    rfl
  have hGt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twLt I.Ch B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levGAt
    rw [hb]
    exact (topLev_levG_m _ _ _ _ _).trans (GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel B.fields (B.primes X) B.R I.Ch hXo hPro hI.ch_ok)
  have hQt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twTt (R := B.R) I.sel (I.tup a) B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levQAt
    rw [hb]
    refine (topLev_levQ_m _ _ _ _ _).trans ?_
    have hd : topDep B.R (I.cst a).M = 4 * B.R.m := by
      have := (hN a).2.1
      unfold topDep
      exact max_eq_left (by omega)
    rw [hd]
    exact GlobalTheory.T.level_quotient_eq_twisted_top B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) hXo hPro hI.sel_ok (fun i => hI.g_mem i)
      (fun v => hI.T_mem v)
  have hTop : ∀ j (hj : j = B.R.m) (c : ((I.rec7 l Z).chTw u a).cls j),
      stabStd I l Z u a j c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (twLt I.Ch j)
        (twTt (R := B.R) I.sel (I.tup a) j) ((I.stp u a j).rep c).1.1 (fun _ => True) := by
    intro j hj c
    subst hj
    rw [stabStd_eq_stabSet_triv I l Z u a _ (by omega) c, hGt, hQt]
  refine ⟨fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => c.1.get (by omega),
    fun c => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2, fun c => ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c).1.1,
    fun i _ c => hrs.1 i c, fun c => PtAt.mem_ybSet _ h1, ?_, ?_, ⟨fun c' => hrs.1 _ c', ?_⟩, ?_, ?_, fun c => hTop _ h1 c⟩
  · intro i hi c c' x
    rw [hrs.2 i (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm
      (Idx.some_get c'.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) h1,
      GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) u (B.R.m - 2) h1]
    rfl
  · intro i _ hi c
    rw [stabStd_eq_stabSet_triv I l Z u a i (by omega) c, hG i c.1 (by omega), hQ i c.1 (by omega)]
    rfl
  · intro b c
    obtain ⟨b0, hb0⟩ := (hI.idx_ok a).last_uniq
    have hcb : c.1.get (by omega) = b := (hb0 _).trans (hb0 b).symm
    rw [stabStd_eq_stabSet, hG _ c.1 (by omega), hQ _ c.1 (by omega), hcb]
    rfl

end GlobalTheory.Pdv

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.unlinkedLengthOneSegments_firstTerms_not_nuTwist : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  first | (exact @GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (exact GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (intros; apply GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  first | (exact @GlobalTheory.DegOneChar.exists_charLift) | (exact GlobalTheory.DegOneChar.exists_charLift) | (intros; apply GlobalTheory.DegOneChar.exists_charLift  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.supercuspidalSupport_twist_nu_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  first | (exact @GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (exact GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (intros; apply GlobalTheory.RoadU.TwistSupp.supp_nu_chars  <;> assumption)
end

section

namespace GlobalTheory.AtG

theorem jetSplitAmb_holds : JetSplitAmb := by
  intro D X s cc δ B χ cD hok hcc hδ hχ a b S N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m
  exact Formalism.L2.Ker.Test.jetAtSplit_ambOf s B χ cD hok hcc hδ hχ a b S N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m

end GlobalTheory.AtG
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ (x γ : WithZero (Multiplicative ℤ)) (hx : x ≠ 0) (hγ : γ < 1) :
    ∃ n : ℕ, γ ^ n < x := by
  by_cases h0 : γ = 0
  · exact ⟨1, by simp [h0, zero_lt_iff.2 hx]⟩
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hg : Multiplicative.toAdd g < 0 := by
    have : g < 1 := by exact_mod_cast hγ
    exact this
  refine ⟨(Multiplicative.toAdd a).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (g ^ ((Multiplicative.toAdd a).natAbs + 1)) < Multiplicative.toAdd a
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  have h1 := neg_abs_le (Multiplicative.toAdd a)
  have h2 : Multiplicative.toAdd g ≤ -1 := by omega
  have h3 := abs_nonneg (Multiplicative.toAdd a)
  nlinarith

theorem GlobalTheory.TwV.Xc.adIso_comp_zero_of_div : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ iE iA hrat hint ι hι z ℓ D hℓ hD hdiv P hP
  set y := ι (iA.symm z) with hy

  have hc : ∀ n : ℕ, iA.symm (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      = ((D : E') / (ℓ : E') ^ n) ⊗ₜ[F'] (1 : FiniteAdeleRing (𝓞 F') F') := by
    intro n
    rw [RingEquiv.symm_apply_eq, hrat]
    simp [map_div₀, map_pow, map_natCast]
  have hbound : ∀ n : ℕ, Valued.v (((D : E') / (ℓ : E') ^ n : E') : P.adicCompletion E') * Valued.v (y P) ≤ 1 := by
    intro n
    have hmem := hdiv n
    have h1 : iA.symm ((((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z) ∈ RInt F' E' := by
      rw [← hint, RingEquiv.apply_symm_apply]; exact hmem
    have h2 := (hι.2 _).1 h1 P
    rw [map_mul, hc, map_mul, hι.1, ← hy] at h2
    rw [← map_mul]
    simpa using h2
  have hval : ∀ c : E', Valued.v ((c : E') : P.adicCompletion E') = P.valuation E' c :=
    fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P c
  have hℓE : ((ℓ : 𝓞 E') : E') = (ℓ : E') := by simp
  have hlt : P.valuation E' (ℓ : E') < 1 := by
    rw [← hℓE]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 hP
  have hℓ0 : P.valuation E' (ℓ : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hℓ.ne'
  have hD0 : P.valuation E' (D : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hD.ne'
  by_contra hyP
  have hyv : Valued.v (y P) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hyP
  obtain ⟨n, hn⟩ := GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ
    (P.valuation E' (D : E') * Valued.v (y P)) (P.valuation E' (ℓ : E')) (mul_ne_zero hD0 hyv) hlt
  have hb := hbound n
  rw [hval, map_div₀, map_pow] at hb
  have hpos : (0 : WithZero (Multiplicative ℤ)) < P.valuation E' (ℓ : E') ^ n :=
    zero_lt_iff.2 (pow_ne_zero _ hℓ0)
  have : P.valuation E' (D : E') * Valued.v (y P) ≤ P.valuation E' (ℓ : E') ^ n := by
    have he : P.valuation E' (D : E') * Valued.v (y P)
        = P.valuation E' (D : E') / P.valuation E' (ℓ : E') ^ n * Valued.v (y P) * P.valuation E' (ℓ : E') ^ n := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero _ hℓ0)]
    rw [he]
    simpa using mul_le_mul' hb (le_refl (P.valuation E' (ℓ : E') ^ n))
  exact absurd hn (not_lt.2 this)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem isPt_move_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad), LocGood σ J A → LocInt A → LocHyp S A → A.ActB → (∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) → ∀ (i : G.comp) (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J → ∀ κa : S.U, A.IsAway i γ κa.1 → ∀ (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))), (∀ v, colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = colSpan (G.P.W v) (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) → ∀ x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κ.1 ∧ S.chi κ * S.chi κa = 1 := by
  intro F E _ _ _ _ _ σ n p G A J T f bad S hG hW hH hA hbad i γ hγ κa hκa g g' hg x x' hx hx'
  have hy := A.isPt_smul hA i g x.1 κa.1 hx γ hκa
  have hyU : GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κa.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (ratInU _ hγ) x.2) (Subgroup.inv_mem _ ((S.U_eq κa.1).1 κa.2).1)
  obtain ⟨κ₁, e₁, hχ₁⟩ := ptOne_of (A := A) S hW hH hbad i (fun v => colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (fun v => (G.lev i).act v γ * g v) g' ⟨_, hyU⟩ x' (fun v => rfl) (fun v => (hg v).symm) hy hx'
  refine ⟨κa⁻¹ * κ₁, ?_, ?_⟩
  · rw [e₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rw [map_mul, map_inv]
    apply Units.ext
    simp [hχ₁]

end GlobalTheory.TwV.Xc

end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CongProd

open _root_.Formalism.L2.Col GlobalTheory.TwU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ _root_.Formalism.L2.Herm.intAf F E := fun x => (_root_.Formalism.L2.DIV.toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int₁ (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (_root_.Formalism.L2.DIV.toRInt F E x).2⟩

theorem intAtA_sum₁ {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int₁ (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add₁ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congAt_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))),
    GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  intro F E _ _ _ _ _ Q n N k k' h h' a b
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (algebraMap (𝓞 E) E (((qOf Q : ℕ) : 𝓞 E) ^ n)) with hd
  have hcd : d * c = 1 := by
    rw [hc, hd, ← map_mul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have e : ((k * k' : GL (Fin N) _) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      ((k : Matrix (Fin N) (Fin N) _) - 1) * ((k' : Matrix (Fin N) (Fin N) _) - 1) +
        (((k : Matrix (Fin N) (Fin N) _) - 1) + ((k' : Matrix (Fin N) (Fin N) _) - 1)) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_add₁ (intAtA_sum₁ _ _ fun l _ => ?_) (intAtA_add₁ (h a b) (h' a b))
  have e2 : ∀ x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, c * (x * y) = d * ((c * x) * (c * y)) := by
    intro x y
    linear_combination (-(c * (x * y))) * hcd
  rw [e2]
  exact intAtA_mul₁ (intAtA_int₁ _) (intAtA_mul₁ (h a l) (h' l b))

end GlobalTheory.CongProd
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem qOf_seamP : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  intro D X s P
  have hJ : (GlobalTheory.TwU.seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
    rw [GlobalTheory.TwU.mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have := (RingOfIntegers.mapRingEquiv s.iE).injective hzx
      subst this; exact hz
  unfold Formalism.L2.Col.qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hJ).toEquiv).symm

end GlobalTheory
end
