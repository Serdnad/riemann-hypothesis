module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle407
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.Chart0

open GlobalTheory.Mem.Col2.MemChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

abbrev lvQ (a : I.ι) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

def yT (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) : GA B (B.R.N 0) :=
  Classical.epsilon fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)

theorem yT_spec (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    PtOf (yT I u a c * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a 0).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1))
    ⟨g * (kStd X u (B.R.N 0))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem cos0 {u : B.Word} {a : I.ι} (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ (by have := B.R.two_le_m; omega)] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem stepZero_classes_bijective_decoratedLattice (hI : I.Ok) (u : B.Word) (a : I.ι) :
    Function.Bijective fun c : (I.stp u a 0).Cl =>
      decoCls (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ((I.stp u a 0).rep c).1.1.deco := by
  letI := StepZero.idxUnique (hI.idx_ok a)
  have h := StepZero.clMap_bijective (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)) (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) (StepZero.levQAt_zero (I.Tp a) (hI.idx_ok a))
  convert h using 1
  funext c
  have e := StepZero.clMap_cl (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) c.1 ((I.stp u a 0).rep c)
  have e2 : (I.stp u a 0).cl c.1 ((I.stp u a 0).rep c) = c := by
    obtain ⟨b, q⟩ := c
    exact congrArg (Sigma.mk b) ((I.stp u a 0).rp_spec b q)
  rw [e2] at e
  exact e.symm

theorem stab_range0 (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (stM (lvG I a) (lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c).range ↔
      ∃ g : UF B.fields.E (B.R.N 0) × (colLev I.Ch 0).grp, ufGL B.fields.E (B.R.N 0) g.1 = γ ∧
        g • ((I.stp u a 0).rep c).1.1.deco = ((I.stp u a 0).rep c).1.1.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) ((I.Tp a).pref u 0) (StepZero.levGAt_zero (I.Tp a) hL) c.1 g, rfl, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) _ (StepZero.levGAt_zero (I.Tp a) hL) c.1 g _).symm.trans (congrArg (fun q => q.1.1.deco) hg)
  · rintro ⟨g₀, rfl, hg⟩
    obtain ⟨g, h1, h2⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy (StepZero.levGAt_zero (I.Tp a) hL)
      (StepZero.levQAt_zero (I.Tp a) hL) c.1 _ _ g₀ hg
    exact ⟨⟨g, h2⟩, congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h1⟩

theorem red0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u), redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)

theorem lev0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q) :
    x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, cos0 I _ _⟩
    · show ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := red0 I hI hPr u a c x κ h1 (h2 ▸ h)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = colLev I.Ch 0 → ∀ g : Λ'.grp,
        g.1 ∈ (colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

theorem chr0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (hxU : x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp)
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ((levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) ⟨x, hxU⟩ : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a 0).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩ = (⟨κ.2.1.1, hΛ c.1 ▸ κ.2.1.2⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((lvG I a c.1).chr κ.2.1 * (lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl



theorem charts_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  intro B X I hI hP l Z u a
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa only [Ideal.absNorm_eq_natCard] using hPr.vT_norm u P hP) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  refine ⟨badG (I.rec7 l Z), Unit, chOf, fun _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)

end GlobalTheory.Mem.Col2.TC.Chart0
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsSpan

variable (D : D7) (S : RatDat D.ntw)

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := by
    simp only [actL, map_one, Units.val_one, inv_one, one_smul]
  map_mul' g h := by
    simp only [actL, map_mul, Units.val_mul, mul_inv]
    exact (smul_mul_smul_comm _ _ _ _).symm

def finiteLevelGroupFintype : Fintype (G0g D.nd) := Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

def opL (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem opL_of (j : ℕ) (g : G0g D.nd) : opL D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [opL, MonoidAlgebra.of_apply, actLHom]

theorem opL_eL (j : ℕ) : opL D S j (eL D) = ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g := by
  rw [finsum_eq_sum_of_fintype]
  simp [opL, eL, MonoidAlgebra.lift_apply, actLHom, Finsupp.sum_fintype]

variable {D S}

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h :=
  (actLHom D S j).map_mul g h

theorem eLop_idem (he : EIdem D) (j : ℕ) (x : S.WL j) :
    opL D S j (eL D) (opL D S j (eL D) x) = opL D S j (eL D) x := by
  rw [← Module.End.mul_apply, ← map_mul, he.1]

theorem eLop_comm (he : EIdem D) (j : ℕ) (g : G0g D.nd) (x : S.WL j) :
    opL D S j (eL D) (actL D S j g x) = actL D S j g (opL D S j (eL D) x) := by
  rw [← opL_of D S j g, ← Module.End.mul_apply, ← map_mul, he.2 g, map_mul, Module.End.mul_apply]

def fintypeU : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _

attribute [local instance] fintypeU


variable (D) in
def cU (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : ↥(Formalism.IndefR.NX.U D.nd)) : ↥D.LL0 :=
  (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * ((psiUOf D.nd (NX.xiRed D) θ u⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

theorem cU_mul (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u' u : ↥(Formalism.IndefR.NX.U D.nd)) :
    ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) * cU D θ (u' * u) = cU D θ u := by
  unfold cU
  rw [mul_inv_rev, map_mul, Units.val_mul, map_inv (psiUOf D.nd (NX.xiRed D) θ) u', Units.val_inv_eq_inv_val]
  have h0 : ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
  field_simp

def projL (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), ((cU D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j u

theorem projL_isot (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u' : ↥(Formalism.IndefR.NX.U D.nd)) (w : S.WL j) :
    actL D S j u' (projL (S := S) θ j w) =
      (((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • projL (S := S) θ j w := by

  simp only [projL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, actL_mul, Module.End.mul_apply]
  congr 1
  rw [← cU_mul θ u' u]
  push_cast
  ring

theorem goodL_of (he : EIdem D) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) (w : S.WL j) :
    opL D S j (eL D) (projL (S := S) θ j w) ∈ goodL D S θ j := by
  unfold goodL
  rw [← opL_eL, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun u => ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul, eLop_idem he]
  · rw [Module.End.mem_eigenspace_iff, ← eLop_comm he, projL_isot, map_smul]

section KSide

variable (T : TwR D.LL0 D.nd)

def projT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), readT D T i b (cU D In.θ u) • (actGT D T S In.rho In.chi i j b u).toLinearMap

theorem card_ne (i : T.Tw) (b : Bool) :
    readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
  refine (map_ne_zero (readT D T i b)).mpr fun h => ?_
  have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
  exact Fintype.card_ne_zero (by exact_mod_cast h')

theorem projT_fix (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (z : FmT D T S i j b)
    (hz : z ∈ Fm0T D T S In.rho In.chi In.θ i j b) : projT T In i j b z = z := by
  have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), actGT D T S In.rho In.chi i j b u z =
      readT D T i b ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
    intro u
    have h := (Submodule.mem_iInf _).mp hz u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  simp only [projT, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
  have hc : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
      (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
    intro u
    unfold cU
    rw [map_inv, Units.val_inv_eq_inv_val]
    have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
    field_simp
  simp only [hc, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
    rw [map_inv₀, ← map_natCast (readT D T i b)]
    exact mul_inv_cancel₀ (card_ne T i b)
  rw [h1, one_smul]

end KSide

theorem projT_phi (T : TwR D.LL0 D.nd) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (Φ : S.WL j →+ FmT D T S i j b)
    (hsl : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hact : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (w : S.WL j) : projT T In i j b (Φ w) = Φ (projL (S := S) In.θ j w) := by

  simp only [projT, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hsl, hact]

theorem span_one_tmul {R A M : Type} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Submodule.span A (Set.range fun m : M => (1 : A) ⊗ₜ[R] m) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m =>
    have h : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy


variable (S) in
def oneT (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) (w : ↥(WKr D S j)) : FmT D T S i j b :=
  (1 : KT D T i b) ⊗ₜ[S.Ks] w

theorem FmT_span (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (T.O i)) (Set.range (oneT S T i j b)) = ⊤ :=
  span_one_tmul (R := S.Ks) (A := KT D T i b) (M := ↥(WKr D S j))

end GlobalTheory.HeightCounting.FormsSpan


open GlobalTheory.HeightCounting.FormsSpan in
theorem GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  intro D S In T i j b _ _ he Φ hsl hact hE h1 y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  rw [← projT_fix T In i j b z hz]
  have key : Submodule.span (FractionRing (T.O i))
      (Set.range (oneT S T i j b)) ≤
      (Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eGT D T S In.rho In.chi i j b ∘ₗ projT T In i j b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eGT D T S In.rho In.chi i j b (projT T In i j b (oneT S T i j b w)) ∈
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [show oneT S T i j b w = Φ (w : S.WL j) from (h1 w).symm, projT_phi T In i j b Φ hsl hact, ← hE, ← opL_eL]
    exact Submodule.subset_span ⟨_, goodL_of he In.θ j (w : S.WL j), rfl⟩
  exact key (Submodule.eq_top_iff'.mp (FmT_span (S := S) T i j b) z)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem star_mul_self_of_pow (D : D7) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    star ((ζ : ↥D.LL0) : D.what₂.LL) * ((ζ : ↥D.LL0) : D.what₂.LL) = 1 := by
  apply D.what₂.embLL.injective
  rw [map_mul, map_one, D.starLL_cx]
  have hp : ((ζ : ↥D.LL0) : D.what₂.LL) ^ n = 1 := by
    have e := congrArg (fun u : (↥D.LL0)ˣ => ((u : ↥D.LL0) : D.what₂.LL)) h
    simpa using e
  have hz : (D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)) ^ n = 1 := by
    rw [← map_pow, hp, map_one]
  have hn1 : ‖D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
  simp

theorem readT_false_eq (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (x : ↥D.LL0) : readT D T i false x = readT D T i true ⟨star (x : D.what₂.LL), hstar x⟩ := by
  simp only [readT, RingHom.comp_apply, Bool.false_eq_true, if_false, if_true]
  rw [T.restX_coefficientEmbedding_conj i x ⟨star (x : D.what₂.LL), hstar x⟩ rfl]

theorem readT_false_mul_true (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    readT D T i false (ζ : ↥D.LL0) * readT D T i true (ζ : ↥D.LL0) = 1 := by
  rw [readT_false_eq D T hstar, ← map_mul]
  have e : (⟨star ((ζ : ↥D.LL0) : D.what₂.LL), hstar _⟩ : ↥D.LL0) * (ζ : ↥D.LL0) = 1 :=
    Subtype.ext (star_mul_self_of_pow D ζ n hn h)
  rw [e, map_one]

theorem mul_pow_g_eq_one (g : ℕ) (m : Multiplicative (ZMod g)) : m ^ g = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem psiUT_eq_thSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  intro D S In T hstar
  refine ⟨fun i b u => ?_, fun _ i k h => ?_⟩
  · simp only [psiUT, MonoidHom.comp_apply, psiUOf_apply, map_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    cases b
    · simp only [thSide, Bool.false_eq_true, if_false, MonoidHom.inv_apply, MonoidHom.comp_apply]
      apply Units.ext
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.coe_map]
      refine eq_inv_of_mul_eq_one_left ?_
      exact readT_false_mul_true D T hstar i _ (D.host.g kv.1) (D.host.g_prime kv.1).ne_zero
        (by rw [← map_pow, mul_pow_g_eq_one, map_one])
    · rfl
  · apply In.θ_ne k
    refine MonoidHom.ext fun x => Units.ext ?_
    apply (readT D T i true).injective
    have e := congrArg (fun u : (FractionRing (T.O i))ˣ => (u : FractionRing (T.O i))) (DFunLike.congr_fun h x)
    simpa using e

end GlobalTheory.HeightCounting.FormsStep
end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.measurePreserving_flagFibreChartCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), MeasurePreserving (coords X κ) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_coords_sorted | exact GlobalTheory.FlagFibre.measurePreserving_coords_sorted | (intros; apply GlobalTheory.FlagFibre.measurePreserving_coords_sorted <;> assumption)
end
