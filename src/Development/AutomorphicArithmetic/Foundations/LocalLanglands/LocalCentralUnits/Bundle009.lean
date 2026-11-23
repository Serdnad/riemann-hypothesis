module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle006
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle007
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem par_of_laws {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : LawsT a ha rc) {y : IrrGL (k := w.adicCompletion E)}
    (hc : y.IsCusp) (hG : Good y) (hd : DZ y) : Par a y (rc y) := by
  exact
    { irr := L.cusp y hc
      dim := L.dim y
      tame := L.depth y hG hd
      central ω hω := L.central y ω hG hω
      type := (typeIff E Ω A w h rc).1 L.type y }

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.recTUnique :
    UpperTheory.Zero.LLC.RecTUnique := by
  rintro E Ω _ _ _ _ _ A w h rc rc' ⟨a, ha, L⟩ ⟨a', ha', L'⟩ x hx
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain rfl : a' = a := (artEx E Ω A w h).unique ha' ha
  have key : ∀ y : IrrGL (k := w.adicCompletion E), y.IsCusp → GoodCusp y → rc y = rc' y := by
    intro y hc hg
    rcases id hg with h1 | ⟨⟨g, hgp, i, hi⟩, y₀, χ, hχ, hdz, rfl⟩
    · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ y).2.2.2.2.1 h1).2
      rw [L.one, L'.one]
    · haveI := hgp
      have ht := (clBasic _ y₀).2.1 χ hχ
      have hc₀ : y₀.IsCusp := ht.2.1.1 hc
      have hG : Good y₀ := ((goodSeg _).2.1 y₀ hc₀).2 (ht.2.2.1.1 hg)
      have e : rc' y₀ = rc y₀ :=
        (parUniq E Ω A w h _ ha g i hi y₀ hc₀ hdz (rc y₀) (par_of_laws L hc₀ hG hdz)).1 (rc' y₀)
          (par_of_laws L' hc₀ hG hdz)
      rw [L.twist _ _ _ hG, L'.twist _ _ _ hG, e, L.one, L'.one]
  obtain ⟨m, hm⟩ := Pr.exh _ x
  have hm' : IsL ((m.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
  rw [L.langlands _ x hm', L'.langlands _ x hm']
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [key Δ.first Δ.isCusp_first (((goodSeg _).1 _ x hm').1 hx Δ hΔ)]
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rc_tw_of_segments {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {r rc : IrrGL (k := w.adicCompletion E) → WD h} (hL : IsLExt r rc)
    (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E))
    (hx : IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (hr : ∀ Δ ∈ l, r (Δ.first.tw χ hχ) = (r Δ.first).lpTwist (χ.comp a) (ha.smooth hχ)) :
    rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨-, hs, ht, -⟩ := GlobalTheory.T.weil_deligne_sum_twist_compat E Ω A w h
  have h2 := GlobalTheory.T.isLanglandsClassification_twist_multisegment _ (l : Multiset (Segment (w.adicCompletion E))) x χ hχ hx
  rw [hL l x hx, hL (l.map fun Δ : Segment _ => Δ.tw χ hχ) (x.tw χ hχ) h2, segSum, segSum, hs, List.map_map, List.map_map]
  refine congrArg sumList (List.map_congr_left fun Δ hΔ => ?_)
  show ((r (Δ.first.tw χ hχ)).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) = WD.lpTwist _ _ _
  rw [(ht _ _ _ _).2, hr Δ hΔ, WD.lpTw, WD.lpTw, GlobalTheory.LocLanglands.ExtTwist.lpTwist_lpTwist_comm]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extTw :
    UpperTheory.Zero.LLC.ExtTw := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hL
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  refine ⟨fun x s => ?_, fun x χ hχ hg => ?_⟩
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have key := rc_tw_of_segments ha hL l x h𝔪 (absPow _ (s : ℂ)) (isSmoothChar_absPow _) (fun Δ _ => by
      have h1 := H.nu _ Δ.isCusp_first s
      rw [WD.lpTw] at h1
      refine h1.trans ?_
      congr 1
      exact (ha.absPow_comp s).symm)
    refine key.trans ?_
    rw [WD.lpTw]
    congr 1
    exact ha.absPow_comp s
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have hg' := ((UpperTheory.Zero.LLC.goodSeg _).1 l x h𝔪).1 hg
    rw [lpChar_lpOfChar]
    exact rc_tw_of_segments ha hL l x h𝔪 χ hχ fun Δ hΔ => H.twist _ Δ.isCusp_first (hg' Δ hΔ) χ hχ

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extInj :
    UpperTheory.Zero.LLC.ExtInj := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hL x y hy hxy
  classical
  obtain ⟨mx, hmx⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
  obtain ⟨my, hmy⟩ := UpperTheory.Zero.LLC.Pr.exh _ y
  have hlx : IsL (↑mx.toList) x.rep := by rw [Multiset.coe_toList]; exact hmx
  have hly : IsL (↑my.toList) y.rep := by rw [Multiset.coe_toList]; exact hmy
  have hgood : ∀ Δ ∈ my.toList, UpperTheory.Zero.LLC.GoodCusp Δ.first :=
    ((UpperTheory.Zero.LLC.goodSeg _).1 _ y hly).1 hy
  have e := hxy
  rw [hL _ x hlx, hL _ y hly] at e
  let f : Segment (HeightOneSpectrum.adicCompletion E w) → WD h × ℕ :=
    fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2), Δ.len - 1)
  have hcomp : (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1))) ∘ f =
      fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
    funext Δ
    simp only [Function.comp, f, Nat.sub_add_cancel Δ.len_pos]
  have hirr : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)), ∀ p ∈ l.map f, IsIrrWD p.1 := by
    intro l p hp
    obtain ⟨Δ, -, rfl⟩ := List.mem_map.mp hp
    exact LExtInj.isIrrWD_lpTw (hr.irr _ (Segment.isCusp_first _)) _
  have hperm := GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq E Ω A w h (mx.toList.map f) (my.toList.map f) (hirr _) (hirr _)
    (by rw [List.map_map, List.map_map, hcomp]; exact e)
  have key : ∀ Δ Δ' : Segment (HeightOneSpectrum.adicCompletion E w),
      UpperTheory.Zero.LLC.GoodCusp Δ'.first → f Δ = f Δ' → Δ = Δ' := by
    intro Δ Δ' hg he
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hl : Δ.len = Δ'.len := by
      have := Δ.len_pos
      have := Δ'.len_pos
      omega
    rw [hl] at h1
    exact Segment.ext_first
      (hr.inj _ _ (Segment.isCusp_first _) (Segment.isCusp_first _) hg (LExtInj.lpTw_injective h1)) hl
  let g : WD h × ℕ → Option (Segment (HeightOneSpectrum.adicCompletion E w)) := fun p =>
    if hp : ∃ Δ ∈ my.toList, f Δ = p then some hp.choose else none
  have hgy : ∀ Δ ∈ my.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    have hp : ∃ Δ' ∈ my.toList, f Δ' = f Δ := ⟨Δ, hΔ, rfl⟩
    simp only [g, dif_pos hp]
    exact congrArg some (key _ _ (hgood Δ hΔ) hp.choose_spec.2)
  have hgx : ∀ Δ ∈ mx.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    obtain ⟨Δ', hΔ', he⟩ := List.mem_map.mp (hperm.subset (List.mem_map_of_mem hΔ))
    have := key Δ Δ' (hgood Δ' hΔ') he.symm
    subst this
    exact hgy _ hΔ'
  have back : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)),
      (∀ Δ ∈ l, g (f Δ) = some Δ) → (l.map f).filterMap g = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b t ih =>
      rw [List.map_cons, List.filterMap_cons_some (hl b List.mem_cons_self)]
      exact congrArg _ (ih fun Δ hΔ => hl Δ (List.mem_cons_of_mem _ hΔ))
  have hp2 : mx.toList.Perm my.toList := by
    have := hperm.filterMap g
    rwa [back _ hgx, back _ hgy] at this
  have hmm : (↑mx.toList : Multiset (Segment (HeightOneSpectrum.adicCompletion E w))) = ↑my.toList :=
    Multiset.coe_eq_coe.mpr hp2
  rw [hmm] at hlx
  exact LExtInj.eq_of_isL UpperTheory.Zero.LLC.Pr.multi _ x y hlx hly
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem summand_dual (H : CuspT a ha r) {Δ Δ' : Segment (w.adicCompletion E)}
    (hg : GoodCusp Δ.first) (hd : SegDual Δ Δ') :
    ((r Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ'.len) =
      (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hl, hD⟩ := hd
  have hc : (Δ.first.nu ((Δ.len : ℂ) - 1)).IsCusp := Δ.isCusp_first.nu _
  have hgn : GoodCusp (Δ.first.nu ((Δ.len : ℂ) - 1)) := by
    rw [IrrGL.nu]
    exact ((clBasic _ Δ.first).2.1 _ _).2.2.1.2 hg
  have e1 := H.dual _ _ hc Δ'.isCusp_first hgn hD
  have e2 : Δ.first.nu ((Δ.len : ℂ) - 1) = Δ.first.nu (((Δ.len : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, H.nu _ Δ.isCusp_first] at e1
  obtain ⟨hS, hT, hP⟩ := GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h
  rw [e1, hl, hP, hT, hT, WD.lpTw_add]
  congr 2
  ring

private theorem map_summand_dual (H : CuspT a ha r) {l l' : List (Segment (w.adicCompletion E))}
    (hg : ∀ Δ ∈ l, GoodCusp Δ.first) (hF : List.Forall₂ SegDual l l') :
    l'.map (fun Δ => ((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
      l.map (fun Δ => (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual) := by
  induction hF with
  | nil => rfl
  | @cons Δ Δ' l l' hd _ ih =>
    rw [List.map_cons, List.map_cons, ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)),
      summand_dual H (hg _ List.mem_cons_self) hd]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDual :
    UpperTheory.Zero.LLC.ExtDual := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hE n π π' hg hπ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ (cls π)
  have hL : IsL ((𝔪.toList : List _) : Multiset (Segment (w.adicCompletion E))) (cls π).rep := by
    rw [Multiset.coe_toList]; exact h𝔪
  obtain ⟨l', hF, hL'⟩ := (UpperTheory.Zero.LLC.Pr.dual (w.adicCompletion E)).2 𝔪.toList (cls π) (cls π') hL ⟨n, π, π', rfl, rfl, hπ⟩
  have hgl := ((UpperTheory.Zero.LLC.goodSeg (w.adicCompletion E)).1 _ _ hL).1 hg
  rw [hE _ _ hL, hE _ _ hL', segSum, segSum, (GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h).1, List.map_map]
  exact congrArg sumList (UpperTheory.Zero.LLC.map_summand_dual H hgl hF)
end
