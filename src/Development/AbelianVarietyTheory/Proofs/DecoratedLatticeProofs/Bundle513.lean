module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle501
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinGrp

open GlobalTheory.FinPl

theorem map_ofFn_prod_eq {G M : Type*} [Group G] [Monoid M] (φ : G →* M) :
    ∀ {r : ℕ} (a : Fin r → G) (i : Fin r), (∀ j, j ≠ i → φ (a j) = 1) → φ (List.ofFn a).prod = φ (a i)
  | 0, _, i, _ => i.elim0
  | r + 1, a, i, h => by
    rw [List.ofFn_succ, List.prod_cons, φ.map_mul]
    cases i using Fin.cases with
    | zero =>
      have h1 : φ (List.ofFn fun j : Fin r => a j.succ).prod = 1 := by
        rw [φ.map_list_prod, List.map_ofFn]
        refine List.prod_eq_one (l := List.ofFn fun j : Fin r => φ (a j.succ)) ?_
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    | succ i' =>
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact map_ofFn_prod_eq φ (fun j => a j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

variable {D : D7}

theorem loc_facts {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (i : Fin F.r) :
    GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) ∧
    IsCompact (GlobalTheory.QuotientFiniteLevel.locK F j σ h i : Set (GA D (c.V (j + 1)))) ∧
    IsOpen {x : grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) |
      (x : GA D (c.V (j + 1))) ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i} := by
  have hd : j + 1 + ((F.Q i).s - j) = (F.Q i).s + 1 := by have := (F.Q i).hs; omega
  obtain ⟨hce, hrange, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1))
    ((F.Q i).X (j + 1) ⊕ Fin ((F.Q i).s - j)) ((F.Q i).FY (j + 1) ((F.Q i).s - j) hd)
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ((F.Q i).gl_loc _ _ hd)
  have hr : ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd).range =
      grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) := by
    rw [hrange]; congr 1; funext p; exact propext Finset.mem_singleton.symm
  obtain ⟨hJo, hJc, -⟩ := (F.Q i).reg.2.2 (j + 1) ((F.Q i).s - j) hd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr]; intro x hx; obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx; exact ⟨g, rfl⟩
  · rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.coe_map]; exact hJc.image hce.continuous
  · obtain ⟨U, hU, hUe⟩ := hce.isInducing.isOpen_iff.1 hJo
    convert hU.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨g, rfl⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.mem_map]
    constructor
    · rintro ⟨g', hg', e⟩
      have : g' ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hUe.symm ▸ hg'
      rw [← e]; exact this
    · intro hU'
      have hg : g ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hU'
      rw [hUe] at hg
      exact ⟨g, hg, rfl⟩

theorem qK_grp : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w →
    ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧
      IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧
      IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) :
        Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  intro D c v t w F hF j σ h
  have hloc := loc_facts F j σ h
  have hv : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have hle : ∀ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := fun i => (hloc i).1.trans
    (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp => (Finset.mem_singleton.1 hp) ▸ hv i)
  have hoff : ∀ i i', i ≠ i' →
      GlobalTheory.QuotientFiniteLevel.locK F j σ h i' ≤ grpAt (c.V (j + 1)) (· ∉ ({(F.Q i).q.v} : Finset (Pl D))) := fun i i' hii' =>
    (hloc i').1.trans (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp hp' =>
      hii' (hF.inj ((Finset.mem_singleton.1 hp').symm.trans (Finset.mem_singleton.1 hp))))
  have hcomm : Pairwise fun i i' => ∀ x y : GA D (c.V (j + 1)),
      x ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i → y ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i' → Commute x y := by
    intro i i' hii' x y hx hy
    exact (GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) {(F.Q i).q.v}).2.2.2.2.1 x ((hloc i).1 hx) y (hoff i i' hii' hy)
  have hqK : GlobalTheory.QuotientFiniteLevel.qK F j σ h = ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i := rfl
  have hQle : GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := iSup_le hle
  refine ⟨hQle, ?_, ?_⟩
  · have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hcont : Continuous (Subgroup.noncommPiCoprod hcomm) := by
      have e : ⇑(Subgroup.noncommPiCoprod hcomm) = fun x =>
          ((List.finRange F.r).map fun i => ((x i : GlobalTheory.QuotientFiniteLevel.locK F j σ h i) : GA D (c.V (j + 1)))).prod := by
        funext x
        simp [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod, Finset.noncommProd, List.ofFn_eq_map]
      rw [e]
      exact continuous_list_prod _ fun i _ => continuous_subtype_val.comp (continuous_apply i)
    haveI : ∀ i, CompactSpace (GlobalTheory.QuotientFiniteLevel.locK F j σ h i) := fun i => isCompact_iff_compactSpace.1 (hloc i).2.1
    have : (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) = Set.range (Subgroup.noncommPiCoprod hcomm) := by
      rw [hqK, ← hrange, MonoidHom.coe_range]
    rw [this]; exact isCompact_range hcont
  · set V := c.V (j + 1) with hVdef
    set K := GlobalTheory.QuotientFiniteLevel.locK F j σ h with hKdef
    obtain ⟨-, -, hQf, -, -, ⟨eQ, heQ⟩, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V w.Q
    have hbot : ∀ a, a ∈ grpAt V (· ∈ w.Q) → a ∈ grpAt V (· ∉ w.Q) → a = 1 := by
      intro a h1 h2
      have : eQ (⟨a, h1⟩, 1) = eQ (1, ⟨a, h2⟩) := by
        apply Subtype.ext; rw [heQ, heQ]; simp
      exact congrArg (fun p => (p.1 : GA D V)) (eQ.injective this)
    choose e he using fun i => (GlobalTheory.FinPl.SetCut.grp_split D V {(F.Q i).q.v}).2.2.2.2.2.1
    have he' : ∀ i (z : GfC V), (z : GA D V) = (((e i).symm z).1 : GA D V) * (((e i).symm z).2 : GA D V) := by
      intro i z; rw [← he i, Homeomorph.apply_symm_apply]
    let ι : grpAt V (· ∈ w.Q) → GfC V := fun x => ⟨x.1, hQf x.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let U : Set (grpAt V (· ∈ w.Q)) := ⋂ i, {x | ((((e i).symm (ι x)).1 : _) : GA D V) ∈ K i}
    have hUo : IsOpen U := isOpen_iInter_of_finite fun i =>
      (hloc i).2.2.preimage (continuous_fst.comp ((e i).symm.continuous.comp hι))
    have h1U : (1 : grpAt V (· ∈ w.Q)) ∈ U := by
      refine Set.mem_iInter.2 fun i => ?_
      have : (e i).symm (ι 1) = 1 := by
        rw [Homeomorph.symm_apply_eq]; apply Subtype.ext; rw [he]; simp [ι]
      show ((((e i).symm (ι 1)).1 : _) : GA D V) ∈ K i
      rw [this]; exact (K i).one_mem
    have hprj : ∀ i, ∀ b ∈ grpAt V (· ∉ ({(F.Q i).q.v} : Finset (Pl D))),
        GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v b = 1 := fun i b hb =>
      ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ b).1 hb).2 _ (by simp)
    have hUsub : U ⊆ (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (grpAt V (· ∈ w.Q)) : Subgroup _) : Set _) := by
      intro x hx
      have hx' := Set.mem_iInter.1 hx
      let a : Fin F.r → GA D V := fun i => (((e i).symm (ι x)).1 : GA D V)
      have ha : ∀ i, a i ∈ K i := fun i => hx' i
      have hp : (List.ofFn a).prod ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h := by
        refine Subgroup.list_prod_mem _ fun y hy => ?_
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (le_iSup K i) (ha i)
      have hy1 : ∀ i, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v ((x : GA D V) * ((List.ofFn a).prod)⁻¹) = 1 := by
        intro i
        have hxi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (x : GA D V) =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) := by
          have := he' i (ι x)
          change (x : GA D V) = a i * _ at this
          rw [this, map_mul, hprj i _ (((e i).symm (ι x)).2).2, mul_one]
        have hpi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (List.ofFn a).prod =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) :=
          map_ofFn_prod_eq _ a i fun j' hj' => hprj i _ (hoff i j' (Ne.symm hj') (ha j'))
        rw [map_mul, map_inv, hxi, hpi, mul_inv_cancel]
      have hyQ : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∈ w.Q) :=
        mul_mem x.2 (inv_mem (hQle hp))
      have hyN : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∉ w.Q) := by
        refine (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ _).2 ⟨hQf hyQ, fun p hp' => ?_⟩
        obtain ⟨i, rfl⟩ := (hF.places p).1 (not_not.1 hp')
        exact hy1 i
      have hxp : (x : GA D V) = (List.ofFn a).prod := mul_inv_eq_one.1 (hbot _ hyQ hyN)
      show (x : GA D V) ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h
      rw [hxp]; exact hp
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds h1U) hUsub)

end GlobalTheory.QFinGrp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimNormal

theorem z_pair {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Fin S₀.rank → D.host.E) (i : Fin ρ) :
    ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i = 0 := by
  have hent : ∀ c, ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i = 0 := fun c => by
    rw [← GlobalTheory.SplitPrimJac.mat_entry S d.i₀ d.e c i, d.i₀e, Matrix.zero_apply]
  have e : ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i =
      ∑ c, star (v c) * ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i := by
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ r, ∑ c, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i :=
            Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ c, ∑ r, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e]
  simp [hent]

end GlobalTheory.PrimNormal

namespace GlobalTheory.PrimNormal

theorem prim_of_normal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNint hMsd hMcore j ρ h
  rw [← l.under]
  have hc : j + (2 * ρ + 1) = l.s + 1 := by have := l.hs; omega
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  have hξ : valuation l.k (ofSplit l.q).xi = 1 := GlobalTheory.QTw.GeoInhab.xi_unit l.q l.unit
  have hsc := hN.1 j
  have hz := hN.2.2.1 j ρ h
  have inner0 : ∀ (x : Fin (Yc D j).rank → D.host.E) (i : Fin ρ),
      (∑ r, ∑ t, star (x r) * HSpace.gram (Yc D j) r t * ((y.bes j ρ h).lev (a.x j).vol).d.e t i) = 0 →
      ∀ (b : l.k) (col : Fin (Yc D j).rank → l.k), (∀ r, col r = b * l.q.pr (incA D (x r))) →
      ∑ r, ∑ t, col r * l.q.pr (cA D (incA D (HSpace.gram (Yc D j) r t))) *
        l.q.pr (cA D (incA D (((y.bes j ρ h).lev (a.x j).vol).d.e t i))) = 0 := by
    intro x i hx b col hcol
    rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ b x _ col hcol, hx, star_zero, map_zero, map_zero, mul_zero]
  have line : ∀ (i : Fin ρ) (b : AE D), GlobalTheory.FinPl.colMul ((y.bes j ρ h).lev (a.x j).vol).d.jX i b ∈
      GlobalTheory.FinPl.latV (Yc D j) (N j) (· = l.q.v) ↔ b ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) := by
    intro i b
    refine GlobalTheory.PrimSplitLine.colMul_mem_latV_iff D l.k l.q _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d (N j) _
      (FY j (2 * ρ + 1) hc) i (Sum.inr ⟨i.val, by omega⟩) (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
      (sc j * (ofSplit l.q).xi ^ (ρ - i.val))
      (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) * (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val))
      (hNsd j (by omega)) (hNint j _ hc) ?_ ?_ ?_ ?_ b
    · rw [map_mul, map_pow, hsc, hξ, one_pow, one_mul]
    · simp only [map_mul, map_div₀, map_pow, Valuation.map_neg, map_one, hsc, hz, hξ]; simp
    · intro r; exact hB.2.2.1 i ⟨i.val, by omega⟩ rfl r
    · intro m
      rcases m with b | m
      · rw [if_neg Sum.inl_ne_inr]
        have hcol : ∀ r, (FY j (2 * ρ + 1) hc).β r (Sum.inl b) = ∑ e, (l.FX j (by omega)).β e b *
            l.q.pr (incA D ((((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e)) := by
          intro r
          rw [hB.2.1 r b, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _
        simp only [hcol, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_eq_zero fun e _ => ?_
        simp only [mul_assoc]
        simp only [← mul_assoc]
        refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e) i ?_ _ _
          fun r => rfl
        rw [← GlobalTheory.SplitPrimJac.mat_entry, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (HSpace.gram _), ((y.bes j ρ h).lev (a.x j).vol).d.i₀e, Matrix.mul_zero, Matrix.zero_apply]
      · by_cases hm : m.val < ρ
        · rw [if_neg (fun he => by cases he; simp at hm; omega)]
          refine inner0 (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r ⟨m.val, hm⟩) i ?_ _ _ (hB.2.2.1 ⟨m.val, hm⟩ m rfl)
          rw [← GlobalTheory.SplitPrimJac.mat_entry, ((y.bes j ρ h).lev (a.x j).vol).d.ee, Matrix.zero_apply]
        · by_cases hm' : m.val = ρ
          · rw [if_neg (fun he => by cases he; simp at hm'; omega)]
            refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ *ᵥ
              vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r) i ?_ _ _ (hB.2.2.2.1 m hm')
            exact z_pair _ _ i
          · have hi' : 2 * ρ - m.val < ρ := by omega
            have hcol := hB.2.2.2.2 ⟨2 * ρ - m.val, hi'⟩ m (by simp; omega)
            rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ _ _ _ _ hcol, ← GlobalTheory.SplitPrimJac.mat_entry,
              ((y.bes j ρ h).lev (a.x j).vol).d.e'e, Matrix.one_apply]
            by_cases hii : (⟨2 * ρ - m.val, hi'⟩ : Fin ρ) = i
            · have hmv : m.val = 2 * ρ - i.val := by rw [← hii]; simp; omega
              rw [if_pos hii, if_pos (by congr 1; exact Fin.ext hmv), star_one, map_one, map_one, mul_one, ← hii]
            · rw [if_neg hii, if_neg (fun he => hii (by cases he; ext; simp; omega)), star_zero, map_zero, map_zero,
                mul_zero]
  obtain ⟨ψk, hχ, hcond⟩ := GlobalTheory.QTw.GeoInhab.exists_char l.q l.unit hψ
  have hε : l.q.e + cA D l.q.e ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) :=
    ⟨GlobalTheory.FinPl.FrameLat.sum_mem_idAt l.q, by
      rw [RingHom.map_add (f := _)]
      exact add_mem (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2)⟩
  intro i i' hii' t ht
  rw [← GlobalTheory.SplitIntChar.int_iff_psiE D l.k l.q ψ ψk hξ hχ hcond t ht]
  constructor
  · intro H
    have h1 := H (l.q.e + cA D l.q.e) ((line i' _).2 hε)
    have ht' : t * (l.q.e + cA D l.q.e) = t := by rw [mul_comm]; exact (GlobalTheory.FinPl.FrameLat.idem_iff l.q t).1 ht
    rwa [line i, ht'] at h1
  · intro H b hb
    rw [line i'] at hb
    rw [line i]
    exact ⟨Ideal.mul_mem_right _ _ H.1, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE H.2 hb.2⟩

end GlobalTheory.PrimNormal
end
end
