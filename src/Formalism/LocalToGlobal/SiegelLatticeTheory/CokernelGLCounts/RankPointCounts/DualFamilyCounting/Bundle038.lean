module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle022
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

section

namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_product_holds : GlueProd :=
  glueProd_of jordan_splitting_exists jordan_invariants_holds jordan_isometry_holds local_gluing_holds

end Formalism.L2.SG.Pf.Cnt
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section S1

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem local_form_add_right (x y y' : L.V p) : (L.H p).h x (y + y') = (L.H p).h x y + (L.H p).h x y' := by
  rw [(L.H p).h_herm (y + y') x, (L.H p).h_add_left, map_add (f := _), ← (L.H p).h_herm y x,
    ← (L.H p).h_herm y' x]

theorem local_form_smul_right (x y : L.V p) (a : (D.s.atP p).Ep) :
    (L.H p).h x (a • y) = (M p).L.cj a * (L.H p).h x y := by
  rw [(L.H p).h_herm (a • y) x, (L.H p).h_smul_left, map_mul, ← (L.H p).h_herm y x]

theorem local_form_zero_left (y : L.V p) : (L.H p).h 0 y = 0 := by
  have h := (L.H p).h_smul_left 0 0 y
  rwa [zero_smul, zero_mul] at h

theorem local_form_zero_right (x : L.V p) : (L.H p).h x 0 = 0 := by
  rw [(L.H p).h_herm 0 x, local_form_zero_left, map_zero]

theorem base_change_smul_integral {δ : ∀ p : PlF D, (D.s.atP p).Fp} (hA : Agree δ M p) (o : 𝓞 D.host.E) (x : (VS D).V) :
    ∃ c ∈ (M p).L.O, L.bc p (o • x) = c • L.bc p x := by
  refine ⟨(D.s.atP p).ιE (o : D.host.E), ?_, ?_⟩
  · rw [hA.2.2.2.1]
    exact PI.CntNotIntW.iE_mem_O D p o
  · rw [← L.bc_smul p (o : D.host.E) x]
    congr 1
    first
    | exact (algebraMap_smul D.host.E o x).symm
    | rfl

theorem local_form_integral_on_lattice (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O)
    (hint : ∀ a ∈ Λ, ∀ b ∈ Λ, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O)
    {x y : L.V p} (hx : x ∈ lattice₂ L p Λ) (hy : y ∈ lattice₂ L p Λ) : (L.H p).h x y ∈ (M p).L.O := by
  unfold lattice₂ at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx0 =>
    obtain ⟨a, ha, rfl⟩ := hx0
    induction hy using Submodule.span_induction with
    | mem y hy0 =>
      obtain ⟨b, hb, rfl⟩ := hy0
      exact hint a ha b hb
    | zero => rw [local_form_zero_right]; exact (M p).L.O.zero_mem
    | add y y' _ _ h1 h2 => rw [local_form_add_right]; exact add_mem h1 h2
    | smul c y _ h1 =>
      rw [show c • y = (c : (D.s.atP p).Ep) • y from rfl, local_form_smul_right]
      exact mul_mem (hcjO _ c.2) h1
  | zero => rw [local_form_zero_left]; exact (M p).L.O.zero_mem
  | add x x' _ _ h1 h2 => rw [(L.H p).h_add_left]; exact add_mem h1 h2
  | smul c x _ h1 =>
    rw [show c • x = (c : (D.s.atP p).Ep) • x from rfl, (L.H p).h_smul_left]
    exact mul_mem c.2 h1

end S1


theorem local_self_dual_holds : LocSelfDual := by
  intro D δ M hA L p
  have hAp := hA p
  obtain ⟨-, -, hcj, hO, -⟩ := hAp
  have hLat := (VS D).standardTuple_isLattice
  have hU := (VS D).baseLattice_isUnimodular
  have hspan : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ :=
    Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hLat.fg


  have hform : ∀ a b : (VS D).V, (L.H p).h (L.bc p a) (L.bc p b) = (D.s.atP p).ιE ((VS D).hT b a) := by
    intro a b; rw [L.bc_form p]; rfl
  have hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O := by
    intro a ha; rw [hcj, hO] at *; exact LocFacts.lf_cj_mem p a ha

  have hint : ∀ a ∈ (VS D).L0, ∀ b ∈ (VS D).L0, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O := by
    intro a ha b hb
    rw [hform]
    have ha' : a ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by
      have : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := hU
      rw [← this] at ha; exact ha
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((LocFacts.lf_mem_hdual).1 ha' b hb)
    rw [← ho, hO]
    exact PI.CntNotIntW.iE_mem_O D p o
  refine ⟨?_, ?_, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  ·
    obtain ⟨s, hs⟩ := hLat.fg
    have : lattice₂ L p (VS D).L0 = Submodule.span (M p).L.O (L.bc p '' (s : Set (VS D).V)) := by
      apply le_antisymm
      · rw [lattice₂, Submodule.span_le, ← hs]
        rintro _ ⟨x, hx, rfl⟩
        induction hx using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
        | smul o y _ hy =>
          obtain ⟨c, hc, he⟩ := base_change_smul_integral L p (hA p) o y
          rw [he]
          exact Submodule.smul_mem _ (⟨c, hc⟩ : (M p).L.O) hy
      · rw [← hs]; exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    rw [this]
    exact Submodule.fg_span (s.finite_toSet.image _)
  ·
    rw [eq_top_iff, ← L.bc_span p, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact add_mem hy hz
    | smul a y _ hy => rw [L.bc_smul p]; exact Submodule.smul_mem _ _ hy
  ·
    exact local_form_integral_on_lattice L p _ hcjO hint hx hy
  ·
    obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := D.host.E) (VS D).L0 hLat.fg
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    choose μ hμL0 hμ using fun i => LocFacts.lf_riesz_lat hLat hU (f i)
    have hV : ∀ v : (VS D).V, v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
      let L2 : (VS D).V →ₗ[D.host.E] (VS D).V := ∑ i, ((VS D).hT (μ i)).smulRight ((g i : (VS D).L0) : (VS D).V)
      have hL2 : ∀ v, L2 v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
        intro v; simp [L2]
      have heq : LinearMap.id = L2 := by
        apply LinearMap.ext_on hspan
        intro y hy
        have e1 := congrArg (fun z : (VS D).L0 => (z : (VS D).V)) (hgf ⟨y, hy⟩)
        rw [LinearMap.id_apply, hL2]
        refine e1.trans ?_
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, ← algebraMap_smul D.host.E, hμ i ⟨y, hy⟩]
      intro v
      rw [← hL2, ← heq, LinearMap.id_apply]
    have hVp : ∀ w : L.V p, w = ∑ i, (L.H p).h w (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V) := by
      intro w
      have hw : w ∈ Submodule.span (D.s.atP p).Ep (Set.range (L.bc p)) := by rw [L.bc_span p]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        have e : ∀ i, (L.H p).h (L.bc p v) (L.bc p (μ i)) = (D.s.atP p).ιE ((VS D).hT (μ i) v) := fun i => hform _ _
        simp only [e, ← L.bc_smul p]

        rw [← map_sum, ← hV v]
      | zero => simp [local_form_zero_left]
      | add w w' _ _ h1 h2 =>
        simp only [(L.H p).h_add_left, add_smul, Finset.sum_add_distrib]
        rw [← h1, ← h2]
      | smul a w _ h1 =>
        simp only [(L.H p).h_smul_left, mul_smul]
        rw [← Finset.smul_sum, ← h1]
    have hmem : (∑ i, (L.H p).h x (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V)) ∈ lattice₂ L p (VS D).L0 := by
      refine Submodule.sum_mem _ fun i _ => ?_
      have hc : (L.H p).h x (L.bc p (μ i)) ∈ (M p).L.O := h _ (Submodule.subset_span ⟨μ i, hμL0 i, rfl⟩)
      have hg : L.bc p ((g i : (VS D).L0) : (VS D).V) ∈ lattice₂ L p (VS D).L0 := Submodule.subset_span ⟨_, (g i).2, rfl⟩
      exact Submodule.smul_mem _ (⟨_, hc⟩ : (M p).L.O) hg
    have hxe := hVp x
    rw [← hxe] at hmem
    exact hmem

end Formalism.L2.SG.Pf.Cnt
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem h_symm (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem h_fe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [h_symm, X.ef b a]
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem inW_pW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  unfold pW

  simp only [map_sub, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, h_fe, X.ff, mul_ite, mul_one, mul_zero,
  Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_zero]
  constructor
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem decomp (y : (VS D).V) :
    y = ∑ c, (VS D).hT (X.fY c) y • X.eX c + ∑ c, (VS D).hT (X.eX c) y • X.fY c + pW X y := by
  unfold pW
  abel

theorem inW_left {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT w (X.eX a) = 0 ∧ (VS D).hT w (X.fY a) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h_symm, (hw a).1, star_zero]
  · rw [h_symm, (hw a).2, star_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

section

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem thetaEx_holds : ThetaEx := by
  intro D
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB D.host, ?_⟩
  rw [Formalism.BasicNotions.Examples₂.conj_half, Formalism.BasicNotions.Examples₂.conj_bE]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

section

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DictLatF : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 → LatQ X (Xq X n) (xq X n) (Mq X n)

def DictLatB : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → LatQ X (Xq X n) (xq X n) (Mq X n) → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0

theorem dictLat_of (hF : DictLatF) (hB : DictLatB) : DictLat :=
  fun X u n hn => ⟨hF X u n hn, hB X u n hn⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev pV (v : InfinitePlace X.B.I.F) (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem hJ_pV (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (pV X v p) (pV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  PI.SchurPlaces.hJ_psiV X v p q

theorem decompY (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ)
    (hye : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.eV X v a) y = 0)
    (hyf : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.fV X v a) y = 0) :
    y = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) y • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) y) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  have hy : y ∈ Submodule.span ℂ (Set.range (Formalism.L2.SG.Pf.LsNc5.fam X u v)) := by
    rw [Formalism.L2.SG.Pf.LsNc5.fam_span]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  subst hc

  have pair : ∀ t : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) t (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      (∑ a, c (Sum.inl a) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.eV X v a)) +
        ((∑ a, c (Sum.inr (Sum.inl a)) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.fV X v a)) +
        ((∑ j, c (Sum.inr (Sum.inr (Sum.inl j))) * hJ (X.B.I.ε v) t (X.wfr u v j)) +
          c (Sum.inr (Sum.inr (Sum.inr ()))) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.zV X u v))) := by
    intro t
    rw [PI.SchurPlaces.hJ_sum_r]
    simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  have hcf : ∀ a, c (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have h := hye a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_ee, Formalism.L2.SG.Pf.LsNc5.fr_ef, Formalism.L2.SG.Pf.LsNc5.fr_ew,
      Formalism.L2.SG.Pf.LsNc5.fr_ez] using h
  have hce : ∀ a, c (Sum.inl a) = 0 := by
    intro a
    have h := hyf a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_fe, Formalism.L2.SG.Pf.LsNc5.fr_ff, Formalism.L2.SG.Pf.LsNc5.fr_fw,
      Formalism.L2.SG.Pf.LsNc5.fr_fz, hcf] using h
  have hw : ∀ j, hJ (X.B.I.ε v) (X.wfr u v j) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inl j))) := by
    intro j
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_we, Formalism.L2.SG.Pf.LsNc5.fr_wf, Formalism.L2.SG.Pf.LsNc5.fr_ww,
      Formalism.L2.SG.Pf.LsNc5.fr_wz]
  have hz : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ)) := by
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_ze, Formalism.L2.SG.Pf.LsNc5.fr_zf, Formalism.L2.SG.Pf.LsNc5.fr_zw,
      Formalism.L2.SG.Pf.LsNc5.frame_z_z_eq_neg_t]
  simp only [hw, hz]
  have hT := Formalism.L2.SG.Pf.LsNc5.T_ne u
  have hcoef : -(c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ))) /
      ((((D.mem u).A.T : ℕ) : ℝ) : ℂ) = c (Sum.inr (Sum.inr (Sum.inr ()))) := by
    push_cast; field_simp
  rw [hcoef]
  simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    hce, hcf, zero_smul, Finset.sum_const_zero, zero_add]

theorem decompW (v : InfinitePlace X.B.I.F) (x : (VS D).V) (hx : InW X x) :
    pV X v x = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x)) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  refine decompY X u v _ (fun a => ?_) (fun a => ?_)
  · show hJ (X.B.I.ε v) (pV X v (X.eX a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).1, map_zero]
  · show hJ (X.B.I.ε v) (pV X v (X.fY a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).2, map_zero]

theorem rowV_w (x : (VS D).V) (v : InfinitePlace X.B.I.F) (j : Fin D.R.k) :
    rowV X u x v (Fin.castSucc j) = hJ (X.B.I.ε v) (pV X v x) (X.wfr u v j) := by
  simp [rowV]

theorem rowV_last_eq_hJ (x : (VS D).V) (v : InfinitePlace X.B.I.F) :
    rowV X u x v (Fin.last D.R.k) = hJ (X.B.I.ε v) (pV X v x) (Formalism.L2.SG.Pf.LsNc5.zV X u v) := by
  simp [rowV]
  rfl

theorem rowV_gram (v : InfinitePlace X.B.I.F) (x y : (VS D).V) (hy : InW X y) :
    embS D (X.pl v) ((VS D).hT x y) =
      (∑ j : Fin D.R.k, rowV X u x v (Fin.castSucc j) * star (rowV X u y v (Fin.castSucc j))) -
        rowV X u x v (Fin.last D.R.k) * star (rowV X u y v (Fin.last D.R.k)) / (((D.mem u).A.T : ℕ) : ℂ) := by
  rw [← hJ_pV, decompW X u v y hy, PI.SchurPlaces.hJ_add_r, PI.SchurPlaces.hJ_sum_r, PI.SchurPlaces.hJ_smul_r]
  simp only [rowV_w, rowV_last_eq_hJ]
  have e1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v y) = star (hJ (X.B.I.ε v) (pV X v y) (X.wfr u v c)) :=
    fun c => hJ_conj' _ _ _
  have e2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v y) =
      star (hJ (X.B.I.ε v) (pV X v y) (Formalism.L2.SG.Pf.LsNc5.zV X u v)) := hJ_conj' _ _ _
  simp only [e1, e2]
  push_cast
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by ring
  · ring

theorem rowV_inj (x : (VS D).V) (hx : InW X x) (h : rowV X u x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hp : pV X v x = 0 := by
    rw [decompW X u v x hx]
    have h1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) = 0 := by
      intro c
      rw [hJ_conj', ← rowV_w, h]; simp
    have h2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x) = 0 := by
      rw [hJ_conj', ← rowV_last_eq_hJ, h]; simp
    simp [h1, h2]
  refine (VS D).nondeg.1 x fun y => ?_
  apply (embS D (X.pl v)).injective
  rw [← hJ_pV, hp, map_zero]
  unfold hJ; simp

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
