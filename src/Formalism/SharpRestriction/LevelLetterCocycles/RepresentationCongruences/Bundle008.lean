module

import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftLeEPA
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
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

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}


omit [Algebra O LL] in
theorem len_quot_span_ne_top_dvr [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) ≠ ⊤ := by
  apply Formalism.MainNotions.BlochKatoDuality.Br.length_quot_ne_top <;> assumption

theorem colLeR_of_exponent [IsDomain O] [IsDiscreteValuationRing O] (PD : PeriodData G Qp K₀ K B BdR)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (g₁ e e' : ℕ)
    (hgen : ∃ s : Finset (LatticeCohomology T₂.L), Submodule.span O (s : Set (LatticeCohomology T₂.L)) = latticeFiniteCohomology PD T₂.L ∧
      s.card ≤ g₁)
    (Z : Finset (G → T₂.V)) (hZ : ∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L)
    (he : ExpIn PD F Z e)
    (hL : F.LiftF PD e') :
    TruncatedSeriesCountingBounds.ColLeR PD F ((g₁ : ℝ) * e + (Z.card : ℝ) * e') := by
  classical
  obtain ⟨s, hs, hscard⟩ := hgen
  have hrep : ∀ x ∈ latticeFiniteCohomology PD T₂.L, ∃ y : G → T₂.V, ∃ hy : y ∈ latticeCocycles T₂.L,
      y ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ (⟨y, hy⟩ : latticeCocycles T₂.L) = x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨z.1, z.2, hz, rfl⟩
  let r : LatticeCohomology T₂.L → (G → T₂.V) := fun x =>
    if hx : x ∈ latticeFiniteCohomology PD T₂.L then (hrep x hx).choose else 0
  let s' : Finset (G → T₂.V) := s.image r
  have hmemH : ∀ x ∈ s, x ∈ latticeFiniteCohomology PD T₂.L := fun x hx => hs ▸ Submodule.subset_span hx
  have hrx : ∀ x (hx : x ∈ latticeFiniteCohomology PD T₂.L), r x = (hrep x hx).choose := fun x hx => by
    simp only [r, dif_pos hx]
  have hs'Z : (↑s' : Set (G → T₂.V)) ⊆ latticeFiniteCocycles PD T₂.L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [hrx x (hmemH x hx)]
    exact (hrep x (hmemH x hx)).choose_spec.choose_spec.1
  have hB : latticeCoboundaries T₂.L ≤ F.ImF PD := by
    unfold LatHom.ImF
    exact le_sup_right
  have hZZ : Submodule.span O (↑Z : Set (G → T₂.V)) ≤ latticeFiniteCocycles PD T₂.L :=
    Submodule.span_le.2 (fun x hx => hZ x hx)
  have hspan : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) = latticeFiniteCocycles PD T₂.L := by
    have hNle : Submodule.span O (↑s' : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) ≤ latticeFiniteCocycles PD T₂.L :=
      sup_le (Submodule.span_le.2 hs'Z) inf_le_right
    refine le_antisymm hNle ?_
    intro c hc
    have hcZ1 : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 hc).1
    have hq : Submodule.mkQ _ (⟨c, hcZ1⟩ : latticeCocycles T₂.L) ∈ latticeFiniteCohomology PD T₂.L := Submodule.mem_map_of_mem hc
    have hle : latticeFiniteCohomology PD T₂.L ≤ ((Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)).comap (latticeCocycles T₂.L).subtype).map (Submodule.mkQ _) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      obtain ⟨hy, _, hyq⟩ := (hrep x (hmemH x hx)).choose_spec
      refine ⟨⟨(hrep x (hmemH x hx)).choose, hy⟩, ?_, hyq⟩
      show (hrep x (hmemH x hx)).choose ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L)
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine Finset.mem_image.2 ⟨x, hx, ?_⟩
      exact hrx x (hmemH x hx)
    obtain ⟨y, hyN, hyq⟩ := hle hq
    have hyN' : (y : G → T₂.V) ∈ Submodule.span O (↑s' : Set (G → T₂.V)) ⊔
        (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) := hyN
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hyq
    have h2 : (y : G → T₂.V) - c ∈ latticeCoboundaries T₂.L := by simpa using Submodule.mem_comap.1 hyq
    have hd : c - (y : G → T₂.V) ∈ latticeCoboundaries T₂.L := by
      have h3 := (latticeCoboundaries T₂.L).neg_mem h2
      simpa using h3
    have hyZ : (y : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L := hNle hyN'
    have hdI : c - (y : G → T₂.V) ∈ F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L :=
      Submodule.mem_inf.2 ⟨hB hd, (latticeFiniteCocycles PD T₂.L).sub_mem hc hyZ⟩
    have e1 : c = (y : G → T₂.V) + (c - (y : G → T₂.V)) := by abel
    rw [e1]
    exact Submodule.add_mem _ hyN' (Submodule.mem_sup_right hdI)
  have hexp : ∀ q ∈ latticeFiniteCocycles PD T₂.L, (PD.p ^ e : ℕ) • q ∈
      Submodule.span O (↑Z : Set (G → T₂.V)) ⊔ (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) := by
    intro q hq
    have h := he q hq
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.1 h
    have hzZ : z ∈ latticeFiniteCocycles PD T₂.L := hZZ hz
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← hiz]
    have hiZ : i ∈ latticeFiniteCocycles PD T₂.L := by
      have e2 : i = ((PD.p : O) ^ e) • q - z := by rw [← hiz]; abel
      rw [e2]
      exact (latticeFiniteCocycles PD T₂.L).sub_mem ((latticeFiniteCocycles PD T₂.L).smul_mem _ hq) hzZ
    rw [add_comm]
    exact Submodule.add_mem_sup hz (Submodule.mem_inf.2 ⟨hi, hiZ⟩)
  have hlift : ∀ q ∈ Submodule.span O (↑Z : Set (G → T₂.V)), (PD.p ^ e' : ℕ) • q ∈
      F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L := by
    intro q hq
    have hqZ : q ∈ latticeFiniteCocycles PD T₂.L := hZZ hq
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact Submodule.mem_inf.2 ⟨hL q hqZ, (latticeFiniteCocycles PD T₂.L).smul_mem _ hqZ⟩
  have key := Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds.length_quotient_le_of_two_step O (G → T₂.V) PD.p g₁ Z.card e e' (latticeFiniteCocycles PD T₂.L)
    (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L) s' Z inf_le_right (Finset.card_image_le.trans hscard) le_rfl
    (fun z hz => hZ z hz) hspan hexp hlift
  have hcomap : (F.ImF PD ⊓ latticeFiniteCocycles PD T₂.L).comap (latticeFiniteCocycles PD T₂.L).subtype =
      (F.ImF PD).comap (latticeFiniteCocycles PD T₂.L).subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [hcomap] at key
  have hcol : F.col PD ≤ ((g₁ * e + Z.card * e' : ℕ) : ℕ∞) * lenOl PD (O := O) := key
  have hlen : lenOl PD (O := O) ≠ ⊤ := len_quot_span_ne_top_dvr (O := O) _ hp0
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlen
  rw [← hk, ← Nat.cast_mul] at hcol
  have hcolfin : F.col PD ≠ ⊤ := fun h => ENat.coe_ne_top _ (top_le_iff.1 (h ▸ hcol))
  obtain ⟨mm, hmm⟩ := ENat.ne_top_iff_exists.1 hcolfin
  refine ⟨mm, k, hmm.symm, hk.symm, ?_⟩
  rw [← hmm] at hcol
  have h4 : mm ≤ (g₁ * e + Z.card * e') * k := by exact_mod_cast hcol
  have h5 : (mm : ℝ) ≤ (((g₁ * e + Z.card * e') * k : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5
  exact h5

end Core

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem ro_le_arc_len : ∀ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n),
    Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ≤ A.len c := by
  intro n A c
  unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem arc_len_le_one_of_no_thick : ∀ {n : ℕ} [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ)
    (h : ¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) (c : ZMod n),
    (arcOf b w S η up size).len c ≤ 1 := by
  intro n _ b w S η up size h c
  unfold arcOf
  dsimp only
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq]
  exact ⟨le_rfl, fun ht => h ⟨_, ht⟩⟩

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {PD : PeriodData G Qp K₀ K B BdR}

theorem cocycle_classes_exponent {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    (Zc : Finset (LatticeCohomology T₂.L))
    (hZc : ∀ z ∈ Zc, z ∈ latticeFiniteCohomology PD T₂.L)
    (h : ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ e) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O (Zc : Set (LatticeCohomology T₂.L))) :
    ∃ Z : Finset (G → T₂.V), Z.card ≤ Zc.card ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD F Z e := by
  classical
  have hrep : ∀ z ∈ Zc, ∃ a : ↥(latticeCocycles T₂.L), (a : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ a = z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hZc z hz)
    exact ⟨a, ha, rfl⟩
  choose! r hr1 hr2 using hrep
  refine ⟨Zc.image (fun z => (r z : G → T₂.V)), Finset.card_image_le, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hr1 z hz
  · intro c hc
    have hc' : c ∈ latticeCocycles T₂.L ⊓ _ := hc
    have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.mp hc').1
    have hx : Submodule.mkQ _ (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) ∈ latticeFiniteCohomology PD T₂.L :=
      Submodule.mem_map_of_mem (p := (latticeFiniteCocycles PD T₂.L).comap (latticeCocycles T₂.L).subtype) hc
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (h _ hx)
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy0
    have ha' : (a : G → T₁.V) ∈ latticeFiniteCocycles PD T₁.L := ha
    have hspan : Submodule.span O (Zc : Set (LatticeCohomology T₂.L)) =
        (Submodule.span O (r '' (Zc : Set (LatticeCohomology T₂.L)))).map (Submodule.mkQ _) := by
      rw [Submodule.map_span, Set.image_image, Set.image_congr (g := fun z => z) (fun z hz => hr2 z hz),
        Set.image_id']
    rw [hspan] at hw
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hw
    have e1 : F.H1map (Submodule.mkQ _ a) =
        Submodule.mkQ _ (⟨F.post a, F.post_Z1T _ a.2⟩ : ↥(latticeCocycles T₂.L)) := rfl
    have hker : ((PD.p : ℕ) : O) ^ e • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) -
        ⟨F.post a, F.post_Z1T _ a.2⟩ - s ∈ (latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype := by
      rw [← Submodule.ker_mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype), LinearMap.mem_ker, map_sub, map_sub,
        map_smul, ← hyw, e1]
      abel
    have hb : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ latticeCoboundaries T₂.L := hker
    have hs' : (s : G → T₂.V) ∈
        Submodule.span O ((Zc.image fun z => (r z : G → T₂.V) : Finset (G → T₂.V)) : Set (G → T₂.V)) := by
      have hm := Submodule.mem_map_of_mem (f := (latticeCocycles T₂.L).subtype) hs
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)
    have hpa : F.post a ∈ F.ImF PD := Submodule.mem_sup_left (Submodule.mem_map_of_mem ha')
    have hbI : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ F.ImF PD := Submodule.mem_sup_right hb
    have key : ((PD.p : ℕ) : O) ^ e • c =
        (F.post a + (((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V))) + s := by abel
    rw [key]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ hpa hbI)) (Submodule.mem_sup_right hs')

end Core

end Formalism.MainNotions.N.Ln17
end
end

section

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem exists_liftF_le_sg_of_thick : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (hth : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i)
    (hbig : (b : ℝ) / 4 < 40 * Sg l b w S η size),
    ∃ e₀ : ℕ, (e₀ : ℝ) ≤ 160 * Sg l b w S η size ∧ f.LiftF ((D.loc l).PD K) e₀ := by
  intro D HW F Cm CR CA CB CK hU l _ K LL hG hK _ _ T₁ T₂ f b w S η m up size Mi hi hB hAlt hth hbig
  obtain ⟨hp11, hSet, hwb, hηb, hSb, ⟨j, hj⟩⟩ := hB
  obtain ⟨hCA, hSur, hηs, hJA, _hlow, hnt, _hJL⟩ := hSet
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := hp ▸ hp11
  have hLift : Formalism.MainNotions.LiftingTheory.coreLiftA ((HW l).W K 1 LL hG) := hU.a2.2.2.2.2.2.2.2.1 l K 1 LL hG

  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht
      omega
  have hb1 : 1 ≤ b := by
    have h1 := hnt j hj
    have h2 := hηs j
    omega
  have hhB : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := if_pos hth

  let Mi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then size i + S else η
  have hJL' : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW l).W K 1 LL hG) T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hM : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hm : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hH : Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi' ≤ b + η + S + η := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hjumps : ∀ u ∈ Formalism.MainNotions.LiftingTheory.jumpSet ((HW l).W K 1 LL hG) T₁
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi')
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi'),
      -((Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' : ℕ) : ℤ) ≤ u ∧
        u ≤ ((b + η + S : ℕ) : ℤ) := by
    intro u hu
    simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc] at hu
    refine ⟨hu.1.1, ?_⟩
    have := hu.1.2
    push_cast at this ⊢
    omega
  have hL := Formalism.MainNotions.N.FrobeniusPowerSeries.lift_le_ePA l hl (b + η + S) η
    (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi')
    (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi') (by omega) (by omega) hH hM _ hjumps
  have hSg : Sg l b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) w S η := by
    unfold Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [hhB]
  have h0 := Formalism.MainNotions.N.FrobeniusPowerSeries.step0 l hl b w S η hb1 hηb hSb hwb (by rw [← hSg]; exact hbig)
  have hLA := hLift hCA T₁ T₂ f Mi' hi' hSur hJL'
  refine ⟨_, ?_, hLA⟩
  rw [hp, hSg]
  linarith

end Formalism.MainNotions.N.Ln17
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le' [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem aI_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (c : ZMod n)
    (hct : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c) (hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1)) :
    (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤
      ((size c : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, -, hnt, -⟩ := hSet
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ (b + η + S) + η :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) =
      (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  have e0 : c - 1 + ((0 + 1 : ℕ) : ZMod n) = c := by push_cast; ring
  have e1 : c - 1 + ((1 + 1 : ℕ) : ZMod n) = c + 1 := by push_cast; ring
  have hc1w : size (c + 1) ≤ w := hnt (c + 1) hc1
  have ht := tsum_three PD.p hp11
    (fun a => ((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((size c + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((w + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℝ) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    (fun a => by positivity)
    (by
      show _ + _ + _ ≤ _
      rw [e0, hwid, hcW])
    (by
      show _ + _ + _ ≤ _
      rw [e1, hwid, hcW]
      have : ((size (c + 1) + S + η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by
        exact_mod_cast (by omega : size (c + 1) + S + η ≤ w + S + η)
      linarith)
    (fun a _ => by
      have := hmax_le' Mi' hi' (c - 1 + ((a + 1 : ℕ) : ZMod n))
      have h' : (((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤
          Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' := by exact_mod_cast this
      show _ + _ + _ ≤ _
      rw [hcW]; linarith)
  have hst := hs.trans ht
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hη1 : η + 1 ≤ b + η + S := by have := hηs c; have := hct.2; omega
  have key := Aa_cut_le PD.p hp11 (b + η + S) w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') (size c + S + η)
    (w + S + η) hη1 hHle (by have := hct.2; omega) le_rfl _ _ hst hA
  have ec : (((size c + S + η : ℕ) : ℝ)) = (size c : ℝ) + S + η := by push_cast; ring
  rw [ec] at key
  exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end
