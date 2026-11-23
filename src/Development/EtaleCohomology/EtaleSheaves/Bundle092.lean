module

public import Development.EtaleCohomology.EtaleSheaves.Bundle021
public import Development.EtaleCohomology.EtaleSheaves.Bundle040
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.EtaleCohomology.EtaleSheaves.Bundle084
public import Development.EtaleCohomology.EtaleSheaves.Bundle076
public import Development.EtaleCohomology.EtaleSheaves.Bundle083
public import Development.EtaleCohomology.EtaleSheaves.Bundle089
public import Development.EtaleCohomology.EtaleSheaves.Bundle047
public import Development.EtaleCohomology.EtaleSheaves.Bundle074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubring
public import Development.EtaleCohomology.EtaleSheaves.Bundle086
public import Development.EtaleCohomology.EtaleSheaves.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

namespace LateralTheory.E.CompositionGoal

theorem goal_of : LateralTheory.E.SHExistsPf.Comp := LateralTheory.E.TruncationIsoComparison.Comp_of

end LateralTheory.E.CompositionGoal
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.StalkGermPf GlobalTheory.StalkLimit

namespace LateralTheory.E.StalkContPf

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}}

theorem diagram_map_eq (p : X ⟶ S) (s : S) {V W : AffNhd s} (i : V ⟶ W) :
    (diagram s p).map i = resO p i.le := by
  apply pullback.hom_ext <;> simp [diagram, resO]

theorem cone_app_eq (p : X ⟶ S) (s : S) (V : AffNhd s) :
    (cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V = toO p s V.1 V.2.1 := by
  apply pullback.hom_ext <;> simp [cone, toO]

theorem pull_cone {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) (V : AffNhd s) (y : Ht q (sch.obj (overO p V.1)) n i) :
    pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V)) (tw q i) n y =
      pull _ (sch.map (toO p s V.1 V.2.1)) (tw q i) n y := by
  rw [cone_app_eq]; rfl

theorem pull_diag {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) {V W : AffNhd s} (f : V ⟶ W)
    (y : Ht q (sch.obj (overO p W.1)) n i) :
    pull _ (sch.map ((diagram s p).map f)) (tw q i) n y = pull _ (sch.map (resO p f.le)) (tw q i) n y := by
  rw [diagram_map_eq]; rfl

theorem exists_aff (s : S) (U : S.Opens) (hs : s ∈ U) : ∃ V : AffNhd s, V.1 ≤ U := by
  obtain ⟨W, h₁, h₂, h₃⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hs
  exact ⟨⟨W, h₂, h₁⟩, h₃⟩

theorem StalkCont_of : StalkCont := by
  intro hC hH q X S p _ _ _ _ hq i n s
  have hc := (nonempty_isLimit (IsPullback.of_hasPullback p (S.fromSpecStalk s))).some
  have hcpt : ∀ V : AffNhd s, CompactSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd s, QuasiSeparatedSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have hu : ∀ V : AffNhd s, IsUnit (q : Γ((diagram s p).obj V, ⊤)) := fun V => by
    have := hq.map ((pullback.fst p V.1.ι ≫ p).appTop).hom
    simp only [map_natCast] at this
    exact this
  obtain ⟨hsurj, hkill⟩ := hC hH q (diagram s p) _ hc (fun f => inferInstance) hcpt hqs hu n i
  constructor
  · intro U hs x hx
    obtain ⟨V0, hV0⟩ := exists_aff s U hs
    have h0 : pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V0)) _ _
        (pull _ (sch.map (resO p hV0)) _ _ x) = 0 := by
      rw [pull_cone, ← pull_mc, toO_res]; exact hx
    obtain ⟨k, f, hf⟩ := hkill V0 _ h0
    have hkV : k.1 ≤ V0.1 := f.le
    refine ⟨k.1, hkV.trans hV0, k.2.1, ?_⟩
    rw [pull_diag, ← pull_mc, res_res] at hf
    exact hf
  · intro z
    obtain ⟨j, y, hy⟩ := hsurj z
    exact ⟨j.1, j.2.1, y, (pull_cone p s j y).symm.trans hy⟩

end LateralTheory.E.StalkContPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.DiagramDescent

theorem descendFP_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) : LeafDescendFP := by
  have hO : LeafObjFP := LateralTheory.E.LeafObjFPPf.objectDescent_of_affineDescent hA
    (LateralTheory.E.LeafObjGluePf.LeafObjGlue_of (LateralTheory.E.LeafInclDescendPf.LeafInclDescend_of hI) hG) hQ
  exact diagramDescent_of_objects_pairs_triples hO (LateralTheory.E.LeafPairFPPf.pairDescent_of_objects_morphisms hO (LateralTheory.E.LeafMapFPPf2.morphismDescent_of_isLimit hL))
    (LateralTheory.E.LeafTripleFPPf.tripleDescent_of_pairRelation (LateralTheory.E.LeafPairRelPf.LeafPairRel_of hO hF))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem cond {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h.w

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h

theorem LeafDescendPreMap_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) :
    LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hRfg, D0, D1, D2, q, d1, d2, v0, v1, v2, hpre⟩ :=
    descendFP_of hA hG hQ hI hL hF k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨hq0, hq1, hq2, p0, p1, p2, m1, m2⟩ := hpre
  have : LocallyOfFinitePresentation p := LateralTheory.E.LeafDescendMapPf.lfp p
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hlfp : LocallyOfFinitePresentation (pullback.snd p bk) := inferInstance
  have ha : e ≫ p = (c0 ≫ toR R) ≫ bk := by
    rw [he, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_base]
  obtain ⟨R', h, hR'fg, g, hg1, hg2⟩ := hF k Ω R hRfg c0 q v0 hq0 p0 (pullback.snd p bk) hlfp
    (pullback.lift e (c0 ≫ toR R) ha) (pullback.lift_snd _ _ _)
  let e1 : pullback (d1 ≫ q) (incl h) ⟶ pullback q (incl h) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl h) ⟶ pullback (d1 ≫ q) (incl h) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl h) = pullback.snd (d2 ≫ d1 ≫ q) (incl h) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR'fg, _, _, _, pullback.snd q (incl h), e1, e2, g ≫ pullback.fst p bk,
    pullback.lift v0 (c0 ≫ toR R') (cond h p0), pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond h p1),
    pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond h p2), ?_, ⟨fp_snd _ _ hq0, ?_, ?_, sq h p0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc,
      LateralTheory.E.LeafDescendMapPf.incl_base]
  · rw [E1]; exact fp_snd _ _ hq1
  · rw [E2]; exact fp_snd _ _ hq2
  · rw [E1]; exact sq h p1
  · rw [E2]; exact sq h p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [← Category.assoc, hg2, pullback.lift_fst]

end LateralTheory.E.DiagramDescent

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafSpreadSeparatedPf

namespace LateralTheory.E.LeafClosedImmSpreadPf

theorem bc_sq {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (BC f g (f ≫ g) rfl t) f (pullback.fst g t) := by
  have e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
    simp only [BC, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)
  · rw [e]; exact IsPullback.of_hasPullback (f ≫ g) t
  · simp only [BC, pullback.map, pullback.lift_fst]

theorem toR_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype : Sp Ω ⟶ Sp R) = toR R := rfl

theorem incl_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω} (h : R ≤ S)
    (h' : R.toSubring ≤ S.toSubring) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h') : Sp S ⟶ Sp R) = incl h := rfl

theorem LeafClosedImmSpread_of : LeafClosedImmSpread := by
  intro k _ Ω _ _ R hR X Y f g hg hfg hci
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hp1, hp2, hp3⟩ := hfg
  have := hg1; have := hg2; have := hg3; have := hp1; have := hp2; have := hp3
  have : QuasiSeparated f := QuasiSeparated.of_comp f g
  have : QuasiCompact f := QuasiCompact.of_comp f g
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype) := by
    rw [toR_eq]; exact IsPullback.of_hasPullback g (toR R)
  have : QuasiCompact (g : Y ⟶ Sp R.toSubring) := hg2
  obtain ⟨F, hF⟩ := GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g
    (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci
  let S : Subalgebra k Ω := R ⊔ Algebra.adjoin k (F : Set Ω)
  have h : R ≤ S := le_sup_left
  have h' : R.toSubring ≤ S.toSubring := fun x hx => h hx
  have hsub : (F : Set Ω) ⊆ S.toSubring := fun x hx =>
    (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)
  refine ⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩
  have hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h')) := by
    rw [incl_eq h h']; exact IsPullback.of_hasPullback g (incl h)
  exact hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.snd _ _) hY1 (bc_sq f g _)

end LateralTheory.E.LeafClosedImmSpreadPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.IdempotentLifting

abbrev Aq : Type := AdjoinRoot (X ^ 2 - X : ℤ[X])

lemma monic_q : (X ^ 2 - X : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_sub
  rw [degree_X]; decide

lemma integral_q : (algebraMap ℤ Aq).IsIntegral := by
  have := monic_q.finite_adjoinRoot
  exact fun x => Algebra.IsIntegral.isIntegral x

def toW {W : Type} [CommRing W] (e : W) (he : IsIdempotentElem e) : Aq →+* W :=
  AdjoinRoot.lift (Int.castRingHom W) e (by simp [sq, he.eq])

theorem IdemLift_of : IdemLift := by
  intro P _ _ W _ w _ e he
  let Z : Scheme.{0} := Spec (CommRingCat.of Aq)
  let t : Z ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Aq))
  have : IsIntegralHom t := IsIntegralHom.SpecMap_iff.2 integral_q
  let g : Spec (CommRingCat.of W) ⟶ Z := Spec.map (CommRingCat.ofHom (toW e he))
  let f₁ : Spec (CommRingCat.of W) ⟶ pullback (specZIsTerminal.from P) t :=
    pullback.lift w g (specZIsTerminal.hom_ext _ _)
  have H : w = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  let d := w.normalizationDesc f₁ (pullback.fst _ _) H
  let r : Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Aq)).inv (AdjoinRoot.root _)
  refine ⟨d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r), ?_⟩
  have key : w.toNormalization ≫ d ≫ pullback.snd (specZIsTerminal.from P) t = g := by
    rw [← Category.assoc, w.toNormalization_normalizationDesc, pullback.lift_snd]
  have h1 : w.toNormalization.appTop (d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r)) =
      g.appTop r := by
    rw [← key]; simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom (g.appTop r) = e := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp [r, toW, AdjoinRoot.lift_root]
  unfold phi
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg _ h1).trans h2

end LateralTheory.E.IdempotentLifting
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.GeoProof
open LateralTheory.E.E4 LateralTheory.E.Bridge_yfiPf

theorem affNbhd {B : Scheme.{0}} (U : B.Etale) (u : U.left) :
    ∃ (U' : B.Etale) (a : U' ⟶ U) (R : CommRingCat.{0}) (_ : U'.left ≅ Spec R) (u' : U'.left), a.left u' = u := by
  let f := U.left.affineCover.f (U.left.affineCover.idx u)
  have : IsOpenImmersion f := U.left.affineCover.map_prop _
  refine ⟨Scheme.Etale.mk (f ≫ U.hom), MorphismProperty.Over.homMk f rfl trivial, _, Iso.refl _, ?_⟩
  exact U.left.affineCover.covers u

def AffGeo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (R : CommRingCat.{0}) (_ : U.left ≅ Spec R) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Shrink : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale)
  (a : U' ⟶ U) (m : ℤ) (u' : U'.left), Sys q i p ι U' m u' → Nonempty (Sys q i p ι U m (a.left u'))

theorem Geo_of (hA : AffGeo) (hS : Shrink) : Geo := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m u
  obtain ⟨U', a, R, e, u', rfl⟩ := affNbhd U u
  obtain ⟨S⟩ := hA hH q k hq i toK ι p hp U' R e m u'
  exact hS q i p ι U U' a m u' S

end LateralTheory.E.GeoProof
end
end
