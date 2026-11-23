module

public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.EtaleCohomology.EtaleSheaves.Bundle066
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.EtaleSheaves.Bundle067
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
public import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFiniteness

def LeafSpreadSmooth1 : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadLQFMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {CA CB A B : Scheme.{0}} (cB : CB ⟶ Sp Ω) (γ : CA ⟶ CB) (qB : B ⟶ Sp R) (g : A ⟶ B) (vA : CA ⟶ A)
    (vB : CB ⟶ B), (LocallyOfFinitePresentation qB ∧ QuasiCompact qB ∧ QuasiSeparated qB) →
    (LocallyOfFinitePresentation (g ≫ qB) ∧ QuasiCompact (g ≫ qB) ∧ QuasiSeparated (g ≫ qB)) →
    IsPullback vB cB qB (toR R) → IsPullback vA (γ ≫ cB) (g ≫ qB) (toR R) → γ ≫ vB = vA ≫ g →
    LocallyQuasiFinite γ →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (EA EB : Scheme.{0})
      (qB' : EB ⟶ Sp R') (h : EA ⟶ EB) (rA : EA ⟶ A) (rB : EB ⟶ B), IsPullback rB qB' qB (incl hR) →
      IsPullback rA (h ≫ qB') (g ≫ qB) (incl hR) → h ≫ rB = rA ≫ g → LocallyQuasiFinite h

def LeafSpreadLQFGraph : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (f : D0 ⟶ X) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsPullback v0 c0 q (toR R) → v0 ≫ f = e →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E0 : Scheme.{0})
      (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0), IsPullback r q' q (incl hR) →
      ∀ (hf' : (r ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
        LocallyQuasiFinite (pullback.lift q' (r ≫ f) hf'.symm)

def LeafBaseChangePreR : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR) ∧
      w0 ≫ r0 = v0 ∧ e1 ≫ r0 = r1 ≫ d1 ∧ e2 ≫ r1 = r2 ≫ d2

theorem incl_toK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated) (hSm : LeafSpreadSmooth1)
    (hG : LeafSpreadLQFGraph) (hM : LeafSpreadLQFMap) (hB : LeafBaseChangePreR) :
    LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := by
  intro k _ X p _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 e he hc0 h1 h2 qf0 qf1 qf2 D0 D1 D2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨f0, f1, f2, p0, p1, p2, m1, m2⟩ := id hpre
  obtain ⟨S0, a0, g0, H0⟩ := hSep k Ω R hR c0 q v0 f0 hc0.2.1.toIsSeparated p0
  obtain ⟨S1, a1, g1, H1⟩ := hSep k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1.toIsSeparated p1
  obtain ⟨S2, a2, g2, H2⟩ := hSep k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1.toIsSeparated p2
  obtain ⟨T0, b0, k0, K0⟩ := hSm k Ω R hR c0 q v0 f0 hc0.2.2 p0
  obtain ⟨T1, b1, k1, K1⟩ := hSm k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.2 p1
  obtain ⟨T2, b2, k2, K2⟩ := hSm k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.2 p2
  obtain ⟨G, aG, gG, HG⟩ := hG k p Ω R hR c0 q v0 f e he hf f0 p0 hve qf0
  obtain ⟨M1, aM1, gM1, HM1⟩ := hM k Ω R hR c0 γ1 q d1 v1 v0 f0 f1 p0 p1 m1 qf1
  obtain ⟨M2, aM2, gM2, HM2⟩ := hM k Ω R hR (γ1 ≫ c0) γ2 (d1 ≫ q) d2 v2 v1 f1 f2 p1 p2 m2 qf2
  let T := S0 ⊔ S1 ⊔ S2 ⊔ T0 ⊔ T1 ⊔ T2 ⊔ G ⊔ M1 ⊔ M2
  have gT : T.FG := ((((((((g0.sup g1).sup g2).sup k0).sup k1).sup k2).sup gG).sup gM1).sup gM2)
  have lS0 : S0 ≤ T := (((((((le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have literatureStatementsS1 : S1 ≤ T := (((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have logSupBoundLevelFree : S2 ≤ T := ((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT0 : T0 ≤ T := (((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT1 : T1 ≤ T := ((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT2 : T2 ≤ T := (((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lG : G ≤ T := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have familyMassFirstBound : M1 ≤ T := (le_sup_right).trans le_sup_left
  have familyMassSecondBound : M2 ≤ T := le_sup_right
  have hRT : R ≤ T := a0.trans lS0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2, n0, n1, n2⟩ :=
    hB k Ω R T hRT c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  have hf' : (r0 ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [Category.assoc, hf, ← Category.assoc, Q0.w, Category.assoc, incl_toK]
  haveI := f0.2.1; haveI := f1.2.1; haveI := f2.2.1
  refine ⟨T, gT, E0, E1, E2, q', e1, e2, r0 ≫ f, w0, w1, w2, hf', ?_⟩
  exact ⟨H0 T lS0 hRT E0 q' r0 Q0, MorphismProperty.of_isPullback (P := @QuasiCompact) Q0 inferInstance,
    K0 T lT0 hRT E0 q' r0 Q0,
    H1 T literatureStatementsS1 hRT E1 (e1 ≫ q') r1 Q1, MorphismProperty.of_isPullback (P := @QuasiCompact) Q1 inferInstance,
    K1 T lT1 hRT E1 (e1 ≫ q') r1 Q1,
    H2 T logSupBoundLevelFree hRT E2 (e2 ≫ e1 ≫ q') r2 Q2, MorphismProperty.of_isPullback (P := @QuasiCompact) Q2 inferInstance,
    K2 T lT2 hRT E2 (e2 ≫ e1 ≫ q') r2 Q2,
    HG T lG hRT E0 q' r0 Q0 hf', HM1 T familyMassFirstBound hRT E1 E0 q' e1 r1 r0 Q0 Q1 n1,
    HM2 T familyMassSecondBound hRT E2 E1 (e1 ≫ q') e2 r2 r1 Q1 Q2 n2, P0, P1, P2, c1, c2,
    by rw [← Category.assoc, n0, hve]⟩

end LateralTheory.E.SpreadingOutQuasiFiniteness

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjGluePf

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

def DescAt (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D), FP q ∧ IsPullback v f q (toR R)

theorem toR_eq {R R' : Subalgebra k Ω} (h : R ≤ R') : toR R' ≫ incl h = toR R := by
  simp only [toR, incl]
  rw [← Spec.map_comp]
  rfl

theorem fp_snd {X Y Z : Scheme.{0}} (q : X ⟶ Z) (g : Y ⟶ Z) (hq : FP q) : FP (pullback.snd q g) := by
  obtain ⟨h1, h2, h3⟩ := hq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem descAt_mono {R R' : Subalgebra k Ω} (h : R ≤ R') {X : Scheme.{0}} {f : X ⟶ Sp Ω}
    (hd : DescAt R f) : DescAt R' f := by
  obtain ⟨D, q, v, hq, hp⟩ := hd
  refine ⟨pullback q (incl h), pullback.snd q (incl h),
    pullback.lift v (f ≫ toR R') (by rw [hp.w, Category.assoc, toR_eq]), fp_snd _ _ hq, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback q (incl h))
  rw [pullback.lift_fst, toR_eq]
  exact hp

def GlueData (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) (U V : X.Opens) : Prop :=
  ∃ (DU DV DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qV : DV ⟶ Sp R) (qW : DW ⟶ Sp R)
    (vU : U.toScheme ⟶ DU) (vV : V.toScheme ⟶ DV) (vW : (U ⊓ V).toScheme ⟶ DW) (φU : DW ⟶ DU) (φV : DW ⟶ DV),
    FP qU ∧ FP qV ∧ FP qW ∧ IsOpenImmersion φU ∧ IsOpenImmersion φV ∧ φU ≫ qU = qW ∧ φV ≫ qV = qW ∧
    IsPullback vU (U.ι ≫ f) qU (toR R) ∧ IsPullback vV (V.ι ≫ f) qV (toR R) ∧
    IsPullback vW ((U ⊓ V).ι ≫ f) qW (toR R) ∧
    vW ≫ φU = X.homOfLE inf_le_left ≫ vU ∧ vW ≫ φV = X.homOfLE inf_le_right ≫ vV

def LeafInclDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens) (R : Subalgebra k Ω), R.FG →
    DescAt R (U.ι ≫ f) → DescAt R (V.ι ≫ f) → DescAt R ((U ⊓ V).ι ≫ f) →
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ GlueData R' f U V

def LeafGlueTwo : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω) (U V : X.Opens) (R : Subalgebra k Ω), U ⊔ V = ⊤ → GlueData R f U V → DescAt R f

theorem LeafObjGlue_of (hI : LeafInclDescend) (hG : LeafGlueTwo) : LeafObjGlue := by
  intro k _ Ω _ _ X f hf U V hUV ⟨R1, h1, d1⟩ ⟨R2, h2, d2⟩ ⟨R3, h3, d3⟩
  obtain ⟨R', -, hR', g⟩ := hI k Ω f hf U V (R1 ⊔ R2 ⊔ R3) ((h1.sup h2).sup h3)
    (descAt_mono (le_sup_left.trans le_sup_left) d1) (descAt_mono (le_sup_right.trans le_sup_left) d2)
    (descAt_mono le_sup_right d3)
  exact ⟨R', hR', hG k Ω f U V R' hUV g⟩

end LateralTheory.E.LeafObjGluePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafQCQSInductPf

def Cov (X : Scheme.{0}) (L : List X.Opens) : Prop :=
  (∀ u ∈ L, IsAffineOpen u) ∧ ∀ x : X, ∃ u ∈ L, x ∈ u

lemma sep_of {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] [X.IsSeparated] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

lemma fp_res {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (hf : FP f) (W : X.Opens)
    (hW : IsCompact (W : Set X)) : FP (W.ι ≫ f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, ?_, inferInstance⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  exact quasiCompact_of_compactSpace _

lemma cov_pull {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) :
    Cov W.toScheme (L.map (W.ι ⁻¹ᵁ ·)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact (hA u hu).preimage_of_isOpenImmersion W.ι (by simpa using hle u hu)
  · intro x
    obtain ⟨u, hu, hx⟩ := hc (W.ι x) (by
      have := Set.mem_range_self (f := W.ι) x
      rwa [Scheme.Opens.range_ι] at this)
    exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hx⟩

lemma exists_list {X : Scheme.{0}} (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ L : List X.Opens, (∀ u ∈ L, IsAffineOpen u) ∧ (∀ u ∈ L, u ≤ W) ∧ ∀ x ∈ W, ∃ u ∈ L, x ∈ u := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  refine ⟨hs.toFinset.toList.map (fun a : X.affineOpens => a.1), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.prop
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [e]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) a (by simpa using ha)
  · intro x hx
    rw [e] at hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, hxa⟩

lemma compact_of_cover {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) : IsCompact (W : Set X) := by
  have : (W : Set X) = ⋃ u ∈ L, (u : Set X) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx => let ⟨u, hu, h⟩ := hc x hx; ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => hle u hu h⟩
  rw [this]
  exact L.finite_toSet.isCompact_biUnion fun u hu => (hA u hu).isCompact

lemma mem_V {X : Scheme.{0}} (L : List X.Opens) (x : X) :
    x ∈ (⨆ u ∈ L, u : X.Opens) ↔ ∃ u ∈ L, x ∈ u := by
  simp

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma glue_step {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (U : X.Opens) (L' : List X.Opens)
    (hc : Cov X (U :: L'))
    (hV : Cov (⨆ u ∈ L', u : X.Opens).toScheme
        (L'.map ((⨆ u ∈ L', u : X.Opens).ι ⁻¹ᵁ ·)) → P ((⨆ u ∈ L', u : X.Opens).ι ≫ f))
    (hW : P ((U ⊓ ⨆ u ∈ L', u : X.Opens).ι ≫ f)) :
    P f := by
  have hU : IsAffineOpen U := hc.1 U (by simp)
  have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
  have hUV : U ⊔ (⨆ u ∈ L', u : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hx⟩ := hc.2 x
    rcases List.mem_cons.mp hu with rfl | hu
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((mem_V L' x).mpr ⟨u, hu, hx⟩))
  refine hG f hf U _ hUV ?_ ?_ ?_
  · haveI : IsAffine U := hU
    exact hA _ inferInstance (fp_res f hf U hU.isCompact)
  · refine hV (cov_pull _ L' hL' (fun u hu => ?_) (fun x hx => (mem_V L' x).mp hx))
    exact le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu
  · exact hW

end

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma empty_case {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (hc : Cov X []) : P f := by
  have : IsEmpty X := ⟨fun x => by obtain ⟨u, hu, _⟩ := hc.2 x; simp at hu⟩
  exact hA f inferInstance hf

lemma stepA : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    X.IsSeparated → Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf _ hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hs hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      have : (⨆ u ∈ L', u : X.Opens).toScheme.IsSeparated := sep_of (⨆ u ∈ L', u : X.Opens).ι
      refine ih _ _ (by simp [hl]) (fp_res f hf _ ?_) this hcV
      exact compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have hA' : ∀ v ∈ L'.map (U ⊓ ·), IsAffineOpen v := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact hU.inf (hL' u hu)
      have hle : ∀ v ∈ L'.map (U ⊓ ·), v ≤ W := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact inf_le_inf_left U (le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
      have hcW : ∀ x ∈ W, ∃ v ∈ L'.map (U ⊓ ·), x ∈ v := by
        intro x hx
        obtain ⟨hxU, hxV⟩ := hx
        obtain ⟨u, hu, h⟩ := (mem_V L' x).mp hxV
        exact ⟨U ⊓ u, List.mem_map.mpr ⟨u, hu, rfl⟩, ⟨hxU, h⟩⟩
      have : W.toScheme.IsSeparated := sep_of W.ι
      exact ih _ ((L'.map (U ⊓ ·)).map (W.ι ⁻¹ᵁ ·)) (by simp [hl])
        (fp_res f hf W (compact_of_cover W _ hA' hle hcW)) this (cov_pull W _ hA' hle hcW)

lemma stepB : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    have hVc : IsCompact ((⨆ u ∈ L', u : X.Opens) : Set X) :=
      compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      exact ih _ _ (by simp [hl]) (fp_res f hf _ hVc) hcV
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have : QuasiSeparated f := hf.2.2
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      have hWc : IsCompact (W : Set X) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU.isCompact (⨆ u ∈ L', u : X.Opens).2 hVc
      obtain ⟨L2, h1, h2, h3⟩ := exists_list W hWc
      haveI : IsAffine U := hU
      have : W.toScheme.IsSeparated := sep_of (X.homOfLE (inf_le_left : W ≤ U))
      exact stepA P hA hG _ (W.ι ≫ f) (L2.map (W.ι ⁻¹ᵁ ·)) rfl (fp_res f hf W hWc) this
        (cov_pull W L2 h1 h2 h3)

end

theorem LeafQCQSInduct_of : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := by
  intro S _ P hA hG X f hf
  have : QuasiCompact f := hf.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨L, h1, -, h3⟩ := exists_list (⊤ : X.Opens) (by simpa using isCompact_univ)
  exact stepB P hA hG _ f L rfl hf ⟨h1, fun x => h3 x trivial⟩

end LateralTheory.E.LeafQCQSInductPf
end
end

section

noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
end
end
