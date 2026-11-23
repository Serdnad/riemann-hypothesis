module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.Bundle003
public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Development.EtaleCohomology.EtaleTrace.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) (z : V l C n) :
    pb l (f ≫ g) n z = pb l f n (pb l g n z) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem pbi (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  show pullHQ l (sch.map (𝟙 X)) n 0 z = z
  rw [CategoryTheory.Functor.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]; rfl

private theorem step {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (hP : Pairs) (hL : Low l k) (G : GysQ k l) (d : ℕ)
    {X : Scheme.{0}} (p : X ⟶ S k) (hs : IsSeparated p) (hsm : SmoothOfRelativeDimension d p) (y : Pt p)
    (U' U : X.Opens) (hU : (U : Set X) = (U' : Set X) \ Set.range y.1) (hy : Set.range y.1 ⊆ (U' : Set X))
    (z : V l X (2 * d)) (hz : pb l U.ι _ z = 0) :
    ∃ r : ℚ_[l], pb l U'.ι _ (z - r • G.pt d y) = 0 := by
  have hsep : IsSeparated (U'.ι ≫ p) := inferInstance
  have hsm' : SmoothOfRelativeDimension d (U'.ι ≫ p) := by
    have h := smoothOfRelativeDimension_comp (n := 0) (m := d) U'.ι p
    rwa [Nat.zero_add] at h
  have hr : Set.range y.1 ⊆ Set.range U'.ι := by simpa using hy
  let y' : S k ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι y.1 hr
  have hy' : y' ≫ U'.ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  let t : Pt (U'.ι ≫ p) := ⟨y', by rw [← Category.assoc, hy', y.2]⟩
  have hpt : IsPair d 0 (U'.ι ≫ p) y' := ((hP k d _ hsep hsm').2 t).1
  have hpy : IsPair d 0 p y.1 := ((hP k d p hs hsm).2 y).1
  have hoff : Off y' (U'.ι ⁻¹ᵁ U) := by
    unfold Off
    ext x
    have hx : U'.ι x ∈ (U' : Set X) := by
      have : U'.ι x ∈ Set.range U'.ι := ⟨x, rfl⟩
      simpa using this
    show U'.ι x ∈ (U : Set X) ↔ x ∉ Set.range y'
    rw [hU]
    constructor
    · rintro ⟨-, h2⟩ ⟨w, rfl⟩
      exact h2 ⟨w, by rw [← hy']; rfl⟩
    · intro h
      refine ⟨hx, ?_⟩
      rintro ⟨w, hw⟩
      apply h
      refine ⟨w, ?_⟩
      apply U'.ι.isOpenEmbedding.injective
      rw [← hw, ← hy']; rfl
  have hdead : pb l (U'.ι ⁻¹ᵁ U).ι _ (pb l U'.ι _ z) = 0 := by
    rw [← pbc, ← morphismRestrict_ι, pbc, hz, map_zero]
  have hprop : IsProper (y' ≫ U'.ι ≫ p) := by
    have : y' ≫ U'.ι ≫ p = 𝟙 _ := t.2
    rw [this]; infer_instance
  obtain ⟨a, ha⟩ := G.onto hpt (zero_add _) _ hoff hprop _ hdead
  obtain ⟨r, hra, -⟩ := hL.line a
  refine ⟨r, ?_⟩
  have hpb : IsPullback y' (𝟙 _) U'.ι y.1 := IsPullback.of_vert_isIso_mono ⟨by simp [hy']⟩
  have hnat := G.nat hpt hpy U'.ι (𝟙 _) rfl hpb (zero_add _) (oneV l (S k))
  rw [pbi] at hnat
  have hpt' : G.pt d y = G.g hpy (zero_add _) (oneV l (S k)) := by
    simp only [GysQ.cls, dif_pos hpy]
  rw [map_sub, map_smul, hpt', hnat, ← map_smul, ← hra, ha, sub_self]

end UpperTheory.Gal.KunnethLefschetz

theorem UpperTheory.Gal.KunnethLefschetz.finSupp_holds :
    UpperTheory.Gal.KunnethLefschetz.FinSupp := by
  unfold FinSupp
  intro _ hP l _ k _ _ _ _ hL G d X p hsep hsm s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U hU z hz
    have hT : U = ⊤ := by
      apply SetLike.coe_injective
      simpa [OffPts] using hU
    subst hT
    have h0 : z = 0 := by
      have e : X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by simp
      have h1 : pb l X.topIso.inv _ (pb l (⊤ : X.Opens).ι _ z) = z := by
        rw [← pbc, e, pbi]
      rw [← h1, hz, map_zero]
    rw [h0]; exact zero_mem _
  | insert y s hy ih =>
    intro U hU z hz
    have hcl : ∀ t : Pt p, IsClosed (Set.range t.1) := fun t => by
      haveI := ((hP k d p hsep hsm).2 t).1.cl
      exact t.1.isClosedEmbedding.isClosed_range
    have hopen : IsOpen ((⋃ t ∈ s, Set.range t.1)ᶜ) :=
      (s.finite_toSet.isClosed_biUnion fun t _ => hcl t).isOpen_compl
    let U' : X.Opens := ⟨_, hopen⟩
    have hU' : OffPts s U' := rfl
    have hU2 : (U : Set X) = (U' : Set X) \ Set.range y.1 := by
      rw [hU, Finset.set_biUnion_insert, Set.compl_union, Set.diff_eq, Set.inter_comm]; rfl
    by_cases hin : Set.range y.1 ⊆ (U' : Set X)
    · obtain ⟨r, hr⟩ := step hP hL G d p hsep hsm y U' U hU2 hin z hz
      have h1 := ih U' hU' _ hr
      have hz' : z = (z - r • G.pt d y) + r • G.pt d y := (sub_add_cancel _ _).symm
      rw [hz']
      exact add_mem h1 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩))
    · have hsub : Subsingleton (S k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have hUU : U = U' := by
        apply SetLike.coe_injective
        rw [hU2]
        ext x
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rintro ⟨w, rfl⟩
          apply hin
          rintro _ ⟨w', rfl⟩
          rwa [Subsingleton.elim w' w]
      subst hUU
      exact ih _ hU' z hz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) : pb l (𝟙 X) n = LinearMap.id := by
  show pullHQ l (sch.map (𝟙 X)) n 0 = _
  rw [sch.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem lift_square {A B C : Scheme.{0}} (i : A ⟶ C) [IsOpenImmersion i] (y : B ⟶ C) (y' : B ⟶ A)
    (h : y' ≫ i = y) : IsPullback y' (𝟙 B) i y := (IsPullback.of_horiz_isIso_mono ⟨by simp [h]⟩ : IsPullback (𝟙 B) y' y i).flip

private theorem pt_restrict {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k}
    (U : X.Opens) (y : Pt p) (y' : Pt (U.ι ≫ p)) (hy : y'.1 ≫ U.ι = y.1)
    (h : IsPair d 0 p y.1) (h' : IsPair d 0 (U.ι ≫ p) y'.1) :
    pb l U.ι _ (G.pt d y) = G.pt d y' := by
  show pb l U.ι _ (G.cls d 0 p y.1) = G.cls d 0 (U.ι ≫ p) y'.1
  unfold GysQ.cls
  rw [dite_eq_left h, dite_eq_left h', G.nat h' h U.ι (𝟙 _) rfl (lift_square U.ι y.1 y'.1 hy), pb_id]
  rfl

theorem trComp_holds : TrComp := by
  intro hC hO hP l _ k _ _ hl R G d hint X p hsp hpj
  obtain ⟨m, U, hU, hcov, hdisj⟩ := hC k d p hsp hpj
  have hex : ∀ j, ∃ lam : V l (U j : Scheme) (2 * d) →ₗ[ℚ_[l]] ℚ_[l],
      ∀ y : Pt ((U j).ι ≫ p), lam (G.pt d y) = 1 :=
    fun j => hint _ (hU j).1 (hU j).2.1 (hU j).2.2
  choose lamj hlamj using hex
  refine ⟨∑ j, (lamj j).comp (pb l (U j).ι (2 * d)), fun y => ?_⟩
  have hsep : IsSeparated p := by
    haveI := hsp.1
    infer_instance
  obtain ⟨hy, -⟩ := (hP k d p hsep hsp.2).2 y
  obtain ⟨s⟩ : Nonempty (S k) := inferInstance
  have hrange : Set.range y.1 = {y.1 s} := by
    ext t
    constructor
    · rintro ⟨t', rfl⟩
      rw [Subsingleton.elim t' s]
      rfl
    · intro ht
      exact ⟨s, ht.symm⟩
  obtain ⟨j, hj⟩ := hcov (y.1 s)
  have hsub : Set.range y.1 ⊆ Set.range (U j).ι := by
    rw [Scheme.Opens.range_ι, hrange]
    simpa using hj
  let y' : Pt ((U j).ι ≫ p) :=
    ⟨IsOpenImmersion.lift (U j).ι y.1 hsub, by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2⟩
  have hfac : y'.1 ≫ (U j).ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hsep' : IsSeparated ((U j).ι ≫ p) := by
    haveI := (hU j).1.1
    infer_instance
  have hy' : IsPair d 0 ((U j).ι ≫ p) y'.1 := ((hP k d ((U j).ι ≫ p) hsep' (hU j).1.2).2 y').1
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [LinearMap.comp_apply, pt_restrict G d (U j) y y' hfac hy hy', hlamj]
  · intro j' _ hj'
    obtain ⟨W, hW⟩ := hO.1 y.1 hy.cl
    have hle : U j' ≤ W := by
      intro t ht
      show t ∈ (W : Set X)
      rw [hW, hrange]
      rintro (rfl : t = y.1 s)
      exact (hdisj j' j hj').le_bot (show y.1 s ∈ U j' ⊓ U j from ⟨ht, hj⟩)
    rw [LinearMap.comp_apply, ← Scheme.homOfLE_ι X hle, pb_comp, LinearMap.comp_apply]
    unfold GysQ.pt GysQ.cls
    rw [dite_eq_left hy, G.off hy _ W hW, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end UpperTheory.Gal.KunnethLefschetz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem inv_of_unit {q : ℕ} {X : Scheme.{0}} (hl : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  simpa using hl.map y'.appTop.hom

private theorem cancel_lemma {q : ℕ} {E : Spc} {n i : ℤ} (h1 : n = n) (h2 : i = i) (x : Ht q E n i) :
    Ht.cast h1 h2 x = x := rfl

private theorem eq_of_mul_mul_eq_of_det_ne_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E n' i') (h : Ht.cast h1 h2 x = y) : x = Ht.cast h1.symm h2.symm y := by
  subst h
  rw [LRingPf.cast_cast, cancel_lemma]

private theorem cancel {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} (hi : Inv q E) {i i' : ℤ} (hs : i + i' = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) {n j w : ℤ}
    (h1 : i' + j = w) (h2 : i + w = j) (c : Ht q E n j) :
    (cup q a ((cup q b c).cast (zero_add n) h1)).cast (zero_add n) h2 = c := by
  obtain ⟨hone, hassoc, -⟩ := h6 q E
  have e1 := hassoc a b c
  rw [eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ hab, cup_cast_left, hone hi, LRingPf.cast_cast] at e1
  have e3 := eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ e1.symm
  rw [cup_cast_right, LRingPf.cast_cast, e3, LRingPf.cast_cast, LRingPf.cast_cast, cancel_lemma]

private theorem swap {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} {i i' : ℤ} (hs : i + i' = 0) (hs' : i' + i = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) :
    (cup q b a).cast (add_zero 0) hs' = one q E := by
  rw [(h6 q E).2.2 b a, cast_usmul, LRingPf.cast_cast, hab]
  simp

private theorem bij_of (hI : In) {k : Type} [Field k] {q : ℕ} [NeZero q] (hq : IsUnit (q : k)) {i i' : ℤ}
    (hs : i + i' = 0) (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 i')
    (huv : (cup q u v).cast (add_zero 0) hs = one q (sch.obj (S k))) {X : Scheme.{0}} (p : X ⟶ S k) (n j w : ℤ)
    (hw : i + j = w) : Function.Bijective (twMul q p hw u n) := by
  have hX : Inv q (sch.obj X) := inv_of_unit (LPdCut.unit_of p hq)
  have hS : Inv q (sch.obj (S k)) := inv_of_unit (LPdCut.unit_of (𝟙 (S k)) hq)
  have hUV : (cup q (pull _ (sch.map p) _ 0 u) (pull _ (sch.map p) _ 0 v)).cast (add_zero 0) hs = one q (sch.obj X) := by
    rw [← (hI.a6nat q).2.1 (sch.map p) hS, ← huv, pull_cast, (hI.a6nat q).1]
  have hs' : i' + i = 0 := by omega
  have hVU := swap hI.a6ring hs hs' _ _ hUV
  have h : i' + w = j := by omega
  refine Function.bijective_iff_has_inverse.2 ⟨twMul q p h v n, fun c => ?_, fun c => ?_⟩
  · exact cancel hI.a6ring hX hs' _ _ hVU hw h c
  · exact cancel hI.a6ring hX hs _ _ hUV h hw c

theorem twBij_holds : TwBij := by
  unfold TwBij
  intro hI k _ q _ hq i u v huv X p n j w
  have hvu := swap hI.a6ring (add_neg_cancel i) (neg_add_cancel i) u v huv
  exact ⟨fun hw => bij_of hI hq (neg_add_cancel i) v u hvu p n j w hw,
    fun hw => bij_of hI hq (add_neg_cancel i) u v huv p n j w hw⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private def castHom {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht q E n i →+ Ht q E n' i' where
  toFun := Ht.cast hn hi
  map_zero' := by subst hn hi; rfl
  map_add' := LRingPf.cast_add hn hi

private def pairSP {k : Type} [Field k] {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h : IsPair d e p ι) : LateralTheory.CohomologicalPurity.SP d :=
  { X := X, Z := Z, S := S k, p := p, ι := ι, e := e
    U := ⟨(Set.range ι)ᶜ, h.cl.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    cl := h.cl, smX := h.big, smZ := h.small, hU := rfl }

theorem UpperTheory.Gal.KunnethLefschetz.gysTL_holds :
    UpperTheory.Gal.KunnethLefschetz.GysTL := by
  unfold GysTL
  intro hI hO k _
  have hg : ∀ d, LateralTheory.CohomologicalPurity.Gysin d := hI.gys
  unfold LateralTheory.CohomologicalPurity.Gysin at hg
  choose gys rs H using hg
  refine ⟨⟨fun q d e Z X p ι h n m i j hn hi =>
    (castHom hn hi).comp (gys d q (pairSP h) n i), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    exact ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.2
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU hs
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    have hx := ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.1
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨u, rfl⟩ := (hx a).1 ha
    rw [hs.elim u 0]
    exact map_zero (rs d q (pairSP h) n i)
  · intro q _ hq d e' e Z' X' Z X p' ι' p ι h' h f u hpb n m i j hn hi a
    subst hn hi
    have hoff : Off ι' (f ⁻¹ᵁ (pairSP h).U) := hO.2 ι' ι f u hpb (pairSP h).U rfl
    have hle : (pairSP h').U ≤ f ⁻¹ᵁ (pairSP h).U :=
      (TopologicalSpace.Opens.ext hoff.symm : (pairSP h').U = f ⁻¹ᵁ (pairSP h).U).le
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.1 (pairSP h') ⟨f, u, hpb, hle⟩ n i).1 a)
  · intro q _ hq d e Z X p ι h n m r s t i j i' j' w h1 h2 h3 h4 k1 k2 k3 k4 a b
    subst h1 h2 h3 k1 k2 k3
    exact (H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.1 n m i j a b
  · intro q r _ hq hr d e Z X p ι h n m i j hn hi a
    subst hn hi
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.2 r hr n i).1 a).symm
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz.PnClsPf

private theorem sm_open {A B C : Scheme.{0}} (i : A ⟶ B) [IsOpenImmersion i] (f : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) : SmoothOfRelativeDimension n (i ≫ f) := by
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) i f
  simpa using this

private theorem empty_v (l : ℕ) [Fact l.Prime] (hI : In) (X : Scheme.{0}) (hX : IsEmpty X) (n : ℤ) :
    Subsingleton (V l X n) := by
  have hE := LEmptyPf.LEmpty_of hI.a5 hI.a9
  haveI h1 : ∀ k, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => hE _ X hX _ n
  haveI h2 : Subsingleton (Hl l (sch.obj X) n 0) := by
    show Subsingleton (HlSub l (sch.obj X) n 0)
    infer_instance
  show Subsingleton (ℚ_[l] ⊗[ℤ_[l]] Hl l (sch.obj X) n 0)
  infer_instance

private theorem iso_sub {A B : Scheme.{0}} (e : A ≅ B) (q : ℕ) (n : ℤ)
    (h : Subsingleton (Ht q (sch.obj B) n 0)) : Subsingleton (Ht q (sch.obj A) n 0) := by
  have key : ∀ z : Ht q (sch.obj A) n 0,
      pull (ZMod q) (sch.map e.hom) (tw q 0) n (pull (ZMod q) (sch.map e.inv) (tw q 0) n z) = z := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, pull_id]
  constructor
  intro x y
  rw [← key x, ← key y,
    Subsingleton.elim (pull (ZMod q) (sch.map e.inv) (tw q 0) n x)
      (pull (ZMod q) (sch.map e.inv) (tw q 0) n y)]

end UpperTheory.Gal.KunnethLefschetz.PnClsPf

open UpperTheory.Gal.KunnethLefschetz.PnClsPf in
theorem UpperTheory.Gal.KunnethLefschetz.pnCls_holds :
    UpperTheory.Gal.KunnethLefschetz.PnCls := by
  intro hI hF hH hO l _ k _ _ hl hR hL hA hG
  obtain ⟨gq⟩ := hG
  have one_ne : oneV l (S k) ≠ 0 := by
    intro h0
    obtain ⟨r, -, hr⟩ := Low.line hL 0
    have h1 := hr 0 (by simp)
    have h2 := hr 1 (by simp [h0])
    exact one_ne_zero (h2.trans h1.symm)
  have key : ∀ d : ℕ, ∃ t : Pt (PNto k d), IsClosedImmersion t.1 ∧
      ∃ U : (PN k d).Opens, Off t.1 U ∧
        ∃ z : V l (PN k d) (2 * (d : ℤ)), z ≠ 0 ∧ pb l U.ι (2 * (d : ℤ)) z = 0 := by
    intro d
    induction d with
    | zero =>
      haveI := (hF k 0).2.2.2
      refine ⟨⟨inv (PNto k 0), IsIso.inv_hom_id _⟩, inferInstance, ⊥, ?_, ?_⟩
      · show ((⊥ : (PN k 0).Opens) : Set (PN k 0)) = (Set.range (inv (PNto k 0)).base)ᶜ
        rw [Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso (inv (PNto k 0)).base).2]
        simp
      · refine ⟨oneV l (PN k 0), ?_, ?_⟩
        · intro h0
          apply one_ne
          have hu := Ring.one_nat hR (inv (PNto k 0))
            (LPdCut.unit_of (PNto k 0) (isUnit_iff_ne_zero.mpr hl))
          rw [← hu]
          change pb l (inv (PNto k 0)) 0 (oneV l (PN k 0)) = 0
          rw [h0, map_zero]
        · have he : IsEmpty ((⊥ : (PN k 0).Opens) : Scheme) := ⟨fun x => by simpa using x.2⟩
          haveI := empty_v l hI ((⊥ : (PN k 0).Opens) : Scheme) he (2 * ((0 : ℕ) : ℤ))
          exact Subsingleton.elim _ _
    | succ d ih =>
      obtain ⟨t, htc, U, hU, z, hz, hzU⟩ := ih
      obtain ⟨ι, U0, hιc, hιp, hoff0, ⟨eU0⟩⟩ := hH k d
      haveI := htc
      haveI := hιc
      let t' : Pt (PNto k (d + 1)) := Pt.map ι hιp t
      have htc' : IsClosedImmersion t'.1 := by
        show IsClosedImmersion (t.1 ≫ ι)
        infer_instance
      obtain ⟨U', hU'⟩ := hO.1 t'.1 htc'
      have hP : IsPair 1 d (PNto k (d + 1)) ι :=
        ⟨hιc, (hF k (d + 1)).1.2, by rw [hιp]; exact (hF k d).1.2⟩
      have hn : 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      refine ⟨t', htc', U', hU', gq.g hP hn z, ?_, ?_⟩
      · intro h0
        apply hz
        have hinj := gq.inj hP hn U0 hoff0 (fun j =>
          iso_sub eU0 (l ^ j) _ (hA j (d + 1) _ (by push_cast; omega)))
        apply hinj
        rw [h0, map_zero]
      · have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
        have hVU : ι ⁻¹ᵁ U' = U := by
          apply TopologicalSpace.Opens.ext
          rw [hU]
          show ι.base ⁻¹' (U' : Set (PN k (d + 1))) = _
          rw [hU']
          ext x
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, t', Pt.map]
          constructor
          · rintro h ⟨y, rfl⟩
            exact h ⟨y, rfl⟩
          · rintro h ⟨y, hy⟩
            apply h
            refine ⟨y, hinj ?_⟩
            rw [← hy]
            rfl
        subst hVU
        have hP' : IsPair 1 d (U'.ι ≫ PNto k (d + 1)) (ι ∣_ U') := by
          refine ⟨inferInstance, sm_open U'.ι _ _ (hF k (d + 1)).1.2, ?_⟩
          rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hιp]
          exact sm_open _ _ _ (hF k d).1.2
        rw [gq.nat hP' hP U'.ι (ι ⁻¹ᵁ U').ι rfl (isPullback_morphismRestrict ι U') hn z, hzU,
          map_zero]
  intro d
  obtain ⟨t, -, U, hU, z, hz, hzU⟩ := key d
  exact ⟨t, U, z, hU, hz, hzU⟩
end
end
