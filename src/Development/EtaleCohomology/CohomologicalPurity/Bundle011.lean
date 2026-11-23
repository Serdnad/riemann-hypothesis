module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd.ExactPf

variable {R : Type} [CommRing R] {A B D I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : δ n m (pb f c) = pb f (δ n m c) :=
  δ_ofHom_comp _ _ _

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' :=
  Cochain.comp_sub _ _ _ _

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' :=
  Cochain.comp_add _ _ _ _

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 :=
  Cochain.comp_zero _ _

theorem pb_w {i : A ⟶ B} {l r : B ⟶ D} (w : i ≫ l = i ≫ r) {n : ℤ} (c : Cochain D I n) :
    pb i (pb l c) = pb i (pb r c) := by
  rw [pb_pb, pb_pb, w]

abbrev zpb (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) : Cocycle A I n := zcomp (Cocycle.ofHom f) b (zero_add n)

theorem zpb_coe (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) : (zpb f b).1 = pb f b.1 := rfl

theorem hpb_mk (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) :
    hpb f I n (CohomologyClass.mk b) = CohomologyClass.mk (zpb f b) := rfl

theorem zero_iff {K L : Cx R} {n : ℤ} (m : ℤ) (hm : m + 1 = n) (x : Cocycle K L n) :
    CohomologyClass.mk x = 0 ↔ ∃ e : Cochain K L m, δ m n e = x.1 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff x m hm]

theorem mk_eq_of {K L : Cx R} {n : ℤ} (m : ℤ) (hm : m + 1 = n) (x y : Cocycle K L n) (e : Cochain K L m)
    (he : x.1 - y.1 = δ m n e) : CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff m hm]
  exact ⟨e, by rw [Cocycle.coe_sub, he]⟩

theorem glue_cocycle {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) {k : ℤ} (c c' : Cochain B I k)
    (hc : δ k (k + 1) c = 0) (hc' : δ k (k + 1) c' = 0) (he : pb i c = pb i c') :
    ∃ b : Cocycle D I k, pb l b.1 = c ∧ pb r b.1 = c' := by
  obtain ⟨b, hl, hr⟩ := h.glue k c c' he
  refine ⟨Cocycle.mk b (k + 1) rfl (h.ext _ _ _ ?_ ?_), hl, hr⟩
  · rw [← pb_δ, hl, hc, pb_zero]
  · rw [← pb_δ, hr, hc', pb_zero]

theorem exact1 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) :
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) := by
  intro y
  obtain ⟨β, rfl⟩ := y.mk_surjective
  constructor
  · intro hy
    rw [hpb_mk, zero_iff (n - 1) (by omega)] at hy
    obtain ⟨α, hα⟩ := hy
    obtain ⟨c, hc⟩ := h.surj (n - 1) α
    obtain ⟨b, hl, hr⟩ := glue_cocycle h (β.1 - δ (n - 1) n c) 0
      (by rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]) (δ_zero _ _)
      (by rw [pb_sub, ← pb_δ, hc, hα, zpb_coe, sub_self, pb_zero])
    refine ⟨⟨CohomologyClass.mk b, ?_⟩, ?_⟩
    · rw [AddMonoidHom.mem_ker, hpb_mk]
      have : zpb r b = 0 := Cocycle.ext (by rw [zpb_coe, hr]; rfl)
      rw [this, CohomologyClass.mk_zero]
    · change hpb l I n (CohomologyClass.mk b) = _
      rw [hpb_mk]
      exact mk_eq_of (n - 1) (by omega) _ _ (-c) (by rw [zpb_coe, hl, δ_neg]; abel)
  · rintro ⟨⟨x, hx⟩, hxy⟩
    rw [← hxy]
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [AddMonoidHom.mem_ker, hpb_mk] at hx
    change hpb i I n (hpb l I n (CohomologyClass.mk b)) = 0
    rw [hpb_mk, hpb_mk]
    have : zpb i (zpb l b) = zpb i (zpb r b) := Cocycle.ext (by simp only [zpb_coe]; exact pb_w h.w _)
    rw [this, ← hpb_mk, hx, map_zero]

theorem exact2 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) (d) (hd : IsDelta i l r I n d) :
    Function.Exact (hpb i I n) d := by
  intro y
  obtain ⟨a, rfl⟩ := y.mk_surjective
  constructor
  · intro h0
    obtain ⟨c, b, ht⟩ := h.tri a
    have hb : CohomologyClass.mk b = 0 := by rw [← hd a c b ht, h0]; rfl
    rw [zero_iff n rfl] at hb
    obtain ⟨e, he⟩ := hb
    obtain ⟨h1, h2, h3⟩ := ht
    let c' : Cocycle B I n := Cocycle.mk (c - pb l e + pb r e) (n + 1) rfl (by
      rw [δ_add, δ_sub, pb_δ, pb_δ, he, h2, h3]; abel)
    refine ⟨CohomologyClass.mk c', ?_⟩
    rw [hpb_mk]
    congr 1
    apply Cocycle.ext
    rw [zpb_coe]
    change pb i (c - pb l e + pb r e) = a.1
    rw [pb_add, pb_sub, pb_w h.w, h1]; abel
  · rintro ⟨y, hy⟩
    obtain ⟨β, rfl⟩ := y.mk_surjective
    rw [← hy]
    have := hd (zpb i β) β.1 0 ⟨rfl, by rw [Cocycle.δ_eq_zero]; exact pb_zero l, pb_zero r⟩
    exact Subtype.ext (this.trans (CohomologyClass.mk_zero _ _ _))

theorem exact3 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) (d) (hd : IsDelta i l r I n d) :
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype) := by
  rintro ⟨x, hx⟩
  obtain ⟨b, rfl⟩ := x.mk_surjective
  show hpb l I (n + 1) (CohomologyClass.mk b) = 0 ↔ _
  constructor
  · intro hl
    rw [AddMonoidHom.mem_ker, hpb_mk, zero_iff n rfl] at hx
    rw [hpb_mk, zero_iff n rfl] at hl
    obtain ⟨e₁, he₁⟩ := hl
    obtain ⟨e₂, he₂⟩ := hx
    obtain ⟨g, hg₁, hg₂⟩ := h.glue n e₂ e₂ rfl
    let b' : Cocycle D I (n + 1) := Cocycle.mk (b.1 - δ n (n + 1) g) (n + 1 + 1) rfl (by
      rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero])
    let a : Cocycle A I n := Cocycle.mk (pb i (e₁ - e₂)) (n + 1) rfl (by
      rw [pb_δ, δ_sub, he₁, he₂, zpb_coe, zpb_coe, pb_sub, pb_w h.w, sub_self])
    have ht : Tri i l r a (e₁ - e₂) b' := by
      refine ⟨rfl, ?_, ?_⟩
      · change pb l (b.1 - δ n (n + 1) g) = _
        rw [pb_sub, ← pb_δ, hg₁, δ_sub, he₁, zpb_coe]
      · change pb r (b.1 - δ n (n + 1) g) = _
        rw [pb_sub, ← pb_δ, hg₂, he₂, zpb_coe, sub_self]
    refine ⟨CohomologyClass.mk a, Subtype.ext ((hd a _ b' ht).trans ?_)⟩
    exact mk_eq_of n rfl _ _ (-g) (by change (b.1 - δ n (n + 1) g) - b.1 = _; rw [δ_neg]; abel)
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := y.mk_surjective
    obtain ⟨c, b0, ht⟩ := h.tri a
    have hb : CohomologyClass.mk b = CohomologyClass.mk b0 := by
      rw [← hd a c b0 ht, hy]
    rw [hb, hpb_mk, zero_iff n rfl]
    exact ⟨c, ht.2.1.symm⟩

end ExactPf

theorem LeafExact_of : LeafExact := by
  intro R _ A B D i l r I h n d hd
  exact ⟨ExactPf.exact1 h n, ExactPf.exact2 h n d hd, ExactPf.exact3 h n d hd⟩

end LateralTheory.CohomologicalPurity.Bd
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Pf
variable {R : Type} [CommRing R] {A B D : Cx R} {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : pb f (δ n m c) = δ n m (pb f c) := by
  simp [pb]

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' := by
  simp [pb]

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 := by
  simp [pb]

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' := by
  simp [pb]

theorem Tri.sub {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a - a') (c - c') (b - b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_sub, h1, h1', Cocycle.coe_sub]
  · rw [Cocycle.coe_sub, pb_sub, h2, h2', δ_sub]
  · rw [Cocycle.coe_sub, pb_sub, h3, h3', sub_zero]

theorem Tri.add {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a + a') (c + c') (b + b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_add, h1, h1', Cocycle.coe_add]
  · rw [Cocycle.coe_add, pb_add, h2, h2', δ_add]
  · rw [Cocycle.coe_add, pb_add, h3, h3', add_zero]

theorem Good.mk_zero (hG : Good i l r I) {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (ha : a ∈ coboundaries A I n) : CohomologyClass.mk b = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨f, hf⟩ := (mem_coboundaries_iff a (n - 1) (by omega)).1 ha
  obtain ⟨g, hg⟩ := hG.surj (n - 1) f
  obtain ⟨e, he1, he2⟩ := hG.glue n (c - δ (n - 1) n g) 0 (by
    rw [pb_sub, pb_δ, hg, hf, h1, sub_self, pb_zero])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff b n rfl]
  refine ⟨e, hG.ext (n + 1) _ _ ?_ ?_⟩
  · rw [pb_δ, he1, h2, δ_sub, δ_δ, sub_zero]
  · rw [pb_δ, he2, h3, δ_zero]

theorem Good.mk_eq (hG : Good i l r I) {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n}
    {b b' : Cocycle D I (n + 1)} (h : Tri i l r a c b) (h' : Tri i l r a' c' b')
    (ha : a - a' ∈ coboundaries A I n) : CohomologyClass.mk b = CohomologyClass.mk b' := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
  exact hG.mk_zero (h.sub h') ha

theorem tri_zero {n : ℤ} : Tri i l r (0 : Cocycle A I n) 0 (0 : Cocycle D I (n + 1)) :=
  ⟨by rw [pb_zero, Cocycle.coe_zero], by rw [Cocycle.coe_zero, pb_zero, δ_zero], by rw [Cocycle.coe_zero, pb_zero]⟩

theorem Tri.ker {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)} (h : Tri i l r a c b) :
    CohomologyClass.mk b ∈ (hpb r I (n + 1)).ker := by
  rw [AddMonoidHom.mem_ker, hpb, cpre_mk, CohomologyClass.mk_eq_zero_iff]
  have : zcomp (Cocycle.ofHom r) b (zero_add (n + 1)) = 0 := Cocycle.ext (by
    change pb r b.1 = _
    rw [h.2.2, Cocycle.coe_zero])
  rw [this]
  exact zero_mem _

theorem LeafDelta_of : LeafDelta := by
  intro R _ A B D i l r I hG n
  choose c b hcb using fun a : Cocycle A I n => hG.tri a
  let F : Cocycle A I n →+ (hpb r I (n + 1)).ker :=
    AddMonoidHom.mk' (fun a => ⟨CohomologyClass.mk (b a), (hcb a).ker⟩) (fun a a' => by
      apply Subtype.ext
      change CohomologyClass.mk (b (a + a')) = CohomologyClass.mk (b a) + CohomologyClass.mk (b a')
      rw [← CohomologyClass.mk_add]
      exact hG.mk_eq (hcb _) ((hcb a).add (hcb a')) (by rw [sub_self]; exact zero_mem _))
  refine ⟨CohomologyClass.descAddMonoidHom F ?_, ?_⟩
  · intro a ha
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    change CohomologyClass.mk (b a) = 0
    rw [← CohomologyClass.mk_zero D I (n + 1)]
    exact hG.mk_eq (hcb a) tri_zero (by rw [sub_zero]; exact ha)
  · intro a c' b' h
    change CohomologyClass.mk (b a) = _
    exact hG.mk_eq (hcb a) h (by rw [sub_self]; exact zero_mem _)

end Pf
end LateralTheory.CohomologicalPurity.Bd
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

def LeafFive : Prop := ∀ δ, IsBd δ → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Mono P'.hom → Mono P.hom →
  (∀ i, Eqv _ φ.left (tw q i)) → (∀ i, Eqv _ φ.right (tw q i)) → Exc q φ

def LeafChartFact : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) →
  ∃ (P : Arrow Spc) (α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P) (β : P ⟶ pr d R), α ≫ β = Φ ∧
    Mono (opn (off (MvPolynomial (Fin d) R) I)).hom ∧ Mono P.hom ∧
    (∀ i, Eqv _ α.left (tw q i)) ∧ (∀ i, Eqv _ α.right (tw q i)) ∧
    IsPullback P.hom β.left β.right (pr d R).hom ∧ Cover2 (ZMod q) β.right (pr d R).hom

theorem dbl_hom_ext {P : Arrow Spc} {X : Spc} {f g : dbl P ⟶ X} (h0 : dbl.inl P ≫ f = dbl.inl P ≫ g)
    (h1 : dbl.inr P ≫ f = dbl.inr P ≫ g) : f = g := pushout.hom_ext h0 h1

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map (α ≫ β) = dbl.map α ≫ dbl.map β := by
  apply dbl_hom_ext
  · rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_comp_apply (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (α ≫ β) n i x = Hs.pull q α n i (Hs.pull q β n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (α ≫ β)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map α) _ n (GlobalTheory.EtC.pull _ (dbl.map β) _ n x.1)
  rw [dbl_map_comp, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (hα : Exc q α) (hβ : Exc q β) :
    Exc q (α ≫ β) := fun n i => by
  have : (Hs.pull q (α ≫ β) n i : Hs q P n i → Hs q P'' n i) = Hs.pull q α n i ∘ Hs.pull q β n i :=
    funext (pull_comp_apply q α β n i)
  rw [this]
  exact (hα n i).comp (hβ n i)

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = GlobalTheory.EtC.pull _ φ.right _ n (Hs.fgt q P n i x) := by
  change GlobalTheory.EtC.pull _ (dbl.inl P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) =
    GlobalTheory.EtC.pull _ φ.right _ n (GlobalTheory.EtC.pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, inl_map, pull_comp]

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (c : Ht q P.right n i) :
    GlobalTheory.EtC.pull _ P'.hom (tw q i) n (GlobalTheory.EtC.pull _ φ.right _ n c) =
      GlobalTheory.EtC.pull _ φ.left _ n (GlobalTheory.EtC.pull _ P.hom (tw q i) n c) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem five (δ : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), Ht q P.left n i →+ Hs q P (n + 1) i) (hδ : IsBd δ)
    (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom)
    (hl : ∀ i, Eqv _ φ.left (tw q i)) (hr : ∀ i, Eqv _ φ.right (tw q i)) (m i : ℤ) :
    Function.Bijective (Hs.pull q φ (m + 1) i) := by
  obtain ⟨hex, hnat, -⟩ := hδ
  obtain ⟨-, e2, e3⟩ := hex q P h m i
  obtain ⟨-, e2', e3'⟩ := hex q P' h' m i
  obtain ⟨e1, -, -⟩ := hex q P h (m + 1) i
  obtain ⟨e1', -, -⟩ := hex q P' h' (m + 1) i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hf : Hs.fgt q P (m + 1) i x = 0 := by
      apply (hr i (m + 1)).1
      rw [← fgt_pull, hx, map_zero, map_zero]
    obtain ⟨u, rfl⟩ := (e3 x).1 hf
    have hu : δ q P' m i (GlobalTheory.EtC.pull _ φ.left _ m u) = 0 := by rw [← hnat q P' P φ h' h m i u]; exact hx
    obtain ⟨w', hw'⟩ := (e2' _).1 hu
    obtain ⟨w, rfl⟩ := (hr i m).2 w'
    rw [res_pull] at hw'
    have := (hl i m).1 hw'
    rw [← this]
    exact (e2 _).2 ⟨w, rfl⟩
  · intro y
    obtain ⟨c, hc⟩ := (hr i (m + 1)).2 (Hs.fgt q P' (m + 1) i y)
    have hc0 : GlobalTheory.EtC.pull _ P.hom (tw q i) (m + 1) c = 0 := by
      apply (hl i (m + 1)).1
      rw [← res_pull, hc, map_zero]
      exact (e1' _).2 ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (e1 c).1 hc0
    have hd : Hs.fgt q P' (m + 1) i (y - Hs.pull q φ (m + 1) i x) = 0 := by
      rw [map_sub, fgt_pull, hx, hc, sub_self]
    obtain ⟨u', hu'⟩ := (e3' _).1 hd
    obtain ⟨u, rfl⟩ := (hl i m).2 u'
    refine ⟨x + δ q P m i u, ?_⟩
    rw [map_add (f := _), hnat q P' P φ h' h m i u, hu', add_sub_cancel]

theorem leafFive : LeafFive := by
  intro δ hδ q P' P φ h' h hl hr n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five δ hδ q φ h' h hl hr m i

end LateralTheory.CohomologicalPurity.Thom.ExcP

namespace LateralTheory.CohomologicalPurity.Thom

theorem excision_of_thom_chart_factorization (hBd : LeafBd) (hSp : LeafExcSp) (hFact : ExcP.LeafChartFact) :
    LeafExcP := by
  intro hH q _ d R _ I hI hq Φ hΦ
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨P, α, β, hαβ, hm1, hm2, hl, hr, hpb, hcov⟩ := hFact hH q d R I hI hq Φ hΦ
  rw [← hαβ]
  exact ExcP.exc_comp q α β (ExcP.leafFive δ hδ q α hm1 hm2 hl hr) (hSp hH.1 q β hpb hcov)

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafFreeCok : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, w]))

def LeafSurjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (t : T ⟶ X), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : V ⟶ U.toScheme, x ≫ U.ι = g ≫ t) ∨ ∃ y : V ⟶ X', y ≫ f = g ≫ t

def LeafInjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (y₁ y₂ : T ⟶ X'), y₁ ≫ f = y₂ ≫ f →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      g ≫ y₁ = g ≫ y₂ ∨ ∃ x : V ⟶ U.toScheme, x ≫ U.ι = (g ≫ y₁) ≫ f

theorem excSheaf_cart_preimage {X' X T : Scheme.{0}} (f : X' ⟶ X) (U : X.Opens) (y : T ⟶ X') (x : T ⟶ U.toScheme)
    (hx : x ≫ U.ι = y ≫ f) : ∃ x' : T ⟶ (f ⁻¹ᵁ U).toScheme, x' ≫ (f ⁻¹ᵁ U).ι = y :=
  ⟨(isPullback_morphismRestrict f U).lift x y hx, (isPullback_morphismRestrict f U).lift_snd _ _ _⟩

theorem LeafExcSheaf_of (hF : LeafFreeCok) (hS : LeafSurjGeo) (hI : LeafInjGeo) : LeafExcSheaf := by
  intro R _ X' X Z f _ ι' ι _ hp U' U hU h
  subst h
  exact hF R (yoneda.map (f ⁻¹ᵁ U).ι) (yoneda.map U.ι) (yoneda.map (f.resLE U (f ⁻¹ᵁ U) le_rfl)) (yoneda.map f)
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (fun T y x hx => excSheaf_cart_preimage f U y x hx) (fun T y => hS f ι' ι hp U hU y)
    (fun T y₁ y₂ h => hI f ι' ι hp U hU y₁ y₂ h)

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem mono_freeP (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((freeP R).map g) := by
  have : ∀ U, Mono (((freeP R).map g).app U) := by
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 inferInstance
    rw [ModuleCat.mono_iff_injective]
    dsimp [freeP]
    exact Finsupp.mapDomain_injective (fun a b h => ULift.ext (hg (congrArg ULift.down h)))
  exact NatTrans.mono_of_mono_app _

theorem mono_free (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((free R).map g) := by
  have := mono_freeP R g
  dsimp [free]
  infer_instance

theorem LeafMono_of : LeafMono := by
  intro R _ U E f hf p
  have hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k) := by
    intro k
    have : Mono (f.app (op (SimplexCategory.mk k))) := inferInstance
    have := mono_free R (f.app (op (SimplexCategory.mk k)))
    simp only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact this
  by_cases h : ∃ k : ℕ, -(k : ℤ) = p
  · obtain ⟨k, rfl⟩ := h
    have e := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl
    change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)
    rw [e]
    have := hk k
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk; exact h ⟨k, hk⟩
    exact hz.mono _
end Bd
end CohomologicalPurity
end LateralTheory
end
end
