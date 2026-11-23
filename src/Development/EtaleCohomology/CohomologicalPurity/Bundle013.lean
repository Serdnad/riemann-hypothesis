module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tn_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_red_cast {q r : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E n i) : red q r E _ _ (x.cast hn hi) = Ht.cast hn hi (red q r E _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_pull_cast, (h q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_pull_cast, (h q).1, ih]

theorem tn_red_cpow (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) {E : Spc} (hI : Inv q E)
    (L : E ⟶ ofCat (glCat 1)) (k : ℕ) : red q r E _ _ (cpow q (c1 q L) k) = cpow r (c1 r L) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_red_cast, ((h q r hr E).2.1 hI).1]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_red_cast, (h q r hr E).1, ih, ((h q r hr E).2.1 hI).2]

theorem tn_pull_hyp (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0) :
    pull _ f _ _ (hyp q N 0 A) = hyp q N 0 B := by
  unfold hyp
  rw [(h q).2.2.1 f _ hI, hl]

theorem tn_pull_poly (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0)
    (hs : f ≫ prod.snd = prod.snd ≫ spMap φ) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ f _ _ (poly q N 0 A m n i a) = poly q N 0 B m n i (fun j => pull _ (spMap φ) _ _ (a j)) := by
  unfold poly

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_pull_cast, (h q).1, ← pull_comp, hs, pull_comp, tn_pull_cpow h q f hI, tn_pull_hyp h q N f hI hl]

theorem tn_red_poly (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) (N : ℕ) {A : Type} [CommRing A]
    (hI : Inv q (PR N 0 A)) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    red q r _ _ _ (poly q N 0 A m n i a) = poly r N 0 A m n i (fun j => red q r _ _ _ (a j)) := by
  unfold poly

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_red_cast, (h q r hr _).1, ← pull_red]
  unfold hyp
  rw [tn_red_cpow h q r hr hI]

theorem LeafTauNat_of (hG : LeafGeo) : LeafTauNat := by
  intro h6 h11 q _ d A _ hq τ hτ
  obtain ⟨a, ha⟩ := hτ
  have hI : Inv q (PR (d + 1) 0 A) := hG.2.1 q (d + 1) 0 A hq
  refine ⟨fun B _ φ g hl hs => ⟨fun j => pull _ (spMap φ) _ _ (a j), ?_⟩,
    fun r hr τ' hτ' => ⟨fun j => red q r _ _ _ (a j), ?_⟩⟩
  · have e : Hs.fgt q (pr d B) _ _ (Hs.pull q g _ _ τ) =
        pull (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) _ g.right _ _
          (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ (pull _ (dbl.map g) _ _ τ.1) =
        pull _ g.right _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [← pull_comp, ← pull_comp, inl_map]
    rw [e, ha, map_add (f := _), tn_pull_cpow h6 q (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) g.right hI,
      tn_pull_hyp h6 q (d + 1) g.right hI hl, tn_pull_poly h6 q (d + 1) φ g.right hI hl hs]
  · have e : Hs.fgt r (pr d A) _ _ τ' = red q r (PR (d + 1) 0 A) _ _
        (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ τ'.1 = red q r _ _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [hτ', pull_red]
    rw [e, ha, map_add (f := _), tn_red_poly h11 q r hr (d + 1) hI]
    unfold hyp
    rw [tn_red_cpow h11 q r hr hI]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

theorem vec_map_comp {N k : ℕ} {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (v : Vec N k X) :
    (Vec.map N k (g ≫ f)).obj v = (Vec.map N k g).obj ((Vec.map N k f).obj v) := by
  apply Subtype.ext
  funext i
  change (g ≫ f).appTop.hom (v.1 i) = g.appTop.hom (f.appTop.hom (v.1 i))
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sch_map_pt {N k : ℕ} {Y X : Scheme.{0}} (f : Y ⟶ X) (v : Vec N k X) :
    sch.map f ≫ Pj.pt v = Pj.pt ((Vec.map N k f).obj v) := by
  ext n U g
  change (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k (g ≫ f)).obj v) =
    (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k g).obj ((Vec.map N k f).obj v))
  exact congrArg (Functor.const (Fin (n.unop.len + 1))).obj (vec_map_comp (show U.unop ⟶ Y from g) f v)

theorem part3 (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x)) := by
  change sch.map _ ≫ _ = _
  rw [sch_map_pt]
  congr 1
  apply Subtype.ext
  funext i
  change (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Fin.cons 1 (φ ∘ x) : Fin (d + 1) → B) i)
  have key := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun g => g.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) key
  refine this.symm.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ ((Fin.cons 1 x : Fin (d + 1) → A) i)) = _
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem part2 (q N k : ℕ) (R : Type) [CommRing R] (hq : IsUnit (q : R)) : Inv q (PR N k R) := by
  intro U ⟨y⟩
  let f : U ⟶ Spec (CommRingCat.of R) := ((prod.snd : PR N k R ⟶ sp R).app _).app (op U) y
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map f.appTop.hom
  rwa [map_natCast, map_natCast] at h

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {a b c : Vec N k U} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = g.1 * f.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {a b : Vec N k U} (e : a = b) : (eqToHom e).1 = 1 := by
  subst e; rfl

theorem incl_map_val {N : ℕ} {U : Scheme.{0}} {a b : Vec N 1 U} (u : a ⟶ b) : ((Vec.incl N U).map u).1 = u.1 := rfl

theorem incl_cancel {N : ℕ} {U : Scheme.{0}} {J : Type} [Category J] (F G : J ⥤ Vec N 1 U)
    (h : F ⋙ Vec.incl N U = G ⋙ Vec.incl N U) : F = G := by
  have hobj : ∀ j, F.obj j = G.obj j := fun j => Subtype.ext (by have := congrArg Subtype.val (Functor.congr_obj h j); exact this)
  refine CategoryTheory.Functor.ext hobj (fun a b f => ?_)
  apply Subtype.ext
  have h2 := congrArg Subtype.val (Functor.congr_hom h f)
  simp only [Functor.comp_map, comp_val, eqToHom_val, incl_map_val, mul_one, one_mul] at h2 ⊢
  exact h2

theorem incl_mono (N : ℕ) : Mono (Pj.incl N) := by
  have : ∀ n, Mono ((Pj.incl N).app n) := fun n => by
    have : ∀ U, Mono (((Pj.incl N).app n).app U) := fun U => by
      rw [mono_iff_injective]
      intro F G h
      exact incl_cancel (U := U.unop) F G h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem part1 (d : ℕ) (R : Type) [CommRing R] : Mono (pr d R).hom := by
  have := incl_mono (d + 1)
  change Mono (prod.map _ _)
  infer_instance

theorem pt_incl {N : ℕ} {X : Scheme.{0}} (v : Vec N 1 X) :
    Pj.pt v ≫ Pj.incl N = Pj.pt ((Vec.incl N X).obj v) := rfl

theorem part4 (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A) (hI : Ideal.span (Set.range x) = I) :
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x := by
  let w : Vec (d + 1) 1 (off A I).toScheme := ⟨((Vec.map (d + 1) 0 (off A I).ι).obj (vec1 x)).1, fun p => by
    have hp : ¬ (Ideal.span (Set.range x) ≤ ((off A I).ι p).asIdeal) := by rw [hI]; exact p.2
    rw [Ideal.span_le] at hp
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ ((off A I).ι p).asIdeal := by
      by_contra hc
      push Not at hc
      exact hp (by rintro _ ⟨j, rfl⟩; exact hc j)
    refine ⟨j.succ, by simp, ?_⟩
    change p ∈ (off A I).toScheme.basicOpen ((off A I).ι.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) j.succ)))
    rw [← Scheme.preimage_basicOpen_top]
    change (off A I).ι p ∈ (Spec (CommRingCat.of A)).basicOpen _
    rw [basicOpen_eq_of_affine]
    simp only [Fin.cons_succ]
    exact hj⟩
  refine ⟨Arrow.homMk (prod.lift (Pj.pt w) (sch.map (off A I).ι)) (chart x) ?_, rfl⟩
  apply prod.hom_ext
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.fst =
      sch.map (off A I).ι ≫ chart x ≫ prod.fst
    rw [prod.map_fst, prod.lift_fst_assoc, chart, prod.lift_fst, pt_incl, sch_map_pt]
    rfl
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.snd =
      sch.map (off A I).ι ≫ chart x ≫ prod.snd
    rw [prod.map_snd, prod.lift_snd_assoc, chart, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom.GeoPf

namespace LateralTheory.CohomologicalPurity.Thom

theorem LeafGeo_of : LeafGeo :=
  ⟨GeoPf.part1, GeoPf.part2, GeoPf.part3, GeoPf.part4⟩

end LateralTheory.CohomologicalPurity.Thom

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

end LateralTheory.CohomologicalPurity.Thom.GeoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafHtpyZero : Prop := A1 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A]
  (h : off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A ⊥) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyOne : Prop := A1 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (x : A), IsUnit (q : A) →
  ∀ (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyMV : Prop := A4 → ∀ (R : Type) [CommRing R] (F : Shv R) {X' X : Scheme.{0}} (p : X' ⟶ X)
  (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ p ⁻¹ᵁ U) (hV : V' ≤ p ⁻¹ᵁ V) (hI : U' ⊓ V' ≤ p ⁻¹ᵁ (U ⊓ V))
  (hS : U' ⊔ V' ≤ p ⁻¹ᵁ (U ⊔ V)),
  Eqv R (sch.map (p.resLE U U' hU)) F → Eqv R (sch.map (p.resLE V V' hV)) F →
  Eqv R (sch.map (p.resLE (U ⊓ V) (U' ⊓ V') hI)) F → Eqv R (sch.map (p.resLE (U ⊔ V) (U' ⊔ V') hS)) F

namespace HtpyPf

theorem offle (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp hz
  apply hp
  change ((I.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  change (I : Set A) ⊆ (PrimeSpectrum.comap Polynomial.C p).asIdeal at hz
  exact SetLike.coe_subset_coe.2 (Ideal.map_le_iff_le_comap.2 hz)

theorem eqv_congr {X' X : Scheme.{0}} (p : X' ⟶ X) {R : Type} [CommRing R] (F : Shv R) {U U₁ : X.Opens}
    {U' U₁' : X'.Opens} (e : U = U₁) (e' : U' = U₁') (h : U' ≤ p ⁻¹ᵁ U) (h₁ : U₁' ≤ p ⁻¹ᵁ U₁) :
    Eqv R (sch.map (p.resLE U U' h)) F ↔ Eqv R (sch.map (p.resLE U₁ U₁' h₁)) F := by
  subst e e'; rfl

theorem off_sup (A : Type) [CommRing A] (I J : Ideal A) : off A (I ⊔ J) = off A I ⊔ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_sup, Set.compl_inter]

theorem off_mul (A : Type) [CommRing A] (I J : Ideal A) : off A (I * J) = off A I ⊓ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I * J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∩ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_mul, Set.compl_union]

end HtpyPf

namespace HtpyPf

theorem span_cons {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {a | a ∈ x :: t} = Ideal.span {x} ⊔ Ideal.span {a | a ∈ t} := by
  rw [← Ideal.span_insert]; congr 1; ext a; simp

theorem span_mul {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {x} * Ideal.span {a | a ∈ t} = Ideal.span {a | a ∈ t.map (x * ·)} := by
  rw [Ideal.span_mul_span']; congr 1; ext a; simp [Set.singleton_mul]

theorem main (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) (a1 : A1) (a4 : A4) (c4 : C4)
    (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hq : IsUnit (q : A)) (i : ℤ) :
    ∀ (n : ℕ) (s : List A), s.length = n →
    ∀ h : off (Polynomial A) ((Ideal.span {a | a ∈ s}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {a | a ∈ s}),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i) := by
  intro n
  induction n with
  | zero =>
    intro s hs h
    obtain rfl : s = [] := List.length_eq_zero_iff.1 hs
    have e : Ideal.span {a | a ∈ ([] : List A)} = ⊥ := by simp
    have e1 : off A (Ideal.span {a | a ∈ ([] : List A)}) = off A ⊥ := by rw [e]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ ([] : List A)}).map Polynomial.C) =
        off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) := by rw [e]
    exact (eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i) e1 e2 h
      (offle A ⊥)).2 (hZ a1 q A (offle A ⊥) i)
  | succ n ih =>
    intro s hs h
    obtain ⟨x, t, rfl⟩ : ∃ x t, s = x :: t := by
      cases s with
      | nil => simp at hs
      | cons x t => exact ⟨x, t, rfl⟩
    have ht : t.length = n := by simpa using hs
    set I := Ideal.span ({x} : Set A)
    set J := Ideal.span {a | a ∈ t}
    set P := Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))
    have hU := offle A I
    have hV := offle A J
    have hI : off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊓ off A J) := fun p hp => ⟨hU hp.1, hV hp.2⟩
    have hS : off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊔ off A J) := by
      rw [← off_sup, ← off_sup, ← Ideal.map_sup]; exact offle A (I ⊔ J)
    have e1 : off A (Ideal.span {a | a ∈ x :: t}) = off A I ⊔ off A J := by rw [span_cons, off_sup]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ x :: t}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) := by
      rw [span_cons, Ideal.map_sup, off_sup]
    refine (eqv_congr P (tw q i) e1 e2 h hS).2 (hMV a4 _ _ P _ _ _ _ hU hV hI hS (hO a1 c4 q A x hq hU i) (ih t ht hV) ?_)
    have e3 : off A (Ideal.span {a | a ∈ t.map (x * ·)}) = off A I ⊓ off A J := by rw [← span_mul, off_mul]
    have e4 : off (Polynomial A) ((Ideal.span {a | a ∈ t.map (x * ·)}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) := by
      rw [← span_mul, Ideal.map_mul, off_mul]
    exact (eqv_congr P (tw q i) e3 e4 (offle A _) hI).1 (ih _ (by simpa using ht) _)

end HtpyPf

theorem LeafHtpy_of (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) : LeafHtpy := by
  intro a1 a4 c4 q _ A _ I hI hq h i
  obtain ⟨S, rfl⟩ := hI
  have e : ({a | a ∈ S.toList} : Set A) = (S : Set A) := by ext a; simp
  have := HtpyPf.main hZ hO hMV a1 a4 c4 q A hq i _ S.toList rfl (by rw [e]; exact HtpyPf.offle A _)
  exact (HtpyPf.eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i)
    (by rw [e]) (by rw [e]) _ h).1 this

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

abbrev ZN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := Zc K (W.ι ⁻¹ᵁ U) n

def BN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := AddSubgroup.closure {a | Bd K (W.ι ⁻¹ᵁ U) n a}

abbrev OK {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)) : Prop :=
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) ∧
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) ∧
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a)

def LeafBdAdd : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), a ∈ BN K U n W → Bd K (W.ι ⁻¹ᵁ U) n a

def LeafBZ : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), Bd K (W.ι ⁻¹ᵁ U) n a → a ∈ ZN K U n W

def LeafZloc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ ZN K U n W, rs h a ∈ ZN K U n V) ∧
  (∀ (W : X.Opens) (a : Sec (K.X n) W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ ZN K U n V) →
    a ∈ ZN K U n W)

def LeafZero : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  IsZero (K.X n) → OK (ZN K U n)

def LeafStep : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), LateralTheory.CohomologicalPurity.Cl.LeafZorn → (∀ s, Injective (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (n : ℤ), OK (ZN K U (n - 1)) → OK (BN K U n)

def LeafTop : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ)
  (c' : Sec (K.X n) (⊤ : X.Opens).toScheme), c' ∈ ZN K U n ⊤ →
  ∃ c ∈ Zc K U n, ∀ V : X.Opens, Sec.res V.ι c = rs le_top c'

def LeafRs : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (T V W : X.Opens) (h : V ≤ W) (h' : T ≤ V)
  (a b : Sec G W.toScheme), rs h (a - b) = rs h a - rs h b ∧ rs h' (rs h a) = rs (h'.trans h) a

theorem LeafRs_of : LeafRs := by
  intro R _ G X T V W h h' a b
  refine ⟨?_, ?_⟩
  · show ((G.obj.map (X.homOfLE h).op).hom (a - b)) = _
    exact map_sub _ a b
  · show ((G.obj.map (X.homOfLE h').op).hom ((G.obj.map (X.homOfLE h).op).hom a)) = (G.obj.map (X.homOfLE (h'.trans h)).op).hom a
    have e : X.homOfLE (h'.trans h) = X.homOfLE h' ≫ X.homOfLE h := (Scheme.homOfLE_homOfLE X h' h).symm
    rw [e, op_comp, Functor.map_comp]
    rfl

theorem LeafFlq_of (hZ : LateralTheory.CohomologicalPurity.Cl.LeafZorn) (hA : LeafBdAdd) (hBZ : LeafBZ) (hL : LeafZloc) (h0 : LeafZero)
    (hS : LeafStep) (hT : LeafTop) : LateralTheory.CohomologicalPurity.Cl.LeafFlq := by
  intro R _ K hinj hneg X U m H
  have hR := LeafRs_of
  have key : ∀ n, n < m → OK (ZN K U (n - 1)) → OK (ZN K U n) := by
    intro n hn hprev
    have hB := hS R K hZ hinj X U n hprev
    have eq : ZN K U n = BN K U n := by
      funext W; ext a; constructor
      · intro ha; apply hB.2.1 W a; intro x hx
        obtain ⟨V, h, hxV, hb⟩ := H n hn W a ha x hx
        exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
      · intro ha; exact hBZ R K X U n W a (hA R K X U n W a ha)
    rw [eq]; exact hB
  have P : ∀ k : ℕ, (k : ℤ) < m → OK (ZN K U (k : ℤ)) := by
    intro k
    induction k with
    | zero => intro h; exact key _ h (h0 R K X U _ (hneg _ (by norm_num)))
    | succ k ih =>
      intro h
      apply key _ h
      have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [e]; exact ih (by omega)
  have hm : OK (ZN K U (m - 1)) := by
    by_cases hc : m - 1 < 0
    · exact h0 R K X U _ (hneg _ hc)
    · have e : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have := P (m - 1).toNat (by omega)
      rw [e] at this; exact this
  have hBm := hS R K hZ hinj X U m hm
  refine ⟨fun W a hloc => hA R K X U m W a (hBm.2.1 W a fun x hx => ?_), ?_⟩
  · obtain ⟨V, h, hxV, hb⟩ := hloc x hx
    exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
  intro A V a ha hcov hagree
  obtain ⟨c', hc'⟩ := hZ R (K.X m) X (BN K U m) hBm.1 hBm.2.1 hBm.2.2 ⊤ A V (fun _ => le_top) a
    (fun x _ => hcov x) (by
      intro k l
      apply hBm.2.1
      intro x hx
      obtain ⟨hxk, hxl⟩ := hx
      obtain ⟨T, hk, hl, hxT, hb⟩ := hagree k l x hxk hxl
      refine ⟨T, le_inf hk hl, hxT, ?_⟩
      have e : rs (le_inf hk hl) (rs (inf_le_left : V k ⊓ V l ≤ V k) (a k) - rs (inf_le_right : V k ⊓ V l ≤ V l) (a l))
          = rs hk (a k) - rs hl (a l) := by
        have rsub : ∀ {V W : X.Opens} (h : V ≤ W) (x y : Sec (K.X m) W.toScheme), rs h (x - y) = rs h x - rs h y :=
          fun {V W} h x y => (hR R _ X V V W h le_rfl x y).1
        have rrs : ∀ {T V W : X.Opens} (h : V ≤ W) (h' : T ≤ V) (x : Sec (K.X m) W.toScheme),
            rs h' (rs h x) = rs (h'.trans h) x := fun {T V W} h h' x => (hR R _ X T V W h h' x x).2
        rw [rsub, rrs, rrs]
      rw [e]; exact AddSubgroup.subset_closure hb)
  have hmem : c' ∈ ZN K U m ⊤ := by
    apply (hL R K X U m).2 ⊤ c'
    intro x _
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨V k, le_top, hk, ?_⟩
    have h1 := hBZ R K X U m (V k) _ (hA R K X U m (V k) _ (hc' k))
    have h2 : a k ∈ ZN K U m (V k) := ha k
    simpa using add_mem h1 h2
  obtain ⟨c, hc, hcV⟩ := hT R K X U m c' hmem
  refine ⟨c, hc, fun k => ?_⟩
  rw [hcV]; exact hA R K X U m (V k) _ (hc' k)

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
