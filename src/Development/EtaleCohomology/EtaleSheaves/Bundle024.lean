module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle017
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2
namespace RingPf

variable {q : ℕ} {E : Spc}

theorem cast_heq {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) : HEq (x.cast hn hi) x := by
  subst hn hi; rfl

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem cast_zero {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn hi; rfl

theorem cast_add {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn hi; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (a.cast h1 h2) b = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (b.cast h1 h2) = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn hi; rfl

abbrev A (q : ℕ) (E : Spc) (k : ℕ) : Type 1 := Ht q E (2 * (k : ℤ)) (k : ℤ)

def gmul {k l : ℕ} (a : A q E k) (b : A q E l) : A q E (k + l) :=
  (cup q a b).cast (by push_cast; ring) (by push_cast; ring)

def gone (q : ℕ) (E : Spc) : A q E 0 := (one q E).cast (by simp) (by simp)

instance : GradedMonoid.GOne (A q E) := ⟨gone q E⟩

theorem negOnePow_even (i j : ℕ) : (2 * (i : ℤ) * (2 * (j : ℤ))).negOnePow = 1 :=
  Int.negOnePow_even _ ⟨2 * i * j, by ring⟩

section
variable (hr : DivisorRingCompatibility) [NeZero q]
include hr

theorem one_cup (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q (one q E) a = a.cast (by ring) (by ring) :=
  (hr q E).1 h a

theorem cup_one (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q a (one q E) = a.cast (by ring) (by ring) := by
  rw [(hr q E).2.2 a (one q E), (hr q E).1 h, cast_cast]
  simp

theorem gmul_assoc {i j k : ℕ} (a : A q E i) (b : A q E j) (c : A q E k) :
    HEq (gmul (gmul a b) c) (gmul a (gmul b c)) := by
  simp only [gmul, cup_cast_left, cup_cast_right, cast_cast]
  rw [(hr q E).2.1 a b c, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

theorem gmul_comm {i j : ℕ} (a : A q E i) (b : A q E j) : HEq (gmul a b) (gmul b a) := by
  simp only [gmul]
  rw [(hr q E).2.2 a b, negOnePow_even, one_smul, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

def gcr (h : Inv q E) : DirectSum.GCommRing (A q E) :=
  letI : GradedMonoid.GMul (A q E) := ⟨gmul⟩
  {
    mul a b := gmul a b
    one := gone q E
    one_mul := by
      rintro ⟨k, a⟩
      refine Sigma.ext (zero_add k) ?_
      show HEq (gmul (gone q E) a) a
      simp only [gmul, gone, cup_cast_left]
      rw [one_cup hr h]
      simp only [cast_cast]
      exact cast_heq _ _ _
    mul_one := by
      rintro ⟨k, a⟩
      refine Sigma.ext (add_zero k) ?_
      show HEq (gmul a (gone q E)) a
      simp only [gmul, gone, cup_cast_right]
      rw [cup_one hr h]
      simp only [cast_cast]
      exact cast_heq _ _ _
    mul_assoc := by
      rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
      exact Sigma.ext (add_assoc i j k) (gmul_assoc hr a b c)
    mul_comm := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      exact Sigma.ext (add_comm i j) (gmul_comm hr a b)
    mul_zero a := by simp only [gmul, map_zero, cast_zero]
    zero_mul b := by simp only [gmul, map_zero, AddMonoidHom.zero_apply, cast_zero]
    mul_add a b c := by simp only [gmul, map_add (f := _), cast_add]
    add_mul a b c := by simp only [gmul, map_add (f := _), AddMonoidHom.add_apply, cast_add]
    natCast n := n • gone q E
    natCast_zero := zero_smul _ _
    natCast_succ n := succ_nsmul _ _
    intCast n := n • gone q E
    intCast_ofNat n := natCast_zsmul _ _
    intCast_negSucc_ofNat n := by
      show Int.negSucc n • gone q E = -((n + 1 : ℕ) • gone q E)
      rw [negSucc_zsmul]
  }
end

section
variable (hn : DivisorNaturality) (hr : DivisorRingCompatibility) [NeZero q]

abbrev ringOf (hr : DivisorRingCompatibility) (E : Spc) (h : Inv q E) : CommRing (DirectSum ℕ (A q E)) :=
  letI := gcr hr h; DirectSum.commRing (A q E)

def projOf (E : Spc) (k : ℕ) : DirectSum ℕ (A q E) →+ A q E k where
  toFun r := r k
  map_zero' := rfl
  map_add' x y := DirectSum.add_apply x y k


include hn in
def mapOf {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') :
    letI := ringOf hr E h; letI := ringOf hr E' h'; DirectSum ℕ (A q E') →+* DirectSum ℕ (A q E) :=
  letI := gcr hr h; letI := gcr hr h'
  DirectSum.toSemiring (fun k => (DirectSum.of (A q E) k).comp (pull (ZMod q) f (tw q k) (2 * (k : ℤ))))
    (by
      show DirectSum.of (A q E) 0 (pull (ZMod q) f (tw q ((0 : ℕ) : ℤ)) (2 * ((0 : ℕ) : ℤ)) (gone q E')) = 1
      rw [gone, pull_cast, (hn q).2.1 f h']
      rfl)
    (by
      intro i j a b
      simp only [AddMonoidHom.comp_apply]
      rw [DirectSum.of_mul_of]
      congr 1
      show pull (ZMod q) f _ _ (gmul a b) = gmul _ _
      simp only [gmul, pull_cast, (hn q).1 f])

include hn in
theorem mapOf_of {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : A q E' k) :
    mapOf hn hr f h h' (DirectSum.of (A q E') k a) = DirectSum.of (A q E) k (pull (ZMod q) f (tw q k) (2 * (k : ℤ)) a) := by
  letI := gcr hr h; letI := gcr hr h'
  exact DirectSum.toSemiring_of _ _ _ k a

end

end RingPf

open RingPf in
theorem etale_even_cohomology_graded_commRing_of_cup_ring_axioms (hn : DivisorNaturality) (hr : DivisorRingCompatibility) : LeafRing := by
  intro q _
  exact ⟨{
    R := fun E _ => DirectSum ℕ (A q E)
    ring := fun E h => ringOf hr E h
    ι := fun {E} _ k => DirectSum.of (A q E) k
    π := fun {E} _ k => projOf E k
    map := fun f h h' => mapOf hn hr f h h'
    π_ι := fun {E} _ k a => by
      show (DirectSum.of (A q E) k a) k = a
      exact DirectSum.of_eq_same (β := A q E) k a
    ι_one := fun {E} _ => rfl
    ι_mul := fun {E} h k l a b => by
      letI := gcr hr h
      exact (DirectSum.of_mul_of (A := A q E) a b).symm
    ι_cpow := fun {E} h k x => by
      letI := gcr hr h
      induction k with
      | zero => rw [pow_zero, cpow_zero]; rfl
      | succ k ih =>
        rw [pow_succ, ← ih, cpow_succ]
        show _ = DirectSum.of (A q E) k _ * DirectSum.of (A q E) 1 _
        rw [DirectSum.of_mul_of]
        congr 1
    map_ι := fun {E E'} f h h' k a => by
      exact mapOf_of hn hr f h h' k a
    π_map := fun {E E'} f h h' k r => by
      letI := gcr hr h; letI := gcr hr h'
      induction r using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of j a =>
        show projOf E k (mapOf hn hr f h h' (DirectSum.of (A q E') j a)) = _
        rw [mapOf_of]
        show (DirectSum.of (A q E) j (pull (ZMod q) f _ _ a)) k = pull (ZMod q) f _ _ ((DirectSum.of (A q E') j a) k)
        by_cases hjk : j = k
        · subst hjk; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy] }⟩

theorem LeafRing_of (hn : LeafA6nat) (hr : LeafA6ring) : LeafRing := etale_even_cohomology_graded_commRing_of_cup_ring_axioms hn hr

end LateralTheory.E.D2
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafLinePf

theorem det_mulVec_one (A : Type) [CommRing A] (g : GL (Fin 1) A) :
    (g : Matrix (Fin 1) (Fin 1) A).mulVec (fun _ => 1) = ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) • (fun _ => (1 : A)) := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, Matrix.det_unique]

def e1 (A : Type) [CommRing A] : Um 1 A := ⟨fun _ => 1, by
  rw [Set.range_const]; exact Ideal.span_singleton_one⟩

def secF (A : Type) [CommRing A] : SingleObj (GL (Fin 1) A) ⥤ Um 1 A where
  obj _ := e1 A
  map g := ⟨(g, Matrix.GeneralLinearGroup.det g), det_mulVec_one A g⟩
  map_id _ := Subtype.ext (Prod.ext rfl (map_one _))
  map_comp f g := Subtype.ext (Prod.ext rfl (map_mul _ _ _))

theorem eqToHom_val {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1 = 1 := by
  cases h; rfl

theorem comp_val {A : Type} [CommRing A] {u v w : Um 1 A} (a : u ⟶ v) (b : v ⟶ w) : (a ≫ b).1 = b.1 * a.1 := rfl

theorem det_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 1) A) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) : Bˣ) : B) = f ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.map_det]
  rfl

def secNat : glCat 1 ⟶ pglCat 1 where
  app A := (secF A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext (funext fun _ => (map_one f.hom).symm)) (fun _ _ g => ?_)
    apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
    refine Prod.ext rfl ?_
    ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom (show GL (Fin 1) A from g)) : (B : Type)ˣ) : (B : Type)) =
      f.hom ((Matrix.GeneralLinearGroup.det (show GL (Fin 1) A from g) : (A : Type)ˣ) : (A : Type))
    exact det_map f.hom _

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap α ≫ ofCatMap β = ofCatMap (α ≫ β) := rfl

theorem ofCatMap_id (C : CommRingCat.{0} ⥤ Cat.{0,0}) : ofCatMap (𝟙 C) = 𝟙 _ := rfl

def sec : ofCat (glCat 1) ⟶ PGL 1 := ofCatMap secNat

theorem sec_pr : sec ≫ PGL.pr 1 = 𝟙 (ofCat (glCat 1)) := rfl

theorem single_eqToHom {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : M) := by
  cases h; rfl

theorem sec_line : sec ≫ PGL.line 1 = 𝟙 (ofCat (glCat 1)) := by
  rw [sec, PGL.line]
  erw [ofCatMap_comp]
  rw [← ofCatMap_id]
  congr 1
  apply NatTrans.ext
  funext A
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => ?_)
  erw [single_eqToHom]
  change _ = ((1 : GL (Fin 1) A) * (id g : GL (Fin 1) A)) * 1
  rw [one_mul, mul_one]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det (id g : GL (Fin 1) A)) = (id g : GL (Fin 1) A)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

end LateralTheory.E.LeafLinePf

namespace LateralTheory.E.D2
open LateralTheory.E.LeafLinePf

theorem LeafLine_of (hA : LeafA6nat) : LeafLine := by
  intro q _ P E h L c hc
  obtain ⟨h0, -, heq⟩ := hc
  have hw : 𝟙 E ≫ L = (L ≫ sec) ≫ PGL.pr 1 := by
    rw [Category.assoc, sec_pr, Category.id_comp, Category.comp_id]
  let σ : E ⟶ PB L := pullback.lift (𝟙 E) (L ≫ sec) hw
  have hpr : σ ≫ PB.pr L = 𝟙 E := pullback.lift_fst _ _ _
  have hline : σ ≫ PB.line L = L := by
    rw [PB.line, ← Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.assoc, sec_line, Category.comp_id]
  have h' : Inv q (PB L) := inv_of (PB.pr L) h
  have hm : ∀ j, P.map σ h h' (P.map (PB.pr L) h' h (P.ι h j (c j))) = P.ι h j (c j) := by
    intro j
    rw [P.map_ι, P.map_ι, ← pull_comp, hpr, pull_id]
  have hx : P.map σ h h' (P.deg1 h' (c1 q (PB.line L))) = P.deg1 h (c1 q L) := by
    rw [Collected.deg1, P.map_ι, pull_cast, (hA q).2.2.1 σ (PB.line L) h', hline]
  have := congrArg (P.map σ h h') heq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add (f := _), map_mul, map_pow, map_zero, zero_add, hm, hx,
    map_one, h0] at this
  simp only [one_mul, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one] at this
  linear_combination this

end LateralTheory.E.D2
end
end

section

noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

theorem local_of_finite (A S : Type) [CommRing A] [HenselianLocalRing A] [CommRing S] [Algebra A S]
    [Module.Finite A S] [Nontrivial S] (hid : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q
  rcases hid e he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · exact (H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))

theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem isLocal (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  haveI := sub_local A B hid {x}
  let y : Algebra.adjoin A ((({x} : Finset B)) : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin A _).val)
  · exact Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)

theorem maxIdeal_comap (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) :
    letI := isLocal A B hid
    letI := sub_local A B hid s
    (maximalIdeal B).comap (Algebra.adjoin A (s : Set B)).val = maximalIdeal (Algebra.adjoin A (s : Set B)) := by
  letI := isLocal A B hid
  letI := sub_local A B hid s
  haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A
  have : ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (fun x => Algebra.IsIntegral.isIntegral x) (maximalIdeal B)
  exact IsLocalRing.eq_maximalIdeal this

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : HenselianLocalRing B := by
  classical
  letI := isLocal A B hid
  refine ⟨fun f hf a0 h0 h1 => ?_⟩
  set s : Finset B := insert a0 f.coeffs
  let S := Algebra.adjoin A (s : Set B)
  letI := sub_local A B hid s
  haveI := sub_finite A B s
  haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc =>
    Algebra.subset_adjoin (by simp [s, hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, Algebra.subset_adjoin (by simp [s])⟩
  have hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B := fun y => by
    rw [← maxIdeal_comap A B hid s]; rfl
  have he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := fun p y => by
    rw [eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]; rfl
  have he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0 := fun p => he' p b0
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b0
    ((hmem _).2 (by rw [he, hgf]; exact h0))
    (by
      rw [← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]
      exact IsLocalRing.notMem_maximalIdeal.2 h1)
  refine ⟨a, ?_, (hmem _).1 ha'⟩
  rw [IsRoot.def, ← hgf, ← he', ha.eq_zero]; rfl

theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

namespace LateralTheory.E.DomCoverPf

theorem aicFrac (R L : Type) [CommRing R] [CommRing L] (φ : R →+* L) (hR : AIC R)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) : AIC L :=
  _root_.UpperTheory.Reformulated.B.Qn19.aicFrac R L φ hR h

def IdemCover : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ t_E3Cut.SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧
    ∀ z : Localization.AtPrime r, ∃ a b : C, IsUnit (algebraMap D (Localization.AtPrime r) (g.hom b)) ∧
      z * algebraMap D (Localization.AtPrime r) (g.hom b) = algebraMap D (Localization.AtPrime r) (g.hom a)

theorem DomCover_of (h2 : IdemCover) : t_E3Cut.DomCover := by
  intro C hC
  obtain ⟨D, g, hi, hs, hr⟩ := h2 C
  refine ⟨D, g, hi, hs, fun r _ => ⟨(hr r).1, ?_⟩⟩
  exact aicFrac C (Localization.AtPrime r) ((algebraMap D (Localization.AtPrime r)).comp g.hom) hC (hr r).2

end LateralTheory.E.DomCoverPf
end
end
