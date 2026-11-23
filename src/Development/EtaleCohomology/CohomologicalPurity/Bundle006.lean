module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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

namespace LateralTheory.CohomologicalPurity.Bd

section Defs
variable {R : Type} [CommRing R] {A B D : Cx R}

abbrev pb (f : A ⟶ B) {I : Cx R} {n : ℤ} (c : Cochain B I n) : Cochain A I n := (Cochain.ofHom f).comp c (zero_add n)

abbrev hpb (f : A ⟶ B) (I : Cx R) (n : ℤ) : CohomologyClass B I n →+ CohomologyClass A I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

structure Good (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) : Prop where
  w : i ≫ l = i ≫ r
  surj : ∀ (n : ℤ) (a : Cochain A I n), ∃ c : Cochain B I n, pb i c = a
  glue : ∀ (n : ℤ) (c c' : Cochain B I n), pb i c = pb i c' → ∃ b : Cochain D I n, pb l b = c ∧ pb r b = c'
  ext : ∀ (n : ℤ) (b b' : Cochain D I n), pb l b = pb l b' → pb r b = pb r b' → b = b'

def Tri (i : A ⟶ B) (l r : B ⟶ D) {I : Cx R} {n : ℤ} (a : Cocycle A I n) (c : Cochain B I n)
    (b : Cocycle D I (n + 1)) : Prop :=
  pb i c = a.1 ∧ pb l b.1 = δ n (n + 1) c ∧ pb r b.1 = 0

def IsDelta (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) (n : ℤ) (d : CohomologyClass A I n →+ (hpb r I (n + 1)).ker) : Prop :=
  ∀ (a : Cocycle A I n) (c : Cochain B I n) (b : Cocycle D I (n + 1)), Tri i l r a c b →
    (d (CohomologyClass.mk a)).1 = CohomologyClass.mk b

theorem Good.tri {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R} (h : Good i l r I) {n : ℤ} (a : Cocycle A I n) :
    ∃ c b, Tri i l r a c b := by
  obtain ⟨c, hc⟩ := h.surj n a.1
  obtain ⟨b, hl, hr⟩ := h.glue (n + 1) (δ n (n + 1) c) 0 (by
    rw [pb, ← δ_ofHom_comp]
    change δ n (n + 1) (pb i c) = _
    rw [hc]; simp [pb])
  refine ⟨c, Cocycle.mk b (n + 1 + 1) rfl (h.ext _ _ _ ?_ ?_), hc, hl, hr⟩
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb l b) = _
    rw [hl, δ_δ]; simp [pb]
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb r b) = _
    rw [hr]; simp [pb]

theorem pb_pb (f : A ⟶ B) (g : B ⟶ D) {I : Cx R} {n : ℤ} (c : Cochain D I n) : pb f (pb g c) = pb (f ≫ g) c := by
  simp [pb, Cochain.ofHom_comp]

end Defs

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ p : ℤ, Mono (((chains R).map f).f p)

def LeafPush : Prop := ∀ (R : Type) [CommRing R] {U E E' D : Spc} (f : U ⟶ E) (g : U ⟶ E') (l : E ⟶ D) (r : E' ⟶ D),
  IsPushout f g l r → ∀ p : ℤ, IsPushout (((chains R).map f).f p) (((chains R).map g).f p) (((chains R).map l).f p)
    (((chains R).map r).f p)

def LeafGood : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  (∀ p, Mono (i.f p)) → (∀ p, IsPushout (i.f p) (i.f p) (l.f p) (r.f p)) → (∀ p, Injective (I.X p)) → Good i l r I

def LeafDelta : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ n : ℤ, ∃ d, IsDelta i l r I n d

def LeafExact : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ (n : ℤ) d, IsDelta i l r I n d →
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) ∧ Function.Exact (hpb i I n) d ∧
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype)

def LeafGen : Prop := ∀ (R : Type) [CommRing R] (P : PSh),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧
  (∀ (P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)),
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x)) ∧
  (∀ (G : Shv R) (φ ψ : (free R).obj P ⟶ G),
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧
  ∀ (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) →
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x

def LeafImgHom : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s),
    (∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s) (U : Scheme.{0}) (x : P.obj (op U)),
      Sec.map (T P s φ) (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x))) ∧
    (∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T P t (φ ≫ I.d s t) = T P s φ ≫ J.d s t) ∧
    ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T P s ((free S).map f ≫ φ) = (free R).map f ≫ T P' s φ

def LeafImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (E : Spc) (n : ℤ), Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n,
    (∀ (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
      (x : Sx E p U), ev (R := R) (T E n α) p s h U x = ρ.app U s (ev (R := S) α p s h U x)) ∧
    (∀ (E : Spc) (n m : ℤ) (α : Cochain ((chains S).obj E) I n), T E m (δ n m α) = δ n m (T E n α)) ∧
    ∀ (E E' : Spc) (f : E ⟶ E') (n : ℤ) (α : Cochain ((chains S).obj E') I n),
      T E n (pb ((chains S).map f) α) = pb ((chains R).map f) (T E' n α)

theorem good (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (R : Type) [CommRing R] (F : Shv R) (P : Arrow Spc)
    (hP : Mono P.hom) : Good ((chains R).map P.hom) ((chains R).map (dbl.inl P)) ((chains R).map (dbl.inr P)) (res R F) :=
  h3 R _ _ _ _ (h1 R _ hP) (h2 R _ _ _ _ (IsPushout.of_hasPushout P.hom P.hom)) fun p => by
    unfold res; infer_instance

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem goal_of (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (h4 : LeafDelta) (h5 : LeafExact) (h6 : LeafImg) :
    LeafBd := by
  have G := fun (q : ℕ) (i : ℤ) => good h1 h2 h3 (ZMod q) (tw q i)
  have ex : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), ∃ d : Ht q P.left n i →+ Hs q P (n + 1) i, Mono P.hom →
      IsDelta ((chains _).map P.hom) ((chains _).map (dbl.inl P)) ((chains _).map (dbl.inr P)) (res _ (tw q i)) n d := by
    intro q P n i
    by_cases hP : Mono P.hom
    · obtain ⟨d, hd⟩ := h4 _ _ _ _ _ (G q i P hP) n
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose d hd using ex
  refine ⟨d, fun q P hP n i => h5 _ _ _ _ _ (G q i P hP) n _ (hd q P n i hP), ?_, ?_⟩
  · intro q P' P φ hP' hP n i u
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G q i P hP).tri a
    have e := hd q P n i hP a c b ht
    have e' := hd q P' n i hP' (zcomp (Cocycle.ofHom ((chains _).map φ.left)) a (zero_add n))
      (pb ((chains _).map φ.right) c) (zcomp (Cocycle.ofHom ((chains _).map (dbl.map φ))) b (zero_add _)) (by
        obtain ⟨t1, t2, t3⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · change _ = pb _ a.1
          rw [← t1, pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, Arrow.w φ]
        · change pb _ (pb _ b.1) = _
          rw [δ_ofHom_comp, ← t2]
          change _ = pb _ (pb _ b.1)
          rw [pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, inl_map]
        · change pb _ (pb _ b.1) = _
          rw [pb_pb, ← Functor.map_comp, dbl.inr_map, Functor.map_comp, ← pb_pb, t3]
          exact Cochain.comp_zero _ _)
    apply Subtype.ext
    refine Eq.trans ?_ e'.symm
    exact congrArg (pull _ (dbl.map φ) (tw q i) (n + 1)) e
  · intro Q q _ _ P hP n i u
    obtain ⟨T, hv, hδ, hp⟩ := h6 _ _ _ _ (redMap Q q i)
    let Z : ∀ (E : Spc) (m : ℤ), Cocycle ((chains _).obj E) (res _ (tw Q i)) m → Cocycle ((chains _).obj E) (res _ (tw q i)) m :=
      fun E m α => Cocycle.mk (T E m α.1) (m + 1) rfl (by rw [← hδ, α.δ_eq_zero, map_zero])
    have key : (∀ E m x, red Q q E m i x = 0) ∨
        ∀ E m α, red Q q E m i (CohomologyClass.mk α) = CohomologyClass.mk (Z E m α) := by
      unfold red SemiMap.op pick
      split_ifs with h
      · exact Or.inr fun E m α => h.choose_spec E m α (Z E m α) (hv E m α.1)
      · exact Or.inl fun _ _ _ => rfl
    rcases key with k | k
    · rw [k, k, map_zero]; rfl
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G Q i P hP).tri a
    have e := hd Q P n i hP a c b ht
    have e' := hd q P n i hP (Z _ _ a) (T _ _ c) (Z _ _ b) (by
      obtain ⟨t1, t2, t3⟩ := ht
      refine ⟨?_, ?_, ?_⟩
      · change _ = T _ _ a.1
        rw [← hp, t1]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t2, hδ]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t3, map_zero])
    rw [k]
    refine e'.trans ?_
    rw [← k]
    exact congrArg _ e.symm

end LateralTheory.CohomologicalPurity.Bd
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem freeSq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) (p : SimplexCategoryᵒᵖ) :
    (free R).map (P'.hom.app p) ≫ (free R).map (φ.right.app p) =
      (free R).map (φ.left.app p) ≫ (free R).map (P.hom.app p) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, Arrow.w φ]

def LeafExcFormal : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) ((freeSq _ φ p).symm))) → Exc q φ

theorem freeSqSch (R : Type) [CommRing R] {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) :
    (free R).map (yoneda.map U'.ι) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (f.resLE U U' h)) ≫ (free R).map (yoneda.map U.ι) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]

def LeafExcSheaf : Prop := ∀ (R : Type) [CommRing R] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X')
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens),
  (U : Set X) = (Set.range ι)ᶜ → ∀ h : U' = f ⁻¹ᵁ U,
  IsIso (cokernel.map ((free R).map (yoneda.map U'.ι)) ((free R).map (yoneda.map U.ι))
    ((free R).map (yoneda.map (f.resLE U U' h.le))) ((free R).map (yoneda.map f)) ((freeSqSch R f U' U h.le).symm))

theorem LeafExc_of (hF : LeafExcFormal) (hS : LeafExcSheaf) : LeafExc := by
  intro _ q X' X Z f _ ι' ι _ hp U' U hU h
  refine hF q _ fun p => ?_
  exact hS (ZMod q) f ι' ι hp U' U hU h

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafGeo : Prop :=
  (∀ (d : ℕ) (R : Type) [CommRing R], Mono (pr d R).hom) ∧
  (∀ (q N k : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (PR N k R)) ∧
  (∀ (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A),
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x))) ∧
  ∀ (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A), Ideal.span (Set.range x) = I →
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x

def LeafAct : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (M : Matrix (Fin d) (Fin d) A), IsUnit M.det →
  ∃ g : pr d A ⟶ pr d A,
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 ∧
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ∧
    ∀ x : Fin d → A, chart x ≫ (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) = chart (M.mulVec x)

def LeafPB : Prop := A1 → DivisorNaturality → D1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ n i : ℤ, Function.Bijective (poly q N 0 R N n i)

def LeafHtpy : Prop := A1 → A4 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), I.FG → IsUnit (q : A) →
  ∀ (h : off (Polynomial A) (I.map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafTail : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ i : ℤ,
  Eqv _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i)

def LeafTau : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  (∃! τ, IsTau q d R τ) ∧ ∀ τ, IsTau q d R τ → ∀ n i : ℤ, Function.Bijective fun a : Ht q (sp R) n i =>
    Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ a) τ

def LeafTauNat : Prop := DivisorNaturality → A11 → ∀ (q : ℕ) [NeZero q] (d : ℕ) (A : Type) [CommRing A], IsUnit (q : A) →
  ∀ τ, IsTau q d A τ →
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (g : pr d B ⟶ pr d A),
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 →
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ≫ spMap φ → IsTau q d B (Hs.pull q g _ _ τ)) ∧
  ∀ r : ℕ, r ∣ q → ∀ τ' : Hs r (pr d A) (2 * d) d, τ'.1 = red q r _ _ _ τ.1 → IsTau r d A τ'

def LeafExcSp : Prop := A1 → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → Exc q φ

def LeafExcP : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) → ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) → Exc q Φ

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem inl_fold (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _

theorem map_comp {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) : dbl.map (ψ ≫ φ) = dbl.map ψ ≫ dbl.map φ := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [← Category.assoc, inl_map, Category.assoc, inl_fold, ← Category.assoc, inl_fold, Category.comp_id, Category.id_comp]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_fold, ← Category.assoc, dbl.inr_fold, Category.comp_id,
      Category.id_comp]

theorem hs_comp (q : ℕ) {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i (Hs.pull q φ n i x) = Hs.pull q (ψ ≫ φ) n i x :=
  Subtype.ext (by
    change pull _ (dbl.map ψ) _ n (pull _ (dbl.map φ) _ n x.1) = pull _ (dbl.map (ψ ≫ φ)) _ n x.1
    rw [map_comp, pull_comp])

theorem hs_act (h : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (φ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b) :=
  Subtype.ext (by
    have e : cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1) =
        pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1) := by
      rw [(h q).1, ← pull_comp, ← pull_comp, map_fold]
    change pull _ (dbl.map φ) _ _ (_ - _) = cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a))
      (pull _ (dbl.map φ) _ m b.1) - pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1)))
    rw [e, map_sub, ← pull_comp _ (dbl.inr P'), dbl.inr_map, pull_comp, ← pull_comp _ (dbl.fold P'), ← map_fold, pull_comp])

theorem hom_ext {P' P : Arrow Spc} (h : Mono P.hom) {φ ψ : P' ⟶ P} (e : φ.right = ψ.right) : φ = ψ := by
  refine Arrow.hom_ext _ _ ?_ e
  rw [← cancel_mono P.hom, Arrow.w, Arrow.w, e]

theorem goal_of (hG : LeafGeo) (hA : LeafAct) (hT : LeafTau) (hN : LeafTauNat) (hE : LeafExcP) : LeafThom := by
  intro H d
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have h11 : A11 := H.2.2.2.2.2.2.2.1
  obtain ⟨hm, -, hpt, hΦ⟩ := hG
  choose Φ hΦ using hΦ d
  let τ : ∀ (q : ℕ) (A : Type) [CommRing A], Hs q (pr d A) (2 * d) d := fun q A _ => pick (IsTau q d A)
  have hτ : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → IsTau q d A (τ q A) :=
    fun q _ A _ hq => pick_spec (hT H q d A hq).1.exists
  have huq : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ t, IsTau q d A t → t = τ q A :=
    fun q _ A _ hq t ht => (hT H q d A hq).1.unique ht (hτ q A hq)
  have hb : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), IsUnit (q : A) →
      Hs.pull q (prMap d φ) _ _ (τ q A) = τ q B := fun q _ A B _ _ φ hq =>
    huq q B (by simpa using hq.map φ) _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 B φ _
      ((prod.map_fst_assoc (𝟙 (Pj (d + 1) 0)) (spMap φ) (Pj.line (d + 1) 0)).trans
        (congrArg (fun f => prod.fst ≫ f) (Category.id_comp _)))
      (prod.map_snd _ _))
  refine ⟨fun q A _ I x hx => Hs.pull q (Φ A I x hx) _ _ (τ q A), fun q _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro A B _ _ φ I J x hx hy h hq
    have e : opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h ≫ Φ A I x hx = Φ B J _ hy ≫ prMap d φ := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, Arrow.comp_right, hΦ, hΦ]
      change spMap φ ≫ chart x = chart (φ ∘ x) ≫ prod.map (𝟙 _) (spMap φ)
      rw [chart, chart, prod.comp_lift, prod.lift_map, hpt, Category.comp_id, Category.comp_id, Category.id_comp]
    beta_reduce
    rw [hs_comp, e, ← hs_comp, hb q A B φ hq]
  · intro A _ I x M hx hy hq hM
    obtain ⟨g, g1, g2, g3⟩ := hA d A M hM
    have e : Φ A I _ hy = Φ A I x hx ≫ g := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, hΦ, hΦ]
      exact (g3 x).symm
    have e2 : Hs.pull q g _ _ (τ q A) = τ q A := huq q A hq _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 A (RingHom.id A) g g1
      (by
        have : spMap (RingHom.id A) = 𝟙 _ := by
          change sch.map (Spec.map (𝟙 _)) = _
          rw [Spec.map_id, CategoryTheory.Functor.map_id]
        rw [this, Category.comp_id]
        exact g2))
    beta_reduce
    rw [e, ← hs_comp, e2]
  · intro R _ I hx hq n i
    have er : (Φ _ I MvPolynomial.X hx ≫ prMap d (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)).right =
        (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
          sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
      rw [Arrow.comp_right, hΦ]
      change chart _ ≫ prod.map (𝟙 _) (spMap _) = _
      rw [chart, prod.lift_map, Category.comp_id, Category.id_comp]
    have hb2 := (hE H q d R I hx hq _ er _ _).comp ((hT H q d R hq).2 _ (hτ q R hq) n i)
    convert hb2 using 1
    funext a
    refine Eq.symm ((hs_act h6 q _ _ _).trans (congrArg₂ (Hs.act q) ?_ ?_))
    · refine (congrArg (fun f => pull _ f _ n (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ n a)) er).trans ?_
      exact (pull_comp _ _ _ _ _ _).symm.trans (congrArg (fun f => pull _ f _ n a) (prod.lift_snd _ _))
    · exact (hs_comp q _ _ _ _ _).symm.trans (congrArg _ (hb q R _ _ hq))
  · intro r hr A _ I x hx hq
    have : NeZero r := ⟨fun h => NeZero.ne q (by simpa [h] using hr)⟩
    have hr' : IsUnit (r : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hr) hq
    have hmem : red q r _ _ _ (τ q A).1 ∈ Hs r (pr d A) (2 * d) d := by
      change pull _ (dbl.inr _) _ _ _ = 0
      have h0 : pull _ (dbl.inr (pr d A)) (tw q d) (2 * d) (τ q A).1 = 0 := (τ q A).2
      rw [pull_red, h0, map_zero]
    have e := huq r A hr' _ ((hN h6 h11 q d A hq _ (hτ q A hq)).2 r hr ⟨_, hmem⟩ rfl)
    change pull _ (dbl.map _) _ _ (τ r A).1 = red q r _ _ _ (pull _ (dbl.map _) _ _ (τ q A).1)
    rw [← e]
    exact pull_red _ _ _ _ _ _

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Good.nbhd {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I) : Nbhd φ I := by
  refine ⟨h.etale, Ideal.quotientMap_injective' ?_, fun y => ?_⟩
  · obtain ⟨r, hr⟩ := h.retr
    have h1 : I.map φ ≤ RingHom.ker r := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change (r.comp φ) a = 0
      rw [hr]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    intro a ha
    have h2 : (r.comp φ) a = 0 := h1 ha
    rw [hr] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := h.surj s
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 ha).symm

theorem exists_obj (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) (A : Type) [CommRing A] (I : Ideal A) :
    ∃ (H : CommRingCat.{0}) (η : A →+* H), HenselianRing H (I.map η) ∧ IndNbhd η I ∧ Univ η I := by
  obtain ⟨Δ⟩ := h1 A I
  let c := colimit.cocone Δ.D
  have hc : IsColimit c := colimit.isColimit Δ.D
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  have hw : ∀ {j k : Δ.J} (e : j ⟶ k), (Δ.leg c j).comp (Δ.s j) = (Δ.leg c k).comp (Δ.s k) := fun {j k} e => by
    have h : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j := congrArg CommRingCat.Hom.hom (c.w e)
    rw [← Δ.nat e, ← RingHom.comp_assoc, h]
  have hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = (Δ.leg c j₀).comp (Δ.s j₀) := fun j =>
    (hw (IsFiltered.leftToMax j j₀)).trans (hw (IsFiltered.rightToMax j j₀)).symm
  refine ⟨c.pt, _, h2 A I Δ c hc _ hη, ?_, h3 A I Δ c hc _ hη⟩
  refine ⟨Δ.J, Δ.cat, Δ.filt, Δ.D, ⟨fun j => CommRingCat.ofHom (Δ.s j), fun j k e => ?_⟩, c.ι, ⟨hc⟩,
    fun j => ⟨(Δ.good j).nbhd, ?_⟩⟩
  · exact CommRingCat.hom_ext (Δ.nat e).symm
  · exact CommRingCat.hom_ext (hη j)

theorem goal_of (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) : LeafHens := by
  choose H η hh hi hu using exists_obj h1 h2 h3
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B), I ≤ J.comap φ →
      ∃! χ : H A I →+* H B J, χ.comp (η A I) = (η B J).comp φ := fun {A B} _ _ {I J} φ h =>
    hu A I _ _ (hh B J) _ fun a ha => Ideal.mem_map_of_mem (η B J) (h ha)
  refine ⟨⟨H, η, fun φ h => (key φ h).exists.choose, fun φ h => (key φ h).exists.choose_spec, fun A _ I h => ?_,
    fun φ ψ h h' h'' => ?_, hh, hi⟩⟩
  · exact (key _ h).unique (key _ h).exists.choose_spec rfl
  · refine (key _ h'').unique (key _ h'').exists.choose_spec ?_
    rw [RingHom.comp_assoc, (key φ h).exists.choose_spec, ← RingHom.comp_assoc, (key ψ h').exists.choose_spec,
      RingHom.comp_assoc]

end LateralTheory.CohomologicalPurity.Hz
end
end
