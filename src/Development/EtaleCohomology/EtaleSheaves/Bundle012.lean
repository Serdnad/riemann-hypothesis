module

public import Development.EtaleCohomology.EtaleSheaves.Bundle005
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E3Cut

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4

def RE (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop := Eqv _ (sch.map (Spec.map f)) (tw q i)

def BC (q : ℕ) (i : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RE q i φ'

def Et : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.Etale

def IE : MorphismProperty CommRingCat.{0} := MorphismProperty.ind.{0} Et

def AlgRes : MorphismProperty CommRingCat.{0} := fun A C f =>
  ∀ Q : Ideal C, Q.IsPrime → ∀ c : C, ∃ p : Polynomial A, (∃ n, f.hom (p.coeff n) ∉ Q) ∧ p.eval₂ f.hom c ∈ Q

def SpS {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  ∀ r : Ideal A, r.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap f.hom = r

abbrev pC (A : CommRingCat.{0}) : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

def Good (q : ℕ) (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) : Prop :=
  ∀ (B : CommRingCat.{0}) (c : A ⟶ B), Et c → BC q i k (t ≫ c)

theorem RE.comp {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f) (hg : RE q i g) :
    RE q i (f ≫ g) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  rw [h]; exact (hg n).comp (hf n)

theorem RE.of_comp_left {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f)
    (hfg : RE q i (f ≫ g)) : RE q i g := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff _ (hf n)).1 this

theorem RE.of_comp_right {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hg : RE q i g)
    (hfg : RE q i (f ≫ g)) : RE q i f := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff' (hg n) _).1 this

theorem RE.of_isIso (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f] : RE q i f := fun n => by
  have h1 : ∀ x, pull _ (sch.map (Spec.map (inv f))) (tw q i) n (pull _ (sch.map (Spec.map f)) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull _ (sch.map (Spec.map f)) (tw q i) n (pull _ (sch.map (Spec.map (inv f))) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem BC.of_one {q : ℕ} {i : ℤ} {A Y C Y' : CommRingCat.{0}} {φ : A ⟶ Y} {c : A ⟶ C} {w : Y ⟶ Y'} {φ' : C ⟶ Y'}
    (h : IsPushout φ c w φ') (hr : RE q i φ') : BC q i φ c := fun _ _ ψ h' => by
  rw [← h.inr_isoIsPushout_hom _ _ h']
  exact hr.comp (RE.of_isIso q i _)

def AlgResProps : Prop :=
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)) ∧
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes (f ≫ g) → AlgRes g) ∧
  (∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → AlgRes f) ∧
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
    AlgRes (CommRingCat.ofHom (algebraMap A B))

def IEComp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

def LocIE : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
  IE (CommRingCat.ofHom (algebraMap A B))

def SHExists : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A), r.IsPrime →
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ ∀ a : A, a ∈ r ↔ ¬ IsUnit (f.hom a)

def AICSH : Prop := ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → SH T

def AICExt : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ Function.Injective g.hom ∧ AIC D

def DomCover : Prop := ∀ (C : CommRingCat.{0}), AIC C → ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧ AIC (Localization.AtPrime r)

def HensInt : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] (f : A →+* B),
  f.IsIntegral → (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → Nonempty (HenselianLocalRing B)

def SHTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → SH Z

def IntClos : Prop := ∀ {A C : CommRingCat.{0}} (c : A ⟶ C) [IsDomain C], SH A → AIC C → AlgRes c →
  ∃ (B : CommRingCat.{0}) (b : A ⟶ B) (j : B ⟶ C), b ≫ j = c ∧ b.hom.IsIntegral ∧ Function.Injective j.hom ∧ IsLocalRing B ∧
    AIC B ∧ ∀ z : C, ∃ s y : B, s ≠ 0 ∧ j.hom s * z = j.hom y

def SHSection : Prop := ∀ (A : CommRingCat.{0}), SH A → ∀ {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ s : Spec A ⟶ V, s ≫ g = 𝟙 _

def Coprod : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (X : ι → Scheme.{0}) (n : ℤ),
  Function.Bijective fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x

def ZarLocal : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X),
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Eqv R (sch.map (g ∣_ V)) F) → Eqv R (sch.map g) F

def Limit : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), Et c → BC q i φ c) → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), IE c → BC q i φ c

def Stalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop,
  (∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)) →
  (∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → ∃ (D : CommRingCat.{0}) (g : C ⟶ D), g.hom.IsIntegral ∧ SpS g ∧ P D (c ≫ g) ∧
    ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
      BC q i φ (c ≫ g ≫ o)) →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BC q i φ c

def SHEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B → RE q i f

def EtaleBaseChangeFractionFieldIndEtaleOverPolynomial : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [Field K] [Algebra T K]
  [IsFractionRing T K], AIC T → IsUnit (q : T) → ∀ (X : CommRingCat.{0}) (h : CommRingCat.of (Polynomial T) ⟶ X), IE h →
  BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ h)

def ULAStalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsLocalRing C], AIC C → AlgRes c → BC q i (pC A ≫ h) c

def ULA : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), AlgRes c → BC q i (pC A ≫ h) c

def Step : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A), IsUnit (q : T) →
  AlgRes k → Good q i k t → Good q i k (t ≫ pC A)

def Base : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (𝟙 _)

def Global : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K),
  (∀ n : ℕ, Good q i k (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p], Eqv _ (sch.map (pullback.fst p (Spec.map k))) (tw q i)

theorem Good.of_equiv {q : ℕ} {i : ℤ} {T K A A' : CommRingCat.{0}} {k : T ⟶ K} {t : T ⟶ A} (h : Good q i k t)
    (e : A ≃+* A') (t' : T ⟶ A') (ht : t ≫ CommRingCat.ofHom e.toRingHom = t') : Good q i k t' := fun B c hc => by
  rw [← ht, Category.assoc]
  exact h B _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) hc)

theorem goal_of (h1 : AlgResProps) (h2 : Base) (h3 : Step) (h4 : Global) : LateralTheory.E.EtaleChapterEThree := by
  intro a1 a2 a3 a4 a5 _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ c3 c4 _ _ _ _ _ _ q _ T _ _ _ hT hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a9, b1, b2, b4, c3, c4⟩
  refine h4 H q i _ (fun n => ?_) p
  induction n with
  | zero =>
    refine (h2 H q i T hT hq).of_equiv (MvPolynomial.isEmptyRingEquiv T (Fin 0)).symm _ ?_
    ext x; simp
  | succ n ih =>
    refine (h3 H q i _ _ hq (h1.2.2.2.2.2 T _ (nonZeroDivisors T)) ih).of_equiv
      (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
    ext1
    exact RingHom.ext fun x => (MvPolynomial.finSuccEquiv T n).symm.commutes x

end LateralTheory.E.t_E3Cut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem inv_of {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E :=
  fun U ⟨x⟩ => h U ⟨(f.app _).app _ x⟩

structure Collected (q : ℕ) where
  R : ∀ E : Spc, Inv q E → Type 1
  ring : ∀ E h, CommRing (R E h)
  ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; Ht q E (2 * k) k →+ R E h
  π : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; R E h →+ Ht q E (2 * k) k
  map : ∀ {E E' : Spc} (_ : E ⟶ E') (h : Inv q E) (h' : Inv q E'), letI := ring E h; letI := ring E' h'; R E' h' →+* R E h
  π_ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (a : Ht q E (2 * k) k), π h k (ι h k a) = a
  ι_one : ∀ {E : Spc} (h : Inv q E), letI := ring E h; ι h 0 ((one q E).cast (by simp) (by simp)) = 1
  ι_mul : ∀ {E : Spc} (h : Inv q E) (k l : ℕ) (a : Ht q E (2 * k) k) (b : Ht q E (2 * l) l), letI := ring E h
    ι h (k + l) ((cup q a b).cast (by push_cast; ring) (by push_cast; ring)) = ι h k a * ι h l b
  ι_cpow : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (x : Ht q E 2 1), letI := ring E h
    ι h k (cpow q x k) = ι h 1 (x.cast (by simp) (by simp)) ^ k
  map_ι : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : Ht q E' (2 * k) k),
    map f h h' (ι h' k a) = ι h k (pull _ f _ _ a)
  π_map : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (r : R E' h'),
    π h k (map f h h' r) = pull _ f _ _ (π h' k r)

instance {q : ℕ} (P : Collected q) (E : Spc) (h : Inv q E) : CommRing (P.R E h) := P.ring E h

abbrev PB {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Spc := pullback V (PGL.pr N)

abbrev PB.pr {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ E := pullback.fst V (PGL.pr N)

abbrev PB.line {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ ofCat (glCat 1) := pullback.snd V (PGL.pr N) ≫ PGL.line N

abbrev Collected.deg1 {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) (x : Ht q E 2 1) : P.R E h := P.ι h 1 (x.cast (by simp) (by simp))

def IsChern {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j) : Prop :=
  P.ι h 0 (c 0) = 1 ∧ (∀ j, N < j → c j = 0) ∧
  ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
    P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) = 0

def newton {A : Type 1} [CommRing A] (c : ℕ → A) (k : ℕ) : A :=
  PowerSeries.coeff k (-(PowerSeries.X * PowerSeries.derivative (PowerSeries.mk c)) * (PowerSeries.mk c).invOfUnit 1)

def LeafA6nat : Prop := DivisorNaturality

def LeafA6ring : Prop := DivisorRingCompatibility

def LeafA6supp : Prop := DivisorSupportCondition

def LeafRing : Prop := ∀ (q : ℕ) [NeZero q], Nonempty (Collected q)

def LeafChern : Prop := D1 → ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)),
  ∃! c, IsChern P h V c

def LeafNat : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') {N : ℕ}
  (V : E' ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E' (2 * j) j), IsChern P h' V c → IsChern P h (f ≫ V) fun j => pull _ f _ _ (c j)

def LocCover {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx E n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    (∃ y : Sx U n Y, (f.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x) ∨
    (∃ y : Sx V n Y, (g.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x)

def LeafCover2 : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g → LocCover f g → Cover2 R f g

def LeafGeom : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ U₂ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V) (p₂ : U₂ ⟶ PB W),
    Mono f₁ ∧ Mono f₂ ∧ LocCover f₁ f₂ ∧ p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _

def LeafWhitney : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {a b : ℕ} (V : E ⟶ ofCat (glCat a))
  (W : E ⟶ ofCat (glCat b)) (c d : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h V c → IsChern P h W d →
  ∃ e, IsChern P h (bsumOf V W) e ∧ ∀ k, P.ι h k (e k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2)

def LeafLine : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) (L : E ⟶ ofCat (glCat 1))
  (c : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h L c → P.ι h 1 (c 1) = -P.deg1 h (c1 q L)

def LeafNewton : Prop :=
  (∀ (A B : Type 1) [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A), c 0 = 1 → ∀ k, φ (newton c k) = newton (fun j => φ (c j)) k) ∧
  (∀ (A : Type 1) [CommRing A] (c d e : ℕ → A), c 0 = 1 → d 0 = 1 → (∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) →
    ∀ k, newton e k = newton c k + newton d k) ∧
  ∀ (A : Type 1) [CommRing A] (c : ℕ → A) (x : A), c 0 = 1 → c 1 = -x → (∀ j, 1 < j → c j = 0) → ∀ k, 0 < k → newton c k = x ^ k

theorem goal_of (hR : LeafRing) (hC : LeafChern) (hN : LeafNat) (hW : LeafWhitney) (hL : LeafLine) (hS : LeafNewton) :
    LateralTheory.E.EtaleChapterDTwo := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD q _ k hk
  classical
  obtain ⟨P⟩ := hR q
  have hE := fun {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) => hC hD q P h V
  choose c hc hu using @hE
  refine ⟨fun {E N} V => if h : Inv q E then P.π h k (newton (fun j => P.ι h j (c h V j)) k) else 0, ?_, ?_, ?_⟩
  · intro E E' N f V h'
    have h := inv_of f h'
    simp only [dif_pos h, dif_pos h']
    rw [← hu h (f ≫ V) _ (hN q P f h h' V _ (hc h' V)), ← P.π_map f h h', hS.1 _ _ _ _ (hc h' V).1]
    simp only [P.map_ι]
  · intro E a b V W h
    simp only [dif_pos h]
    obtain ⟨e, he, hk⟩ := hW q P h V W _ _ (hc h V) (hc h W)
    rw [← hu h _ e he, hS.2.1 _ (fun j => P.ι h j (c h V j)) (fun j => P.ι h j (c h W j)) _ (hc h V).1 (hc h W).1 hk, map_add (f := _)]
  · intro E L h
    simp only [dif_pos h]
    rw [hS.2.2 _ _ _ (hc h L).1 (hL q P h L _ (hc h L)) (fun j hj => by rw [(hc h L).2.1 j hj, map_zero]) k hk,
      ← P.ι_cpow, P.π_ι]

end LateralTheory.E.D2
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneLocPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have h2 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} (P.map g.op x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg _ h2)

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (Sx.res g x) := by
  unfold ev
  have hn := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  change _ = _ at hn
  rw [Sx.res, ← freeGen_res]
  exact hn.symm

def LeafPrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

theorem LeafOneLoc_of (hprim : LeafPrimLoc) : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := by
  intro q _ E hE α hα U x
  obtain ⟨S, hS, hP⟩ := hprim q U (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  exact ⟨ζ, (ev_res α.1 0 0 (by simp) g x).trans (hα V (Sx.res g x) ζ)⟩

end LateralTheory.E.LeafOneLocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
end
end
