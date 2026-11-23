module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.RingTheory.Artinian.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle037
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.polynomial_roots_of_closed_quotient : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  first | exact @GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | exact GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | (intros; apply GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.InitialCoh

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T₀ : C}

def pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : ComposableArrows C (n + 1) :=
  s.precomp (h.to s.left)

theorem pre_map (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) (a b : Fin (n + 1)) (hab : a ≤ b) :
    (pre h s).map (homOfLE (Fin.succ_le_succ_iff.2 hab)) = s.map (homOfLE hab) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  rfl

theorem map_homOfLE_source_eq {m : ℕ} (s : ComposableArrows C m) {a a' b : Fin (m + 1)} (hab : a ≤ b) (hab' : a' ≤ b) (e : a = a') :
    s.map (homOfLE hab) = eqToHom (congrArg s.obj e) ≫ s.map (homOfLE hab') := by
  subst e
  simp

theorem val_congr (F : C ⥤ ModuleCat.{w} R) {m : ℕ} (y : Cn F m) {a b : ComposableArrows C m} (e : a = b) {X : C}
    (φ : a.obj (Fin.last m) ⟶ X) (ψ : b.obj (Fin.last m) ⟶ X)
    (hφ : φ = eqToHom (congrArg (fun c : ComposableArrows C m => c.obj (Fin.last m)) e) ≫ ψ) :
    (F.map φ).hom (y a) = (F.map ψ).hom (y b) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hφ
  rw [hφ]

theorem hom_from_initial (h : Limits.IsInitial T₀) {X Y : C} (e : X = T₀) (a b : X ⟶ Y) : a = b := by
  subst e
  exact h.hom_ext a b

theorem whisker_congr {k l : ℕ} (a b : Fin (k + 1) ⥤ Fin (l + 1)) (e : ∀ i, a.obj i = b.obj i) (P : ComposableArrows C l) :
    a ⋙ P = b ⋙ P := by
  have : a = b := CategoryTheory.Functor.ext e (fun _ _ _ => Subsingleton.elim _ _)
  rw [this]

theorem face_zero_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : face 0 (pre h s) = s :=
  whisker_congr _ (Fin.succFunctor _) (fun i => by simp) (pre h s)

theorem face_face {m : ℕ} (P : ComposableArrows C (m + 2)) (a a' : Fin (m + 2)) (b b' : Fin (m + 3))
    (e : ∀ x, b.succAbove (a.succAbove x) = b'.succAbove (a'.succAbove x)) : face a (face b P) = face a' (face b' P) :=
  whisker_congr ((Fin.succAboveOrderEmb a).monotone.functor ⋙ (Fin.succAboveOrderEmb b).monotone.functor)
    ((Fin.succAboveOrderEmb a').monotone.functor ⋙ (Fin.succAboveOrderEmb b').monotone.functor) e P

theorem eq_of_face_zero (h : Limits.IsInitial T₀) {n : ℕ} {P Q : ComposableArrows C (n + 1)} (h0 : P.obj 0 = T₀) (h1 : Q.obj 0 = T₀)
    (e : face 0 P = face 0 Q) : P = Q := by
  refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
  · refine Fin.cases (h0.trans h1.symm) (fun j => ?_) i
    have := Functor.congr_obj e j
    simpa [face] using this
  · cases i with
    | zero => exact hom_from_initial h h0 _ _
    | succ i =>
      exact Functor.congr_hom e (homOfLE (Nat.le_succ i) : (⟨i, by omega⟩ : Fin (n + 1)) ⟶ ⟨i + 1, by omega⟩)

theorem face_succ_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    face i.succ (pre h s) = pre h (face i s) := by
  refine eq_of_face_zero h ?_ rfl ?_
  · change (pre h s).obj (i.succ.succAbove 0) = T₀
    rw [Fin.succ_succAbove_zero]
    rfl
  · rw [face_zero_pre, face_face (pre h s) 0 i i.succ 0 (fun x => by simp [Fin.succ_succAbove_succ]), face_zero_pre]

theorem val_zero (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F n) (s : ComposableArrows C n) :
    (F.map (toLast 0 (pre h s))).hom (y (face 0 (pre h s))) = y s := by
  have e : (0 : Fin (n + 2)).succAbove (Fin.last n) = Fin.last (n + 1) := by simp
  have := val_congr F y (face_zero_pre h s) (toLast 0 (pre h s)) (𝟙 _)
    ((map_homOfLE_source_eq (pre h s) _ le_rfl e).trans
      (congrArg (fun g => eqToHom _ ≫ g) ((pre h s).map_id (Fin.last (n + 1)))))
  refine this.trans ?_
  rw [F.map_id]
  rfl

theorem val_succ (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F (n + 1))
    (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    (F.map (toLast i.succ (pre h s))).hom (y (face i.succ (pre h s))) =
      (F.map (toLast i s)).hom (y (pre h (face i s))) := by
  have e : i.succ.succAbove (Fin.last (n + 1)) = (i.succAbove (Fin.last n)).succ := by
    rw [← Fin.succ_last, Fin.succ_succAbove_succ]
  exact val_congr F y (face_succ_pre h s i) (toLast i.succ (pre h s)) (toLast i s)
    ((map_homOfLE_source_eq (pre h s) _ (Fin.succ_le_succ_iff.2 (Fin.le_last _)) e).trans
      (congrArg (fun g => eqToHom _ ≫ g) (pre_map h s _ _ (Fin.le_last _))))

def con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) : Cn F n := fun s => y (pre h s)

theorem d_con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) (hy : d F (n + 1) y = 0) :
    d F n (con F h n y) = y := by
  funext s
  have key : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
    congrFun hy (pre h s)
  rw [Fin.sum_univ_succ] at key
  simp only [val_succ, Fin.val_succ, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib] at key
  rw [val_zero] at key
  exact (add_neg_eq_zero.1 key).symm

theorem resUpTo_one (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀) :
    (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  have hid : h.to T₀ = 𝟙 T₀ := h.hom_ext _ _
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ⟨con F h n y, ?_⟩⟩
  · funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) = 0
    have e : ∀ i : Fin 2, (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) =
        (F.map (h.to (s.obj (Fin.last 1)))).hom x := fun i => by
      rw [← ModuleCat.comp_apply, ← F.map_comp, h.hom_ext (h.to _ ≫ toLast i s) (h.to _)]
    simp only [e]
    simp [Fin.sum_univ_two]
  · have : (F.map (h.to T₀)).hom x = 0 := congrFun hx (ComposableArrows.mk₀ T₀)
    rw [hid] at this
    simpa using this
  · refine ⟨y (ComposableArrows.mk₀ T₀), funext fun s => ?_⟩
    have key : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
      congrFun hy (pre h s)
    have e1 : face 1 (pre h s) = ComposableArrows.mk₀ T₀ := ComposableArrows.ext₀ rfl
    have t1 : (F.map (toLast 1 (pre h s))).hom (y (face 1 (pre h s))) =
        (F.map (h.to (s.obj (Fin.last 0)))).hom (y (ComposableArrows.mk₀ T₀)) :=
      val_congr F y e1 _ _ (hom_from_initial h rfl _ _)
    rw [Fin.sum_univ_two, t1] at key
    have t0 := val_zero F h y s
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at key
    rw [t0] at key
    rw [one_smul]
    exact (add_neg_eq_zero.1 key).symm
  · rw [one_smul]
    exact d_con F h n y hy

end GlobalTheory.CompanionTheory.InitialCoh
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CupAssocC

section
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem term_term (F : C ⥤ ModuleCat.{w} R) {p m n : ℕ} (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g) (g' : Fin (p + 1) → Fin (m + 1)) (hg' : Monotone g') :
    (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (term F (hg.functor ⋙ s) f g' hg') =
      term F s f (g ∘ g') (hg.comp hg') := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last (g' (Fin.last p)))) ≫
      s.map (homOfLE (Fin.le_last (g (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (g (g' (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have key : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj X),
      (F.map b).hom ((F.map a).hom x) = (F.map (a ≫ b)).hom x := by
    intro X Y Z a b x
    rw [F.map_comp]; rfl
  refine (key _ _ _).trans ?_
  exact congrArg (fun φ => (F.map φ).hom (f ((hg.comp hg').functor ⋙ s))) e

theorem term_id (F : C ⥤ ModuleCat.{w} R) {n : ℕ} (s : ComposableArrows C n) (f : Cn F n) :
    term F s f id monotone_id = f s := by
  have e : s.map (homOfLE (Fin.le_last (id (Fin.last n)))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  unfold term
  rw [e, F.map_id]
  rfl

theorem term_cupC {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q a n : ℕ} (h : p + q = a) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) (θ : Fin (a + 1) → Fin (n + 1)) (hθ : Monotone θ) :
    term F₃ s (P.cupC h f g) θ hθ =
      P.μ _ (term F₁ s f (θ ∘ front h) (hθ.comp (front_mono h)))
        (term F₂ s g (θ ∘ back h) (hθ.comp (back_mono h))) := by
  rw [← term_term F₁ s f θ hθ _ (front_mono h), ← term_term F₂ s g θ hθ _ (back_mono h), P.nat]
  rfl

theorem cupC_at {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) :
    P.cupC h f g s = P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)) := rfl

theorem term_one (A : C ⥤ CommAlgCat.{w} R) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin (0 + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (modF A) s (fun s => (1 : A.obj (s.obj (Fin.last 0)))) g hg = (1 : A.obj (s.obj (Fin.last n))) :=
  map_one (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 0)))))).hom

end

theorem cup_assocC : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R), (∀ n (x : Cn (modF A) n), (mulP A).cupC (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) x = x ∧ (mulP A).cupC (Nat.add_zero n) x (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = x) ∧ ∀ {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n) x y z, (mulP A).cupC h₂ ((mulP A).cupC h₁ x y) z = (mulP A).cupC h₄ x ((mulP A).cupC h₃ y z) := by
  intro R _ C _ A
  refine ⟨fun n x => ⟨?_, ?_⟩, ?_⟩
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (back_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [back])), term_id]
    exact one_mul (M := A.obj (s.obj (Fin.last n))) _
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (front_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [front])), term_id]
    exact mul_one (M := A.obj (s.obj (Fin.last n))) _
  · intro p q r a b n h₁ h₂ h₃ h₄ x y z
    funext s
    rw [cupC_at, cupC_at, term_cupC, term_cupC,
      term_congr (modF A) s x ((front_mono h₂).comp (front_mono h₁)) (front_mono h₄)
        (funext fun i => Fin.ext (by simp [front])),
      term_congr (modF A) s y ((front_mono h₂).comp (back_mono h₁)) ((back_mono h₄).comp (front_mono h₃))
        (funext fun i => Fin.ext (by simp [front, back])),
      term_congr (modF A) s z (back_mono h₂) ((back_mono h₄).comp (back_mono h₃))
        (funext fun i => Fin.ext (by simp [back]; omega))]
    exact mul_assoc (G := A.obj (s.obj (Fin.last n))) _ _ _

end GlobalTheory.CompanionTheory.CupAssocC
end

section

open CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.ArtinTower

universe w

theorem coset_chain {W : Type} [CommRing W] {M : Type w} [AddCommGroup M] [Module W M]
    [IsArtinian W M] (K : ℕ → Submodule W M) (hK : ∀ k, K (k + 1) ≤ K k) (c : ℕ → M)
    (hc : ∀ k, c (k + 1) - c k ∈ K k) : ∃ x, ∀ k, x - c k ∈ K k := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)
  have hdiff : ∀ k j, c (k + j) - c k ∈ K k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : c (k + j + 1) - c (k + j) ∈ K k := hanti (Nat.le_add_right k j) (hc (k + j))
      have h2 := add_mem h1 ih
      rw [sub_add_sub_cancel] at h2
      exact h2
  refine ⟨c m, fun k => ?_⟩
  rcases le_total k m with hkm | hmk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    exact hdiff k j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    have hKeq : K m = K (m + j) := hm (m + j) (Nat.le_add_right m j)
    rw [← hKeq]
    have h3 := neg_mem (hdiff m j)
    rw [neg_sub] at h3
    exact h3

section
variable {W : Type} [CommRing W] (S : Sys.{w} W) (N : ∀ n, Submodule W (S.M n))
  (y : ∀ n, S.M n)

noncomputable def imgSub : ℕ → ∀ n, Submodule W (S.M n)
  | 0, n => N n
  | k + 1, n => (imgSub k (n + 1)).map (S.r n)

noncomputable def imgPt : ℕ → ∀ n, S.M n
  | 0, n => y n
  | k + 1, n => S.r n (imgPt k (n + 1))

def stable (n : ℕ) : Set (S.M n) := {x | ∀ k, x - imgPt S y k n ∈ imgSub S N k n}

variable {S N y}

theorem imgSub_succ_le (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) :
    ∀ k n, imgSub S N (k + 1) n ≤ imgSub S N k n := by
  intro k
  induction k with
  | zero =>
    intro n
    show Submodule.map (S.r n) (N (n + 1)) ≤ N n
    exact Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)
  | succ k ih =>
    intro n
    show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    exact Submodule.map_mono (ih (n + 1))

theorem imgPt_step (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) :
    ∀ k n, imgPt S y (k + 1) n - imgPt S y k n ∈ imgSub S N k n := by
  intro k
  induction k with
  | zero => intro n; exact hy n
  | succ k ih =>
    intro n
    show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    rw [← map_sub]
    exact Submodule.mem_map_of_mem (ih (n + 1))

theorem stable_nonempty (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) (n : ℕ) [IsArtinian W (S.M n)] :
    ∃ x, x ∈ stable S N y n := by
  obtain ⟨x, hx⟩ := coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n)
    (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)
  exact ⟨x, hx⟩

theorem stable_surj (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) {n : ℕ} [IsArtinian W (S.M (n + 1))]
    {x : S.M n} (hx : x ∈ stable S N y n) :
    ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := by
  have hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n := hx
  have hA : ∀ k, ∃ u : S.M (n + 1),
      S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1) := by
    intro k
    have h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1)) :=
      hxk (k + 1)
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp h1
    refine ⟨v + imgPt S y k (n + 1), ?_, ?_⟩
    · rw [map_add (f := _), hve]
      show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x
      exact sub_add_cancel _ _
    · rw [add_sub_cancel_right]
      exact hv
  choose c hc1 hc2 using hA
  have hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤
      LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) :=
    fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))
  have hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) := by
    intro k
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]
    · have e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) +
          (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1)) := by
        abel
      rw [e]
      exact sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1)))
        (imgPt_step hy k (n + 1))) (hc2 k)
  obtain ⟨x', hx'⟩ := coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1))
    hKanti c hstep
  refine ⟨x', fun k => ?_, ?_⟩
  · have e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1)) := by abel
    rw [e]
    exact add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)
  · have h0 := (Submodule.mem_inf.mp (hx' 0)).1
    rw [LinearMap.mem_ker, map_sub, hc1, sub_eq_zero] at h0
    exact h0

end

theorem exists_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W),
    (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n),
    (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) →
    ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  intro W _ S hA N y hN hy
  have h0 : ∃ x, x ∈ stable S N y 0 := by
    haveI := hA 0
    exact stable_nonempty hN hy 0
  have hs : ∀ n (x : S.M n), x ∈ stable S N y n →
      ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := fun n x hx => by
    haveI := hA (n + 1)
    exact stable_surj hN hy hx
  let f : ∀ n, {x : S.M n // x ∈ stable S N y n} := fun n =>
    Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n})
      ⟨h0.choose, h0.choose_spec⟩
      (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n
  have hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1 := fun n =>
    (hs n (f n).1 (f n).2).choose_spec.2
  refine ⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩
  unfold CrystallineSemistableComparison.Sys.lim
  exact fun n => hf n

end GlobalTheory.CompanionTheory.ArtinTower
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_functorial : ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K) (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  first | exact @GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | exact GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | (intros; apply GlobalTheory.CompanionTheory.KapRhoHom.rho_hom <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  first | exact @GlobalTheory.CompanionTheory.KapChain.rho_smul | exact GlobalTheory.CompanionTheory.KapChain.rho_smul | (intros; apply GlobalTheory.CompanionTheory.KapChain.rho_smul <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_unique : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (f f' : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho x f' → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.KapUniq.rho_unique | exact GlobalTheory.CompanionTheory.KapUniq.rho_unique | (intros; apply GlobalTheory.CompanionTheory.KapUniq.rho_unique <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_unit_class : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  first | exact @GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | exact GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | (intros; apply GlobalTheory.CompanionTheory.KapUnit.rho_one_eval <;> assumption)
end

section

open DividedPowers CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.mem_lattice_ideal_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LatIdeal.mem_I | exact GlobalTheory.CompanionTheory.LatIdeal.mem_I | (intros; apply GlobalTheory.CompanionTheory.LatIdeal.mem_I <;> assumption)
end

section

open DividedPowers CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.mem_lattice_sub_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  first | exact @GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | exact GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | (intros; apply GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.frobenius_power_solution_lift : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | exact GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow <;> assumption)
end
