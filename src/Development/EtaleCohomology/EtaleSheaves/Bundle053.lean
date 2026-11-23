module

public import Development.EtaleCohomology.EtaleSheaves.Bundle041
public import Development.EtaleCohomology.EtaleSheaves.Bundle043
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf

namespace LateralTheory.E.FibStalkPf

theorem eqv_iso {X Y : Scheme.{0}} (e : X ≅ Y) (q : ℕ) (i : ℤ) : Eqv _ (sch.map e.hom) (tw q i) := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map e.inv) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_comp {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (hf : Eqv _ f F) (hg : Eqv _ g F) :
    Eqv _ (f ≫ g) F := by
  intro n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_left {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hg : Eqv _ g F) :
    Eqv _ f F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff _ (hg n)).1 h1

theorem eqv_right {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hf : Eqv _ f F) :
    Eqv _ g F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 h1

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSH : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of A)),
  AICSch S → ∀ s : (pullback p (cpt A) : Scheme.{0}), SH ((pullback p (cpt A)).presheaf.stalk s)

def FibreEqv : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.snd (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))
      (cpt ((pullback p (cpt A)).presheaf.stalk s)))) (tw q i)

theorem FibStalk_of (hS : StalkSH) (hF : FibreEqv) : FibStalk := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  have hsh : SH ((pullback p (cpt A)).presheaf.stalk s) := hS A p hSs s
  obtain ⟨_, _⟩ := id hsh
  have hu0 : IsUnit (q : Γ((pullback p (cpt A) : Scheme.{0}), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  have hu : IsUnit (q : (pullback p (cpt A)).presheaf.stalk s) := by
    simpa using hu0.map ((pullback p (cpt A)).presheaf.germ ⊤ s trivial).hom
  have hfst := hB _ hsh hu ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A))
  have hfib := hF H h0 hA q i A hq c p hZs hSs hB s
  have hE1 : Eqv _ (sch.map (cpt ((pullback p (cpt A)).presheaf.stalk s))) (tw q i) :=
    H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  have core : Eqv _ (sch.map (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))) (tw q i) := by
    refine eqv_right ?_ hfst
    rw [← Functor.map_comp, pullback.condition, Functor.map_comp]
    exact eqv_comp hfib hE1
  have sq2 : IsPullback (pullback.fst (c ≫ p) (cpt A)) (fm c p ≫ 𝟙 _) c (pullback.fst p (cpt A)) := by
    rw [Category.comp_id]; exact (fm_isPullback c p).flip
  have big := (IsPullback.of_hasPullback (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s)).paste_horiz sq2
  have hsnd : Eqv _ (sch.map (pullback.snd (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) (tw q i) := by
    rw [← big.isoPullback_hom_snd, Functor.map_comp]; exact eqv_comp (eqv_iso _ q i) core
  refine eqv_left (g := sch.map (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) ?_
    (eqv_iso (asIso (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) q i)
  rw [← Functor.map_comp]
  convert hsnd using 2
  rw [pullback.map]; erw [pullback.lift_snd]; exact Category.comp_id _

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSHS : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, SH (S.presheaf.stalk x)

def QuotSH : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R'), Function.Surjective f → SH R → SH R'

theorem StalkSH_of (hS : StalkSHS) (hQ : QuotSH) : StalkSH := by
  intro A _ _ S p hSs s
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks (pullback.fst p (cpt A)) := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  exact hQ _ _ ((pullback.fst p (cpt A)).stalkMap s).hom ((pullback.fst p (cpt A)).stalkMap_surjective s) (hS S hSs _)

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

theorem quotSH : QuotSH := by
  intro R R' _ _ _ f hf ⟨hH, hK⟩
  have hl : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hmem : ∀ x, f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩
  refine ⟨⟨fun g hg a₀' h0 h1 => ?_⟩, ?_⟩
  · obtain ⟨G, hGm, -, hGmon⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts g).2 fun n => hf _) hg
    obtain ⟨a₀, rfl⟩ := hf a₀'
    have e0 : f (G.eval a₀) = g.eval (f a₀) := by rw [← hGm, Polynomial.eval_map, eval₂_at_apply]
    have e1 : f (G.derivative.eval a₀) = g.derivative.eval (f a₀) := by
      rw [← hGm, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian G hGmon a₀ ((hmem _).1 (e0 ▸ h0))
      (isUnit_of_map_unit f _ (e1 ▸ h1))
    refine ⟨f a, ?_, ?_⟩
    · rw [IsRoot, ← hGm, Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
    · rw [← map_sub]; exact (hmem _).2 ha'
  · have hs : Function.Surjective (ResidueField.map f) := by
      intro y
      obtain ⟨y, rfl⟩ := residue_surjective y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨residue R x, ResidueField.map_residue f x⟩
    refine IsSepClosed.of_exists_root _ fun p hpm hpi hps => ?_
    obtain ⟨P, hP, hdeg, -⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts p).2 fun n => hs _) hpm
    have hPs : P.Separable := (separable_map (ResidueField.map f)).1 (hP ▸ hps)
    have hPd : P.degree ≠ 0 := by
      have := hpi.natDegree_pos
      intro h; rw [natDegree_eq_zero_iff_degree_le_zero.2 h.le] at hdeg; omega
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hPd hPs
    exact ⟨ResidueField.map f x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx.eq_zero]; simp⟩

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

theorem aic_root {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : ∀ (n : ℕ) (f : R[X]), f.Monic → f.natDegree = n →
    ∀ a₀, f.eval a₀ ∈ maximalIdeal R → ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hm hd a₀ h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hm hd, eval_one] at h0
    exact absurd ((Ideal.eq_top_iff_one _).2 h0) (maximalIdeal.isMaximal R).ne_top
  | succ n ih =>
    intro f hm hd a₀ h0
    obtain ⟨b, hb⟩ := h f hm (by omega)
    have hf : (X - C b) * (f /ₘ (X - C b)) = f := by rw [mul_divByMonic_eq_iff_isRoot]; exact hb
    have hgm : (f /ₘ (X - C b)).Monic := (monic_X_sub_C b).of_mul_monic_left (by rw [hf]; exact hm)
    have hgd : (f /ₘ (X - C b)).natDegree = n := by rw [natDegree_divByMonic f (monic_X_sub_C b), natDegree_X_sub_C]; omega
    rw [← hf, eval_mul, eval_sub, eval_X, eval_C] at h0
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h0 with h1 | h2
    · exact ⟨b, hb, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨a, ha, ha'⟩ := ih _ hgm hgd a₀ h2
      exact ⟨a, by rw [IsRoot, ← hf, eval_mul, ha.eq_zero, mul_zero], ha'⟩

theorem sh_of_aic {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : SH R := by
  refine ⟨{ is_henselian := fun f hf a₀ h0 _ => aic_root h _ f hf rfl a₀ h0 }, ?_⟩
  refine IsSepClosed.of_exists_root _ fun p hpm hpi _ => ?_
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).2 fun n => residue_surjective _) hpm
  obtain ⟨x, hx⟩ := h P hPm (by have := hpi.natDegree_pos; omega)
  exact ⟨residue R x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx]; simp⟩

theorem stalkSHS_of (hA : StalkAIC) : StalkSHS := fun S hS x => sh_of_aic (hA S hS x)

end LateralTheory.E.FibStalkPf
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.PartDiagCut

structure Part (A : Type) [CommRing A] : Type where

  blocks : Finset A
  idem : ∀ e ∈ blocks, IsIdempotentElem e ∧ e ≠ 0
  orth : ∀ e ∈ blocks, ∀ e' ∈ blocks, e ≠ e' → e * e' = 0
  sum_eq : ∑ e ∈ blocks, e = 1

instance (A : Type) [CommRing A] : Preorder (Part A) where
  le P Q := ∀ e' ∈ Q.1, ∃ e ∈ P.1, e' * e = e'
  le_refl P := fun e he => ⟨e, he, (P.idem e he).1.eq⟩
  le_trans P Q R hPQ hQR := fun e'' he'' => by
    obtain ⟨e', he', h1⟩ := hQR e'' he''
    obtain ⟨e, he, h2⟩ := hPQ e' he'
    exact ⟨e, he, by rw [← h1, mul_assoc, h2]⟩

variable {B : Type} [CommRing B]

def S (I : Ideal B) (e : B ⧸ I) : Submonoid B where
  carrier := {s | ∃ t, Ideal.Quotient.mk I s * t * e = e}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨t, ht⟩ ⟨u, hu⟩
    refine ⟨t * u, ?_⟩
    show Ideal.Quotient.mk I (a * b) * (t * u) * e = e
    rw [map_mul]
    calc _ = Ideal.Quotient.mk I a * t * (Ideal.Quotient.mk I b * u * e) := by ring
      _ = e := by rw [hu, ht]

theorem S_mono (I : Ideal B) {e e' : B ⧸ I} (h : e' * e = e') : S I e ≤ S I e' := by
  rintro s ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc Ideal.Quotient.mk I s * t * e' = Ideal.Quotient.mk I s * t * (e' * e) := by rw [h]
    _ = e' * (Ideal.Quotient.mk I s * t * e) := by ring
    _ = e' := by rw [ht, h]

abbrev PiLocalization₂ (I : Ideal B) (P : Part (B ⧸ I)) : Type := ∀ e : P.1, Localization (S I e.1)

def par {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : P.1 :=
  ⟨Classical.choose (h e.1 e.2), (Classical.choose_spec (h e.1 e.2)).1⟩

theorem par_spec {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : e.1 * (par h e).1 = e.1 :=
  (Classical.choose_spec (h e.1 e.2)).2

def stageMap (I : Ideal B) {P Q : Part (B ⧸ I)} (h : P ≤ Q) : PiLocalization₂ I P →+* PiLocalization₂ I Q :=
  RingHom.pi fun e => (IsLocalization.map (M := S I (par h e).1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B)
    (S_mono I (par_spec h e)) : Localization (S I (par h e).1) →+* _).comp (Pi.evalRingHom _ (par h e))

def βP (I : Ideal B) (P : Part (B ⧸ I)) : B →+* PiLocalization₂ I P :=
  RingHom.pi fun e => algebraMap B (Localization (S I e.1))

def DiagId : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (h : P ≤ P),
  stageMap I h = RingHom.id (PiLocalization₂ I P)

def DiagComp : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q R : Part (B ⧸ I)) (h1 : P ≤ Q) (h2 : Q ≤ R),
  stageMap I (h1.trans h2) = (stageMap I h2).comp (stageMap I h1)

def DiagNat : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q : Part (B ⧸ I)) (h : P ≤ Q),
  (stageMap I h).comp (βP I P) = βP I Q

def PartDirected : Prop := ∀ (A : Type) [CommRing A], IsDirected (Part A) (· ≤ ·) ∧ Nonempty (Part A)

def StageProd : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∀ P : Part (B ⧸ I), ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
    (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (PiLocalization₂ I P ≃+* ∀ k, R k)

def PartA : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)),
  Function.Bijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map)

def PartB : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (x : PiLocalization₂ I P),
  x ∈ I.map (βP I P) → IsUnit (1 + x)

def PartC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P), p.Monic → p.eval a₀ ∈ I.map (βP I P) →
    IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (p.derivative.eval a₀)) →
    ∃ (Q : Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
      a - stageMap I h a₀ ∈ I.map (βP I Q)

def diag (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) : Part (B ⧸ I) ⥤ CommRingCat.{0} where
  obj P := CommRingCat.of (PiLocalization₂ I P)
  map f := CommRingCat.ofHom (stageMap I (leOfHom f))
  map_id P := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_id, CommRingCat.hom_ofHom]
    exact hid B I P _
  map_comp f g := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact hcomp B I _ _ _ _ _

def diagβ (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) :
    (Functor.const _).obj (CommRingCat.of B) ⟶ diag I hid hcomp where
  app P := CommRingCat.ofHom (βP I P)
  naturality P Q f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    change βP I Q x = stageMap I (leOfHom f) (βP I P x)
    rw [← RingHom.comp_apply, hnat]

theorem goal_of (hdir : PartDirected) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) (hprod : StageProd)
    (ha : PartA) (hb : PartB) (hc : PartC) : LateralTheory.E.HensCut.PartDiag := by
  intro q B _ _ I hB hq
  have := (hdir (B ⧸ I)).1
  have := (hdir (B ⧸ I)).2
  refine ⟨Part (B ⧸ I), inferInstance, inferInstance, diag I hid hcomp, diagβ I hid hcomp hnat, ?_, ?_, ?_, ?_⟩
  · intro P; exact hprod q B I hB hq P
  · intro P; exact ha B I P
  · intro P x hx
    refine ⟨P, 𝟙 P, ?_⟩
    rw [(diag I hid hcomp).map_id, CommRingCat.hom_id]
    exact hb B I P x hx
  · intro P p a₀ hp h1 h2
    obtain ⟨Q, h, a, h3, h4⟩ := hc B I hB P p a₀ hp h1 h2
    exact ⟨Q, homOfLE h, a, h3, h4⟩

end LateralTheory.E.PartDiagCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

theorem LateralTheory.E.ProEqvPf.stageA (hC : Cont) (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y)
    (hc : ClopenSys y D c ι) (hp : ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) (n : ℤ)
    (x : Ht q (sch.obj Y) n i) (hx : pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0) :
    ∃ j, pull _ (sch.map (ι j)) _ _ x = 0 := by
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have e1 : pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n
      (pull _ (sch.map (c.π.app j0 ≫ ι j0)) (tw q i) n x) = pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n 0 := by
    rw [map_zero, ← pull_comp, ← Functor.map_comp]
    have : pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A) ≫ c.π.app j0 ≫ ι j0 =
        fm (c.π.app j0 ≫ ι j0) g ≫ pullback.fst g (cpt A) := by
      unfold fm pullback.map; rw [pullback.lift_fst]
    rw [this, Functor.map_comp, pull_comp, hx, map_zero]
  have e2 := (hp j0 n).1 e1
  rw [Functor.map_comp, pull_comp] at e2
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  obtain ⟨k, f, hk⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).2 j0 _ e2
  refine ⟨k, ?_⟩
  rw [← (hD f).1, Functor.map_comp, pull_comp]
  exact hk

namespace LateralTheory.E.ProEqvPf

def StageB : Prop := Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

theorem stage_of (hB : StageB) : PiLocalization₂ := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n
  exact ⟨fun x hx => stageA hC H q i A hq g y D c ι hc hp n x hx, hB hC H q i A hq g y D c ι hc hp n⟩

theorem etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue (hC : Cont) (hM : MV) (hB : StageB) (hG : Glue) : ProEqv :=
  ProEqv_of hC hM (stage_of hB) hG

end LateralTheory.E.ProEqvPf
end
end

section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LocalizationIntegralClosure

theorem aic_loc (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B) (hB : AIC B) :
    AIC (Localization M) := by
  classical
  intro p hp hd
  set L := Localization M
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (R := B) M
    ((Finset.range (p.natDegree + 1)).image p.coeff) (S := L)
  set t : L := algebraMap B L (s : B) with ht
  have hlift : scaleRoots p t ∈ lifts (algebraMap B L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_or_ge i p.natDegree with hi | hi
    · obtain ⟨c, hc⟩ := hs (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (s : B) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, pow_succ, Algebra.smul_def, ← ht]
      ring
    · rcases eq_or_lt_of_le hi with h | h
      · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
      · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hp)
  obtain ⟨b, hb⟩ := hB q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := IsLocalization.map_units L s
  refine ⟨algebraMap B L b * ((u⁻¹ : Lˣ) : L), ?_⟩
  have h1 : (scaleRoots p t).eval (algebraMap B L b) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, hb, map_zero]
  have h2 : (scaleRoots p t).eval (t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L))) =
      t ^ p.natDegree * p.eval (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) :=
    scaleRoots_eval₂_mul (p := p) (RingHom.id L) (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) t
  have h3 : t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) = algebraMap B L b := by
    rw [ht, ← hu, mul_comm (algebraMap B L b), ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1] at h2
  have hunit : IsUnit (t ^ p.natDegree) := (hu ▸ u.isUnit).pow _
  exact (hunit.mul_right_eq_zero).1 h2.symm

theorem LocAIC_of : LateralTheory.E.HensCut.LocAIC := by
  intro B _ _ M h0 hB
  have hle : M ≤ nonZeroDivisors B := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))
  exact ⟨IsLocalization.isDomain_localization hle, aic_loc B M hB⟩

end LateralTheory.E.LocalizationIntegralClosure
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
end
end
