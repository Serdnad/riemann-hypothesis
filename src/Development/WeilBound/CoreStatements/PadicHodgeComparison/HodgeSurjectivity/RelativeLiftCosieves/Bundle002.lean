module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle073
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris
open GlobalTheory.CatH (face toLast)

universe w v u

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace RelativeFormLift

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def liftS {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (s : ComposableArrows C n) (hs : Q (s.obj 0)) :
    ComposableArrows Q.FullSubcategory n :=
  Q.lift s fun k => hQ (s.map (homOfLE (Fin.zero_le _))) hs


open Classical in
def extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) : CH.Cn F n :=
  fun s => if hs : Q (s.obj 0) then b (liftS hQ s hs) else 0

theorem d_extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) (s : ComposableArrows C (n + 1))
    (hs : Q (s.obj 0)) : CH.d F n (extZ F hQ b) s = CH.d (Q.ι ⋙ F) n b (liftS hQ s hs) := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (extZ F hQ b (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((Q.ι ⋙ F).map (toLast i (liftS hQ s hs))).hom (b (face i (liftS hQ s hs)))
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Q ((face i s).obj 0) := hQ (s.map (homOfLE (Fin.zero_le _))) hs
  have e : extZ F hQ b (face i s) = b (liftS hQ (face i s) h) := dif_pos h
  rw [e]
  rfl

end RelativeFormLift


open RelativeFormLift in
theorem relLiftOf_pf : RelLiftOf := by
  intro hS hO K _ W Z q i _ a n y hy
  have hQ : Cosieve (On q i) := (hS K W Z W q i i).2.1
  have hQ' : Cosieve ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) :=
    fun _ _ f h => ⟨trivial, hQ f h.2⟩
  have h : ∀ T, (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))) T →
      ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) ((smS i rfl).G.obj T) := fun T _ =>
    ⟨trivial, ((hS K W Z W q i i).2.2.2.2.2 T).1
      ⟨pullback.lift (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T)
        (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T) rfl,
        pullback.lift_snd _ _ _⟩⟩
  have hbij := hO K W Z q i ⊤ ⊤ h (fun _ _ => trivial) a n
  obtain ⟨⟨z₀, hz₀⟩, hy0⟩ := Submodule.Quotient.mk_surjective
    (((CH.cx (G q a)).B n).submoduleOf ((CH.cx (G q a)).Z n)) (show (CH.cx (G q a)).H n from y)
  have hz₀' : CH.d (G q a) n z₀ = 0 := hz₀
  subst hy0
  set w₀ := (CH.Mor.restrict (G q a) ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι).pullC n z₀ with hw
  have hw₀ : CH.d _ n w₀ = 0 := by rw [hw, CH.Mor.d_pullC, hz₀', map_zero]
  have e1 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) =
      (CH.Mor.restrict (G (i ≫ q) a) (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))).ι).pull n
        (pullH i rfl a n (Submodule.Quotient.mk ⟨z₀, hz₀⟩)) := rfl
  have e2 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) = 0 := by
    rw [e1, hy, map_zero]
  have e3 : (CH.cx _).cls w₀ hw₀ = 0 := hbij.1 (by rw [e2, map_zero])
  have e4 : w₀ ∈ (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).B n :=
    (Submodule.Quotient.mk_eq_zero (((CH.cx _).B n).submoduleOf ((CH.cx _).Z n))
      (x := (⟨w₀, hw₀⟩ : (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).Z n))).1 e3
  cases n with
  | zero =>
    have e5 : w₀ = 0 := (Submodule.mem_bot K).1 e4
    refine ⟨z₀, hz₀', fun s hs => ?_, rfl⟩
    exact congrFun e5 (liftS hQ' s ⟨trivial, hs⟩)
  | succ m =>
    obtain ⟨b', hb'⟩ := e4
    have hz : CH.d (G q a) (m + 1) (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) = 0 := by
      rw [map_sub, hz₀', CH.d_d, sub_zero]
    refine ⟨z₀ - CH.d (G q a) m (extZ (G q a) hQ' b'), hz, fun s hs => ?_, ?_⟩
    · change z₀ s - CH.d (G q a) m (extZ (G q a) hQ' b') s = 0
      rw [d_extZ (G q a) hQ' b' s ⟨trivial, hs⟩]
      rw [hb']
      exact sub_self _
    · show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq]
      refine ⟨-extZ (G q a) hQ' b', ?_⟩
      rw [map_neg]
      change -(CH.d (G q a) m (extZ (G q a) hQ' b')) = (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) - z₀
      abel

end CrystallineSemistableComparison.Onto

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Onto

theorem topRes_pf : TopRes := by
  intro R _ C _ F U Q hU n
  let L : C ⥤ U.FullSubcategory := U.lift (𝟭 C) hU
  have back : ∀ z : CH.Cn F n, ∀ s : ComposableArrows C n,
      (CH.Mor.restrict F U.ι).pullC n z (s ⋙ L) = z s := fun _ _ => rfl
  refine ⟨⟨fun z z' h => funext fun s => ?_, fun w => ⟨fun s => w (s ⋙ L), ?_⟩⟩, fun z => ⟨?_, ?_⟩⟩
  · rw [← back z s, ← back z' s, h]
  · funext t
    rfl
  · intro hz s hs
    rw [← back z s]
    exact hz (s ⋙ L) hs
  · intro hz t ht
    exact hz (t ⋙ U.ι) ht

end CrystallineSemistableComparison.Onto

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace OmegaRestriction

variable {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))

def phi {V V' : Z.Opens} (h : V' ≤ V) : Sec q V →ₐ[K] Sec q V' :=
  { (rs h : Γ(Z, V) →+* Γ(Z, V')) with
    commutes' := fun r => by
      have e : q.appLE ⊤ V le_top ≫ Z.presheaf.map (homOfLE h).op = q.appLE ⊤ V' le_top :=
        Scheme.Hom.appLE_map _ _ _
      exact congrArg (fun f => ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f).hom r) e }

theorem ev_res {V V' : Z.Opens} (h : V' ≤ V) (T : Thick (smFun Z q)) (hT : inU q V' T) (hT' : inU q V T)
    (g : Γ(Z, V)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T hT (rs h g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T hT' g := by
  unfold ev GlobalTheory.Cris.evalAt rs
  have e : (pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE V ⊤ hT' =
      Z.presheaf.map (homOfLE h).op ≫
        (pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE V' ⊤ hT := by
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rfl

def anyLift {V : Z.Opens} (T : (inU q V).FullSubcategory) (g : Sec q V) : T.obj.B :=
  (Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose

theorem anyLift_spec {V : Z.Opens} (T : (inU q V).FullSubcategory) (g : Sec q V) :
    Ideal.Quotient.mk T.obj.J (anyLift q T g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g :=
  (Ideal.Quotient.mk_surjective _).choose_spec

theorem lifts_nonempty (V : Z.Opens) : Nonempty (Lifts q V) :=
  ⟨{ v := fun T g => anyLift q T g
     hv := fun T g => anyLift_spec q T g }⟩


open Classical in
def ext {V V' : Z.Opens} (h : V' ≤ V) (Λ' : Lifts q V') : Lifts q V where
  v T g := if hT : inU q V' T.obj then Λ'.v ⟨T.obj, hT⟩ (rs h g) else anyLift q T g
  hv T g := by
    by_cases hT : inU q V' T.obj
    · rw [dif_pos hT]
      exact (Λ'.hv ⟨T.obj, hT⟩ (rs h g)).trans (ev_res q h T.obj hT T.property g)
    · rw [dite_eq_right hT]
      exact anyLift_spec q T g

theorem ext_v {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (Λ' : Lifts q V')
    (T : (inU q V').FullSubcategory) (g : Sec q V) :
    (ext q h Λ').v ((ObjectProperty.ιOfLE k).obj T) g = Λ'.v T (rs h g) :=
  dif_pos T.property

theorem ext_form {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (Λ' : Lifts q V') {a : ℕ}
    (g₀ : Sec q V) (g : Fin a → Sec q V) (s : ComposableArrows (inU q V').FullSubcategory a) :
    (ext q h Λ').form g₀ g (s ⋙ ObjectProperty.ιOfLE k) = Λ'.form (rs h g₀) (fun j => rs h (g j)) s := by
  have hv : ∀ (j : Fin (a + 1)) (x : Sec q V),
      (ext q h Λ').v ((s ⋙ ObjectProperty.ιOfLE k).obj j) x = Λ'.v (s.obj j) (rs h x) :=
    fun j x => ext_v q h k Λ' (s.obj j) x
  simp only [Lifts.form, hv]
  rfl

theorem form_uniq {V : Z.Opens} {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V} {c c' : HV q V a a}
    (hc : IsForm q V g₀ g c) (hc' : IsForm q V g₀ g c') : c = c' := by
  obtain ⟨Λ⟩ := lifts_nonempty q V
  obtain ⟨f, hf, rfl, hfs⟩ := hc Λ
  obtain ⟨f', hf', rfl, hfs'⟩ := hc' Λ
  have e : f = f' := funext fun s => Subtype.ext ((hfs s).trans (hfs' s).symm)
  subst e
  rfl

theorem isForm_res {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) {a : ℕ} (g₀ : Sec q V)
    (g : Fin a → Sec q V) (c : HV q V a a) (hc : IsForm q V g₀ g c) :
    IsForm q V' (phi q h g₀) (fun j => phi q h (g j)) ((resU (G q a) k).pull a c) := by
  intro Λ'
  obtain ⟨f, hf, rfl, hfs⟩ := hc (ext q h Λ')
  refine ⟨(resU (G q a) k).pullC a f, ?_, rfl, fun s => ?_⟩
  · exact (CH.Mor.d_pullC _ a f).trans ((congrArg _ hf).trans (map_zero _))
  · exact (hfs (s ⋙ ObjectProperty.ιOfLE k)).trans (congrArg _ (ext_form q h k Λ' g₀ g s))

theorem isOm_res {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (hFL : FormLaws) (a : ℕ)
    (e : Om K (Sec q V) a →ₗ[K] HV q V a a) (e' : Om K (Sec q V') a →ₗ[K] HV q V' a a)
    (he : IsOm q V a e) (he' : IsOm q V' a e') (ω : Om K (Sec q V) a) :
    (resU (G q a) k).pull a (e ω) = e' (omMap (phi q h) a ω) := by
  have key : ((resU (G q a) k).pull a).comp e = e'.comp (omMap (phi q h) a) := by
    refine LinearMap.ext_on (hFL K (Sec q V) (Sec q V') a).1 ?_
    rintro _ ⟨g₀, g, rfl⟩
    change (resU (G q a) k).pull a (e (form K g₀ g)) = e' (omMap (phi q h) a (form K g₀ g))
    rw [((hFL K (Sec q V) (Sec q V') a).2 (phi q h)).1]
    exact form_uniq q (isForm_res q h k g₀ g _ (he g₀ g)) (he' _ _)
  exact LinearMap.congr_fun key ω

end OmegaRestriction

theorem omRes_pf : OmRes := by
  intro K _ Z q V V' h k
  exact ⟨OmegaRestriction.phi q h, fun g => rfl, fun a g₀ g c hc => OmegaRestriction.isForm_res q h k g₀ g c hc,
    fun a e e' he he' ω => OmegaRestriction.isOm_res q h k GlobalTheory.T.onto_form_laws a e e' he he' ω⟩

end CrystallineSemistableComparison.Onto

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

theorem prod_mem_pdPow {b : Base} {L : b.Fun} (T : Thick L) : ∀ (n : ℕ) (f : Fin n → T.B), (∀ k, f k ∈ T.J) →
    ∏ k, f k ∈ T.pdPow n
  | 0, f, _ => by rw [Fin.prod_univ_zero, T.pdPow_zero]; trivial
  | n + 1, f, hf => by
    rw [Fin.prod_univ_succ, Pb.pdPow_eq]
    have := dividedPowerFiltration_mul T.δ 1 n (T.J_le_pdPow_one (hf 0)) (prod_mem_pdPow T n _ fun k => hf k.succ)
    rwa [Nat.add_comm] at this

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem lift_sub_mem (Λ : Lifts q V) {T T' : (inU q V).FullSubcategory} (f : T ⟶ T') (g : Sec q V) :
    f.hom.φ (Λ.v T g) - Λ.v T' g ∈ T'.obj.J := by
  rw [← Ideal.Quotient.eq, Λ.hv T' g]
  have e : Ideal.Quotient.mk T'.obj.J (f.hom.φ (Λ.v T g)) =
      Ideal.quotientMap T'.obj.J f.hom.φ f.hom.hle (Ideal.Quotient.mk T.obj.J (Λ.v T g)) := rfl
  rw [e, Λ.hv T g]
  exact (GlobalTheory.CompanionTheory.GrForm.ev_nat f.hom T.property T'.property g).symm

theorem lift_mul_mem (Λ : Lifts q V) (T : (inU q V).FullSubcategory) (g h : Sec q V) :
    Λ.v T g * Λ.v T h - Λ.v T (g * h) ∈ T.obj.J := by
  rw [← Ideal.Quotient.eq, map_mul, Λ.hv, Λ.hv, Λ.hv]
  exact (map_mul _ g h).symm

theorem comp_φ {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) {i j k : Fin (n + 1)} (hij : i ≤ j)
    (hjk : j ≤ k) (y : (s.obj i).obj.B) :
    (s.map (homOfLE hjk)).hom.φ ((s.map (homOfLE hij)).hom.φ y) = (s.map (homOfLE (hij.trans hjk))).hom.φ y := by
  rw [show (homOfLE (hij.trans hjk) : i ⟶ k) = homOfLE hij ≫ homOfLE hjk from rfl, s.map_comp]
  rfl

def lv (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1)) (x : Sec q V) :
    (s.obj (Fin.last n)).obj.B :=
  (s.map (homOfLE (Fin.le_last i))).hom.φ (Λ.v _ x)

theorem lv_sub_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - Λ.v _ x ∈ (s.obj (Fin.last n)).obj.J :=
  lift_sub_mem Λ _ x

theorem lv_diff_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i j : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - lv Λ s j x ∈ (s.obj (Fin.last n)).obj.J := by
  have := sub_mem (lv_sub_mem Λ s i x) (lv_sub_mem Λ s j x)
  rwa [sub_sub_sub_cancel_right] at this

theorem lv_last (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x : Sec q V) :
    lv Λ s (Fin.last n) x = Λ.v _ x := by
  unfold lv
  rw [show (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ from rfl, s.map_id]
  rfl

theorem form_eq (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) :
    Λ.form x₀ x s = Λ.v _ x₀ * ∏ k : Fin n, (lv Λ s k.succ (x k) - lv Λ s k.castSucc (x k)) := rfl

theorem form_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) : Λ.form x₀ x s ∈ (s.obj (Fin.last n)).obj.pdPow n := by
  rw [form_eq]
  exact Ideal.mul_mem_left _ _ (prod_mem_pdPow _ n _ fun k => lv_diff_mem Λ s _ _ _)

theorem form_map (Λ : Lifts q V) {m n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n)
    (e : Fin (m + 1) → Fin (n + 1)) (he : Monotone e) (x₀ : Sec q V) (x : Fin m → Sec q V) :
    (s.map (homOfLE (Fin.le_last (e (Fin.last m))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)) =
      lv Λ s (e (Fin.last m)) x₀ * ∏ k : Fin m, (lv Λ s (e k.succ) (x k) - lv Λ s (e k.castSucc) (x k)) := by
  rw [Lifts.form, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_sub]
  congr 1
  · exact comp_φ s (he (Fin.le_last k.succ)) (Fin.le_last _) _
  · exact comp_φ s (he (Fin.le_last k.castSucc)) (Fin.le_last _) _

theorem key (Λ : Lifts q V) {a a' : ℕ} (g₀ h₀ : Sec q V) (g : Fin a → Sec q V) (h : Fin a' → Sec q V)
    (s : ComposableArrows (inU q V).FullSubcategory (a + a')) :
    (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + a' = a + a') (Fin.last a))))).hom.φ
        (Λ.form g₀ g ((CH.front_mono (rfl : a + a' = a + a')).functor ⋙ s)) *
      (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + a' = a + a') (Fin.last a'))))).hom.φ
        (Λ.form h₀ h ((CH.back_mono (rfl : a + a' = a + a')).functor ⋙ s)) -
      Λ.form (g₀ * h₀) (Fin.append g h) s ∈ (s.obj (Fin.last (a + a'))).obj.pdPow (a + a' + 1) := by
  rw [form_map Λ s _ (CH.front_mono rfl), form_map Λ s _ (CH.back_mono rfl), form_eq Λ s, Fin.prod_univ_add]
  have e1 : ∀ k : Fin a, (Fin.castAdd a' k).succ = CH.front (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.front])
  have e2 : ∀ k : Fin a, (Fin.castAdd a' k).castSucc = CH.front (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.front])
  have e3 : ∀ k : Fin a', (Fin.natAdd a k).succ = CH.back (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.back]; omega)
  have e4 : ∀ k : Fin a', (Fin.natAdd a k).castSucc = CH.back (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.back])
  have e5 : CH.back (rfl : a + a' = a + a') (Fin.last a') = Fin.last (a + a') := Fin.ext (by simp [CH.back])
  simp only [Fin.append_left, Fin.append_right, e1, e2, e3, e4, e5, lv_last]
  have hF := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a
    (fun k => lv Λ s (CH.front rfl k.succ) (g k) - lv Λ s (CH.front rfl k.castSucc) (g k))
    fun k => lv_diff_mem Λ s _ _ _
  have hB := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a'
    (fun k => lv Λ s (CH.back rfl k.succ) (h k) - lv Λ s (CH.back rfl k.castSucc) (h k))
    fun k => lv_diff_mem Λ s _ _ _
  have hl : lv Λ s (CH.front rfl (Fin.last a)) g₀ * Λ.v _ h₀ - Λ.v _ (g₀ * h₀) ∈
      (s.obj (Fin.last (a + a'))).obj.J := by
    have := add_mem (Ideal.mul_mem_right (Λ.v _ h₀) _ (lv_sub_mem Λ s (CH.front rfl (Fin.last a)) g₀))
      (lift_mul_mem Λ _ g₀ h₀)
    convert this using 1
    ring
  have := dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ 1 (a + a')
    ((s.obj (Fin.last (a + a'))).obj.J_le_pdPow_one hl) (dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ a a' hF hB)
  rw [show 1 + (a + a') = a + a' + 1 by omega] at this
  rw [Pb.pdPow_eq]
  convert this using 1
  ring

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem term_eq (Λ : Lifts q V) {a n : ℕ}
    (f : CH.Cn (Pb.sq ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι) ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι)) a) (x₀ : Sec q V) (x : Fin a → Sec q V)
    (hf : ∀ s, (show sqM ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι)
      ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι) _ from f s).1 = Ideal.Quotient.mk _ (Λ.form x₀ x s))
    (s : ComposableArrows (inU q V).FullSubcategory n) (e : Fin (a + 1) → Fin (n + 1)) (he : Monotone e) :
    CH.term _ s f e he = sqMk (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))
      ((s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)))
      ((thFil (smFun Z q) (a : ℤ)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom
        (form_mem Λ (he.functor ⋙ s) x₀ x)) := by
  apply Subtype.ext
  exact congrArg (Ideal.quotientMap ((thFil (smFun Z q) ((a : ℤ) + 1)).S (s.obj (Fin.last n)).obj)
    (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ
    (fun z hz => (thFil (smFun Z q) ((a : ℤ) + 1)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom hz))
    (hf (he.functor ⋙ s))

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto

open Pb HT FormCupProduct

theorem formCup_pf : FormCup := by
  intro K _ Z q V a a' g₀ h₀ g h x y hx hy Hx Hy
  let P : CH.Pairing ((inU q V).ι ⋙ G q a) ((inU q V).ι ⋙ G q a') ((inU q V).ι ⋙ G q (a + a')) :=
    ⟨fun T => (grOk (smFun Z q) (rfl : a + a' = a + a')).pair.μ T.obj, fun φ => (grOk (smFun Z q) rfl).pair.nat φ.hom⟩
  obtain ⟨hz, ez⟩ := CrystallineSemistableComparison.P.cup_cls P rfl x y hx hy
  refine ⟨hz, fun Λ => ?_⟩
  obtain ⟨f, hf, ef, hfs⟩ := Hx Λ
  obtain ⟨f', hf', ef', hfs'⟩ := Hy Λ
  obtain ⟨hz', ez'⟩ := CrystallineSemistableComparison.P.cup_cls P rfl f f' hf hf'
  refine ⟨P.cupC rfl f f', hz', ez.symm.trans ((congrArg₂ (P.cup rfl) ef ef').trans ez'), fun s => ?_⟩
  change ((grOk (smFun Z q) (rfl : a + a' = a + a')).mul (CH.term _ s f (CH.front rfl) (CH.front_mono rfl))
    (CH.term _ s f' (CH.back rfl) (CH.back_mono rfl))).1 = _
  rw [term_eq Λ f g₀ g hfs s _ (CH.front_mono rfl), term_eq Λ f' h₀ h hfs' s _ (CH.back_mono rfl), MulOk.mul_mk]
  exact Ideal.Quotient.eq.2 (key Λ g₀ h₀ g h s)

end CrystallineSemistableComparison.Onto
end
end
