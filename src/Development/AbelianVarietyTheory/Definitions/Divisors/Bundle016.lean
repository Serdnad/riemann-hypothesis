module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
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

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def wSub (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ w0 ^ r, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

abbrev LevGrp (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Type :=
  (D.La ⧸ wSub D w0 r) ≃ₗ[D.O] (D.La ⧸ wSub D w0 r)

def IsEtPlace (b : Base D R) (w0 : Ideal (𝓞 D.F)) : Prop :=
  w0.IsMaximal ∧ (p : 𝓞 D.F) ∈ w0 ∧ (∀ i, Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) = ⊤) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k) (φ : 𝓞 D.F →+* k), RingHom.ker φ = w0 → φ D.ω = β b.ρ

def IsEtLev {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (lv : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, lv x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ y, toUnit (Over.mk x) ≫ lv y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, toUnit (Over.mk x) ≫ lv y = g

structure EtModel (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : Obj b N s
  lv : D.La → (𝟙_ (Over X) ⟶ univ.A)
  isLev : IsEtLev univ w0 r lv
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s') (l : D.La → (𝟙_ (Over S) ⟶ o.A)),
    IsEtLev o w0 r l → ∃! f : S ⟶ X, f ≫ s = s' ∧ ∃ m : ObjMap o univ f, ∀ y, (l y).left ≫ m.φ = f ≫ (lv y).left

end GlobalTheory.UPel.HT.EtLev
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]



include hI hs in
theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add (f := _), e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}



end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)



variable {C : Type} [Category.{0} C]




end Line

end GlobalTheory.Obs.Model
end
end

section

noncomputable section

namespace GlobalTheory.KS

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

abbrev pow (A : Over S) (m : ℕ) : Over S := ∏ᶜ fun _ : Fin m => A

abbrev pr (A : Over S) {m : ℕ} (i : Fin m) : pow A m ⟶ A := Pi.π (fun _ : Fin m => A) i

def matEnd {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : pow A m ⟶ pow A m :=
  Pi.lift fun i => (List.ofFn fun j => pr A j ≫ act.act (M i j)).prod

def powMap {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (h : φ ≫ A.hom = A'.hom ≫ f)
    (m : ℕ) : (pow A' m).left ⟶ (pow A m).left :=
  (Pi.lift (fun i => Over.homMk ((pr A' i).left ≫ φ) (by
    rw [Category.assoc, h, ← Category.assoc, Over.w]; rfl)) : Over.mk ((pow A' m).hom ≫ f) ⟶ pow A m).left

variable {B B' : Scheme.{0}}

abbrev ksBC (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : Scheme.{0} := pullback ((pow A m).hom ≫ p) b

def matBC {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (M : Matrix (Fin m) (Fin m) O) :
    ksBC A m p b ⟶ ksBC A m p b :=
  pullback.map _ _ _ _ (matEnd act M).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp)

variable (l : ℕ) [Fact l.Prime] (E : Type) [CommRing E] [Algebra ℚ_[l] E]

abbrev HE (Y : Scheme.{0}) (n : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n 0

def pullE {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : HE l E Y' n →ₗ[E] HE l E Y n :=
  (pullHQ l (sch.map u) n 0).baseChange E

variable {E}

def op {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n : ℤ) : Module.End E (HE l E (ksBC A m p b) n) :=
  ε.sum fun M c => c • pullE l E (matBC act p b M) n


variable (E) in
abbrev HEt (Y : Scheme.{0}) (n t : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n t



end GlobalTheory.KS
end
end
