module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreField

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull

section Ring

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def homRing : Subring (AddMonoid.End (Additive (A ⟶ A))) where
  carrier := {f | ∃ u : A ⟶ A, IsMonHom u ∧ ∀ x : A ⟶ A, f (Additive.ofMul x) = Additive.ofMul (x ≫ u)}
  mul_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    exact ⟨v ≫ u, inferInstance, fun x => by
      change f (g _) = _
      rw [hg, hf, Category.assoc]⟩
  one_mem' := ⟨𝟙 A, inferInstance, fun x => by rw [Category.comp_id]; rfl⟩
  add_mem' := by
    rintro f g ⟨u, hu, hf⟩ ⟨v, hv, hg⟩
    refine ⟨u * v, by rw [Hom.mul_def]; infer_instance, fun x => ?_⟩
    rw [MonObj.comp_mul, ofMul_mul, ← hf, ← hg]; rfl
  zero_mem' := ⟨1, by rw [Hom.one_def]; infer_instance, fun x => by rw [MonObj.comp_one]; rfl⟩
  neg_mem' := by
    rintro f ⟨u, hu, hf⟩
    refine ⟨u⁻¹, by rw [Hom.inv_def]; infer_instance, fun x => ?_⟩
    rw [GrpObj.comp_inv, ofMul_inv, ← hf]; rfl

variable {A}

def toRing (u : A ⟶ A) [IsMonHom u] : homRing A :=
  ⟨MonoidHom.toAdditive (IsMonHom.monoidHom u A), u, inferInstance, fun _ => rfl⟩

theorem toRing_apply (u : A ⟶ A) [IsMonHom u] (x : A ⟶ A) :
    (toRing u).1 (Additive.ofMul x) = Additive.ofMul (x ≫ u) := rfl

theorem natCast_mul_apply (n : ℕ) (f : homRing A) (x : Additive (A ⟶ A)) :
    ((n : homRing A) * f).1 x = n • f.1 x := by
  rw [← nsmul_eq_mul]; rfl

theorem homRing_ext {f g : homRing A}
    (h : f.1 (Additive.ofMul (𝟙 A)) = g.1 (Additive.ofMul (𝟙 A))) : f = g := by
  obtain ⟨f, u, hu, hf⟩ := f
  obtain ⟨g, v, hv, hg⟩ := g
  have e : u = v := by
    simpa only [hf, hg, Category.id_comp, EmbeddingLike.apply_eq_iff_eq] using h
  subst e
  exact Subtype.ext (AddMonoidHom.ext fun x => (hf x.toMul).trans (hg x.toMul).symm)

noncomputable def iter (σ : A ≅ A) : ℕ → (A ≅ A)
  | 0 => Iso.refl A
  | m + 1 => iter σ m ≪≫ σ

omit [IsCommMonObj A] in
instance isMonHom_iter (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) : IsMonHom (iter σ m).hom := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 A))
  | succ m ih => exact inferInstanceAs (IsMonHom ((iter σ m).hom ≫ σ.hom))

theorem toRing_pow (σ : A ≅ A) [IsMonHom σ.hom] (m : ℕ) :
    toRing σ.hom ^ m = toRing (iter σ m).hom := by
  induction m with
  | zero => exact homRing_ext (by rw [toRing_apply]; simp [iter])
  | succ m ih =>
    rw [pow_succ', ih]
    exact homRing_ext (by
      change (toRing σ.hom).1 ((toRing (iter σ m).hom).1 _) = _
      simp only [toRing_apply, iter, Iso.trans_hom, Category.assoc])


omit [GrpObj A] [IsCommMonObj A] in
theorem hasGen_iter {L : LB A.left} (hL : L.IsLB) (σ : A ≅ A)
    (h : HasGen L (K := Fin 2) ![σ.hom.left, 𝟙 A.left] ![1, -1]) (m : ℕ) :
    HasGen L (K := Fin 2) ![(iter σ m).hom.left, 𝟙 A.left] ![1, -1] := by
  induction m with
  | zero =>
    exact (h.mul h.inv).of_formEq hL (fun U _ f => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, iter])
  | succ m ih =>
    exact ((h.pull (iter σ m).hom.left).mul ih).of_formEq hL (fun U _ f => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, iter])

theorem exists_iter_fix (σ : A ≅ A) [IsMonHom σ.hom] (T : Over S) (n : ℕ)
    [Finite {x : T ⟶ A // x ^ n = 1}] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x : T ⟶ A, x ^ n = 1 → x ≫ (iter σ m).hom = x := by
  let f : {x : T ⟶ A // x ^ n = 1} → {x : T ⟶ A // x ^ n = 1} := fun x =>
    ⟨x.1 ≫ σ.hom, by rw [← MonObj.pow_comp, x.2, MonObj.one_comp]⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((cancel_mono σ.hom).1 (congrArg Subtype.val h))
  let e : Equiv.Perm {x : T ⟶ A // x ^ n = 1} := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have he : ∀ (m : ℕ) x, ((e ^ m) x).1 = x.1 ≫ (iter σ m).hom := by
    intro m
    induction m with
    | zero => intro x; simp [iter]
    | succ m ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      change ((e ^ m) x).1 ≫ σ.hom = _
      rw [ih, iter, Iso.trans_hom, Category.assoc]
  refine ⟨orderOf e, (orderOf_pos e).ne', fun x hx => ?_⟩
  have := he (orderOf e) ⟨x, hx⟩
  rw [pow_orderOf_eq_one] at this
  exact this.symm

end Ring

theorem exists_odd_ne_zero (K : Type) [Field K] : ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : ((5 : ℕ) : K) = 0
  · refine ⟨11, by decide, by decide, fun h' => ?_⟩
    have : (1 : K) = ((11 : ℕ) : K) - 2 * ((5 : ℕ) : K) := by push_cast; ring
    rw [h, h'] at this
    simp at this
  · exact ⟨5, by decide, le_rfl, h⟩

theorem serre_algClosed :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u → (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) → (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), Odd n → 5 ≤ n → (n : K) ≠ 0 → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ^ n = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A) → (∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : ℕ), 3 ≤ M → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A := by
  intro hM hdiv hsep hfin hmink K _ _ P M hM3 σ hσ hL hfix
  obtain ⟨n, hodd, h5, hn⟩ := exists_odd_ne_zero K
  haveI := (hM _ P n (by omega)).1
  haveI := finite_torsion_of_isFinite_mul K P n
  obtain ⟨m, hm0, hm⟩ := exists_iter_fix σ (baseOver (Spec (CommRingCat.of K))) n
  have hord : (iter σ m).hom = 𝟙 P.A :=
    hfin K P n hodd h5 hn (iter σ m) inferInstance (hasGen_iter P.isLB σ hL m) hm
  have hu : IsMonHom (σ.hom * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (σ.hom * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix T x hx, Category.comp_id, mul_inv_cancel])
  have key : toRing σ.hom = 1 := by
    refine hmink (homRing P.A) M hM3 ?_ ?_ (toRing σ.hom) (toRing φ) m hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _, _, -⟩ := hM _ P k (by omega)
        haveI : Epi (mulA P.A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (mulA P.A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K P q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.SerreField
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NoBasePoint

theorem exists_section_mem {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (W : Y.Opens) (hW : (W : Set Y).Nonempty) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ Y, σ ≫ f = 𝟙 _ ∧ ∀ p, σ p ∈ W := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp f c hc, fun p =>
    (congrArg (· ∈ W) (pointOfClosedPoint_apply f c hc p)).mpr hcW⟩

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translPt_eq {T : Over S} (a : T ⟶ A) : translPt A a = (fst T A ≫ a) * snd T A := rfl

theorem ptSecT_translT {T : Over S} (a x : T ⟶ A) : ptSecT A x ≫ translT A a = ptSecT A (a * x) := by
  simp [ptSecT, translT, translPt_eq, comp_lift, MonObj.comp_mul]

theorem exists_two_points {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S)
    [LocallyOfFiniteType A.hom] [IsIntegral (Over.mk t ⊗ A).left] (D : (Over.mk t ⊗ A).left.Opens)
    (hD : (D : Set (Over.mk t ⊗ A).left).Nonempty) (x c : Over.mk t ⟶ A) :
    ∃ a : Over.mk t ⟶ A, (∀ p, (ptSecT A (a * x)).left p ∈ D) ∧ ∀ p, (ptSecT A (a⁻¹ * c)).left p ∈ D := by
  let T := Over.mk t
  let u₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x))
  let w₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x)⁻¹)
  let u₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((snd T A)⁻¹ * (fst T A ≫ c))
  let w₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ c) * (snd T A)⁻¹)
  have e₁ : w₁ ≫ u₁ = 𝟙 _ := by
    ext <;> simp [u₁, w₁, MonObj.comp_mul]
  have e₂ : w₂ ≫ u₂ = 𝟙 _ := by
    ext <;> simp [u₂, w₂, MonObj.comp_mul, GrpObj.comp_inv]
  have ne : ∀ u w : T ⊗ A ⟶ T ⊗ A, w ≫ u = 𝟙 _ → ((u.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty := by
    intro u w e
    obtain ⟨d, hd⟩ := hD
    refine ⟨w.left d, ?_⟩
    show u.left (w.left d) ∈ D
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact hd
  have hne : ((u₁.left ⁻¹ᵁ D ⊓ u₂.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty :=
    nonempty_preirreducible_inter (u₁.left ⁻¹ᵁ D).isOpen (u₂.left ⁻¹ᵁ D).isOpen (ne _ _ e₁) (ne _ _ e₂)
  have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Spec (CommRingCat.of K)) (fst T A).left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
  obtain ⟨σ, hσ, hm⟩ := exists_section_mem (Y := (T ⊗ A).left) (fst T A).left _ hne
  let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
    rw [← Over.w (fst T A), ← Category.assoc]
    exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
  have hf : σ' ≫ fst T A = 𝟙 T := Over.OverMorphism.ext hσ
  have f₁ : σ' ≫ u₁ = ptSecT A ((σ' ≫ snd T A) * x) := by
    simp [u₁, ptSecT, comp_lift, MonObj.comp_mul, hf, reassoc_of% hf]
  have f₂ : σ' ≫ u₂ = ptSecT A ((σ' ≫ snd T A)⁻¹ * c) := by
    simp [u₂, ptSecT, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, hf, reassoc_of% hf]
  refine ⟨σ' ≫ snd T A, fun p => ?_, fun p => ?_⟩
  · rw [← f₁]; exact (hm p).1
  · rw [← f₂]; exact (hm p).2

variable {L : LB A.left}

theorem unitAt_of_local (hL : L.IsLB) {T : Over S} [Subsingleton T.left] {I : Type} [Fintype I]
    (φ : I → ((T ⊗ A).left ⟶ A.left)) (ε : I → ℤ) (p : T.left) (V : T.left.Opens) (hp : p ∈ V)
    (c : LB.Gen ((LB.LinComb L φ ε).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) (y : (T ⊗ A).left) :
    UnitAt L φ ε y := by
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q p]; exact hp
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (T ⊗ A).left) ((fst T A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst T A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr hL ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_transl (hL : L.IsLB) {T : Over S} (θ : LB.Sec (LPow A L 1 T)) (k : (LPow A L 1 T).ι)
    (a : T ⟶ A) (y : (T ⊗ A).left) (hy : (translT A a).left y ∈ (T ⊗ A).left.basicOpen (θ.f k)) :
    UnitAt L (K := Fin 1) (fun _ => (translPt A a).left) (fun _ => 1) y := by
  refine UnitAt.congr hL ?_ ⟨pullSec θ (translT A a).left, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Over.comp_left, translT, lift_snd]
  · rw [sval_pullSec θ _ (𝟙 _) y hJ]
    exact isUnit_sval θ _ y hJ k hy

theorem exists_value_one (hL : L.IsLB) {T : Over S} [Subsingleton T.left] (n : ℤ) (x : T ⟶ A) (p : T.left)
    (h : UnitAt L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => n) ((ptSecT A x).left p)) :
    ∃ (s : LB.Sec (LPow A L n T))
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))),
      τ.IsGen ∧ IsValueAt A L n s x τ 1 := by
  obtain ⟨s, hs⟩ := h
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ ((ptSecT A x).left p))
  have hm := Good.mem hI (fun _ : Fin 1 => (snd T A).left) (𝟙 _)
  have hb : (ptSecT A x).left p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => I (𝟙 _ ≫ (snd T A).left))) :=
    ((T ⊗ A).left.mem_basicOpen _ _ hm).2 ((congrArg IsUnit (gs_eq (𝟙 _) _ _ hm _)).mp (hs I hI))
  let s' := GlobalTheory.EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A x).left
    (fun _ => x.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd]) (val_le A L x) s
  have hu : ∀ j, IsUnit (s'.f j) := fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun q hq => by
    obtain rfl : q = p := Subsingleton.elim _ _
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ q)
    have u := isUnit_sval s (ptSecT A x).left q hJ _ hb
    have e := sec_trans s (ptSecT A x).left q (val_le A L x j hq) (Good.mem hJ _ (ptSecT A x).left)
    have e' : gs (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) (s'.f j) =
        gs (𝟙 T.left ≫ (ptSecT A x).left) q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) :=
      (gs_res (𝟙 T.left) q (val_le A L x j) hq _).trans
        (gs_pull (𝟙 T.left) (ptSecT A x).left q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j)
          (val_le A L x j hq) (s.f j))
    rw [Category.id_comp] at e'
    exact (congrArg IsUnit ((gs_eq (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) hq _).symm.trans
      (e'.trans e))).mpr ((Units.isUnit _).mul u)
  refine ⟨s, ⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun j => ?_⟩
  rw [map_one, _root_.one_mul]
  rfl

end

theorem exists_sec_value_isUnit :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v := by
  intro hGI hsq hH0 _ S _ P K _ _ t n hn x
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ inferInstance inferInstance
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := hH0 S P K t 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hsq S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e1 : translPt P.A (1 : Over.mk t ⟶ P.A) = snd _ _ := by
    rw [translPt_eq, MonObj.comp_one, _root_.one_mul]
  obtain ⟨s, τ, hτ, hv⟩ := exists_value_one P.isLB ((m + 2 : ℕ) : ℤ) x p
    (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by
      simp [Fin.sum_univ_succ, e1]
      module) (main m 1))
  exact ⟨s, τ, 1, hτ, hv, isUnit_one⟩

end GlobalTheory.NoBasePoint
end
end
