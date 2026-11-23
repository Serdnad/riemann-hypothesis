module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_hom_of_ker_eq {P L M : Type} [CommRing P] [Field L] [Field M]
    (Φ : P →+* L) (Ψ : P →+* M) (h : RingHom.ker Φ = RingHom.ker Ψ) :
    ∃ (S : Subfield L) (e : S →+* M), ∃ hS : ∀ p, Φ p ∈ S, ∀ p, e ⟨Φ p, hS p⟩ = Ψ p := by
  haveI : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ
  let Q := P ⧸ RingHom.ker Φ
  let f1 : Q →+* L := RingHom.kerLift Φ
  have hf1 : Function.Injective f1 := RingHom.kerLift_injective Φ
  let f2 : Q →+* M := Ideal.Quotient.lift _ Ψ (fun a ha => by
    rw [h] at ha; exact ha)
  have hf2 : Function.Injective f2 :=
    RingHom.lift_injective_of_ker_le_ideal _ _ h.ge
  let i1 : FractionRing Q →+* L := IsFractionRing.lift hf1
  let i2 : FractionRing Q →+* M := IsFractionRing.lift hf2
  have h1 : ∀ p, i1 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Φ p := fun p => by
    simp only [i1, IsFractionRing.lift_algebraMap]
    exact RingHom.kerLift_mk Φ p
  have h2 : ∀ p, i2 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Ψ p := fun p => by
    simp only [i2, IsFractionRing.lift_algebraMap]
    rfl
  refine ⟨i1.fieldRange, i2.comp i1.rangeRestrictFieldEquiv.symm.toRingHom,
    fun p => ⟨_, h1 p⟩, fun p => ?_⟩
  have : i1.rangeRestrictFieldEquiv.symm ⟨Φ p, ⟨_, h1 p⟩⟩
      = algebraMap Q _ (Ideal.Quotient.mk _ p) := by
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (h1 p).symm
  rw [← h2 p, ← this]
  rfl

theorem exists_embedding_of_homogeneous_ker_eq :
    ∀ (o K σ : Type) [CommRing o] [Field K] (β : o →+* K) (em : o →+* ℂ) (u : σ → K) (w : σ → ℂ) (a₀ : σ), u a₀ ≠ 0 → Subfield.closure (Set.range β ∪ Set.range (fun a => u a / u a₀)) = ⊤ → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) = RingHom.ker (MvPolynomial.eval₂Hom em w) → ∃ (e : K →+* ℂ) (c : ℂ), c ≠ 0 ∧ e.comp β = em ∧ ∀ a, e (u a) = c * w a := by
  intro o K σ _ _ β em u w a₀ hu hcl hker
  let i0 : Polynomial K →+* RatFunc K := algebraMap _ _
  have hi0 : Function.Injective i0 := IsFractionRing.injective _ _
  set Φ₀ := MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
    (fun a => Polynomial.C (u a) * Polynomial.X) with hΦ₀
  have hk : RingHom.ker (i0.comp Φ₀) = RingHom.ker (MvPolynomial.eval₂Hom em w) := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff i0 hi0]
  obtain ⟨S, e, hS, he⟩ := exists_hom_of_ker_eq _ _ hk
  let j : K →+* RatFunc K := i0.comp Polynomial.C
  have hC : ∀ r, (i0.comp Φ₀) (MvPolynomial.C r) = j (β r) := fun r => by
    simp [hΦ₀, j]
  have hX : ∀ a, (i0.comp Φ₀) (MvPolynomial.X a) = j (u a) * i0 Polynomial.X := fun a => by
    simp [hΦ₀, j]
  have hT : i0 Polynomial.X ≠ 0 := (map_ne_zero_iff i0 hi0).2 Polynomial.X_ne_zero
  have hdiv : ∀ a, j (u a / u a₀)
      = (i0.comp Φ₀) (MvPolynomial.X a) / (i0.comp Φ₀) (MvPolynomial.X a₀) := fun a => by
    rw [hX, hX, map_div₀, mul_div_mul_right _ _ hT]
  have hj : ∀ x, j x ∈ S := by
    have : (⊤ : Subfield K) ≤ S.comap j := by
      rw [← hcl, Subfield.closure_le]
      rintro x (⟨r, rfl⟩ | ⟨a, rfl⟩)
      · show j (β r) ∈ S
        rw [← hC]; exact hS _
      · show j (u a / u a₀) ∈ S
        rw [hdiv]; exact S.div_mem (hS _) (hS _)
    exact fun x => this (Subfield.mem_top x)
  let e' : K →+* ℂ := e.comp (j.codRestrict S hj)
  have hw : w a₀ ≠ 0 := by
    intro h0
    have : MvPolynomial.X a₀ ∈ RingHom.ker (i0.comp Φ₀) := by
      rw [hk, RingHom.mem_ker]; simpa using h0
    rw [RingHom.mem_ker, hX] at this
    exact mul_ne_zero ((map_ne_zero j).2 hu) hT this
  have hr : ∀ a, e' (u a / u a₀) = w a / w a₀ := fun a => by
    have h1 := he (MvPolynomial.X a)
    have h2 := he (MvPolynomial.X a₀)
    rw [MvPolynomial.eval₂Hom_X'] at h1 h2
    rw [← h1, ← h2, ← map_div₀]
    exact congrArg e (Subtype.ext (hdiv a))
  have he0 : e' (u a₀) ≠ 0 := (map_ne_zero e').2 hu
  refine ⟨e', e' (u a₀) / w a₀, div_ne_zero he0 hw, ?_, fun a => ?_⟩
  · ext r
    have h1 := he (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h1
    rw [← h1]
    exact congrArg e (Subtype.ext (hC r).symm)
  · have h := hr a
    rw [map_div₀, div_eq_iff he0] at h
    rw [h]; ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace MinkDiv

variable {A : Type} [AddCommGroup A]

theorem iterate_eq (f g : A →+ A) (hfg : ∀ z, f z = z + g z) (y : A) (hy : g (g (g y)) = 0)
    (n : ℕ) : f^[n] y = y + n • g y + (n.choose 2) • g (g y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, hfg y,
      hfg (g y), hfg (g (g y)), hy, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    simp only [add_nsmul, smul_add, one_nsmul, add_zero]
    abel

theorem prime_case (l p : ℕ) (hl : l.Prime) (ho : Odd l) (hp : p.Prime) (f : A →+ A)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x)
    (hord : ∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[p] x = x)
    (hfix : ∀ x : A, l • x = 0 → f x = x) :
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  set g : A →+ A := f - AddMonoidHom.id A with hg
  have hfg : ∀ z, f z = z + g z := fun z => by simp [hg]
  have key : ∀ k : ℕ, ∀ x : A, l ^ (k + 1) • x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := hfix x (by simpa using hx)
      simp [hg, this]
    | succ k ih =>
      intro x hx
      have h1 : ∀ z : A, l • z = 0 → g z = 0 := fun z hz =>
        ih z (by rw [pow_succ, mul_smul, hz, smul_zero])
      have h2 : ∀ z : A, l ^ (k + 1 + 1) • z = 0 → l • g z = 0 := fun z hz => by
        rw [← map_nsmul]
        exact ih _ (by rw [← mul_smul, ← pow_succ]; exact hz)
      by_cases hpl : p = l
      · subst hpl
        obtain ⟨y, rfl⟩ := hdiv x
        have hy : p ^ (k + 1 + 1 + 1) • y = 0 := by rw [pow_succ, mul_smul]; exact hx
        have e1 : p • p • g y = 0 := by
          rw [← map_nsmul g p y]; exact h2 _ hx
        have e2 : p • g (g y) = 0 := by
          apply h2
          rw [pow_succ, pow_succ, mul_smul, mul_smul, e1, smul_zero]
        have e3 : g (g (g y)) = 0 := h1 _ e2
        have e4 := iterate_eq f g hfg y e3 p
        rw [hord y _ hy] at e4
        have h3 : 2 < p := by
          rcases hp.two_le.lt_or_eq with h | h
          · exact h
          · subst h; exact absurd ho (by decide)
        obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) h3
        rw [hc, mul_comm, mul_smul, e2, smul_zero, add_zero] at e4
        rw [map_nsmul]
        exact (add_eq_left.mp e4.symm)
      · have e1 : l • g x = 0 := h2 x hx
        have e2 : g (g x) = 0 := h1 _ e1
        have e4 := iterate_eq f g hfg x (by rw [e2, map_zero]) p
        rw [hord x _ hx, e2, smul_zero, add_zero] at e4
        have e5 : p • g x = 0 := add_eq_left.mp e4.symm
        have hc : Nat.Coprime p l := (Nat.coprime_primes hp hl).mpr hpl
        have d1 := addOrderOf_dvd_of_nsmul_eq_zero e5
        have d2 := addOrderOf_dvd_of_nsmul_eq_zero e1
        have d3 := Nat.dvd_gcd d1 d2
        rw [hc, Nat.dvd_one] at d3
        exact AddMonoid.addOrderOf_eq_one_iff.mp d3
  intro a x hx
  have := key a x (by rw [pow_succ', mul_smul, hx, smul_zero])
  rw [hfg, this, add_zero]

theorem add_case (l : ℕ) (hl : l.Prime) (ho : Odd l)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x) (r : ℕ) (hr : r ≠ 0) :
    ∀ f : AddMonoid.End A, (∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[r] x = x) →
    (∀ x : A, l • x = 0 → f x = x) →
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  induction r using induction_on_primes with
  | zero => exact absurd rfl hr
  | one => intro f h _ a x hx; exact h x a hx
  | prime_mul p b hp ih =>
    intro f hord hfix
    have hb : b ≠ 0 := by rintro rfl; simp at hr
    have hc : ((f ^ p : AddMonoid.End A) : A → A) = f^[p] := AddMonoid.End.coe_pow _ _ _
    have := ih hb (f ^ p)
      (fun x a hx => by rw [hc, ← Function.iterate_mul]; exact hord x a hx)
      (fun x hx => by rw [hc]; exact Function.iterate_fixed (hfix x hx) p)
    exact prime_case l p hl ho hp f hdiv
      (fun x a hx => by have h := this a x hx; rw [hc] at h; exact h) hfix

end MinkDiv

theorem minkowski_divisible : ∀ (Q : Type) [CommGroup Q] (l : ℕ) (u : Q ≃* Q) (r : ℕ), l.Prime → Odd l → 0 < r → (∀ x : Q, ∃ y : Q, y ^ l = x) → (∀ x, u^[r] x = x) → (∀ x, x ^ l = 1 → u x = x) → ∀ (x : Q) (a : ℕ), x ^ (l ^ a) = 1 → u x = x := by
  intro Q _ l u r hl ho hr hdiv hord hfix x a hx
  exact MinkDiv.add_case (A := Additive Q) l hl ho (fun x => hdiv x.toMul) r hr.ne'
    (MonoidHom.toAdditive u.toMonoidHom) (fun x _ _ => hord x.toMul) (fun x hx => hfix x.toMul hx)
    a (Additive.ofMul x) hx

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.LevQuot

variable {X Y : Scheme.{0}}

theorem isOpenImmersion_graph (r : X ⟶ Y) [Etale r] (f : X ⟶ X) (h : 𝟙 X ≫ r = f ≫ r) :
    IsOpenImmersion (pullback.lift (𝟙 X) f h) := by
  have hpost : (@IsOpenImmersion : MorphismProperty Scheme.{0}).HasOfPostcompProperty
      (@Etale : MorphismProperty Scheme.{0}) := by
    refine MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr ?_
    intro A B u hu
    have : Etale u := hu
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal u))
  have hsec : IsOpenImmersion (pullback.lift (𝟙 X) f h ≫ pullback.fst r r) := by
    rw [pullback.lift_fst]
    infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) _ (pullback.fst r r)
    (inferInstance : Etale (pullback.fst r r)) hsec

theorem appLE_congr_hom {Z : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  simp only [e]

theorem exists_geomPoint (Z : Scheme.{0}) (z : Z) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k)
    (w : Spec (CommRingCat.of k) ⟶ Z) (p : Spec (CommRingCat.of k)), w p = z := by
  let K := AlgebraicClosure (Z.residueField z)
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z, p, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem invariant_descends (r : X ⟶ Y) [Etale r] [QuasiCompact r] [Surjective r] {Γ : Type} (ρ : Γ → (X ⟶ X))
    (hρ : ∀ g, ρ g ≫ r = r)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Spec (CommRingCat.of k) ⟶ X), y ≫ r = y' ≫ r →
      ∃ g, y' = y ≫ ρ g) (V : Y.Opens) :
    Function.Injective (r.app V).hom ∧ ∀ f : Γ(X, r ⁻¹ᵁ V),
      (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom := by
  have hcond : ∀ g, 𝟙 X ≫ r = ρ g ≫ r := fun g => by rw [Category.id_comp, hρ g]
  have hpb := IsPullback.of_hasPullback r r
  have hsame : ∀ x : ↥(pullback r r), r (pullback.snd r r x) = r (pullback.fst r r x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hgW : pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V ≤ pullback.snd r r ⁻¹ᵁ r ⁻¹ᵁ V := fun x hx => by
    change r (pullback.snd r r x) ∈ V
    rw [hsame]
    exact hx
  have hinvle : ∀ g, r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V) := fun g y hy => by
    change r (ρ g y) ∈ V
    rw [← Scheme.Hom.comp_apply, hρ g]
    exact hy
  have key := fun s => GlobalTheory.FlatDescent.existsUnique_app_eq_iff r hpb V
    (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) rfl le_rfl hgW s
  have hcompat : r.app V ≫ (pullback.fst r r).appLE _ _ le_rfl =
      r.app V ≫ (pullback.snd r r).appLE _ _ hgW :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans
      ((appLE_congr_hom pullback.condition _ _ _ _).trans (Scheme.Hom.comp_appLE _ _ _ _ _))
  constructor
  · intro a b hab
    obtain ⟨c, -, huniq⟩ := (key ((r.app V).hom a)).mpr (congrArg (fun φ => φ.hom a) hcompat)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  · intro f hinv
    refine ExistsUnique.exists ((key f).mpr ?_)
    apply TopCat.Presheaf.section_ext (pullback r r).sheaf
    intro x hx
    obtain ⟨k, _, _, w, pt, hw⟩ := exists_geomPoint (pullback r r) x
    obtain ⟨g, hg⟩ := htr k (w ≫ pullback.fst r r) (w ≫ pullback.snd r r)
      (by simp only [Category.assoc, pullback.condition])
    obtain ⟨ι, hιfst, hιsnd, hιop⟩ : ∃ ι : X ⟶ pullback r r,
        ι ≫ pullback.fst r r = 𝟙 X ∧ ι ≫ pullback.snd r r = ρ g ∧ IsOpenImmersion ι :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, isOpenImmersion_graph r (ρ g) (hcond g)⟩
    have hwι : w = (w ≫ pullback.fst r r) ≫ ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιfst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, hιsnd, hg, Category.assoc]
    have hxι : x = ι ((w ≫ pullback.fst r r) pt) := by
      rw [← Scheme.Hom.comp_apply, ← hwι, hw]
    subst hxι
    have hfi : ∀ y, pullback.fst r r (ι y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, hιfst]
      rfl
    have hle : ι ⁻¹ᵁ (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) ≤ r ⁻¹ᵁ V := fun y hy => by
      change r (pullback.fst r r (ι y)) ∈ V at hy
      rw [hfi] at hy
      exact hy
    have e1 : (pullback.fst r r).appLE (r ⁻¹ᵁ V) _ le_rfl ≫ ι.app _ =
        X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιfst _ _ _ hle]
      dsimp only [Scheme.Hom.appLE]
      rw [Scheme.Hom.id_app]
      exact Category.id_comp _
    have e2 : (pullback.snd r r).appLE (r ⁻¹ᵁ V) _ hgW ≫ ι.app _ =
        (ρ g).appLE (r ⁻¹ᵁ V) (r ⁻¹ᵁ V) (hinvle g) ≫ X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hιsnd _ _ _ (hle.trans (hinvle g)), Scheme.Hom.appLE_map]
    apply (ConcreteCategory.bijective_of_isIso (ι.stalkMap _)).1
    erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have h1 := congrArg (fun φ => φ.hom f) e1
    have h2 := congrArg (fun φ => φ.hom f) e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
    rw [hinv g (hinvle g)] at h2
    exact h1.trans h2.symm

def autOver (r : X ⟶ Y) : Subgroup (Aut X) where
  carrier := {ρ | ρ.asIso.hom ≫ r = r}
  mul_mem' := fun {a b} ha hb => by
    show (b.asIso.hom ≫ a.asIso.hom) ≫ r = r
    rw [Category.assoc, ha, hb]
  one_mem' := Category.id_comp _
  inv_mem' := fun {a} ha => by
    show a.asIso.inv ≫ r = r
    exact (Iso.inv_comp_eq a.asIso).2 (Eq.symm ha)

theorem exists_liftAut {P Q : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ X} {q : Q ⟶ Y} {r : X ⟶ Y} (h : IsPullback φ p q r) :
    ∃ τ : autOver r →* Aut P, ∀ ω, (τ ω).asIso.hom ≫ φ = φ ∧ (τ ω).asIso.hom ≫ p = p ≫ ω.1.asIso.hom := by
  have hom_r : ∀ ω : autOver r, ω.1.asIso.hom ≫ r = r := fun ω => ω.2
  have inv_r : ∀ ω : autOver r, ω.1.asIso.inv ≫ r = r := fun ω => (Iso.inv_comp_eq ω.1.asIso).2 (hom_r ω).symm
  have sq : ∀ u : X ⟶ X, u ≫ r = r → φ ≫ q = (p ≫ u) ≫ r := fun u hu => by
    rw [Category.assoc, hu, h.w]
  have back : ∀ (u v : X ⟶ X) (hu : u ≫ r = r) (hv : v ≫ r = r), u ≫ v = 𝟙 X →
      h.lift φ (p ≫ u) (sq u hu) ≫ h.lift φ (p ≫ v) (sq v hv) = 𝟙 P := fun u v hu hv huv => by
    apply h.hom_ext
    · simp
    · simp only [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc, huv, Category.comp_id,
        Category.id_comp]
  let lift1 : autOver r → Aut P := fun ω =>
    Aut.of ⟨h.lift φ (p ≫ ω.1.asIso.hom) (sq _ (hom_r ω)),
      h.lift φ (p ≫ ω.1.asIso.inv) (sq _ (inv_r ω)),
      back _ _ (hom_r ω) (inv_r ω) ω.1.asIso.hom_inv_id,
      back _ _ (inv_r ω) (hom_r ω) ω.1.asIso.inv_hom_id⟩
  refine ⟨{ toFun := lift1, map_one' := ?_, map_mul' := ?_ }, fun ω => ⟨h.lift_fst _ _ _, h.lift_snd _ _ _⟩⟩
  · ext1
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = 𝟙 P ≫ φ
      rw [IsPullback.lift_fst, Category.id_comp]
    · change h.lift _ _ _ ≫ p = 𝟙 P ≫ p
      rw [IsPullback.lift_snd, Category.id_comp]
      exact Category.comp_id p
  · intro a b
    ext1
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = (h.lift φ (p ≫ b.1.asIso.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.asIso.hom) (sq _ (hom_r a))) ≫ φ
      simp only [IsPullback.lift_fst, Category.assoc]
    · change h.lift _ _ _ ≫ p = (h.lift φ (p ≫ b.1.asIso.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.asIso.hom) (sq _ (hom_r a))) ≫ p
      simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
      rfl

theorem exists_subgroup_of_finite {G : Type} [Group G] (S : Submonoid G) [Finite S] :
    ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ S := by
  refine ⟨{ S with inv_mem' := fun {x} hx => ?_ }, fun _ => Iff.rfl⟩
  have hx' : IsOfFinOrder x := by
    by_contra hne
    have hinj := injective_pow_iff_not_isOfFinOrder.mpr hne
    exact not_injective_infinite_finite (fun n : ℕ => (⟨x ^ n, S.pow_mem hx n⟩ : S))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  obtain ⟨n, hn⟩ := hx'.mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  rw [← hn]
  exact S.pow_mem hx n

end GlobalTheory.LevQuot
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem smooth_of_isPullback_of_surjective_of_flat :
    ∀ (X X' Y Y' : Scheme.{0}) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), IsPullback φ p p' π → Surjective π → Flat p' → LocallyOfFinitePresentation p' → Smooth p → Smooth p' := by
  intro X X' Y Y' π φ p p' h hπ hflat hlfp hsm

  refine Smooth.of_smooth_fiberToSpecResidueField p' fun y' => ?_

  obtain ⟨y, rfl⟩ := hπ.surj y'

  have hsq := (isPullback_fiberToSpecResidueField_of_isPullback h y).flip

  have hff : (π.residueFieldMap y).hom.FaithfullyFlat := by
    letI := (π.residueFieldMap y).hom.toAlgebra
    show Module.FaithfullyFlat _ _
    infer_instance
  obtain ⟨hF, hS⟩ := (flat_and_surjective_SpecMap_iff _).2 hff

  have hfib : Smooth (p.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField y)))

  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ⟨⟨hS, hF⟩, inferInstance⟩ hfib

end GlobalTheory
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.entire_antilinear_lattice_periods_const : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v → (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) → t = 0 ∧ ∀ z, v z = v 0 := by
  first | exact @GlobalTheory.entire_antilinear_periods_const | exact GlobalTheory.entire_antilinear_periods_const | (intros; apply GlobalTheory.entire_antilinear_periods_const <;> assumption)
end
