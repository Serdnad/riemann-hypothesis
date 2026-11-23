module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

def HolCoord : Prop :=
  ∀ (Z : Scheme.{0}) (n g : ℕ) (B : Set (Fin n → ℂ)) (e : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z)) (A : Type) [CommRing A]
    (v : Sp (DualNumber A) ⟶ Z) (ψ : (Fin n → ℂ) → (A →+* ℂ)) (w : (Fin n → ℂ) → Fin g → ℂ), IsOpen B →
    IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e bz.1 bz.2) →
    (∀ a, DifferentiableOn ℂ (fun t => ψ t a) B) →
    (∀ t ∈ B, IsDerivAt0 (e t) (w t) (spMap (dualMap (ψ t)) ≫ v)) →
    (∀ t ∈ B, ∀ w₁ w₂ u, IsDerivAt0 (e t) w₁ u → IsDerivAt0 (e t) w₂ u → w₁ = w₂) →
    ∀ t₀ ∈ B, AnalyticAt ℂ w t₀

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition.ChartForm

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ (V : X.Opens) (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V) (hg : genPt ξ ∈ V) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f) := by
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

theorem exists_form {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (U : X.Opens) (hU : genPt ξ ∈ U) :
    ∃ g : MvPolynomial (Σ k, J k) ℤ, g ∉ mCoordIdeal y ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ),
      genPt ξ ⤳ centre z → CoordsAt ξ y z w → aeval w g ≠ 0 → centre z ∈ U := by
  classical
  have hξ := T.gen
  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨V, hV, hmem⟩ := T.affine c hc.1
  have hgV : genPt ξ ∈ V := (hmem _).2 ⟨specializes_rfl, hc⟩
  obtain ⟨f, hfU, hgf⟩ := hV.exists_basicOpen_le ⟨genPt ξ, hU⟩ hgV
  obtain ⟨a, ha⟩ : ∃ a : Ω, a = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hgV f) := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    have h1 := (X.mem_basicOpen f (genPt ξ) hgV).1 hgf
    rw [ha]
    exact (h1.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  have haA := (T.ring c hc.1 a).2 fun p hp =>
    ⟨_, (genMap_germ V f p ((hmem _).2 ⟨p.2, hp⟩) hgV).trans ha.symm⟩
  let t : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  have h1 : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      (aeval t : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Ω).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩
    change aeval t (∏ k, MvPolynomial.X ⟨k, j k⟩) = _
    rw [map_prod]
    simp only [aeval_X, t]
    exact Finset.prod_div_distrib _ _
  obtain ⟨F₀, hF₀⟩ := h1 haA
  have hF₀' : aeval t F₀ = a := hF₀
  obtain ⟨F, d, hF⟩ := exists_homog c F₀
  refine ⟨F * ∏ k, MvPolynomial.X ⟨k, c k⟩, fun h => ?_, fun z w hz hw hne => ?_⟩
  · have h2 := hF (MvPolynomial K Ω) (fun p => C (y p) * MvPolynomial.X p.1)
      (fun p => C (y p / y ⟨p.1, c p.1⟩)) (fun k => C (y ⟨k, c k⟩) * MvPolynomial.X k)
      (fun k => by simp [div_self (hy k)])
      (fun p => by rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hy p.1)])
    have h3 : aeval (fun p : Σ k, J k => (C (y p) * MvPolynomial.X p.1 : MvPolynomial K Ω))
      (F * ∏ k, MvPolynomial.X ⟨k, c k⟩) = 0 := h
    have h4 := map_aeval_int (C : Ω →+* MvPolynomial K Ω) t F₀
    rw [map_mul, h2, map_prod, ← h4, hF₀'] at h3
    have h5 : ∀ k, (C (y ⟨k, c k⟩) * MvPolynomial.X k : MvPolynomial K Ω) ≠ 0 := fun k =>
      mul_ne_zero (by simpa using hy k) (X_ne_zero k)
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero d (h5 k)) (by simpa using ha0))
      (Finset.prod_ne_zero_iff.2 fun k _ => ?_) h3
    rw [aeval_X]
    exact h5 k
  · rw [map_mul, map_prod] at hne
    have hw0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
      have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne) k (Finset.mem_univ k)
      rwa [aeval_X] at this
    have hr : ∀ p : Σ k, J k, ∃ r : ℂ, ValAt ξ z (t p) r ∧ w p = r * w ⟨p.1, c p.1⟩ := fun p =>
      (hw.2 p.1 (c p.1) (hw0 p.1).isUnit).2 p.2
    choose s hs1 hs2 using hr
    have hs3 : ∀ k, s ⟨k, c k⟩ = 1 := fun k => by
      have h6 : w ⟨k, c k⟩ = s ⟨k, c k⟩ * w ⟨k, c k⟩ := hs2 ⟨k, c k⟩
      exact (mul_right_cancel₀ (hw0 k) (h6.symm.trans (one_mul _).symm))
    have h7 := hF ℂ w s (fun k => w ⟨k, c k⟩) hs3 hs2
    have h8 : aeval s F₀ ≠ 0 := right_ne_zero_of_mul (h7 ▸ left_ne_zero_of_mul hne)
    obtain ⟨φ, hφ, _⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z hz hξ
    have hreg : ∀ p, t p ∈ regAt ξ ⟨centre z, hz⟩ := fun p => ((hφ _ _).1 (hs1 p)).1
    have hφs : ∀ p, φ ⟨t p, hreg p⟩ = s p := fun p => ((hφ _ _).1 (hs1 p)).2
    have hzc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
      refine ⟨hc.1, fun j => ?_⟩
      have h9 : (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) = ∏ k, t ⟨k, j k⟩ := (Finset.prod_div_distrib _ _).symm
      change (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ _
      rw [h9]
      exact prod_mem fun k _ => hreg _
    have hzV : centre z ∈ V := (hmem _).2 ⟨hz, hzc⟩
    let b : regAt ξ ⟨centre z, hz⟩ := aeval (fun p => (⟨t p, hreg p⟩ : regAt ξ ⟨centre z, hz⟩)) F₀
    have hb : (b : Ω) = a := by
      rw [← hF₀']
      exact map_aeval_int (regAt ξ ⟨centre z, hz⟩).subtype _ F₀
    have hφb : φ b = aeval s F₀ := by
      rw [map_aeval_int]
      simp only [hφs]
    have hval : ValAt ξ z a (aeval s F₀) := by
      rw [← hb, ← hφb]
      exact (hφ _ _).2 ⟨b.2, rfl⟩
    obtain ⟨_, σ, e1, e2⟩ := hval
    have e3 : σ = X.presheaf.germ V (centre z) hzV f :=
      hξ.inj ⟨centre z, hz⟩ (e1.trans (ha.trans (genMap_germ V f ⟨centre z, hz⟩ hzV hgV).symm))
    have e4 : IsUnit ((Scheme.stalkClosedPointTo z).hom σ) := by
      rw [e2]
      exact h8.isUnit
    have e5 : IsUnit σ := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit σ e4
    exact hfU ((X.mem_basicOpen f (centre z) hzV).2 (e3 ▸ e5))

end SheetDecomposition.ChartForm
end
end

section

noncomputable section

namespace SheetDecomposition.ChartForm

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

set_option backward.isDefEq.respectTransparency false in
theorem germ_point {V : X.Opens} (hV : IsAffineOpen V) {R : CommRingCat} [IsLocalRing R] (φ : Γ(X, V) ⟶ R)
    (h : (Spec.map φ ≫ hV.fromSpec) (IsLocalRing.closedPoint R) ∈ V) :
    X.presheaf.germ V _ h ≫ Scheme.stalkClosedPointTo (Spec.map φ ≫ hV.fromSpec) = φ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc hV.fromSpec V _ h]
  rw [IsAffineOpen.fromSpec_app_self, Category.assoc, TopCat.Presheaf.germ_res_assoc]
  erw [Scheme.germ_stalkClosedPointTo_Spec φ]
  exact Iso.inv_hom_id_assoc _ _

private theorem valAt_add_volume_equality {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, s₁, h₁, h₂⟩ := ha
  obtain ⟨h', s₂, h₃, h₄⟩ := hb
  refine ⟨h, s₁ + s₂, ?_, ?_⟩
  · rw [map_add (f := _), h₁]
    exact congrArg (a + ·) h₃
  · exact ((Scheme.stalkClosedPointTo z).hom.map_add s₁ s₂).trans (by rw [h₂, h₄])

private theorem valAt_intCast' {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

private theorem coordTie_unit_prod {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => κ) k =>
      ∏ k, (fun p : (Σ _ : Unit, κ) => x p.2) ⟨k, c' k⟩) := by
  have hx : (fun c' : (k : Unit) → (fun _ : Unit => κ) k =>
      ∏ k, (fun p : (Σ _ : Unit, κ) => x p.2) ⟨k, c' k⟩) = fun c' : Unit → κ => x (c' ()) := by
    funext c'
    simp
  have hin : ∀ (c' : Unit → κ) (p : Cpt ξ),
      InChart ξ (fun c' : Unit → κ => x (c' ())) c' p ↔ InChart ξ x (c' ()) p := by
    intro c' p
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, fun j => h1 (fun _ => j)⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, fun c'' => h1 (c'' ())⟩
  have hr : ∀ c' : Unit → κ, (Set.range fun j' : Unit → κ => x (j' ()) / x (c' ())) =
      Set.range fun j => x j / x (c' ()) := by
    intro c'
    ext a
    constructor
    · rintro ⟨j', rfl⟩
      exact ⟨j' (), rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨fun _ => j, rfl⟩
  rw [hx]
  refine ⟨T.gen, fun p => ?_, fun c' hc' => ?_, fun c' hc' a => ?_⟩
  · obtain ⟨c, hc⟩ := T.cover p
    exact ⟨fun _ => c, (hin _ p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := T.affine (c' ()) hc'
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun h => (hin c' ⟨q, h⟩).symm)⟩
  · rw [hr c', T.ring (c' ()) hc' a]
    exact forall_congr' fun p => imp_congr_left (hin c' p).symm

theorem exists_point_hom {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* ℂ) :
    ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧
      ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a) := by
  have T' := coordTie_unit_prod T
  have hgen : ∀ j, x j / x c ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
    fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  let w : (Σ _ : Unit, κ) → ℂ := fun p => ψ ⟨x p.2 / x c, hgen p.2⟩
  have hw1 : ∀ k : Unit, w ⟨k, c⟩ = 1 := by
    intro k
    have e : (⟨x c / x c, hgen c⟩ : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = 1 :=
      Subtype.ext (div_self hc)
    simp only [w, e, map_one]
  have hu : ∀ k : Unit, ∃ c' : κ, IsUnit (w ⟨k, c'⟩) := fun k => ⟨c, by rw [hw1 k]; exact isUnit_one⟩
  have hk : ∀ g ∈ mCoordIdeal (fun p : (Σ _ : Unit, κ) => x p.2), aeval w g = 0 :=
    TiePoints.aeval_eq_zero_of_ratio (fun p : (Σ _ : Unit, κ) => x p.2) (fun _ => c) (fun _ => hc) w
      (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring ψ
      (fun p => ⟨x p.2 / x c, hgen p.2⟩) (fun _ => rfl) (fun p => by rw [hw1, mul_one])
  obtain ⟨z, hz, hzc⟩ := (TiePoints.existsUnique_point T' w hu hk).exists
  have hval : ∀ i, ValAt ξ z (x i / x c) (ψ ⟨x i / x c, hgen i⟩) := by
    intro i
    obtain ⟨r, hr, hwr⟩ := (hzc.2 () c (by rw [hw1]; exact isUnit_one)).2 i
    rw [hw1, mul_one] at hwr
    have e : ψ ⟨x i / x c, hgen i⟩ = r := hwr
    rw [e]
    exact hr
  refine ⟨z, hz, ?_⟩
  rintro ⟨a, ha⟩
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact hval i
  | algebraMap n =>
    have e : (⟨algebraMap ℤ Ω n, Subalgebra.algebraMap_mem _ n⟩ :
        Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = (n : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      Subtype.ext (by simp)
    rw [e, map_intCast]
    simpa using valAt_intCast' hz n
  | add a b ha hb iha ihb =>
    show ValAt ξ z (a + b) (ψ (⟨a, ha⟩ + ⟨b, hb⟩))
    rw [ψ.map_add]
    exact valAt_add_volume_equality iha ihb
  | mul a b ha hb iha ihb =>
    show ValAt ξ z (a * b) (ψ (⟨a, ha⟩ * ⟨b, hb⟩))
    rw [map_mul]
    exact TiePoints.valAt_mul T.gen iha ihb


theorem exists_point {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (w : (Σ k, J k) → ℂ) (hu : ∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) (hk : ∀ g ∈ mCoordIdeal y, aeval w g = 0) :
    ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  exact (TiePoints.existsUnique_point T w hu hk).exists

end SheetDecomposition.ChartForm
end
end
