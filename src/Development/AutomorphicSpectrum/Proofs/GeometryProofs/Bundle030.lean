module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.regular_local_ring_fraction_field : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | exact GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.existsUnique_centre_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R), IsLocalHom φ → ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | exact GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.valAt_comp_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) → ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | exact GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_proper_integral_model : ∀ (Ω : Type) [Field Ω] (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → ∃ (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of o)), CoordTie o ξ x ∧ (∀ q : X, genPt ξ ⤳ q) ∧ IsIntegral X ∧ IsProper s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | exact GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_cl_scheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.regAt_noetherian_model_noetherian : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_along_unique_up_to_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT | exact GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E : Type} [AddCommGroup E] [Module Ω E]

section Units

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unitAt.zpow {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  obtain ⟨h0, h1, h2⟩ := hu
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_natCast]; exact pow_mem h1 n
    · rw [zpow_natCast, ← inv_pow]; exact pow_mem h2 n
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem h2 n
    · rw [zpow_neg, zpow_natCast, inv_inv]; exact pow_mem h1 n

theorem unitAt.prod {K : Type} (s : Finset K) {u : K → Ω} (hu : ∀ k ∈ s, unitAt ξ p (u k)) :
    unitAt ξ p (∏ k ∈ s, u k) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k hk => (hu k hk).1, prod_mem fun k hk => (hu k hk).2.1, ?_⟩
  rw [← Finset.prod_inv_distrib]
  exact prod_mem fun k hk => (hu k hk).2.2

theorem span_singleton_eq_of_unitAt {u : Ω} (hu : unitAt ξ p u) {e e' : E} (h : e' = u • e) :
    Submodule.span (regAt ξ p) {e'} = Submodule.span (regAt ξ p) {e} := by
  obtain ⟨h0, h1, h2⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, h1⟩, h.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, h2⟩, ?_⟩
    show u⁻¹ • e' = e
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]

end Units

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

end Lat

section Pull

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem Dominates.map_genPt (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let pt' : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  have h1 : (ξ' ≫ f) pt' = (Spec.map (CommRingCat.ofHom i) ≫ ξ) pt' :=
    congrArg (fun g : Spec (CommRingCat.of Ω') ⟶ X => g pt') h
  have h2 : (Spec.map (CommRingCat.ofHom i)) pt' = pt :=
    (inferInstance : Subsingleton (PrimeSpectrum Ω)).elim _ _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2] at h1
  exact h1

theorem Dominates.specializes (h : Dominates ξ' ξ f i) (p' : Cpt ξ') : genPt ξ ⤳ f p'.1 := by
  rw [← h.map_genPt]
  exact p'.2.map f.continuous

theorem Lat.pull_apply {F : Type} [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (h : Dominates ξ' ξ f i)
    (j : E →+ F) (p' : Cpt ξ') :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, h.specializes p'⟩ : Set E)) := by
  show Submodule.span _ _ = _
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨h.specializes p', e, he, rfl⟩

end Pull

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Multi

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

theorem block_ratio_mem {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h2 := h.2 (Function.update c k i)
  have e1 : ∏ k', y ⟨k', c k'⟩ = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    (Finset.mul_prod_erase _ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)).symm
  have e2 : ∏ k', y ⟨k', Function.update c k i k'⟩ = y ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [← Finset.mul_prod_erase _ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 := by
    intro h0
    exact h.1 (by show ∏ k', y ⟨k', c k'⟩ = 0; rw [e1, h0, mul_zero])
  simp only [e1, e2] at h2
  rwa [mul_div_mul_right _ _ hP] at h2

theorem block_coord_ne_zero {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

end Multi

section Single

variable {κ : Type} {x : κ → Ω}

end Single

end Lat

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem adjugate_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ}
    (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (i j : Fin r) :
    P.adjugate i j ∈ R := by
  let P' : Matrix (Fin r) (Fin r) R := fun a b => ⟨P a b, hP a b⟩
  have hPP : P = (R.subtype).mapMatrix P' := by
    ext a b
    rfl
  rw [hPP, ← RingHom.map_adjugate]
  exact (P'.adjugate i j).2

theorem linearIndependent_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {β : Fin r → E} (hβ : LinearIndependent Ω β) (P : Matrix (Fin r) (Fin r) Ω) (hd : P.det ≠ 0) :
    LinearIndependent Ω (fun k => ∑ a, P a k • β a) := by
  rw [Fintype.linearIndependent_iff] at hβ ⊢
  intro g hg
  have h1 : ∀ a, ∑ k, P a k * g k = 0 := by
    apply hβ
    refine Eq.trans ?_ hg
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have h2 : Matrix.mulVec P g = 0 := by
    funext a
    exact h1 a
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hd h2
  intro i
  rw [h3]
  rfl

theorem span_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ}
    (β : Fin r → E) (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (hd : P.det ≠ 0)
    (hdi : P.det⁻¹ ∈ R) :
    Submodule.span R (Set.range fun k => ∑ a, P a k • β a) = Submodule.span R (Set.range β) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)
    refine sum_mem fun a _ => ?_
    exact Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro b
    show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)
    have hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b := fun a =>
      (Matrix.mul_apply).symm
    have hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b := by
      calc ∑ k, P.adjugate k b • ∑ a, P a k • β a
          = ∑ a, (∑ k, P a k * P.adjugate k b) • β a := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = ∑ a, (P * P.adjugate) a b • β a := by
            simp only [hm]
        _ = P.det • β b := by
            rw [Matrix.mul_adjugate]
            simp [Matrix.one_apply]
    have key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a := by
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [key]
    refine sum_mem fun k _ => ?_
    exact Submodule.smul_mem _
      (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R)
      (Submodule.subset_span ⟨k, rfl⟩)

theorem isFrameAt_matrix_comb : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ)
    (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det →
    L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  intro X Ω _ ξ E _ _ L r β q P h1 h2 h3
  obtain ⟨hli, hspan⟩ := h1
  obtain ⟨hne, -, hinv⟩ := h3
  show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧
    L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)
  refine ⟨linearIndependent_matrix_comb hli P hne, ?_⟩
  rw [hspan]
  exact (span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.wedge_eq_span_of_isFrameAt :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p →
      L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} := by
  intro X Ω _ ξ E _ _ L r b p h
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨v, hv, rfl⟩
    have hc : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • b j = v i := fun i => by
      have := hv i
      rw [h.2] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using hc
    have hv' : v = fun i => ∑ j, ((c i j : Ω)) • b j := by
      funext i
      rw [← hc i]
      rfl
    have hsum : exteriorPower.ιMulti Ω r v =
        ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
      rw [hv']
      have := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
        (fun i j => ((c i j : Ω)) • b j)
      refine this.trans (Finset.sum_congr rfl fun f _ => ?_)
      have h2 := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
        (fun i => (c i (f i) : Ω)) (fun i => b (f i))
      simp only [RingHom.id_apply] at h2
      refine h2.trans ?_
      have h3 : ((∏ i, c i (f i) : regAt ξ p) : Ω) = ∏ i, (c i (f i) : Ω) := by simp
      rw [← h3]
      rfl
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h4 := (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, h4]
      have hm := Submodule.mem_span_singleton_self (R := regAt ξ p) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  · refine Submodule.span_mono ?_
    rintro w rfl
    refine ⟨b, fun i => ?_, rfl⟩
    rw [h.2]
    exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_restrict_comap_span {Ω R E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [Semiring R] [SMul R Ω]
    [Module R E] [IsScalarTower R Ω E] (V : Submodule Ω E) {r : ℕ} (b : Fin r → V) :
    (Submodule.span R (Set.range fun i => (b i : E))).comap (V.subtype.restrictScalars R) =
      Submodule.span R (Set.range b) := by
  have h : (Set.range fun i => (b i : E)) = (V.subtype.restrictScalars R) '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

theorem Lat.restrict_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E),
    L.IsVBOn T r V → (L.comap V.subtype).IsVBOn T r ⊤ ∧
      ∀ p ∈ T, ((L.comap V.subtype).map V.subtype) p = L p := by
  intro X Ω _ ξ E _ _ L T r V h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    have hbV : ∀ i, b i ∈ V := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
    let b' : Fin r → V := fun i => ⟨b i, hbV i⟩
    have hval : (fun i => (b' i : E)) = b := rfl
    refine ⟨U, hpU, b', ?_, ?_⟩
    · apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
      have h1 : (Set.range b) = V.subtype '' Set.range b' := by
        rw [← Set.range_comp]; rfl
      rw [Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]
    · intro q hqT hqU
      obtain ⟨hli, hsp⟩ := hq q hqT hqU
      refine ⟨?_, ?_⟩
      · exact LinearIndependent.of_comp V.subtype hli
      · show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _
        rw [hsp, ← hval]
        exact lat_restrict_comap_span V b'
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    obtain ⟨_, hsp⟩ := hq p hp hpU
    have hle : ∀ e ∈ L p, e ∈ V := by
      intro e he
      rw [hsp] at he
      have : Submodule.span (regAt ξ p) (Set.range b) ≤ V.restrictScalars (regAt ξ p) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this he
    show ((L p).comap (V.subtype.restrictScalars (regAt ξ p))).map (V.subtype.restrictScalars (regAt ξ p)) = L p
    ext e
    simp only [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro he
      exact ⟨⟨e, hle e he⟩, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieBaseAct

theorem baseChange_act : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V') (O : Type) [CommRing O] (act : O → (G ⟶ G)) (act' : O → (G' ⟶ G')) (ρ : O →+* Module.End Ω V) (ρ' : O →+* Module.End Ω' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → M.IsActOf act ρ → M'.IsActOf act' ρ' → (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) → ∀ a e, ρ' a (j e) = j (ρ a e) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' j O _ act act' ρ ρ' _ hpb hpt hM hM' hcomm a e
  apply M'.inj
  rw [hM' a (j e)]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · simp only [Over.comp_left, Category.assoc, hcomm a]
    rw [← Category.assoc, hpt e, hpt (ρ a e), hM a e, Over.comp_left]
    simp only [Category.assoc]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.LieBaseAct
end
end

section

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.eigen_component_map_compat : ∀ (k k' V V' O : Type) [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V'), (∀ (c : k) x, j (c • x) = κ c • j x) → ∀ (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V'), (∀ a x, ρ' a (j x) = j (ρ a x)) → ∀ (σ : O →+* k) (x : V), eigComp ρ σ x ≠ 0 → eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map <;> assumption)
end
