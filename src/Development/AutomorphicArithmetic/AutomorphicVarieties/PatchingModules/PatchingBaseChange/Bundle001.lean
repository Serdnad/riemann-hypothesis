module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
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
public import Mathlib.RingTheory.Congruence.Hom
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.nonSS_mono :
    ∀ (R R' S G G' : Type) [CommRing R] [CommRing R'] [CommRing S] [Group G] [Group G'] (p : G' →* G) (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R' G')) (φ : R →+* S) (φ' : R' →+* S) (Q : Ideal S), Function.Surjective p → (∀ z ∈ I', MonoidAlgebra.mapDomainRingHom S p (MonoidAlgebra.mapRingHom G' φ' z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I)) → NonSS I φ Q → NonSS I' φ' Q := by
  intro R R' S G G' _ _ _ _ _ p I I' φ φ' Q hp hI ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' (f.comp φ') '' I') with hJ'
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    J.ringCon.mk'.comp (MonoidAlgebra.mapDomainRingHom κ p)
  have hψs : Function.Surjective ψ := by
    have h1 : Function.Surjective (MonoidAlgebra.mapDomainRingHom κ p) := by
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact ⟨0, map_zero _⟩
      | add a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add _ _ _⟩
      | single g c =>
        obtain ⟨g', rfl⟩ := hp g
        exact ⟨MonoidAlgebra.single g' c, by simp⟩
    exact (RingCon.mk'_surjective _).comp h1
  have hcomm : ∀ w : MonoidAlgebra S G',
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G' f w) =
        MonoidAlgebra.mapRingHom G f (MonoidAlgebra.mapDomainRingHom S p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hcomp : ∀ (T H : Type) [CommRing T] [Group H] (θ : T →+* S) (z : MonoidAlgebra T H),
      MonoidAlgebra.mapRingHom H (f.comp θ) z =
        MonoidAlgebra.mapRingHom H f (MonoidAlgebra.mapRingHom H θ z) := by
    intro T H _ _ θ z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I) ≤
      J.comap (MonoidAlgebra.mapRingHom G f) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, ← hcomp]
    exact TwoSidedIdeal.subset_span ⟨y, hy, rfl⟩
  have hle' : J' ≤ J.comap (MonoidAlgebra.mapDomainRingHom κ p) := by
    rw [hJ', TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hcomp, hcomm, ← TwoSidedIdeal.mem_comap]
    exact hle (hI z hz)
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    have h1 : a - b ∈ J' := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    have h2 := hle' h1
    rw [TwoSidedIdeal.mem_comap, map_sub] at h2
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h2)
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  exact ⟨(x : J'.ringCon.Quotient), rfl⟩
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tr_map {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : GDet n R G)
    (f : R →+* R') (x : G) :
    (D.map f).tr (MonoidAlgebra.single x 1) = f (D.tr (MonoidAlgebra.single x 1)) := by
  have h := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one] at h
  exact h

private theorem tr_comap {n : ℕ} {R G G' : Type} [CommRing R] [Group G] [Group G'] (D : GDet n R G)
    (p : G' →* G) (x : G') :
    (D.comap p).tr (MonoidAlgebra.single x 1) = D.tr (MonoidAlgebra.single (p x) 1) := by
  unfold GDet.tr GDet.lam GDet.comap GDet.chi
  simp only [MonoidAlgebra.mapRingHom_single, map_one, MonoidHom.coe_comp, Function.comp_apply]
  have hY : ((MonoidAlgebra.mapDomainRingHom (Polynomial R) p :
        MonoidAlgebra (Polynomial R) G' →+* MonoidAlgebra (Polynomial R) G) :
        MonoidAlgebra (Polynomial R) G' →* MonoidAlgebra (Polynomial R) G)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) =
      MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single (p x) 1 := by
    change (MonoidAlgebra.mapDomainRingHom (Polynomial R) p)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = _
    rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]
  exact congrArg (fun y => (-1) ^ 1 * ((D.D (Polynomial R)) y).coeff (n - 1)) hY

theorem UpperTheory.V.Pa.BC.discSt_map :
    ∀ (n : ℕ) (R R' G : Type) [CommRing R] [CommRing R'] [Group G] (D : GDet n R G), (∀ (g : R →+* R') (Q : Ideal R'), DiscSt (D.map g) Q ↔ DiscSt D (Q.comap g)) ∧ (∀ (G' : Type) [Group G'] (p : G' →* G), Function.Surjective p → ∀ Q : Ideal R, DiscSt (D.comap p) Q ↔ DiscSt D Q) ∧ ∀ Q Q' : Ideal R, Q ≤ Q' → DiscSt D Q' → DiscSt D Q := by
  intro n R R' G _ _ _ D
  refine ⟨fun g Q => ?_, fun G' _ p hp Q => ?_, fun Q Q' hQ hD => ?_⟩
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G,
        (Matrix.of fun i j => (D.map g).tr (MonoidAlgebra.single (a i * b j) 1)).det =
        g ((Matrix.of fun i j => D.tr (MonoidAlgebra.single (a i * b j) 1)).det) := by
      intro a b
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, tr_map]
    simp only [key, Ideal.mem_comap]
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G',
        (Matrix.of fun i j => (D.comap p).tr (MonoidAlgebra.single (a i * b j) 1)) =
        Matrix.of fun i j => D.tr (MonoidAlgebra.single (p (a i) * p (b j)) 1) := by
      intro a b
      ext i j
      simp [tr_comap]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨fun i => p (a i), fun j => p (b j), by simpa only [key] using h⟩
    · rintro ⟨a, b, h⟩
      refine ⟨fun i => Function.surjInv hp (a i), fun j => Function.surjInv hp (b j), ?_⟩
      simp only [key, Function.surjInv_eq hp]
      exact h
  · obtain ⟨a, b, h⟩ := hD
    exact ⟨a, b, fun hq => h (hQ hq)⟩
end
