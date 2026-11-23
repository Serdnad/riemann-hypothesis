module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagK

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

def fi {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 0 else 1

lemma Jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Jm ε = Matrix.diagonal (fun a => ((sgn ε a : ℝ) : ℂ)) := by
  unfold Jm sgn; congr 1; funext a; split_ifs <;> simp

lemma star_mul_self' (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

lemma mul_star_self' (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self']

lemma col_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (b : Fin n) :
    ∑ a, sgn ε a * ‖M a b‖ ^ 2 = sgn ε b := by
  have hb := congrFun (congrFun h b) b
  rw [Jm_eq, Matrix.mul_apply] at hb
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at hb
  apply Complex.ofReal_injective
  push_cast
  rw [← hb]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_right_comm, star_mul_self']; push_cast; ring

lemma row_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * Jm ε * Mᴴ = Jm ε) (a : Fin n) :
    ∑ b, sgn ε b * ‖M a b‖ ^ 2 = sgn ε a := by
  have ha := congrFun (congrFun h a) a
  rw [Jm_eq, Matrix.mul_apply] at ha
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at ha
  apply Complex.ofReal_injective
  push_cast
  rw [← ha]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_right_comm, mul_star_self']; push_cast; ring

lemma other_side {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) : M * Jm ε * Mᴴ = Jm ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, hJ]
  have h2 : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

lemma key {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) :
    ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2 = 0 := by
  have h1 : ∑ b, fi ε b * (∑ a, sgn ε a * ‖M a b‖ ^ 2) = ∑ b, fi ε b * sgn ε b := by
    simp only [col_sum ε M h]
  have h2 : ∑ a, fi ε a * (∑ b, sgn ε b * ‖M a b‖ ^ 2) = ∑ a, fi ε a * sgn ε a := by
    simp only [row_sum ε M (other_side ε M h)]
  simp only [Finset.mul_sum] at h1 h2
  rw [Finset.sum_comm] at h1
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ a, ∑ b, fi ε b * sgn ε a * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε b * (sgn ε a * ‖M a b‖ ^ 2) by
      simp only [mul_assoc],
    show (∑ a, ∑ b, fi ε a * sgn ε b * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε a * (sgn ε b * ‖M a b‖ ^ 2) by
      simp only [mul_assoc], h1, h2, sub_self]

lemma offdiag_zero {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0) :
    ∀ a b, ε a = false → ε b = true → M a b = 0 := by
  have hk := key ε M h
  have hs : ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2
      = - ∑ a, ∑ b, (if ε a = false ∧ ε b = true then ‖M a b‖ ^ 2 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases ha : ε a <;> cases hb : ε b <;> simp [fi, sgn, ha, hb, hTF a b]
  rw [hs, neg_eq_zero] at hk
  intro a b ha hb
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs <;> positivity)).mp hk a (Finset.mem_univ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
    split_ifs <;> positivity)).mp h0 b (Finset.mem_univ _)
  simp only [ha, hb, and_self, if_true] at h1
  simpa using h1

lemma comm_of {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0)
    (hFT : ∀ a b, ε a = false → ε b = true → M a b = 0) : M * Jm ε = Jm ε * M := by
  ext a b
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ha : ε a <;> cases hb : ε b <;> simp [sgn, ha, hb, hTF a b, hFT a b]

end GlobalTheory.OffDiagK


open GlobalTheory.OffDiagK in
theorem GlobalTheory.offDiag_zero_iff_mem_K : ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε),
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 = 0 ↔ g ∈ KG ε := by
  intro n ε g
  have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
  rw [Formalism.REAL.mem_KG, Fintype.sum_eq_zero_iff_of_nonneg (fun _ => by positivity)]
  constructor
  · intro h0
    have hTF : ∀ a b, ε a = true → ε b = false → toM g a b = 0 := by
      intro a b ha hb
      have := congrFun h0 ⟨(a, b), ha, hb⟩
      simpa using this
    have hFT := offdiag_zero ε _ hg hTF
    have hc := comm_of ε _ hTF hFT
    refine ⟨?_, hc⟩
    rw [Matrix.mem_unitaryGroup_iff']
    have hJ := Formalism.REAL.Jm_mul_self ε
    calc star (toM g) * toM g = (toM g)ᴴ * (toM g * Jm ε) * Jm ε := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [hc, ← Matrix.mul_assoc, hg, hJ]
  · rintro ⟨_, hc⟩
    funext z
    obtain ⟨⟨a, b⟩, ha, hb⟩ := z
    simp only at ha hb
    have e := congrFun (congrFun hc a) b
    rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [sgn, ha, hb] at e
    push_cast at e
    have h0 : toM g a b = 0 := by linear_combination (-1/2 : ℂ) * e
    simp [h0]
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PadicMvPowerSeriesExt

theorem eq_zero_of_forall_pow_dvd (p : ℕ) (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (A : Type) [CommRing A] [Algebra O A]
    [Module.Projective O A] (x : A) (hx : ∀ m : ℕ, (p : A) ^ m ∣ x) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O A)
  have h0 : s x = 0 := by
    ext a
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : O)}) O) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hx n
    have hxy : x = ((p : O) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, hy]
    rw [hxy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h1 := LinearMap.congr_fun hs x
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at h1
  exact h1.symm

theorem algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  classical
  intro p O _ _ σ _ A _ _ _ _ F F' hX hF hF'
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd p O A _ fun m => ?_
  obtain ⟨N₁, hN₁⟩ := hF m
  obtain ⟨N₂, hN₂⟩ := hF' m
  set g := MvPowerSeries.trunc' O (Finsupp.equivFunOnFinite.symm fun _ : σ => max N₁ N₂) f with hg
  have hpoly : F.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      F'.comp (MvPolynomial.coeToMvPowerSeries.algHom O) :=
    MvPolynomial.algHom_ext fun i => by simpa using hX i
  have hg' : F (g : MvPowerSeries σ O) = F' (g : MvPowerSeries σ O) := by
    simpa using DFunLike.congr_fun hpoly g
  have hlow : ∀ α : σ →₀ ℕ, α.degree < max N₁ N₂ →
      MvPowerSeries.coeff α (f - (g : MvPowerSeries σ O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hg, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    intro i
    exact (Finsupp.le_degree i α).trans (by simpa using hα.le)
  have hdiff : F f - F' f = F (f - (g : MvPowerSeries σ O)) - F' (f - (g : MvPowerSeries σ O)) := by
    rw [map_sub, map_sub, hg']
    ring
  rw [hdiff]
  exact dvd_sub (hN₁ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_left _ _)))
    (hN₂ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_right _ _)))

end GlobalTheory.PadicMvPowerSeriesExt
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_generic_jacobian_data_iterated_alt : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_iterated | exact GlobalTheory.exists_generic_jacobian_data_iterated | (intros; apply GlobalTheory.exists_generic_jacobian_data_iterated <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geometricallyConnected_of_smooth_of_section :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  intro k _ X f e _ he _
  exact GlobalTheory.RatPointConn.of_section f e he

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))

end GlobalTheory

namespace GlobalTheory

theorem isProper_map_inf_subschemeι : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  intro S W W' f π hsep hlft T' T'' h₁ h₂
  have hle₁ : T'.map π ⊓ T'' ≤ T'.map π := inf_le_left
  have hle₂ : T'.map π ⊓ T'' ≤ T'' := inf_le_right
  let g₁ := Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁
  let g₂ := Scheme.IdealSheafData.inclusion hle₂
  have e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f := by simp [g₁]
  have e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f := by simp [g₂]
  have huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have huc : UniversallyClosed (T'.subschemeι ≫ π) :=
    UniversallyClosed.of_comp_of_isSeparated _ f
  have hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π) := by
    rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
    exact (T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq
  have hmul : T'.map π * T'' ≤ T'.map π ⊓ T'' := by
    intro U
    exact Ideal.mul_le_inf
  have hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x := by
    intro x
    have hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hx' := Scheme.IdealSheafData.support_antitone hmul hx
    rw [Scheme.IdealSheafData.support_mul] at hx'
    have hinj := (T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective
    rcases hx' with hx' | hx'
    · rw [hsupp] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inl ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inr ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  have huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f) :=
    universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)
  exact { }

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FerrandFlat

theorem flat_of_appLE {Y : Scheme.{0}} {P : CommRingCat.{0}} (y : Y ⟶ Spec P) (h : ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat) : Flat y :=
  HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) (fun V => h V.1 V.2)

theorem flat_pushout : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y hy₁ hy₂
  have H := GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂
  exact ⟨GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₁ p₁ y (Spec.map f₁) inferInstance inferInstance inferInstance hy₁
      (fun V hV => (H V hV).2.1),
    GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₂ p₂ y (Spec.map f₂) inferInstance inferInstance inferInstance hy₂
      (fun V hV => (H V hV).2.2),
    flat_of_appLE y (fun V hV => (H V hV).1)⟩

end GlobalTheory.FerrandFlat
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatBaseChangeIdeal

theorem toImage_std {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem ker_comap_flat {X Y V : Scheme.{0}} (h : X ⟶ Y) [QuasiCompact h] (g : V ⟶ Y) [Flat g] :
    h.ker.comap g = (pullback.fst g h).ker := by
  have := toImage_std h
  let m : pullback g h ⟶ pullback g h.imageι :=
    pullback.map g h g h.imageι (𝟙 _) h.toImage (𝟙 _) (by simp) (by simp)
  have hm1 : m ≫ pullback.fst g h.imageι = pullback.fst g h := by
    simp only [m, pullback.lift_fst, Category.comp_id]
  have hm2 : m ≫ pullback.snd g h.imageι = pullback.snd g h ≫ h.toImage := by
    simp only [m, pullback.lift_snd]
  have big : IsPullback (pullback.snd g h) (m ≫ pullback.fst g h.imageι)
      (h.toImage ≫ h.imageι) g := by
    rw [hm1, h.toImage_imageι]; exact (IsPullback.of_hasPullback g h).flip
  have hsq : IsPullback (pullback.snd g h) m h.toImage (pullback.snd g h.imageι) :=
    IsPullback.of_bot big hm2.symm (IsPullback.of_hasPullback g h.imageι).flip
  have hd : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback hsq
  rw [← hm1, Scheme.Hom.ker_comp, hd.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  congr 1
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

end GlobalTheory.FlatBaseChangeIdeal

namespace GlobalTheory.FlatBaseChangeIdeal

theorem map_comap_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π →
    ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  intro W W' V V' π g g' π' H hg hπ T
  have big : IsPullback (pullback.snd g' T.subschemeι) (pullback.fst g' T.subschemeι ≫ π')
      (T.subschemeι ≫ π) g :=
    (IsPullback.of_hasPullback g' T.subschemeι).flip.paste_vert H
  rw [Scheme.IdealSheafData.map, ker_comap_flat, Scheme.IdealSheafData.comap,
    Scheme.IdealSheafData.map_ker, ← big.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end GlobalTheory.FlatBaseChangeIdeal
end
