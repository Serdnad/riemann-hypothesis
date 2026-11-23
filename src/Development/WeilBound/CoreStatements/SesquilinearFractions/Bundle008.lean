module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle007
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  intro E _ _ _ H D I _ _ e hcard he
  classical
  have := D.fin
  have := D.proj
  obtain ⟨n, hn, hsp⟩ := exists_nsmul_mem_span_full_family e (hcard.trans D.rank.symm) he
  refine ⟨fun hdet => ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image v)
    choose u hu using fun m => hc (v m) (Finset.mem_image_of_mem v (Finset.mem_univ m))
    have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero c
    have huv : ∀ m, (u m : E) = (c : 𝓞 E) * v m := fun m => by
      rw [show ((u m : 𝓞 E) : E) = algebraMap (𝓞 E) E (u m) from rfl, hu m, Algebra.smul_def]
    set z : D.La := ∑ i, u i • e i with hz

    have hzj : ∀ j, sesq D z (e j) = 0 := by
      intro j
      rw [hz, sesq_sum_smul_left]
      have hvj := congrFun hv j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gramE, Matrix.of_apply] at hvj
      simp_rw [huv]
      calc ∑ i, (c : 𝓞 E) * v i * sesq D (e i) (e j) = (c : 𝓞 E) * ∑ i, v i * sesq D (e i) (e j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hvj, mul_zero]
    have hz0 : ∀ x, sesq D x z = 0 := by
      intro x
      obtain ⟨S, hS⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hsp x)
      have h1 : sesq D z (n • x) = (n : E) * sesq D z x := by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]; simp
      have h2 : sesq D z (n • x) = 0 := by
        rw [← hS, sesq_sum_smul_right]
        exact Finset.sum_eq_zero fun j _ => by rw [hzj j, mul_zero]
      have h3 : sesq D z x = 0 := by
        rw [h2] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast hn.ne')
      rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 z x, h3, map_zero, neg_zero]
    have hzz : z = 0 := (GlobalTheory.T.sesq_unimodular_dual E H D).1 z hz0
    have hu0 := (Fintype.linearIndependent_iff.1 he) u (by rw [← hz]; exact hzz)
    apply hv0
    funext m
    have : (c : 𝓞 E) * v m = 0 := by rw [← huv, hu0 m]; simp
    simpa [hc0] using this
  · refine (Set.finite_le_nat n).preimage (f := fun ℓ : Nat.Primes => (ℓ : ℕ))
      (fun a _ b _ h => Subtype.ext h) |>.subset ?_
    intro ℓ hℓ
    simp only [Set.mem_setOf_eq] at hℓ ⊢
    by_contra hlt
    apply hℓ
    refine ⟨he, n, fun hd => hlt ?_, hsp⟩
    exact Nat.le_of_dvd hn hd

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def projectionCoeffsAddHom (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (a : Fin p) : D.La →+ E :=
  AddMonoidHom.mk' (fun y => projectionCoeffs D x' y a) (fun y y' => by rw [projectionCoeffs_add]; rfl)

theorem exists_common_denominator_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ m : ℕ, ¬ (ℓ : ℕ) ∣ m ∧ ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a := by
  classical
  have := D.fin
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := 𝓞 E) (M := D.La)
  have hpt : ∀ i a, ∃ n : ℕ, ¬ (ℓ : ℕ) ∣ n ∧ ∃ b : 𝓞 E, (n : E) * projectionCoeffs D x' (t i) a = b := fun i a => by
    obtain ⟨n, b, hn, hb⟩ := (GlobalTheory.T.padic_integral_iff_denominator E ℓ _).1 (fun j => padic_norm_projectionCoeffs_le D x' ℓ hdet hlog (t i) a j)
    exact ⟨n, hn, b, hb⟩
  choose n hn b hb using hpt
  refine ⟨∏ i, ∏ a, n i a, ?_, fun y a => ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 ℓ.2) _).1 h
    obtain ⟨a, -, ha⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 ℓ.2) _).1 hi
    exact hn i a ha
  · have hy : y ∈ Submodule.span (𝓞 E) (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hy
    have hdv : ∀ i, ∃ w : ℕ, ∏ i, ∏ a, n i a = n i a * w := fun i =>
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    choose w hw using hdv
    have he : projectionCoeffs D x' (∑ i, c i • t i) a = ∑ i, IsCMField.complexConj E (c i : E) * projectionCoeffs D x' (t i) a := by
      show projectionCoeffsAddHom D x' a (∑ i, c i • t i) = _

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show projectionCoeffs D x' (c i • t i) a = _
      rw [projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul]
    have hmem : ((∏ i, ∏ a, n i a : ℕ) : E) * projectionCoeffs D x' (∑ i, c i • t i) a ∈ (algebraMap (𝓞 E) E).range := by
      rw [he, Finset.mul_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [mul_left_comm, hw i, Nat.cast_mul, mul_comm ((n i a : ℕ) : E), _root_.mul_assoc, hb i a]
      exact Subring.mul_mem _ ⟨H.bar (c i), H.bar_eq (c i)⟩ (Subring.mul_mem _ ⟨(w i : 𝓞 E), by simp⟩ ⟨b i a, rfl⟩)
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, hg⟩

end GlobalTheory.CompanionTheory.Ar.Fl

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem algebraMap_bar_eq_conj (a : 𝓞 E) :
    algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq a

def familyCombination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : (Fin p → 𝓞 E) →ₗ[𝓞 E] D.La where
  toFun c := ∑ a, c a • x' a
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

section Maps

variable (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (m : ℕ)
  (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a)

def integralCoeffsRaw (y : D.La) (a : Fin p) : 𝓞 E := Classical.choose (hm y a)

theorem algebraMap_integralCoeffsRaw (y : D.La) (a : Fin p) :
    algebraMap (𝓞 E) E (integralCoeffsRaw D x' m hm y a) = m * projectionCoeffs D x' y a := Classical.choose_spec (hm y a)

def integralCoeffs : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) where
  toFun y a := H.bar (integralCoeffsRaw D x' m hm y a)
  map_add' y y' := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.add_apply]
    rw [map_add (f := _), algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_add,
      Pi.add_apply, mul_add, map_add]
  map_smul' c y := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [map_mul, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, map_mul, map_mul, IsCMField.complexConj_apply_apply, map_natCast]
    show _ = ((c : 𝓞 E) : E) * _
    ring

theorem conj_integralCoeffs (y : D.La) (a : Fin p) :
    IsCMField.complexConj E (algebraMap (𝓞 E) E (integralCoeffs D x' m hm y a)) = m * projectionCoeffs D x' y a := by
  show IsCMField.complexConj E (algebraMap (𝓞 E) E (H.bar (integralCoeffsRaw D x' m hm y a))) = _
  rw [algebraMap_bar_eq_conj, IsCMField.complexConj_apply_apply, algebraMap_integralCoeffsRaw]

def orthogonalComponent : D.La →ₗ[𝓞 E] D.La := (m : 𝓞 E) • LinearMap.id - familyCombination D x' ∘ₗ integralCoeffs D x' m hm

theorem orthogonalComponent_mem (hdet : (gramE D x').det ≠ 0) (y : D.La) : orthogonalComponent D x' m hm y ∈ orthogonalFamilyAlt D x' := by
  show ∀ a, sesq D (x' a) (orthogonalComponent D x' m hm y) = 0
  intro b
  have hsub : ∀ u v w : D.La, sesq D u (v - w) = sesq D u v - sesq D u w := by
    intro u v w
    simp only [sesq, map_sub, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  have hsm : ∀ u v : D.La, sesq D u ((m : 𝓞 E) • v) = m * sesq D u v := by
    intro u v
    rw [Nat.cast_smul_eq_nsmul]
    simp only [sesq, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.mul_sum,
      _root_.mul_assoc]
  have hcomb : familyCombination D x' (integralCoeffs D x' m hm y) =
      ∑ a, integralCoeffs D x' m hm y a • x' a := rfl
  have hG := congrFun (gram_mulVec_projection_coeffs D x' hdet y) b
  simp only [Matrix.mulVec, dotProduct, pairingVector] at hG
  have hd : ∀ a, IsCMField.complexConj E ((integralCoeffs D x' m hm y a : 𝓞 E) : E) =
      m * projectionCoeffs D x' y a := fun a => conj_integralCoeffs D x' m hm y a
  simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  rw [hsub, hsm, hcomb, sesq_integral_combination]
  simp only [hd]
  rw [← hG, Finset.mul_sum]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro a _
  ring

end Maps

end GlobalTheory.CompanionTheory.Ar.Fl

end
end
