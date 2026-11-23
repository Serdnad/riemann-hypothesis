module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle078
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Mathlib.FieldTheory.Galois.Infinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitPlaces

variable {R : Ranks} (H : Host R)

theorem sqrt_sq : (H.sqd) ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_sqrt : H.conj (H.sqd) = -H.sqd :=
  by apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption

theorem exists_conjPl (l : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ∃ w' ∈ placesOver H.E l, IsConjPl H w w' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  refine ⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩
  · show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  · intro x y hxy
    have : y = c x := by
      apply RingOfIntegers.ext
      rw [hxy]; rfl
    subst this
    show _ ↔ c.symm (c x) ∈ w.asIdeal
    rw [c.symm_apply_apply]

theorem not_isConjPl_self {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hld : l ≠ H.d)
    (hj : jacobiSym (-(H.d : ℤ)) l = 1) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ¬ IsConjPl H w w := by
  intro h
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  have hdvd : (l : ℤ) ∣ n * n + H.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hint : IsIntegral ℤ (H.sqd) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    exact (isIntegral_natCast _).neg
  let b : 𝓞 H.E := ⟨H.sqd, hint⟩
  have hb : b ^ 2 = -(H.d : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_pow, map_natCast, e]
    exact sqrt_sq H
  have hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal := by
    rw [h (b - n) (-(b + n)) ?_, neg_mem_iff]
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_add (f := _), map_sub, map_intCast, e, conj_sqrt]
    ring
  have hprod : (b - n) * (b + n) ∈ w.asIdeal := by
    obtain ⟨k, hk⟩ := hdvd
    have hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E) := by rw [hk]
    push_cast at hk'
    have : (b - n) * (b + n) = (l : 𝓞 H.E) * (-k) := by
      linear_combination hb - hk'
    rw [this]
    exact w.asIdeal.mul_mem_right _ hw
  have hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h1 | h1
    exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]
  have h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hboth.2 hboth.1
    convert this using 1
    push_cast; ring
  have hlo := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have hl2n : (l : ℤ) ∣ 2 * n := by
    rw [← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]
    simpa using h2n
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rcases hp.dvd_or_dvd hl2n with h1 | h1
  · have h3 : l ∣ 2 := by exact_mod_cast h1
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  · have h3 : (l : ℤ) ∣ H.d := (dvd_add_right (h1.mul_right n)).mp hdvd
    have h4 : l ∣ H.d := by exact_mod_cast h3
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)

theorem placesSplit : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  intro R H l ⟨hl, h5, _, hd, _, hc⟩ w hw
  have hl2 : l ≠ 2 := by omega
  obtain ⟨hN, hj⟩ := (primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc
  refine ⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩
  rintro w' h rfl
  exact not_isConjPl_self H hl hl2 hd hj _ hw h

end GlobalTheory.SplitPlaces
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_split_loc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)),
      g = h * finGL E a (locGL E a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion E),
          h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  intro E _ _ _ a w g
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL E a (locGL E a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w)
      (GeneralLinearGroup.map (pFin E) (g * (finGL E a (locGL E a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL E a (locGL E a w gw))⁻¹ = k at hk ⊢
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

end GlobalTheory.CuspGeneric
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.NmUnfCol

theorem continuous_pFin (E : Type) [Field E] [NumberField E] : Continuous (pFin E) := by
  unfold pFin; exact continuous_snd

theorem col_inv_mul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (u p : GA E (a + 1)) (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1))) (l : Fin (a + 1)) :
    ((p⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 =
      (((u⁻¹ * p)⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 := by
  have e : ((u⁻¹ * p)⁻¹ : GA E (a + 1)) = p⁻¹ * u := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  have hcol : ∀ j : Fin (a + 1), (u : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) j 0 = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hu.2 0]
    · rw [if_neg hj]; exact hu.1 j 0 (Fin.pos_iff_ne_zero.2 hj)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finite_first_col_inv_compact : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  intro E _ _ r b₁ ⟨C, hC, hsupp⟩
  let f : GA E (r + 1) → (Fin (r + 1) → Af E) :=
    fun c l => pFin E (((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)
  have hf : Continuous f := by
    refine continuous_pi fun l => (continuous_pFin E).comp ?_
    have h0 : Continuous (fun c : GA E (r + 1) => ((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) :=
      Units.continuous_coe_inv
    exact (continuous_apply 0).comp ((continuous_apply l).comp h0)
  refine ⟨f '' C, hC.image hf, fun p hp => ?_⟩
  obtain ⟨u, hu, huC⟩ := hsupp p hp
  refine ⟨u⁻¹ * p, huC, funext fun l => ?_⟩
  simp only [f]
  rw [col_inv_mul u p hu l]

end GlobalTheory.NmUnfCol
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem GlobalTheory.JSW.lastRow_finite_compact : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  intro E _ _ m S β ⟨C, hC, hCβ⟩
  let F : GA E (m + 1) → (Fin (m + 1) → Af E) :=
    fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)
  have hF : Continuous F := by
    refine continuous_pi fun j => ?_
    have h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) :=
      Units.continuous_val
    have h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j :=
      h0.matrix_elem (Fin.last m) j
    exact continuous_snd.comp h1
  refine ⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩
  obtain ⟨u, hu, huC⟩ := hCβ h hS hβ
  refine ⟨u⁻¹ * h, huC, ?_⟩
  set c : GA E (m + 1) := u⁻¹ * h with hc
  have hh : h = u * c := by rw [hc]; group
  have key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
    intro j
    have hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := by
      rw [hh]; rfl
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hu.2, one_mul]
    · intro l _ hl
      rw [hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  funext j
  simp only [F, key j]
end

section

noncomputable section

namespace GlobalTheory.JSW

def padTo {m n : ℕ} (_h : m ≤ n) (l : Fin m → ℕ) : Fin n → ℕ :=
  fun i => if hi : (i : ℕ) < m then l ⟨i, hi⟩ else 0


open Classical in
def antiParts (m d : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m d).filter Antitone

def jtDet {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) : A :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat))

def staircase (m : ℕ) : Fin m → ℕ := fun i => m - 1 - i

def alternant (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) : MvPolynomial (Fin m) A :=
  Matrix.det (Matrix.of fun i j : Fin m => (MvPolynomial.X j : MvPolynomial (Fin m) A) ^ μ i)

theorem schur_eq_jtDet (n : ℕ) (l : Fin n → ℕ) :
    schur n l = jtDet n (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := rfl

theorem mem_antiParts {m d : ℕ} {l : Fin m → ℕ} : l ∈ antiParts m d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

theorem padTo_self {m : ℕ} (l : Fin m → ℕ) : padTo le_rfl l = l := by
  funext i; simp [padTo, i.2]

end GlobalTheory.JSW
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_lin_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖w ^ k - 1 - k * (w - 1)‖ ≤ ‖w - 1‖ ^ 2 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerBound.main
  | exact _root_.GlobalTheory.UltrametricPowerBound.main
  | (apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerBound.main ..)

theorem exists_nat_norm_sub_le (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) :
    ∃ k : ℕ, ‖x - k‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
  let y : ℤ_[l] := ⟨x, hx⟩
  refine ⟨y.appr 1, ?_⟩
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 (y.appr_spec 1)
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
  simpa using h

theorem norm_pow_pow_sub_one (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (b : ℕ) :
    ‖u ^ (l ^ b) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have h := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj u hu ((l ^ b : ℕ) : ℤ) (by exact_mod_cast pow_ne_zero _ hl.ne_zero)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.prime_pow] at h
  rw [h]; push_cast; rfl

theorem exists_norm_sub_pow_le (j : ℕ) (hj : Lev l j) (u s : ℚ_[l]) (hu1 : ‖u‖ = 1)
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (hs : ‖s - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) (m : ℕ) :
    ∃ a : ℕ, ‖s - u ^ a‖ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  induction m with
  | zero => exact ⟨0, by simpa using hs⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    set w := u ^ (l ^ m) with hw
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_pow, hu1, one_pow]
    have hd : ‖w - 1‖ = (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := norm_pow_pow_sub_one j hj u hu m
    have hdpos : 0 < ‖w - 1‖ := by rw [hd]; positivity
    have hd0 : w - 1 ≠ 0 := norm_pos_iff.1 hdpos
    set t := u ^ a with ht
    have ht1 : ‖t‖ = 1 := by rw [ht, norm_pow, hu1, one_pow]
    have ht0 : t ≠ 0 := norm_pos_iff.1 (by rw [ht1]; exact one_pos)
    obtain ⟨k, hk⟩ := exists_nat_norm_sub_le ((s - t) / (t * (w - 1))) (by
      rw [norm_div, norm_mul, ht1, one_mul, div_le_one hdpos, hd]; exact ha)
    refine ⟨a + l ^ m * k, ?_⟩
    have h : s - u ^ (a + l ^ m * k) = t * (w - 1) * ((s - t) / (t * (w - 1)) - k)
        + -(t * (w ^ k - 1 - k * (w - 1))) := by
      rw [pow_add, pow_mul, ← hw, ← ht]
      field_simp
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, ht1, one_mul, hd]
      calc _ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) * (l : ℝ) ^ (-1 : ℤ) := by gcongr
        _ = _ := by
          rw [← zpow_add₀ hl0.ne']; congr 1; push_cast; ring
    · rw [norm_neg, norm_mul, ht1, one_mul]
      refine (norm_pow_sub_lin_le w hw1.le k).trans ?_
      rw [hd, ← zpow_natCast, ← zpow_mul]
      apply zpow_le_zpow_right₀ hl1.le
      have := hj.1
      push_cast; omega

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, (le_sup_left : K0 K ≤ Ks K j) x.2⟩

theorem gen_dense : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  intro l _ act χ _ hχ K j hj
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hn, hcont, hG⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  refine ⟨?_, fun g hg => ?_⟩
  · have hp : ‖(l : ℚ_[l]) ^ j‖ = (l : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_pow, Padic.norm_p]; simp
    have hlt : ‖(l : ℚ_[l]) ^ j‖ < 1 := by
      rw [hp]; apply zpow_lt_one_of_neg₀ hl1; have := hj.1; omega
    have hu : ‖(1 : ℚ_[l]) + (l : ℚ_[l]) ^ j‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
        norm_one, max_eq_left hlt.le]
    obtain ⟨g, hg0, hg⟩ := (GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective l K).2 χ hχ _ hu
    have : ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by rw [hg, add_sub_cancel_left, hp]
    exact ⟨g, ((hG K g hg0).1 j).2 this.le, this⟩
  have hg0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hg.1
  have hcos : ∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n := by
    intro σ hσ n
    have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hσ
    obtain ⟨a, ha⟩ := exists_norm_sub_pow_le j hj _ _ (hn g) hg.2 (((hG K σ hσ0).1 j).1 hσ) n
    refine ⟨a, ((hG K _ (mul_mem hσ0 (inv_mem (pow_mem hg0 a)))).1 n).2 ?_⟩
    have h0 : (χ g : ℚ_[l]) ≠ 0 := Units.ne_zero _
    have h : ((χ (σ * (g ^ a)⁻¹) : ℚ_[l]ˣ) : ℚ_[l]) - 1
        = ((χ σ : ℚ_[l]) - (χ g : ℚ_[l]) ^ a) / (χ g : ℚ_[l]) ^ a := by
      simp only [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp
    rw [h, norm_div, norm_pow, hn, one_pow, div_one]
    refine ha.trans (zpow_le_zpow_right₀ hl1.le ?_)
    push_cast; omega
  refine ⟨fun b => ?_, hcos, fun σ hσ => ?_⟩
  · have : ‖(χ (g ^ (l ^ b)) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
      rw [map_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_pow_sub_one j hj _ hg.2 b
    exact ⟨((hG K _ (pow_mem hg0 _)).1 _).2 this.le, this⟩
  · rw [mem_closure_iff]
    intro U hU hσU
    have hW : IsOpen (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) :=
      isOpen_biUnion fun h _ => hU.preimage (by fun_prop)
    have hcl : ∀ n : ℕ, IsClosed (Gj K n : Set (GQ l)) := fun n =>
      InfiniteGalois.fixingSubgroup_isClosed _
    have hanti : Antitone fun n : ℕ => (Gj K n : Set (GQ l)) := by
      intro m n hmn x hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K n hx
      refine ((hG K x hx0).1 m).2 ((((hG K x hx0).1 n).1 hx).trans
        (zpow_le_zpow_right₀ hl1.le (by omega)))
    have hint : ∀ x ∈ ⋂ n : ℕ, (Gj K n : Set (GQ l)),
        (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) ∈ nhds x := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K 0 (hx 0)
      have hxH : x ∈ Hinf K := by
        refine (hG K x hx0).2.2 (Units.ext ?_)
        rw [Units.val_one, ← sub_eq_zero, ← norm_le_zero_iff]
        by_contra hne
        obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (not_le.1 hne) (inv_lt_one_of_one_lt₀ hl1)
        have := ((hG K x hx0).1 n).1 (hx n)
        rw [zpow_neg, zpow_natCast, ← inv_pow] at this
        linarith
      exact hW.mem_nhds (Set.mem_biUnion hxH (by simpa using hσU))
    obtain ⟨n, hn'⟩ := exists_subset_nhds_of_compactSpace hanti.directed_ge hcl
      (mem_nhdsSet_iff_forall.2 hint)
    obtain ⟨a, ha⟩ := hcos σ hσ n
    obtain ⟨h, hh, hU'⟩ := Set.mem_iUnion₂.1 (hn' ha)
    refine ⟨h * g ^ a, ?_, h, hh, a, rfl⟩
    simpa [mul_assoc] using hU'

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.FrobDense

theorem placesS_finite (D : D7) (l : ℕ) : (placesS D l).Finite := by
  have h0 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 1) (D.host.g_prime 1).ne_zero
  have h2 := Formalism.L2.TwC.placesOver_finite' D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)
    (by split_ifs <;> first | exact D.host.pde'_prime.ne_zero | exact D.host.pde_prime.ne_zero)
  refine ((h0.union h1).union h2).subset ?_
  rintro v ⟨hv | hv | hv, -⟩
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr hv)
  · exact Or.inr hv

theorem frob_dense_goodSplit : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  intro D l Q hl hC
  have hfin : (placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host))).Finite :=
    ((Formalism.L2.TwC.placesOver_finite' D.host.E l hl.ne_zero).union (placesS_finite D l)).union Q.finite_toSet
  refine (hC hfin.toFinset).mono ?_
  rintro σ ⟨w, hwS, hsp, B, hB, hF⟩
  have hw : w ∉ placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host)) := by
    simpa using hwS
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  exact ⟨w, ⟨hsp, hw.1.1, hw.1.2, hw.2⟩, B, hB, hF⟩

end GlobalTheory.FrobDense
end
end
