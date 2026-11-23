module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def orthogonalFamilyAlt (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : Submodule (𝓞 E) D.La where
  carrier := {y | ∀ a, sesq D (x' a) y = 0}
  add_mem' := by
    intro y y' hy hy' a
    rw [(sesq_sesquilinear_properties D).2.2.1, hy a, hy' a, add_zero]
  zero_mem' := by
    intro a
    have := (sesq_sesquilinear_properties D).2.2.2.2.1 0 (x' a) 0
    simpa using this
  smul_mem' := by
    intro c y hy a
    rw [(sesq_sesquilinear_properties D).2.2.2.2.1, hy a, mul_zero]

theorem nsmul_injective_lattice (D : Datum H) {m : ℕ} (hm : m ≠ 0) {y y' : D.La} (h : m • y = m • y') : y = y' := by
  haveI := D.fin
  haveI := D.proj
  have hm' : (m : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  have h' : (m : 𝓞 E) • y = (m : 𝓞 E) • y' := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  exact smul_right_injective _ hm' h'

theorem padic_norm_sesq_le (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (y y' : D.La) :
    ‖j (sesq D y y')‖ ≤ Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0, -, hL⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) _ hinj hne
  have hca : (j.comp (algebraMap (𝓞 E) E)) a = j (a : E) := rfl
  have hja : 0 < ‖j (a : E)‖ := by
    rw [← hca]
    exact norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).mpr ha0)
  rw [hL, hca, Real.exp_neg, Real.exp_log hja]
  obtain ⟨b, hb⟩ := (sesq_sesquilinear_properties D).2.2.2.2.2.2 a ha y y'
  have hb1 : ‖j (b : E)‖ ≤ 1 :=
    (GlobalTheory.T.padic_integral_iff_denominator E ℓ (b : E)).mpr ⟨1, b, Nat.Prime.not_dvd_one ℓ.prop, by simp⟩ j
  have hm : ‖j (a : E)‖ * ‖j (sesq D y y')‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul, hb]
    exact hb1
  calc ‖j (sesq D y y')‖ = ‖j (a : E)‖⁻¹ * (‖j (a : E)‖ * ‖j (sesq D y y')‖) := by
        field_simp
    _ ≤ ‖j (a : E)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hja.le)
    _ = ‖j (a : E)‖⁻¹ := mul_one _

def pairingVector (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E := fun b => sesq D (x' b) y

def projectionCoeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E :=
  (gramE D x')⁻¹ *ᵥ pairingVector D x' y

theorem padic_norm_projectionCoeffs_le (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) (y : D.La) (a : Fin p)
    (j : E →+* ℂ_[ℓ]) : ‖j (projectionCoeffs D x' y a)‖ ≤ 1 := by
  classical
  set R := Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hdetn : ‖j (gramE D x').det‖ = R ^ p := by
    have h0 : 0 < ‖j (gramE D x').det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hdet)
    rw [← Real.exp_log h0, hlog j, hR, ← Real.exp_nat_mul]
    congr 1
    ring
  have he : projectionCoeffs D x' y a =
      (gramE D x').det⁻¹ * ((gramE D x').updateCol a (pairingVector D x' y)).det := by
    rw [projectionCoeffs, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
      ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  have hb : ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ R ^ p := by
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] (Fin p) (j.mapMatrix ((gramE D x').updateCol a (pairingVector D x' y)))
      R hR0.le (fun b c => by
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        split_ifs
        · exact padic_norm_sesq_le D ℓ j _ _
        · simpa [gramE] using padic_norm_sesq_le D ℓ j (x' b) (x' c))
    simpa using this
  rw [he, map_mul, norm_mul, map_inv₀, norm_inv, hdetn]
  calc (R ^ p)⁻¹ * ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ (R ^ p)⁻¹ * R ^ p :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := inv_mul_cancel₀ (pow_pos hR0 p).ne'

theorem projectionCoeffs_add (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y y' : D.La) :
    projectionCoeffs D x' (y + y') = projectionCoeffs D x' y + projectionCoeffs D x' y' := by
  have : pairingVector D x' (y + y') = pairingVector D x' y + pairingVector D x' y' := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_add]

theorem projectionCoeffs_smul (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (c : 𝓞 E) (y : D.La) :
    projectionCoeffs D x' (c • y) = IsCMField.complexConj E (c : E) • projectionCoeffs D x' y := by
  have : pairingVector D x' (c • y) = IsCMField.complexConj E (c : E) • pairingVector D x' y := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_smul]

theorem gram_mulVec_projection_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0) (y : D.La) :
    gramE D x' *ᵥ projectionCoeffs D x' y = pairingVector D x' y := by
  rw [projectionCoeffs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

theorem sesq_integral_combination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (d : Fin p → 𝓞 E) (b : Fin p) :
    sesq D (x' b) (∑ a, d a • x' a) = ∑ a, gramE D x' b a * IsCMField.complexConj E (d a : E) := by
  let f : D.La →+ E := AddMonoidHom.mk' (sesq D (x' b)) (fun y y' => (sesq_sesquilinear_properties D).2.2.1 _ _ _)
  have hf : sesq D (x' b) (∑ a, d a • x' a) = f (∑ a, d a • x' a) := rfl

  rw [hf, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show sesq D (x' b) (d a • x' a) = _
  rw [(sesq_sesquilinear_properties D).2.2.2.2.1, mul_comm]
  simp [gramE]

end GlobalTheory.CompanionTheory.Ar.Fl

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem pure_type_periods_span_whole_space {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {n : ℕ} (hn : 0 < n)
    (h : ∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} = ⊤ := by
  classical
  set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
  have hsub : Set.range P ⊆ (Submodule.span ℂ S : Set (Fin g → ℂ)) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h y
    have h1 : P a ∈ Submodule.span ℂ S := Submodule.subset_span ⟨true, ⟨a, ha⟩, rfl⟩
    have h2 : P b ∈ Submodule.span ℂ S := Submodule.subset_span ⟨false, ⟨b, hb⟩, rfl⟩
    have h3 : (n : ℂ) • P y = P a + P b := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hab, map_add (f := _)]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h4 : P y = (n : ℂ)⁻¹ • (P a + P b) := by
      rw [← h3, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [SetLike.mem_coe, h4]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 h2)
  have hR := hP.2.2.2.1
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hR]; trivial
  have hle : Submodule.span ℝ (Set.range P) ≤ (Submodule.span ℂ S).restrictScalars ℝ :=
    Submodule.span_le.mpr hsub
  exact hle hz

theorem periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  intro E _ _ _ H D g ty P hP n hn h
  classical
  refine ⟨?_, ?_⟩
  · have h1 := (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2
    have h2 := GlobalTheory.datum_finrank_int D
    exact Nat.eq_of_mul_eq_mul_left two_pos (h1.symm.trans h2)
  · have hspan := pure_type_periods_span_whole_space hP hn h
    set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
    obtain ⟨s, hsS, hs, hli⟩ := exists_linearIndependent ℂ S
    have hst : Submodule.span ℂ (Set.range ((↑) : s → (Fin g → ℂ))) = ⊤ := by
      rw [Subtype.range_coe, hs, hspan]
    let bs := Module.Basis.mk hli (le_of_eq hst.symm)
    let e : Fin g ≃ s := (bs.indexEquiv (Pi.basisFun ℂ (Fin g))).symm
    have hmem : ∀ k, ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = (e k : Fin g → ℂ) :=
      fun k => hsS (e k).2
    choose bf af haf using hmem
    refine ⟨bf, af, fun z => ?_⟩
    have hz : z ∈ Submodule.span ℂ (Set.range fun k => P (af k)) := by
      have hr : (Set.range fun k => P (af k)) = Set.range ((↑) : s → (Fin g → ℂ)) := by
        ext v
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨e k, (haf k).symm⟩
        · rintro ⟨t, rfl⟩
          exact ⟨e.symm t, by simp [haf]⟩
      rw [hr, hst]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    exact ⟨c, hc.symm⟩

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem sesq_zero_left' (y : D.La) : sesq D 0 y = 0 := by
  have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem sesq_sum_smul_left {I : Type} [Fintype I] (c : I → 𝓞 E) (e : I → D.La) (y : D.La) :
    sesq D (∑ i, c i • e i) y = ∑ i, (c i : E) * sesq D (e i) y := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [sesq_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1, ih]

theorem sesq_zero_right' (x : D.La) : sesq D x 0 = 0 := by
  have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1 x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem sesq_sum_smul_right {I : Type} [Fintype I] (c : I → 𝓞 E) (e : I → D.La) (x : D.La) :
    sesq D x (∑ i, c i • e i) = ∑ i, IsCMField.complexConj E (c i : E) * sesq D x (e i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [sesq_zero_right']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, ih]

end

theorem exists_transition_matrix_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → ∃ T : Matrix I I E, IsTransition D x e T ∧ gramE D x = T * gramE D e * (T.map (IsCMField.complexConj E)).transpose ∧ (LinearIndependent (𝓞 E) x → T.det ≠ 0) ∧ ∃ (n : ℕ) (S : Matrix I I (𝓞 E)), 0 < n ∧ (∀ a, n • x a = ∑ b, S a b • e b) ∧ ∀ a b, (S a b : E) = n * T a b := by
  intro E _ _ _ H D I _ _ x e hcard he
  classical
  have := D.fin
  have := D.proj
  obtain ⟨n, hn, hsp⟩ := exists_nsmul_mem_span_full_family e (hcard.trans D.rank.symm) he
  have hS : ∀ a, ∃ c : I → 𝓞 E, ∑ b, c b • e b = n • x a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hsp (x a))
  choose S hSx using hS
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  set T : Matrix I I E := Matrix.of fun a b => (S a b : E) / n with hT
  have hST : ∀ a b, (S a b : E) = n * T a b := fun a b => by
    simp only [hT, Matrix.of_apply]; field_simp
  have hsn : ∀ (z y : D.La), sesq D (n • z) y = (n : E) * sesq D z y := fun z y => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1]; simp
  have hsn' : ∀ (z y : D.La), sesq D z (n • y) = (n : E) * sesq D z y := fun z y => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]; simp
  have htrans : IsTransition D x e T := by
    intro m y
    have h := congrArg (fun z => sesq D z y) (hSx m)
    rw [sesq_sum_smul_left, hsn] at h
    apply mul_left_cancel₀ hn0
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hST]; ring
  have hcol : ∀ i k, sesq D (e i) (x k) = ∑ j, IsCMField.complexConj E (T k j) * sesq D (e i) (e j) := by
    intro i k
    have h := congrArg (fun z => sesq D (e i) z) (hSx k)
    rw [sesq_sum_smul_right, hsn'] at h
    apply mul_left_cancel₀ hn0
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hST, map_mul, map_natCast]; ring
  refine ⟨T, htrans, ?_, ?_, n, S, hn, fun a => (hSx a).symm, hST⟩
  · ext m k
    simp only [gramE, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [htrans m (x k)]
    simp_rw [hcol, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro hx hdet
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image v)
    choose w hw using fun m => hc (v m) (Finset.mem_image_of_mem v (Finset.mem_univ m))
    have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.coe_ne_zero c
    have hwv : ∀ m, (w m : E) = (c : 𝓞 E) * v m := fun m => by
      rw [show ((w m : 𝓞 E) : E) = algebraMap (𝓞 E) E (w m) from rfl, hw m, Algebra.smul_def]
    have hsum : ∑ m, (w m * (n : 𝓞 E)) • x m = 0 := by
      have e1 : ∑ m, (w m * (n : 𝓞 E)) • x m = ∑ b, (∑ m, w m * S m b) • e b := by
        simp_rw [mul_smul, Nat.cast_smul_eq_nsmul, ← hSx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
      rw [e1]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : (∑ m, w m * S m b : 𝓞 E) = 0 := by
        apply RingOfIntegers.coe_injective (K := E)
        push_cast
        simp_rw [hwv, hST]
        have hvb := congrFun hv b
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hvb
        calc ∑ m, (c : 𝓞 E) * v m * (n * T m b) = (c : 𝓞 E) * n * ∑ m, v m * T m b := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
          _ = 0 := by rw [hvb, mul_zero]
          _ = ((0 : 𝓞 E) : E) := by simp
      rw [this, zero_smul]
    have hz := (Fintype.linearIndependent_iff.1 hx) _ hsum
    apply hv0
    funext m
    have hm := hz m
    have hw0 : w m = 0 := by
      rcases mul_eq_zero.1 hm with h | h
      · exact h
      · exact absurd h (by exact_mod_cast hn.ne')
    have : (c : 𝓞 E) * v m = 0 := by rw [← hwv, hw0]; simp
    simpa [hc0] using this

end PositivityTheory.Xgf
end
