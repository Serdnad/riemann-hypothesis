module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pLocFour :
    LocFour := by
  intro F _ _ v tr nm hΔ u hu
  haveI : CharZero (HeightOneSpectrum.adicCompletion F v) :=
    (RingHom.charZero_iff (algebraMap F (HeightOneSpectrum.adicCompletion F v)).injective).mp inferInstance
  have h2 : (2 : HeightOneSpectrum.adicCompletion F v) ≠ 0 := two_ne_zero
  have hD : ((tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm) ≠ 0 := by
    have h := (Int.cast_ne_zero (α := HeightOneSpectrum.adicCompletion F v)).mpr hΔ
    push_cast at h
    exact h
  set D : HeightOneSpectrum.adicCompletion F v := (tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm
    with hDdef
  let c : Fin 5 → HeightOneSpectrum.adicCompletion F v := ![1, -(D / 4), 1, -(D / 4), -u]
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, hD, hu]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le F v (ι := Fin 5) (by simp) c
  obtain ⟨z, hz4, hz⟩ := GlobalTheory.HermLocal.exists_zero_coord h2 hc hx0 hx 4
  have hz' : z 0 ^ 2 + -(D / 4) * z 1 ^ 2 + z 2 ^ 2 + -(D / 4) * z 3 ^ 2 + -u * z 4 ^ 2 = 0 := by
    rw [Fin.sum_univ_five] at hz
    simpa [c] using hz
  obtain ⟨w, hw⟩ : ∃ w, z 4 * w = 1 := ⟨(z 4)⁻¹, mul_inv_cancel₀ hz4⟩
  refine ⟨z 0 * w - tr / 2 * (z 1 * w), z 1 * w, z 2 * w - tr / 2 * (z 3 * w), z 3 * w, ?_⟩
  unfold qf
  rw [hDdef] at hz'
  linear_combination w ^ 2 * hz' + u * (z 4 * w + 1) * hw
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma pow_neg_three_lt_two_norm_sq (q : ℕ) [hq : Fact q.Prime] :
    (q : ℝ) ^ (-3 : ℤ) < ‖(2 : ℤ_[q])‖ ^ 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  by_cases h : q = 2
  · subst h
    have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
      have := PadicInt.norm_p_pow (p := 2) 1
      simpa using this
    rw [h2]
    norm_num
  · have h1 : ‖(2 : ℤ_[q])‖ = 1 := by
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have hd := (PadicInt.norm_int_lt_one_iff_dvd (p := q) 2).1 (by exact_mod_cast hlt)
      have hd' : q ∣ 2 := by exact_mod_cast hd
      exact h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hd')
    rw [h1, one_pow, _root_.zpow_neg]
    have hlt : (1 : ℝ) < (q : ℝ) ^ (3 : ℤ) := one_lt_zpow₀ (by linarith) (by norm_num)
    exact inv_lt_one_of_one_lt₀ hlt

private lemma sq_of_close (q : ℕ) [hq : Fact q.Prime] (z : ℤ_[q])
    (hz : ‖(1 : ℤ_[q]) - z‖ < ‖(2 : ℤ_[q])‖ ^ 2) : ∃ x : ℤ_[q], x ^ 2 = z := by
  have hn : ‖Polynomial.aeval (1 : ℤ_[q]) (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q])‖ <
      ‖Polynomial.aeval (1 : ℤ_[q])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q]))‖ ^ 2 := by
    simpa [Polynomial.derivative_X_pow, one_add_one_eq_two] using hz
  obtain ⟨x, hx, -⟩ := hensels_lemma hn
  refine ⟨x, ?_⟩
  simpa [sub_eq_zero] using hx

theorem UpperTheory.Gal.G1.pPadicSqFin :
    PadicSqFin := by
  intro q hq
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero 3 hq.out.ne_zero⟩
  refine ⟨Fintype.card (ZMod (q ^ 3)), fun u => Fintype.equivFin (ZMod (q ^ 3))
    (if h : ‖u‖ ≤ 1 then PadicInt.toZModPow 3 ⟨u, h⟩ else 0), ?_⟩
  intro u u' hu hu' hk
  simp only [dif_pos hu.le, dif_pos hu'.le, (Fintype.equivFin _).injective.eq_iff] at hk
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[q], (a : ℚ_[q]) = u ∧ PadicInt.toZModPow 3 a =
      PadicInt.toZModPow 3 ⟨u, hu.le⟩ := ⟨⟨u, hu.le⟩, rfl, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[q], (b : ℚ_[q]) = u' ∧ PadicInt.toZModPow 3 b =
      PadicInt.toZModPow 3 ⟨u', hu'.le⟩ := ⟨⟨u', hu'.le⟩, rfl, rfl⟩
  have hmem : b - a ∈ RingHom.ker (PadicInt.toZModPow (p := q) 3) := by
    rw [RingHom.sub_mem_ker_iff, ha.2, hb.2]
    exact hk.symm
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hd : ‖u' - u‖ ≤ (q : ℝ) ^ (-3 : ℤ) := by
    have h1 : ‖b - a‖ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
      rw [hc, norm_mul, PadicInt.norm_p_pow]
      have hc1 := PadicInt.norm_le_one c
      have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by positivity
      calc _ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) * 1 := mul_le_mul_of_nonneg_left hc1 hpos
        _ = _ := mul_one _
    rw [PadicInt.norm_def, PadicInt.coe_sub, ha.1, hb.1] at h1
    simpa using h1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hz : ‖u' / u‖ ≤ 1 := by
    rw [norm_div, hu, hu']
    simp
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[q], (w : ℚ_[q]) = u' / u := ⟨⟨u' / u, hz⟩, rfl⟩
  obtain ⟨x, hx⟩ := sq_of_close q w (by
    have e : ‖(1 : ℤ_[q]) - w‖ = ‖u' - u‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hw,
        show (1 : ℚ_[q]) - u' / u = (u - u') / u by field_simp, norm_div, hu, div_one,
        norm_sub_rev]
    rw [e]
    exact lt_of_le_of_lt hd (pow_neg_three_lt_two_norm_sq q))
  refine ⟨x, ?_⟩
  have hx' : (x : ℚ_[q]) ^ 2 = u' / u := by
    rw [← hw, ← hx]
    simp
  rw [hx']
  field_simp
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private theorem norm_padicEquiv_of_valued_eq_one (v : HeightOneSpectrum ℤ) (u : v.adicCompletion ℚ)
    (hu : Valued.v u = 1) : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hmem : ∀ w : v.adicCompletion ℚ, Valued.v w ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hw
    have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hw'
    simpa using this
  have h1 := hmem u hu.le
  have h2 := hmem u⁻¹ (by rw [map_inv₀, hu, inv_one])
  have h3 : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ *
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, norm_one]
  have h4 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u)
  have h5 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹)
  nlinarith

theorem UpperTheory.Gal.G1.pZSqFin :
    PadicSqFin → ZSqFin := by
  intro hP v
  obtain ⟨m, κ, hκ⟩ := hP (Rat.HeightOneSpectrum.primesEquiv v).1
  refine ⟨m, fun u => κ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u), ?_⟩
  intro u u' hu hu' huu
  obtain ⟨x, hx⟩ := hκ _ _ (norm_padicEquiv_of_valued_eq_one v u hu)
    (norm_padicEquiv_of_valued_eq_one v u' hu') huu
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x, ?_⟩
  have h := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hx
  rw [map_mul, map_pow] at h
  simpa using h
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pTrivMat :
    TrivMat := by
  intro E _ _ _ n H hH hH' hd R _ _ K _ _ ψ β x t hx
  let L := K ⊗[↥(maximalRealSubfield E)] E
  letI : Algebra ℚ L := ((algebraMap K L).comp (ψ.comp (algebraMap ℚ R))).toAlgebra
  let s : R →+* L := (algebraMap K L).comp ψ
  let e : E →+* L := Algebra.TensorProduct.includeRight.toRingHom
  let f : R →ₐ[ℚ] Matrix (Fin n) (Fin n) L := ((algebraMap L (Matrix (Fin n) (Fin n) L)).comp s).toRatAlgHom
  let g : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) L := (e.mapMatrix).toRatAlgHom
  have hfg : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes (s a) (g b)
  let φ := Algebra.TensorProduct.lift f g hfg
  have hφ : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), φ (r ⊗ₜ m) = s r • m.map e := by
    intro r m
    show f r * g m = _
    rw [Algebra.smul_def]
    rfl
  let c := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  have hc1 : ∀ y : E, c (e y) = e (cj E y) := by
    intro y
    simp [c, e, GlobalTheory.HermGlobal.baseConj]
  have hc2 : ∀ r : R, c (s r) = s r := by
    intro r
    show c (ψ r ⊗ₜ 1) = ψ r ⊗ₜ 1
    simp [c, GlobalTheory.HermGlobal.baseConj]
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  have hinv : (H.map e)⁻¹ = H⁻¹.map e := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hright : H.map e * H⁻¹.map e = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hmap : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E),
      (s r • m.map e).map c = s r • (m.map (cj E)).map e := by
    intro r m
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc1, hc2]
  have hH2 : H.map ⇑(↑(IsCMField.complexConj E) : E →+* E) = H := hH'
  have hstar : ∀ y, φ (MulOpposite.unop ((starT (hermStar H hd) R) y)) =
      H⁻¹.map e * ((φ y).map c)ᵀ * H.map e := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [starT_tmul, hermStar_apply, hφ, hφ, hmap, hH2, Matrix.map_mul, Matrix.map_mul,
        Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
    | add a b ha hb =>
      simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
      rw [Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  refine ⟨φ x, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit.map φ)
  · have key := congrArg φ hx
    rw [map_mul, map_mul, hstar, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, hφ, hφ, map_one, one_smul, Matrix.map_one _ (map_zero e) (map_one e)] at key
    show φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ = ψ t • H⁻¹.map e
    have hsm : ψ t • H⁻¹.map e = s t • H⁻¹.map e := (algebraMap_smul L (ψ t) _).symm
    rw [hsm]
    calc φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ
        = φ x * β.map e * (H⁻¹.map e * ((φ x).map c)ᵀ * H.map e) * H⁻¹.map e := by
          rw [Matrix.map_mul]
          simp only [Matrix.mul_assoc, hright, Matrix.mul_one]
      _ = s t • H⁻¹.map e := by
          rw [key, Matrix.smul_mul, Matrix.one_mul]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem key_mat {E : Type} [Field E] {n : ℕ} (H Q b b' R : Matrix (Fin n) (Fin n) E) (hd : H.det ≠ 0) (s : E)
    (h : b' * H⁻¹ = Q * (s • (b * H⁻¹)) * R) : b' = s • (Q * b * (H⁻¹ * R * H)) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  have h1 : b' = (b' * H⁻¹) * H := (Matrix.nonsing_inv_mul_cancel_right _ _ hu).symm
  rw [h1, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem pRelOf : RelOf := by
  intro E _ _ _ A n p _ S B B' s hs P hP h
  have hH := A.det_ne n
  have key := key_mat (A.H n) Pᵀ (mat S ↑B.β) (mat S ↑B'.β) (P.map ⇑(IsCMField.complexConj E)) hH
    (s : E) h
  have hdetT : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hP
  have hu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdetT
  have hHc : (A.H n).map ⇑(IsCMField.complexConj E) = A.H n := by
    have h1 := A.herm n
    calc (A.H n).map ⇑(IsCMField.complexConj E) = (((A.H n).map (cj E))ᵀ)ᵀ :=
          (Matrix.transpose_transpose _).symm
      _ = (A.H n)ᵀ := by rw [h1]
      _ = A.H n := by simp [Arith.H]
  have hsh : MulOpposite.unop (hermStar (A.H n) hH Pᵀ) = (A.H n)⁻¹ * P.map ⇑(IsCMField.complexConj E) * A.H n := by
    rw [hermStar_apply]
    change ((A.H n).map ⇑(IsCMField.complexConj E))⁻¹ * ((Pᵀ).map ⇑(IsCMField.complexConj E))ᵀ *
      (A.H n).map ⇑(IsCMField.complexConj E) = _
    rw [hHc, Matrix.transpose_map, Matrix.transpose_transpose]
  refine ⟨hu.unit, s, hs, ?_⟩
  change mat S ↑B'.β = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s *
    (Pᵀ * mat S ↑B.β * MulOpposite.unop (hermStar (A.H n) hH Pᵀ))
  rw [hsh, key, ← Algebra.smul_def, ← algebraMap_smul E s, eq_ratCast]

end UpperTheory.Gal.G1
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

open scoped MatrixOrder ComplexOrder in
private lemma exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ A = Bᴴ * B := by
  have h0 : 0 ≤ A := hA.posSemidef.nonneg
  have h1 := CFC.sqrt_mul_sqrt_self A h0
  have h2 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  refine ⟨CFC.sqrt A, ?_, ?_⟩
  · have hu : IsUnit (CFC.sqrt A * CFC.sqrt A) := by
      rw [h1]
      exact hA.isUnit
    exact isUnit_of_mul_isUnit_left hu
  · rw [← Matrix.star_eq_conjTranspose, h2.star_eq, h1]

open scoped ComplexOrder in
private lemma smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {ε : ℝ}
    (h : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (M *ᵥ x)).re) : ((ε : ℂ) • M).PosDef := by
  have hH : ((ε : ℂ) • M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hM.eq]
    simp
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have him := hM.im_star_dotProduct_mulVec_self x
  have e : star x ⬝ᵥ ((ε : ℂ) • M) *ᵥ x = (ε : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [e, Complex.lt_def]
  simp only [RCLike.im_to_complex] at him
  constructor
  · simpa [him] using h x hx
  · simp [him]

theorem UpperTheory.Gal.G1.pInfCongr :
    InfCongr := by
  intro n G G' hG hG' ε h h'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, by simp, ?_⟩
    exact Subsingleton.elim _ _
  have hε : (ε : ℂ) ≠ 0 := by
    intro h0
    have hx : (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, hn⟩
      simp at this
    have := h _ hx
    rw [Complex.ofReal_eq_zero.1 h0] at this
    simp at this
  obtain ⟨B, hB, hBe⟩ := exists_factor (smul_posDef hG h)
  obtain ⟨C, hC, hCe⟩ := exists_factor (smul_posDef hG' h')
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  set P := B⁻¹ * C with hP
  have hBP : B * P = C := by
    rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBd, Matrix.one_mul]
  have key : (ε : ℂ) • G' = (ε : ℂ) • (Pᴴ * G * P) := by
    calc (ε : ℂ) • G' = Cᴴ * C := hCe
      _ = (B * P)ᴴ * (B * P) := by rw [hBP]
      _ = Pᴴ * (Bᴴ * B) * P := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Pᴴ * ((ε : ℂ) • G) * P := by rw [hBe]
      _ = (ε : ℂ) • (Pᴴ * G * P) := by rw [Matrix.mul_smul, Matrix.smul_mul]
  have hG'P : G' = Pᴴ * G * P := smul_right_injective _ hε key
  refine ⟨P.map (starRingEnd ℂ), ?_, ?_⟩
  · have hdet := (starRingEnd ℂ).map_det P
    rw [RingHom.mapMatrix_apply] at hdet
    rw [← hdet, map_ne_zero, hP, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det B hBd).mul hCd).ne_zero
  · have e1 : (P.map (starRingEnd ℂ))ᵀ = Pᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have e2 : (P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P := by
      ext i j
      simp
    rw [e1, e2]
    exact hG'P
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pPadMap :
    PadMap := by
  intro F _ _ w
  set u : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w with hu
  set v : HeightOneSpectrum ℤ := GlobalTheory.NormLevelCompare.primeCorr.symm u with hv
  have hw : HeightOneSpectrum.under (𝓞 ℚ) w = GlobalTheory.NormLevelCompare.primeCorr v := by
    rw [hv, Equiv.apply_symm_apply]
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let f₁ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom
  letI : Algebra ℚ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (Rat.HeightOneSpectrum.primesEquiv v)).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (Rat.HeightOneSpectrum.primesEquiv v))
  let f₂ := (Padic.adicCompletionEquiv (𝓞 ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v)).toRingEquiv.toRingHom
  refine ⟨v, ((GlobalTheory.LFun.complMap (F := ℚ) (E := F) hw).comp f₂).comp f₁, ?_⟩
  intro q hq
  have hgen : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator u := by
    change (Rat.HeightOneSpectrum.primesEquiv v).1 = (Rat.HeightOneSpectrum.primesEquiv u).1
    simp [hv, GlobalTheory.NormLevelCompare.primeCorr]
  set p := Rat.HeightOneSpectrum.natGenerator u with hp
  have hdvd : (p : ℤ) ∣ q := by
    have hfix : Rat.IsIntegralClosure.intEquiv ℤ q = q := by
      simpa using map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) q
    have hmem : q ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
      rw [← hfix]
      exact (Ideal.apply_mem_of_equiv_iff).2 hq
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, hgen] at hmem
    exact hmem
  have hpu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff u (n := p)).1 dvd_rfl
    rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p] at h
    exact (Ideal.apply_mem_of_equiv_iff).1 h
  have hpw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have h : algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal := hpu
    simpa using h
  obtain ⟨k, rfl⟩ := hdvd
  push_cast
  exact Ideal.mul_mem_right _ _ (by exact_mod_cast hpw)
end
