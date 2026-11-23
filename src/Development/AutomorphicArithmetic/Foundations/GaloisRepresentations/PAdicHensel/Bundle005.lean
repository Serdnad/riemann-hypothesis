module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem re_dot_swap {n : ℕ} (y x : Fin n → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem def_of_inv {n : ℕ} (M Mi : Matrix (Fin n) (Fin n) ℂ) (h1 : Mi * M = 1) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (Mi *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hy : M *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (fun v => Mi *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, h1] using this
  have := h _ hy
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, re_dot_swap] at this

private theorem def_conj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (M *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x)).re := by
  have hy : star x ≠ 0 := by
    intro h0
    apply hx
    simpa using congrArg star h0
  have key : star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x) =
      starRingEnd ℂ (star (star x) ⬝ᵥ (M *ᵥ star x)) := by

    simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
  rw [key, Complex.conj_re]
  exact h _ hy

private theorem inv_map_ring {n : ℕ} {R R' : Type*} [Field R] [Field R'] (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (hA : A.det ≠ 0) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
    Matrix.map_one _ (map_zero f) (map_one f)]

private theorem herm_N {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (H β : Matrix (Fin n) (Fin n) E)
    (hH : H.map (cj E) = H) (hT : Hᵀ = H) (hd : H.det ≠ 0) (hs : H⁻¹ * (β.map (cj E))ᵀ * H = β) (a b : Fin n) :
    IsCMField.complexConj E ((β * H⁻¹) a b) = (β * H⁻¹) b a := by
  have hHi : (H⁻¹).map (cj E) = H⁻¹ := by rw [inv_map_ring _ _ hd, hH]
  have hHiT : (H⁻¹)ᵀ = H⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have key : ((β * H⁻¹).map (cj E))ᵀ = β * H⁻¹ := by
    rw [Matrix.map_mul, hHi, Matrix.transpose_mul, hHiT]
    conv_rhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_one]
  have := congrFun (congrFun key b) a
  rw [Matrix.transpose_apply, Matrix.map_apply] at this
  exact this

theorem UpperTheory.Gal.G1.pDefSign :
    DefSign := by
  classical
  intro E _ _ _ A n p _ S B
  have hT : (A.H n)ᵀ = A.H n := Matrix.diagonal_transpose _
  have hH' : (A.H n).map (cj E) = A.H n := by
    have h := congrArg Matrix.transpose (A.herm n)
    rw [Matrix.transpose_transpose] at h
    rw [h]
    exact hT
  have hsym : (A.H n)⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * A.H n = mat S ↑B.β := by
    have h := B.sym
    change MulOpposite.unop (hermStar (A.H n) (A.det_ne n) (mat S ↑B.β)) = mat S ↑B.β at h
    rw [hermStar_apply] at h
    change ((A.H n).map (cj E))⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * (A.H n).map (cj E) = _ at h
    rwa [hH'] at h
  refine ⟨herm_N _ _ hH' hT (A.det_ne n) hsym, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · have hu : IsUnit (mat S ↑B.β) := B.β.isUnit
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero (A.det_ne n)
  · intro τ x hx
    set v := InfinitePlace.mk τ with hvdef
    set ε : ℝ := if v = InfinitePlace.mk A.τ₀ then 1 else -1 with hεdef
    have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < ε *
        (star y ⬝ᵥ ((((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *ᵥ y)).re := by
      intro y hy
      have hp := B.posR v y hy
      have hsig : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
      rw [hsig] at hp
      have hme : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
      by_cases hv : v = InfinitePlace.mk A.τ₀
      · have h1 := ((S.sig v.embedding).1 (by rw [hme]; exact hv)).1
        rw [hεdef, if_pos hv, one_mul]
        exact hp.1 h1
      · have h0 := ((S.sig v.embedding).2 (by rw [hme]; exact hv)).1
        rw [hεdef, if_neg hv, neg_one_mul, neg_pos]
        exact hp.2 (by rw [h0]; exact zero_ne_one)
    have h1 : (((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *
        (mat S ↑B.β * (A.H n)⁻¹).map v.embedding = 1 := by
      have hb : mat S ↑(B.β⁻¹) * mat S ↑B.β = 1 := B.β.inv_mul
      have h2 : A.H n * mat S ↑(B.β⁻¹) * (mat S ↑B.β * (A.H n)⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mat S ↑(B.β⁻¹)), hb, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A.det_ne n))]
      rw [← Matrix.transpose_map, hT, ← Matrix.map_mul, ← Matrix.map_mul, h2,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hM := def_of_inv _ _ h1 ε hpos
    rcases InfinitePlace.embedding_mk_eq τ with he | he
    · have he' : v.embedding = τ := he
      rw [he'] at hM
      exact hM x hx
    · have he' : v.embedding = ComplexEmbedding.conjugate τ := he
      rw [he'] at hM
      have hc := def_conj _ ε hM x hx
      have hcc : ((mat S ↑B.β * (A.H n)⁻¹).map (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) =
          (mat S ↑B.β * (A.H n)⁻¹).map τ := by
        ext i j
        simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [hcc] at hc
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem splitCore {n : ℕ} {B : Type*} [CommRing B] (s : B →+* B) (e e' : B)
    (hee' : e * e' = 0) (hsum : e + e' = 1) (hse : s e = e') (hse' : s e' = e)
    (G G' Gi : Matrix (Fin n) (Fin n) B) (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hG : (G.map s)ᵀ = G) (hG' : (G'.map s)ᵀ = G') (hdet : IsUnit G'.det) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ G' = Pᵀ * G * P.map s := by
  classical
  have hs1 : (G.map s) * (Gi.map s) = 1 := by
    rw [← Matrix.map_mul, hGGi, Matrix.map_one s s.map_zero s.map_one]
  have hsGi : (Gi.map s)ᵀ = Gi := by
    have h2 : (Gi.map s)ᵀ * G = 1 := by
      have := congrArg Matrix.transpose hs1
      rwa [Matrix.transpose_mul, hG, Matrix.transpose_one] at this
    calc (Gi.map s)ᵀ = (Gi.map s)ᵀ * (G * Gi) := by rw [hGGi, Matrix.mul_one]
      _ = ((Gi.map s)ᵀ * G) * Gi := by rw [Matrix.mul_assoc]
      _ = Gi := by rw [h2, Matrix.one_mul]
  have hA : ((G' * Gi)ᵀ).map s = Gi * G' := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hsGi, hG']
  have hee : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [hsum, hee', mul_one, sub_zero]
  have he'e' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e * e' := by ring
      _ = e' := by rw [hsum, hee', mul_one, sub_zero]
  have he'e : e' * e = 0 := by rw [mul_comm, hee']
  have hu : IsUnit G'.det := hdet
  set A : Matrix (Fin n) (Fin n) B := (G' * Gi)ᵀ with hAdef
  set Ai : Matrix (Fin n) (Fin n) B := (G * G'⁻¹)ᵀ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G'⁻¹,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, hGGi, Matrix.transpose_one]
  refine ⟨e • A + e' • 1, ?_, ?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := e • Ai + e' • 1)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      Matrix.mul_one, Matrix.one_mul, hAAi, hee, he'e', hee', he'e, zero_smul, add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]
  · have hP : (e • A + e' • (1 : Matrix (Fin n) (Fin n) B)).map s = e' • (Gi * G') + e • 1 := by
      rw [Matrix.map_add _ (map_add s), Matrix.map_smul' _ _ _ (map_mul s),
        Matrix.map_smul' _ _ _ (map_mul s), hA, Matrix.map_one s s.map_zero s.map_one, hse, hse']
    rw [hP]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hAdef,
      Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hGiG, hGGi,
      ← Matrix.mul_assoc Gi G, ← Matrix.mul_assoc G Gi, hee, he'e', hee', he'e, zero_smul,
      add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]

theorem UpperTheory.Gal.G1.pSplitCongr :
    SplitCongr := by
  intro E _ _ _ n N N' hN hN' hN0 hN'0 K _ _ θ D hD hθc hθ r hr
  set σ := IsCMField.complexConj E with hσeq
  set R : E →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeRight with hReq
  set L : K →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeLeft with hLeq
  set sB := GlobalTheory.HermGlobal.baseConj σ K with hsBeq
  have hsL : ∀ a : K, sB (L a) = L a := by
    intro a
    simp [hsBeq, hLeq, GlobalTheory.HermGlobal.baseConj]
  have hsR : ∀ x : E, sB (R x) = R (σ x) := by
    intro x
    simp [hsBeq, hReq, GlobalTheory.HermGlobal.baseConj]
  have hDE : (D : E) ≠ 0 := Int.cast_ne_zero.mpr hD
  set w := L r * R (θ / D) with hweq
  have hww : w * w = 1 := by
    have h1 : L r * L r = R (D : E) := by
      rw [← map_mul, ← sq, hr, map_intCast, map_intCast]
    calc w * w = (L r * L r) * (R (θ / D) * R (θ / D)) := by rw [hweq]; ring
      _ = R ((D : E) * (θ / D * (θ / D))) := by rw [h1, ← map_mul, ← map_mul]
      _ = 1 := by
        rw [div_mul_div_comm, ← sq θ, hθ]
        rw [show (D : E) * ((D : E) / (D * D)) = 1 by field_simp]
        exact map_one R
  have hsw : sB w = -w := by
    rw [hweq, map_mul, hsL, hsR, map_div₀, hθc, map_intCast, neg_div, map_neg, mul_neg]
  set h := R (2 : E)⁻¹ with hheq
  have hsh : sB h = h := by
    rw [hheq, hsR, map_inv₀, map_ofNat]
  have h2 : h * 2 = 1 := by
    rw [hheq, show (2 : K ⊗[maximalRealSubfield E] E) = R 2 from (map_ofNat R 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero), map_one]
  set e := h * (1 + w) with heeq
  set e' := h * (1 - w) with he'eq
  have hee' : e * e' = 0 := by
    calc e * e' = h * h * (1 - w * w) := by rw [heeq, he'eq]; ring
      _ = 0 := by rw [hww, sub_self, mul_zero]
  have hsum : e + e' = 1 := by
    calc e + e' = h * 2 := by rw [heeq, he'eq]; ring
      _ = 1 := h2
  have hse : sB e = e' := by
    rw [heeq, he'eq, map_mul, map_add (f := _), map_one, hsh, hsw, sub_eq_add_neg]
  have hse' : sB e' = e := by
    rw [heeq, he'eq, map_mul, map_sub, map_one, hsh, hsw, sub_neg_eq_add]
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN0
  have hN'u : IsUnit N'.det := isUnit_iff_ne_zero.mpr hN'0
  have hGGi : N.map R * N⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hGiG : N⁻¹.map R * N.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG'G'i : N'.map R * N'⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N' hN'u, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG : ((N.map R).map sB.toRingHom)ᵀ = N.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN b a))
  have hG' : ((N'.map R).map sB.toRingHom)ᵀ = N'.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN' b a))
  obtain ⟨P, hP, hPe⟩ := splitCore sB.toRingHom e e' hee' hsum hse hse' (N.map R) (N'.map R)
    (N⁻¹.map R) hGGi hGiG hG hG' (Matrix.isUnit_det_of_right_inverse hG'G'i)
  refine ⟨P, hP, ?_⟩
  exact hPe
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pIsoEx :
    NormTwo → BlockMat → IsoEx := by
  intro hN hB E _ _ _ A n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, y, hxy, hint⟩ := hN E A
  have hinv : ∀ z, cF E (cF E z) = z := fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z
  have hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) := by
    refine (conjFin_algebraMap _ _).trans (congrArg _ ?_)
    change IsCMField.complexConj E (A.c : E) = (A.c : E)
    rw [← A.bar_eq, A.c_real]
  obtain ⟨a, ha, hS⟩ := hB _ (cF E) hinv _ x y hfix hxy m
  refine ⟨a, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map
        (algebraMap E (FiniteAdeleRing (𝓞 E) E)) =
        Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else
          algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Arith.dg]
      split_ifs <;> simp
    rw [hd]
    exact ha
  · intro w q hq hg hqw
    obtain ⟨h1, h2, h3, h4⟩ := hint w q hq hg hqw
    have hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈
        (w.adicCompletionIntegers E).toSubring.comap (pLoc E w) := by
      change Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le
        (HeightOneSpectrum.valuation_le_one w A.c)
    have hall := hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc
    rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
    refine ⟨fun i j => (hall i j).1, fun i j => ?_⟩
    rw [← map_inv]
    exact (hall i j).2
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pNormTwo :
    AdFour → NormTwo := by
  intro hA E _ _ _ A
  let F : Type := maximalRealSubfield E
  have hcF : (A.c : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff E, ← A.bar_eq, A.c_real]
  let cf : F := ⟨(A.c : E), hcF⟩
  have hcfE : algebraMap F E cf = (A.c : E) := rfl
  have hcint : IsIntegral ℤ cf := by
    have h : IsIntegral ℤ (algebraMap F E cf) := by rw [hcfE]; exact A.c.2
    exact (isIntegral_algebraMap_iff ).1 h
  let c0 : 𝓞 F := ⟨cf, hcint⟩
  have hc0 : ((c0 : 𝓞 F) : F) = cf := rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have h1 : ((c0 : 𝓞 F) : F) = 0 := by rw [h]; simp
    have h2 : (A.c : E) = 0 := by
      rw [← hcfE, ← hc0, h1, map_zero]
    exact A.c_ne h2
  obtain ⟨a, ha1, ha2⟩ := hA F A.tr A.nm A.disc_neg.ne c0 hc0ne
  let ι := GlobalTheory.AdeleBaseChange.adMap F E
  let ω' : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.ω : E)
  let ωb : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((A.bar A.ω : 𝓞 E) : E)
  have hfix : ∀ x : F, (IsCMField.complexConj E).toRingEquiv (algebraMap F E x) = algebraMap F E x := fun x =>
    (IsCMField.complexConj_eq_self_iff E _).2 x.2
  have hcι : ∀ z, cF E (ι z) = ι z := fun z => GlobalTheory.DefU.ClassFin.conjFin_adMap _ hfix z
  have hcω : cF E ω' = ωb := by
    show conjFin _ (algebraMap E _ _) = _
    rw [conjFin_algebraMap]
    show algebraMap E _ (IsCMField.complexConj E (A.ω : E)) = _
    rw [← A.bar_eq]
  have hsum : ω' + ωb = (A.tr : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) + ((A.bar A.ω : 𝓞 E) : E) = (A.tr : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.tr_eq
      simpa using this
    show algebraMap E _ _ + algebraMap E _ _ = _
    rw [← map_add (f := _), h, map_intCast]
  have hprod : ω' * ωb = (A.nm : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) * ((A.bar A.ω : 𝓞 E) : E) = (A.nm : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.nm_eq
      simpa using this
    show algebraMap E _ _ * algebraMap E _ _ = _
    rw [← map_mul, h, map_intCast]
  have hnorm : ∀ s t, (ι s + ι t * ω') * cF E (ι s + ι t * ω') = ι (qf A.tr A.nm s t) := by
    intro s t
    rw [map_add (f := _), map_mul, hcι, hcι, hcω]
    simp only [qf, map_add (f := _), map_mul, map_pow, map_intCast]
    linear_combination (ι s * ι t) * hsum + (ι t) ^ 2 * hprod
  have hcalg : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) =
      ι (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c0 : 𝓞 F) : F)) := by
    rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap]
    rfl
  refine ⟨ι (a 0) + ι (a 1) * ω', ι (a 2) + ι (a 3) * ω', ?_, ?_⟩
  · rw [hnorm, hnorm, hcalg, ← map_add (f := _), ← map_mul, ha1, map_one]
  · intro w q hq hG hqw
    let v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F)
    have hqv : (q : 𝓞 F) ∈ v.asIdeal := by
      show algebraMap (𝓞 F) (𝓞 E) (q : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hqw
    have hcv : c0 ∉ v.asIdeal := by
      intro hc
      have hcw : A.c ∈ w.asIdeal := hc
      obtain ⟨e, hcop, -, c', hc'⟩ := hG.2
      have hew : (e : 𝓞 E) ∈ w.asIdeal := hc' ▸ w.asIdeal.mul_mem_right c' hcw
      have hb := Nat.isCoprime_iff_coprime.2 hcop
      obtain ⟨u, u', huu⟩ := hb
      have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
        have h2 : (u : 𝓞 E) * (e : 𝓞 E) + (u' : 𝓞 E) * (q : 𝓞 E) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huu
        rw [← h2]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hew) (w.asIdeal.mul_mem_left _ hqw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hai : ∀ i, a i v ∈ v.adicCompletionIntegers F :=
      ha2 v q hq hqv hG.1.1 hG.1.2 hcv
    have hιi : ∀ i, pLoc E w (ι (a i)) ∈ w.adicCompletionIntegers E := fun i =>
      GlobalTheory.AdeleBaseChange.locMap_int w _ (hai i)
    have hωi : pLoc E w ω' ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w A.ω
    have hωbi : pLoc E w ωb ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w (A.bar A.ω)
    have hform : ∀ i j, pLoc E w (ι (a i) + ι (a j) * ω') ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωi)
    have hformc : ∀ i j, pLoc E w (cF E (ι (a i) + ι (a j) * ω')) ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul, hcι, hcι, hcω, map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωbi)
    exact ⟨hform 0 1, hform 2 3, hformc 0 1, hformc 2 3⟩
end
