module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private theorem mu_algebraMap {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ) (r : R) :
    μ (algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r) =
      (r ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
  ext i k
  have h : algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r = r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := rfl
  rw [h, hμ r 1 i k]
  by_cases hik : i = k
  · subst hik; simp
  · simp [Matrix.one_apply, hik]

private theorem conj_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ} (D : Matrix (Fin n) (Fin n) K)
    (a g : GL (Fin n) K) (c : K) (ha : (a.val.map σ)ᵀ * D * a.val = 1)
    (hg : (g.val.map σ)ᵀ * g.val = c • (1 : Matrix (Fin n) (Fin n) K)) :
    ((a * g * a⁻¹).val.map σ)ᵀ * D * (a * g * a⁻¹).val = c • D := by
  set b : Matrix (Fin n) (Fin n) K := ((a⁻¹).val.map σ)ᵀ with hb
  have h1 : (a.val.map σ)ᵀ * b = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have h1' : b * (a.val.map σ)ᵀ = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hD : D = b * (a⁻¹).val := by
    calc D = (b * (a.val.map σ)ᵀ) * D * (a.val * (a⁻¹).val) := by rw [h1', Units.mul_inv]; simp
      _ = b * ((a.val.map σ)ᵀ * D * a.val) * (a⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = b * (a⁻¹).val := by rw [ha, Matrix.mul_one]
  have e : ((a * g * a⁻¹).val.map σ)ᵀ = b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ := by
    simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, hb, Matrix.mul_assoc]
  rw [e]
  calc b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ * D * (a * g * a⁻¹).val
      = b * (g.val.map σ)ᵀ * ((a.val.map σ)ᵀ * D * a.val) * g.val * (a⁻¹).val := by
        simp only [Units.val_mul, Matrix.mul_assoc]
    _ = b * ((g.val.map σ)ᵀ * g.val) * (a⁻¹).val := by
        rw [ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = c • D := by
        rw [hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hD]

private theorem key {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E]
    (hst : MuStar) (A : Arith E) {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (u : (R ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) (s : R)
    (h : ((μ u).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ u =
      (s ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))) :
    (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * (starT (hermStar (A.H n) (A.det_ne n)) R u).unop =
      algebraMap R _ s := by
  set x' := (starT (hermStar (A.H n) (A.det_ne n)) R (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop with hx'
  have h1 := hst R E A n μ hμ u
  have hne : ∀ i, ((A.dg n i : 𝓞 E) : E) ≠ 0 := fun i => by
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this]
  have hDi : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) *
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have : ∀ i, ((A.dg n i : E))⁻¹ * (A.dg n i : E) = 1 := fun i => inv_mul_cancel₀ (hne i)
    simp only [this]
    exact Matrix.diagonal_one
  have h2 : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * (μ x' * μ u) =
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * ((s ⊗ₜ[ℚ] (1 : E)) • 1) := by
    rw [← Matrix.mul_assoc, h1, h, Matrix.mul_smul, Matrix.mul_one]
  have h3 : μ x' * μ u = (s ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
    have := congrArg (fun M => Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) * M) h2
    simpa only [← Matrix.mul_assoc, hDi, Matrix.one_mul] using this
  have h4 : x' * (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) = algebraMap R _ s :=
    μ.injective (by rw [map_mul, h3, mu_algebraMap μ hμ])
  calc (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * x'
      = u * (x' * u) * (↑u⁻¹ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = algebraMap R _ s := by
        rw [h4, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem pJEx :
    MuStar → JEx := by
  intro hst E _ _ _ A n p _ S T μ hμ a ha
  let m : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) :=
    { toFun := fun g => μ.symm ((a * mat g * a⁻¹).val.map T.Φ)
      map_one' := by
        simp only [map_one, mul_one, mul_inv_cancel, Units.val_one]
        rw [Matrix.map_one _ (map_zero _) (map_one _), map_one]
      map_mul' := fun g h => by
        rw [← map_mul, ← Matrix.map_mul]
        congr 2
        simp only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left] }
  have hm : ∀ g, μ (m g) = (a * mat g * a⁻¹).val.map T.Φ := fun g => μ.apply_symm_apply _
  let f₁ : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ := m.toHomUnits
  let f₂ : GUf E n →* (AfP p)ˣ := (Units.map (T.ρ : AfQ →* AfP p)).comp sim
  have mem : ∀ g, (f₁.prod f₂) g ∈ UPts (hermStar (A.H n) (A.det_ne n)) (AfP p) := by
    intro g
    show ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) *
        (starT (hermStar (A.H n) (A.det_ne n)) (AfP p)
          ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop =
      algebraMap (AfP p) _ (T.ρ (sim g : AfQˣ))
    apply key hst A μ hμ
    have hf : μ ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) =
      (a * mat g * a⁻¹).val.map T.Φ := hm g
    rw [hf]
    have h0 := conj_form (conjFin (conjE E)) (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))) a (mat g)
      (finiteAdeleMap ℚ E (sim g : AfQˣ)) ha.1 g.2
    have h1 := congrArg (fun M => M.map T.Φ) h0
    have e1 : ((((a * mat g * a⁻¹).val.map (conjFin (conjE E)))ᵀ).map T.Φ) =
        (((a * mat g * a⁻¹).val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
      ext i k
      exact T.Φ_conj _
    have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      exact T.Φ_E _
    have e3 : (finiteAdeleMap ℚ E (sim g : AfQˣ) •
        Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        (T.ρ (sim g : AfQˣ) ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [← e2]
      ext i k
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, T.Φ_Q]
    simp only [Matrix.map_mul] at h1
    rw [e1, e2, e3] at h1
    exact h1
  refine ⟨MonoidHom.codRestrict (f₁.prod f₂) (UPts S.G.star (AfP p)) mem, ?_, ?_⟩
  · intro g
    exact hm g
  · intro g
    rfl

end UpperTheory.Gal.W2.Seed
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem ohat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E)
    {x y : AfP p ⊗[ℚ] E} (hx : x ∈ OHat p E) (hy : y ∈ OHat p E) : x * y ∈ OHat p E := by
  obtain ⟨a, rfl⟩ := T.Φ_surj x
  obtain ⟨b, rfl⟩ := T.Φ_surj y
  rw [← map_mul, T.Φ_int]
  intro w hw
  rw [map_mul, map_mul]
  exact mul_le_one' ((T.Φ_int a).1 hx w hw) ((T.Φ_int b).1 hy w hw)

private theorem one_mem_ohat {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E) :
    (1 : AfP p ⊗[ℚ] E) ∈ OHat p E := by
  rw [← map_one T.Φ, T.Φ_int]
  intro w hw
  simp

theorem UpperTheory.Gal.W2.Seed.pKNIff :
    LatCoord → KNIff := by
  intro hL E _ _ _ A n p _ S T g
  obtain ⟨ν, -, hact, hlat⟩ := hL E A n p S T.μ T.mu
  have hM : T.μ (S.mx (T.j g)) = (T.a * mat g * T.a⁻¹).val.map T.Φ := T.j_mx g
  generalize hY : T.a * mat g * T.a⁻¹ = Y at hM ⊢
  have hactM : ∀ v, ν (S.L.actG (T.j g) v) = (Y.val.map T.Φ) *ᵥ ν v := fun v => by rw [hact, hM]
  have hcol : ∀ k i, ((Y.val.map T.Φ) *ᵥ (Pi.single k 1 : Fin n → AfP p ⊗[ℚ] E)) i = T.Φ (Y.val i k) := by
    intro k i
    simp [Matrix.mulVec_single_one]
  have hsingle : ∀ k, ν.symm (Pi.single k 1) ∈ LaHat S.D := by
    intro k
    rw [hlat]
    intro i
    rw [ν.apply_symm_apply, Pi.single_apply]
    split_ifs
    · exact one_mem_ohat T.toAdT
    · exact zero_mem _
  have hΦ1 : ∀ i k, T.Φ ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) i k := by
    intro i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hw1 : ∀ (w : Plc E) i k, pLoc E w ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by
    intro w i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · constructor
    · intro h w hw i k
      have := (hlat _).1 (h _ (hsingle k)) i
      rw [hactM, ν.apply_symm_apply, hcol, T.Φ_int] at this
      exact this w hw
    · intro h v hv
      rw [hlat]
      intro i
      rw [hactM]
      have hv' := (hlat v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
      rw [Matrix.map_apply, T.Φ_int]
      exact fun w hw => h w hw i k
  · intro N hN
    constructor
    · intro h w hw i k
      obtain ⟨u, hu, e⟩ := h _ (hsingle k)
      have e2 := congrFun (congrArg ν e) i
      rw [hactM, ν.apply_symm_apply, hcol, map_add (f := _), map_nsmul, ν.apply_symm_apply] at e2
      have hui := (hlat u).1 hu i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν u i)
      have hxi := (T.Φ_int x).1 (hx ▸ hui) w hw
      have e3 : T.Φ (Y.val i k - (1 : Matrix (Fin n) (Fin n) (Af E)) i k - (N : Af E) * x) = 0 := by
        rw [map_sub, map_sub, map_mul, hΦ1, hx, map_natCast, e2, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
          Matrix.one_apply, Pi.single_apply]
        simp [eq_comm]
      have e4 := (T.Φ_ker _).1 e3 w hw
      rw [map_sub, map_sub, map_mul, hw1, map_natCast, sub_eq_zero, sub_eq_iff_eq_add'] at e4
      have e5 : ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k = (N : w.adicCompletion E) * pLoc E w x := by
        rw [Matrix.sub_apply]
        show pLoc E w (Y.val i k) - _ = _
        rw [e4]
        ring
      rw [e5, map_mul]
      exact mul_le_of_le_one_right' hxi
    · intro h v hv
      have hv' := (hlat v).1 hv
      have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      obtain ⟨Ninv, hNinvdef⟩ : ∃ Ninv : Af E, Ninv = algebraMap E (Af E) ((N : E)⁻¹) := ⟨_, rfl⟩
      have hNinv : (N : Af E) * Ninv = 1 := by
        rw [hNinvdef, ← map_natCast (algebraMap E (Af E)) N, ← map_mul, mul_inv_cancel₀ hN0, map_one]
      obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E),
          ∀ i k, C i k = T.Φ (Ninv * (Y.val - 1) i k) := ⟨Matrix.of fun i k => T.Φ (Ninv * (Y.val - 1) i k), fun _ _ => rfl⟩
      have hC : Y.val.map T.Φ = 1 + ((N : AfP p ⊗[ℚ] E)) • C := by
        ext i k
        rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hΦ1, hCdef,
          ← map_natCast T.Φ N, ← map_mul, ← map_add]
        congr 1
        rw [← mul_assoc, hNinv, one_mul, Matrix.sub_apply]
        ring
      refine ⟨ν.symm (C *ᵥ ν v), ?_, ?_⟩
      · rw [hlat]
        intro i
        rw [ν.apply_symm_apply]
        simp only [Matrix.mulVec, dotProduct]
        refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
        rw [hCdef, T.Φ_int]
        intro w hw
        have h1 := h w hw i k
        have hp' : (N : w.adicCompletion E) * pLoc E w Ninv = 1 := by
          rw [← map_natCast (pLoc E w) N, ← map_mul, hNinv, map_one]
        have h2 : (N : w.adicCompletion E) ≠ 0 := left_ne_zero_of_mul_eq_one hp'
        have h3 : pLoc E w Ninv = (N : w.adicCompletion E)⁻¹ := eq_inv_of_mul_eq_one_right hp'
        have e : pLoc E w ((Y.val - 1) i k) = ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k := by
          rw [Matrix.sub_apply, map_sub, hw1, Matrix.sub_apply]
          rfl
        rw [map_mul, h3, e, map_mul, map_inv₀]
        exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h2))).2 h1
      · apply ν.injective
        rw [hactM, hC, map_add (f := _), map_nsmul, ν.apply_symm_apply, Matrix.add_mulVec, Matrix.one_mulVec,
          Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

variable (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ)

private def muHom : R ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) :=
  Algebra.TensorProduct.lift
    (((Algebra.ofId (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E))).restrictScalars ℚ).comp
      Algebra.TensorProduct.includeLeft)
    (AlgHom.mapMatrix Algebra.TensorProduct.includeRight)
    (fun r x => Algebra.commutes _ _)

private theorem muHom_tmul (r : R) (x : Matrix (Fin n) (Fin n) E) (i k : Fin n) :
    muHom R E n (r ⊗ₜ x) i k = r ⊗ₜ x i k := by
  have h : muHom R E n (r ⊗ₜ x) =
      algebraMap (R ⊗[ℚ] E) (Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (r ⊗ₜ 1) *
        x.map (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] R ⊗[ℚ] E) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r x
  rw [h, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_apply, Matrix.map_apply]
  simp

private def muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : R ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ∑ i, ∑ k, LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) (M i k)

private theorem muInv_add (M N : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muInv R E n (M + N) = muInv R E n M + muInv R E n N := by
  simp [muInv, Matrix.add_apply, map_add (f := _), Finset.sum_add_distrib]

private theorem muInv_muHom (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    muInv R E n (muHom R E n y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [muInv]
  | add a b ha hb =>
    rw [map_add (f := _), muInv_add, ha, hb]
  | tmul r x =>
    simp only [muInv, muHom_tmul, LinearMap.lTensor_tmul, Matrix.singleLinearMap_apply]
    simp only [← TensorProduct.tmul_sum]
    rw [← Matrix.matrix_eq_sum_single x]

private theorem muHom_single (i k : Fin n) (b : R ⊗[ℚ] E) :
    muHom R E n (LinearMap.lTensor R (Matrix.singleLinearMap ℚ i k) b) = Matrix.single i k b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.single_add]
  | tmul r x =>
    ext a c
    rw [LinearMap.lTensor_tmul, muHom_tmul, Matrix.singleLinearMap_apply]
    by_cases h : i = a ∧ k = c
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto), Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
      simp

private theorem muHom_muInv (M : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) :
    muHom R E n (muInv R E n M) = M := by

  simp only [muInv, map_sum, muHom_single]
  exact (Matrix.matrix_eq_sum_single M).symm

private def muEquiv : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E) where
  toFun := muHom R E n
  invFun := muInv R E n
  left_inv := muInv_muHom R E n
  right_inv := muHom_muInv R E n
  map_mul' := map_mul _
  map_add' := map_add _

end UpperTheory.Gal.W2.Seed

end

theorem UpperTheory.Gal.W2.Seed.pMuEx :
    MuEx := by
  intro R E _ _ _ _ n
  exact ⟨muEquiv R E n, fun r x i k => muHom_tmul R E n r x i k⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem conj_H {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have hc : (IsCMField.complexConj E) ((A.c : 𝓞 E) : E) = (A.c : E) := by
    rw [← A.bar_eq, A.c_real]
  ext i j
  simp only [Arith.H, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  · simp

private theorem H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [Arith.H, ← Matrix.diagonal_smul]
  congr 1

private theorem diag_mul_conj_H_inv {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) E) :
    Matrix.diagonal (fun i => (A.dg n i : E)) *
        (((A.H n).map (IsCMField.complexConj E : E →+* E))⁻¹ * y * (A.H n).map (IsCMField.complexConj E : E →+* E)) =
      y * Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [conj_H]
  have hc : (-(A.c : E)) ≠ 0 := neg_ne_zero.mpr A.c_ne
  have hD : Matrix.diagonal (fun i => (A.dg n i : E)) = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hu : IsUnit (A.H n).det := isUnit_iff_ne_zero.mpr (A.det_ne n)
  rw [hD, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem UpperTheory.Gal.W2.Seed.pMuStar :
    MuStar := by
  intro R E _ _ _ _ _ A n μ hμ x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have hk := diag_mul_conj_H_inv A n ((m.map (IsCMField.complexConj E : E →+* E))ᵀ)
    ext i k
    rw [starT_tmul, hermStar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hμ,
      Matrix.transpose_apply, Matrix.map_apply, hμ, conjT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := congrFun (congrFun hk i) k
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  | add x y hx hy =>
    rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), Matrix.mul_add, hx, hy, map_add (f := _),
      Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul]
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem UpperTheory.Gal.W2.Seed.card_signs {n : ℕ} (hn : 1 ≤ n) (r : Fin n → ℝ)
    (h0 : ∀ i : Fin n, (i : ℕ) = 0 → 0 < r i) (h1 : ∀ i : Fin n, (i : ℕ) ≠ 0 → r i < 0) :
    Fintype.card {i // 0 < r i} = 1 ∧ Fintype.card {i // r i < 0} = n - 1 := by
  have hiff : ∀ i : Fin n, r i < 0 ↔ ¬ 0 < r i := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hp := h0 i hi
      exact ⟨fun h => by linarith, fun h => absurd hp h⟩
    · have hq := h1 i hi
      exact ⟨fun _ h' => by linarith, fun _ => hq⟩
  have hc1 : Fintype.card {i // 0 < r i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, hn⟩, h0 _ rfl⟩, fun ⟨j, hj⟩ => ?_⟩
    apply Subtype.ext
    apply Fin.ext
    by_contra hne
    exact absurd hj (not_lt.mpr (le_of_lt (h1 j hne)))
  refine ⟨hc1, ?_⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype_compl, hc1,
    Fintype.card_fin]

theorem UpperTheory.Gal.W2.Seed.pSigSt :
    HdSign → SigSt := by
  intro hS E _ _ _ A n hn τ
  have hdiag : gramAt (A.H n) τ = diagonal (fun i => ((τ (A.hd n i : E)).re : ℂ)) := by
    ext i j
    simp only [gramAt, Arith.H, transpose_apply, map_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, Complex.ext_iff]
      simp [(hS E A n τ i).1]
    · simp [h, Ne.symm h]
  have aux : ∀ (r : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
      M = diagonal (fun i => (r i : ℂ)) →
      sigPosH hM = Fintype.card {i // 0 < r i} ∧ sigNegH hM = Fintype.card {i // r i < 0} := by
    rintro r M hM rfl
    exact sigPosH_sigNegH_diagonal n r hM
  obtain ⟨hp, hneg⟩ := aux _ _ (isHermitian_gramAt (A.herm n) τ) hdiag
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · have hcs := card_signs hn _ (fun i hi => (hS E A n τ i).2.2.1 ⟨hτ, hi⟩)
      (fun i hi => (hS E A n τ i).2.2.2 (fun h => hi h.2))
    exact ⟨hp.trans hcs.1, hneg.trans hcs.2⟩
  · have hall : ∀ i : Fin n, (τ (A.hd n i : E)).re < 0 := fun i =>
      (hS E A n τ i).2.2.2 (fun h => hτ h.1)
    refine ⟨hp.trans ?_, hneg.trans ?_⟩
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => absurd hi (not_lt.mpr (le_of_lt (hall i)))⟩
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]
end
