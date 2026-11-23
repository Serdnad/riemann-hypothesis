module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem core {Z R B : Type} [CommRing Z] [CommRing R] [CommRing B] (f : R →+* B) (zc : Z →+* R) (zb : Z →+* B)
    (hz : ∀ x, f (zc x) = zb x) (n a s g : R) (nZ : Z) (hn : zc nZ = n) {d d' : ℕ}
    (V : Matrix (Fin d) (Fin d) R) (V' : Matrix (Fin d') (Fin d') R) (Pm : Matrix (Fin d) (Fin d') Z)
    (e : Fin d → Z) (e' : Fin d' → Z) (h3 : ∀ i j, n ∣ (V * Pm.map zc - Pm.map zc * V') i j)
    (h4 : ∀ i, nZ ∣ (Pm *ᵥ e' - e) i) (ui : Fin d → B) (vj : Fin d' → B) (w : B) (ai : Fin d → R) (bj : Fin d' → R)
    (ha : ∀ i, f (ai i) = f a * ui i) (hv : ∀ j, vj j = f n * f (bj j)) (hw : w = f n * f g) :
    ∃ Y : R, f a * (∑ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i * ui i +
      ∑ j, (V'.map f *ᵥ fun i => zb (e' i)) j * vj j - f s * w) = f (n * Y) := by
  choose W hW using h3
  choose r hr using h4
  have hPb : Pm.map zb = (Pm.map zc).map f := by
    ext i j; simp [hz]
  have hE : (fun j => zb (e' j)) = f ∘ (fun j => zc (e' j)) := by
    ext j; simp [hz]
  have hD : V * Pm.map zc - Pm.map zc * V' = n • Matrix.of W := by
    ext i j; simp [hW]
  have hM : V.map f * Pm.map zb - Pm.map zb * V'.map f = (n • Matrix.of W).map f := by
    rw [← hD, hPb, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul]
  have hq : (fun i => zb ((Pm *ᵥ e' - e) i)) = f ∘ (fun i => n * zc (r i)) := by
    ext i; simp only [Function.comp, hr i, map_mul, hz, ← hn]
  have h1 : ∀ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i =
      f n * f ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) := by
    intro i
    rw [hM, hE, hq, Pi.sub_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_mul, ← map_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ j, (V'.map f *ᵥ fun i => zb (e' i)) j = f ((V' *ᵥ fun i => zc (e' i)) j) := by
    intro j; rw [hE, ← RingHom.map_mulVec]
  refine ⟨∑ i, ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) * ai i +
    ∑ j, a * (V' *ᵥ fun i => zc (e' i)) j * bj j - a * s * g, ?_⟩

  simp only [h1, h2, hv, hw, map_mul, map_add (f := _), map_sub, map_sum, ha, Finset.mul_sum, mul_add, mul_sub]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

variable {l : ℕ} [Fact l.Prime]

private theorem u_alg {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l]) :
    uB T (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  show T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact T.zB z

private theorem iB_zC (z : ℤ_[l]) : iB l (zC l z) = Per.zB l z := rfl

private theorem exists_iB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (c : ↥(MaximalUnramifiedExtension l))
    (hc : ‖(c : Om l)‖ ≤ 1) : ∃ y : Per.Acris l, iB l y = uB T c := by
  obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T (adjExt (c : Om l)) ⟨c, mem_adjExt _, c.2⟩ hc
  refine ⟨iA l w, ?_⟩
  have h : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := hw
  show _ = T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c)
  rw [← h, T.ιA]
  rfl

private theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1

private theorem scale {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l)) (n : ℕ) (y : Om l) :
    uB T (lam ((n : Om l) * y)) = (n : Per.Bcris l) * uB T (lam y) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trStep_holds :
    Func → TrId → TrStep := by
  intro hF hI l _ P AI T s d d' m M c₁ c₂ t t' c pv p θ Pi e e' V V' h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := norm_l
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (l : Om l) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact (inv_pos.2 hlpos).ne hn
  have hlK : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg (fun x : ↥(MaximalUnramifiedExtension l) => (x : Om l)) h0
    simpa using this
  have hsmall : ∀ y : Om l, ‖y‖ ≤ ((l : ℝ) ^ M)⁻¹ → ‖y / (l : Om l) ^ M‖ ≤ 1 := by
    intro y hy
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ (by simpa using hy) (by positivity) |>.trans le_rfl
  let δ : Fin d' → Om l := fun j => ∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k
  let η : Om l := θ - ∑ k, c k * pv k
  let x : Fin d ⊕ Fin d' ⊕ Unit → Om l := Sum.elim (fun i => (l : Om l) ^ c₁ * t i)
    (Sum.elim (fun j => δ j / (l : Om l) ^ M) (fun _ => η / (l : Om l) ^ M))
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro (i | j | _)
    · exact h7 i
    · exact hsmall _ (h5 j)
    · exact hsmall _ h6
  obtain ⟨lam, hl1, hl2, hl3⟩ := hF l (MaximalUnramifiedExtension l) (Fin d ⊕ Fin d' ⊕ Unit) x ((l : Om l) ^ c₁ * (p - θ)) hx h8
  have hid := hI l (Per.Bcris l) (uB T) (Per.zB l) (u_alg T) (iB l s) d d' m t t' c pv p θ Pi e e'
    (V.map (iB l)) (V'.map (iB l)) h1 h2 lam
  choose ai hai using fun i => exists_iB T (lam (x (Sum.inl i))) (hl1 _)
  choose bj hbj using fun j => exists_iB T (lam (x (Sum.inr (Sum.inl j)))) (hl1 _)
  obtain ⟨g, hg⟩ := exists_iB T (lam (x (Sum.inr (Sum.inr ())))) (hl1 _)
  have hpow : ∀ (k : ℕ) (y : Om l), uB T (lam ((l : Om l) ^ k * y)) = (l : Per.Bcris l) ^ k * uB T (lam y) := by
    intro k y
    have := scale T lam (l ^ k) y
    push_cast at this
    exact this
  have hdiv : ∀ y : Om l, uB T (lam y) = (l : Per.Bcris l) ^ M * uB T (lam (y / (l : Om l) ^ M)) := by
    intro y
    rw [← hpow, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨Y, hY⟩ := core (iB l) (zC l) (Per.zB l) iB_zC ((l : Per.Acris l) ^ M) ((l : Per.Acris l) ^ c₁) s g
    ((l : ℤ_[l]) ^ M) (by simp) V V' Pi e e' h3 h4
    (fun i => uB T (lam (t i))) (fun j => uB T (lam (δ j))) (uB T (lam η)) ai bj
    (fun i => by
      rw [hai i]
      simp only [map_pow, map_natCast]
      exact hpow c₁ (t i))
    (fun j => by
      rw [hbj j]
      simp only [map_pow, map_natCast]
      exact hdiv (δ j))
    (by
      rw [hg]
      simp only [map_pow, map_natCast]
      exact hdiv η)
  rw [← hid] at hY
  set q : ↥(MaximalUnramifiedExtension l) := lam ((l : Om l) ^ c₁ * (p - θ)) with hq
  have huq : uB T q = (l : Per.Bcris l) ^ c₁ * uB T (lam (p - θ)) := hpow c₁ (p - θ)
  have hqn : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(q : Om l)‖ := h9.trans hl2
  have hq0 : q ≠ 0 := by
    intro h0
    have h00 : (0 : ℝ) < ((l : ℝ) ^ c₂)⁻¹ := by positivity
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hqn
    exact absurd hqn (not_le.2 h00)
  have hq' : ‖(((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ hqn (norm_nonneg _)
  obtain ⟨y', hy'⟩ := exists_iB T _ hq'
  refine ⟨Y * y', GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l ?_⟩
  have hqq : q * ((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q) = (l : ↥(MaximalUnramifiedExtension l)) ^ c₂ := mul_div_cancel₀ _ hq0
  have hu : uB T q * iB l y' = (l : Per.Bcris l) ^ c₂ := by
    rw [hy', ← map_mul, hqq, map_pow, map_natCast]
  show iB l _ = iB l _
  rw [← mul_assoc, map_mul (iB l) _ y', ← hY]
  simp only [map_mul, map_pow, map_natCast]
  rw [← hu, huq]
  ring
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem secU_holds : CoreU → SecU := by
  intro hU l _ K bk N
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1
  refine ⟨n₀ + 2 * N * n₀, fun d A A' hA => ?_⟩
  set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ
  obtain ⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩ := GlobalTheory.AcrisFrobE.main l K bk
  have hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s) := fun s => by
    simp only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]
  have hu : phiA l (ψ X) = ψ X ^ l := by rw [hφψ, frobS_X, map_pow]
  have hdiff : ∀ s : bk.S, ∃ t : Per.Acris l,
      ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t := by
    intro s
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    refine ⟨ψ (frobS l bk.a t), ?_⟩
    rw [← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0 := by simp
  set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def
  have hw0u : IsUnit w0 := ((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ
  have hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0 := by
    rw [hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]
  set u : Per.Acris l := ψ X with hudef
  set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef
  set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef
  set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef
  have hav : a * v = 1 := Units.inv_mul v
  have hbw : b * w0 = 1 := by rw [hbdef]; exact hw0u.val_inv_mul
  set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB
  set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0
  have hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    intro f
    rw [← Matrix.map_mul, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfE : fB bk.E = (l : Per.Acris l) * v := hv
  have hfE0 : fB0 bk.E = (l : Per.Acris l) * w0 := hP0
  have hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) := by
    intro c y h
    calc c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) * (c * y) ^ (2 * N) := by ring
      _ = _ := by rw [h, one_pow, mul_one]
  have hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]
  have hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]
  choose G hG using fun i j => hdiff (A i j)
  obtain ⟨z, hz⟩ := hdiff bk.E
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow w0 v N
  have hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) =
      u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0) := by
    ext i j
    have h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j := hG i j
    have h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z := by rw [← hfE, ← hfE0]; exact hz
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    have h4 : (a * v) ^ N = 1 := by rw [hav, one_pow]
    have h5 : (b * w0) ^ N = 1 := by rw [hbw, one_pow]
    linear_combination ((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 +
      ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 +
      (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5
  obtain ⟨Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩ := hU (Per.Acris l) d l l N htor hcomp (phiA l) u hu
    (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))
  refine ⟨Q, Q', ⟨hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩⟩
  · rw [hY]; rfl
  · rw [hY']; rfl
  · have key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l)) := by
      rw [← mul_smul_comm, hQ, smul_mul_assoc]
    have e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N := by
      rw [mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]
    have e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N := by
      rw [hv]
      calc ((l : Per.Acris l) * v) ^ N * w0 ^ N * a ^ N = ((l : Per.Acris l) * w0) ^ N * (a * v) ^ N := by ring
        _ = _ := by rw [hav, one_pow, mul_one]
    show P ^ N • (Q * A.map fB0) =
      ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))
    rw [hP0, e1, ← smul_smul, key, smul_smul, e2]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem map_smul_ringHom {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {d : ℕ} (c : S)
    (M : Matrix (Fin d) (Fin d) S) : (c • M).map f = f c • M.map f := by
  ext i j; simp

private theorem dvd_mul_entries_left {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ B i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k j) _

private theorem dvd_mul_entries_right {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ A i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (h i k) _

private theorem map_intertwine {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (ψ : S →+* S) (φ : T →+* T)
    (hf : ∀ s, φ (f s) = f (ψ s)) {d d' : ℕ} (c : S) (A : Matrix (Fin d) (Fin d) S) (A₁ : Matrix (Fin d') (Fin d') S)
    (R : Matrix (Fin d) (Fin d') S) (h : ∀ i j, c ∣ (R * A₁ - A * R.map ψ) i j) (i : Fin d) (j : Fin d') :
    f c ∣ (R.map f * A₁.map f - A.map f * (R.map f).map φ) i j := by
  have e : R.map f * A₁.map f - A.map f * (R.map f).map φ = (R * A₁ - A * R.map ψ).map f := by
    have e' : (R.map f).map φ = (R.map ψ).map f := by
      ext i j; simp [hf]
    rw [e']
    ext i j

    simp [Matrix.mul_apply, map_sum]
  rw [e, Matrix.map_apply]
  exact map_dvd f (h i j)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkQ_holds :
    ZeroAp → LinkRec → LinkQ := by
  intro hZ hR l _ K bk N M
  obtain ⟨n, hn⟩ := hZ l K bk (3 * N) M
  refine ⟨n, ?_⟩
  intro k d d' A A₁ A₁' Q Q' Q₁ Q₁' R hA hS hS₁ hRel
  obtain ⟨-, -, ⟨v, hv⟩, hφι, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hv' : fA bk bk.E = (l : Per.Acris l) * v := hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : (Per.Acris l)ˣ, f0 bk bk.E = (l : Per.Acris l) * w₀ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨(Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map (fA bk).toMonoidHom, ?_⟩
    simp [f0, hc]
  have hφA : ∀ s, phiA l (fA bk s) = fA bk (frobS l bk.a s) := fun s => by
    simp only [fA, RingHom.comp_apply, hφι, bk.ev_frob]
  have hφ0 : ∀ s, phiA l (f0 bk s) = f0 bk (frobS l bk.a s) := fun s => by
    rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, hφA, frobS_C,
      show f0 bk (frobS l bk.a s) = fA bk (PowerSeries.C (PowerSeries.constantCoeff (frobS l bk.a s))) from rfl,
      constantCoeff_frobS_apply]
  have hdiff : ∀ s, uC bk ∣ fA bk s - f0 bk s := fun s => by
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    have e : fA bk s - f0 bk s = uC bk ^ l * fA bk t := by
      rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, ← map_sub, ht, map_mul]
      congr 1
      simp [fA, uC, frobS_X]
    rw [e]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Fact.out : l.Prime).ne_zero) _
  have hlc : ∀ f : bk.S →+* Per.Acris l, f ((l : bk.S) ^ n) = (l : Per.Acris l) ^ n := fun f => by
    rw [map_pow, map_natCast]
  have h1 : A₁.map (f0 bk) * A₁'.map (f0 bk) =
      ((l : Per.Acris l) * w₀) ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') (Per.Acris l)) := by
    rw [← hw₀, ← Matrix.map_mul, hA, map_smul_ringHom, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((l : Per.Acris l) * v) ^ N • (Q * A.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A.map (fA bk) * Q.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS.frob
  have h3 : ((l : Per.Acris l) * v) ^ N • (Q₁ * A₁.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A₁.map (fA bk) * Q₁.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS₁.frob
  have h4 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (fA bk) * A₁.map (fA bk) - A.map (fA bk) * (R.map (fA bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (fA bk)]
    exact map_intertwine (fA bk) (frobS l bk.a) (phiA l) hφA _ A A₁ R hRel i j
  have h5 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (f0 bk) * A₁.map (f0 bk) - A.map (f0 bk) * (R.map (f0 bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (f0 bk)]
    exact map_intertwine (f0 bk) (frobS l bk.a) (phiA l) hφ0 _ A A₁ R hRel i j
  obtain ⟨F, F', hF⟩ := hR (Per.Acris l) (phiA l) (l : Per.Acris l) ((l : Per.Acris l) ^ n) v w₀ N d d'
    (A.map (fA bk)) (A.map (f0 bk)) Q (A₁.map (fA bk)) (A₁.map (f0 bk)) (A₁'.map (f0 bk)) Q₁
    (R.map (fA bk)) (R.map (f0 bk)) h1 h2 h3 h4 h5
  refine hn d d' _ F F' ?_ hF
  intro i j
  have hD : R.map (fA bk) * Q₁ - Q * R.map (f0 bk) =
      R.map (fA bk) * (Q₁ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d') (Fin d') (Per.Acris l))) +
        (l : Per.Acris l) ^ k • (R.map (fA bk) - R.map (f0 bk)) -
        (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) * R.map (f0 bk) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub]
    abel
  rw [hD, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply]
  refine dvd_sub (dvd_add (dvd_mul_entries_left _ _ _ hS₁.mod i j) ?_) (dvd_mul_entries_right _ _ _ hS.mod i j)
  rw [smul_eq_mul]
  exact Dvd.dvd.mul_left (hdiff _) _
end
