module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Formalism.SatakeDualWeyl.StatementG
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbGL

variable {K : Type} [Field K] (V : ValuationSubring K)

theorem mem_range_iff (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by
  constructor
  · rintro ⟨a, rfl⟩; exact a.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem matLat_le_of_entries {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ V) :
    matLat V g (stdLat V n) ≤ stdLat V n := by
  intro v hv
  rw [mem_matLat] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [mem_stdLat] at hu ⊢
  intro i
  have hu' := fun j => (mem_range_iff V _).1 (hu j)
  apply (mem_range_iff V _).2
  simp only [Matrix.mulVec, dotProduct]
  exact V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)

theorem entries_of_matLat_le {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : matLat V g (stdLat V n) ≤ stdLat V n) (i j : Fin n) : g i j ∈ V := by
  have hs : (Pi.single j (1 : K) : Fin n → K) ∈ stdLat V n := by
    rw [mem_stdLat]
    intro l
    rw [mem_range_iff]
    by_cases h : l = j
    · subst h; simp [V.one_mem]
    · simp [Pi.single_apply, h, V.zero_mem]
  have hm : g *ᵥ (Pi.single j (1 : K)) ∈ stdLat V n := hg ((mem_matLat _ _ _).2 ⟨_, hs, rfl⟩)
  rw [mem_stdLat] at hm
  have := (mem_range_iff V _).1 (hm i)
  simpa [Matrix.mulVec_single] using this

theorem matLat_mono {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := Submodule.map_mono h

end GlobalTheory.LatOrbGL


open GlobalTheory.LatOrbGL in
theorem GlobalTheory.LatOrb.mem_GLint_iff_matLat_std :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  intro K _ V n k
  constructor
  · rintro ⟨g, rfl⟩
    set k := Formalism.UG.bc V.toSubring.subtype g with hk
    have e1 : ∀ i j, k.val i j ∈ V := by
      intro i j; exact ((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    have e2 : ∀ i j, (k⁻¹).val i j ∈ V := by
      intro i j; rw [hk, ← map_inv]; exact (((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    apply le_antisymm (matLat_le_of_entries V _ e1)
    have : k.val * (k⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc stdLat V n = matLat V (k.val * (k⁻¹).val) (stdLat V n) := by rw [this, matLat_one]
      _ = _ := matLat_mul _ _ _
      _ ≤ _ := matLat_mono V _ (matLat_le_of_entries V _ e2)
  · intro h
    have e1 := entries_of_matLat_le V k.val h.le
    have h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n := by
      conv_lhs => rw [← h]
      rw [← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]
    have e2 := entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le
    let A : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨k.val i j, e1 i j⟩
    let B : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩
    have hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val := by ext i j; rfl
    have hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val := by ext i j; rfl
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) V.toSubring.subtype) := by
      intro X Y hXY; ext i j; exact congrFun (congrFun hXY i) j
    have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl
end

section

open NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace GlobalTheory.InertConjVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiO (φ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (φ : E →+* E)

theorem coe_phiO (φ : E →ₐ[F] E) (y : 𝓞 E) : ((phiO φ y : 𝓞 E) : E) = φ (y : E) := rfl

theorem phiO_comp (φ : E →ₐ[F] E) :
    (phiO φ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := by
  refine RingHom.ext fun f => RingOfIntegers.ext ?_
  rw [RingHom.comp_apply, coe_phiO]
  have h : ((algebraMap (𝓞 F) (𝓞 E) f : 𝓞 E) : E) = algebraMap F E (f : F) := rfl
  rw [h]
  exact φ.commutes _

theorem map_phiO_pow (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    Ideal.map (phiO φ) (w.asIdeal ^ n) = w.asIdeal ^ n := by
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin, ← Ideal.map_pow, Ideal.map_map, phiO_comp]

theorem intVal_phi_le (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO φ y) ≤ w.intValuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero]
  have h0 : w.intValuation y ≠ 0 := w.intValuation_ne_zero y hy
  have h1 : w.intValuation y ≤ 1 := w.intValuation_le_one y
  set k := WithZero.log (w.intValuation y) with hk
  have hek : w.intValuation y = WithZero.exp k := (WithZero.exp_log h0).symm
  have hk0 : k ≤ 0 := by
    rw [hek, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  have hn : w.intValuation y = WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) := by
    rw [hek, Int.toNat_of_nonneg (by omega), neg_neg]
  have hm : y ∈ w.asIdeal ^ (-k).toNat := (w.intValuation_le_pow_iff_mem y _).1 hn.le
  rw [hn]
  refine (w.intValuation_le_pow_iff_mem _ _).2 ?_
  rw [← map_phiO_pow φ v w hin]
  exact Ideal.mem_map_of_mem _ hm

theorem bij (σ : E →ₐ[F] E) : Function.Bijective σ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact σ.bijective

theorem intVal_phi (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO σ y) = w.intValuation y := by
  refine le_antisymm (intVal_phi_le σ v w hin y) ?_
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (bij σ)
  have h := intVal_phi_le (τ.symm : E →ₐ[F] E) v w hin (phiO σ y)
  have e : phiO (τ.symm : E →ₐ[F] E) (phiO σ y) = y := by
    apply RingOfIntegers.ext
    rw [coe_phiO, coe_phiO]
    show τ.symm (τ (y : E)) = (y : E)
    exact τ.symm_apply_apply _
  rwa [e] at h

theorem val_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  intro F E _ _ _ _ _ σ v w hin x
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, map_div₀, map_div₀]
  have e : ∀ y : 𝓞 E, σ (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E (phiO σ y) := fun y => rfl
  rw [e, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intVal_phi σ v w hin, intVal_phi σ v w hin]

end GlobalTheory.InertConjVal
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralAdeleProducts

theorem intAf_mul {F : Type} [Field F] [NumberField F] {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) (hb : b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) : a * b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F :=
  fun v => mul_mem (ha v) (hb v)

theorem intAE_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) :
    s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  unfold HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht
  induction hs using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    obtain ⟨a, ha, p, rfl⟩ := hx
    induction ht using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨b, hb, q, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

end GlobalTheory.IntegralAdeleProducts
end

section

open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap

noncomputable section

namespace GlobalTheory.GaussCutoff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutErr (c : ℝ) (y : E) : ℂ := GroundTheory.Global.gaussianSchwartz E (c • y) - 1

theorem contDiff_cutErr (c : ℝ) : ContDiff ℝ ∞ (cutErr (E := E) c) :=
  (((GroundTheory.Global.gaussianSchwartz E).smooth ⊤).comp (contDiff_const_smul c)).sub contDiff_const

theorem norm_cutErr_le (c : ℝ) (y : E) : ‖cutErr c y‖ ≤ Real.pi * c ^ 2 * ‖y‖ ^ 2 := by
  unfold cutErr
  rw [GroundTheory.Global.gaussianSchwartz_apply]
  have hx : ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hx]
  set a := Real.pi * c ^ 2 * ‖y‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have h1 : Real.exp (-Real.pi * (c ^ 2 * ‖y‖ ^ 2)) = Real.exp (-a) := by
    congr 1; rw [ha_def]; ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  rw [h1, show ((Real.exp (-a) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-a)]

theorem norm_iteratedFDeriv_cutErr_le (c : ℝ) {j : ℕ} (hj : j ≠ 0) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by
  set g := GroundTheory.Global.gaussianSchwartz E with hg
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hgL : ContDiff ℝ ∞ ((g : E → ℂ) ∘ L) := (g.smooth ⊤).comp L.contDiff
  have hfun : cutErr (E := E) c = ((g : E → ℂ) ∘ L) - fun _ => (1 : ℂ) := by
    funext z; simp [cutErr, hL, hg]
  rw [hfun, iteratedFDeriv_sub_apply (hgL.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    L.iteratedFDeriv_comp_right (g.smooth ⊤) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ |c| := by
    rw [hL]; refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hD : ‖iteratedFDeriv ℝ j g (L y)‖ ≤ SchwartzMap.seminorm ℝ 0 j g := by
    simpa using SchwartzMap.le_seminorm ℝ 0 j g (L y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hLn j) hD (norm_nonneg _)
    (pow_nonneg (abs_nonneg c) j)

theorem norm_iteratedFDeriv_cutErr_le' (c : ℝ) (hc : |c| ≤ 1) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * (1 + ‖y‖) ^ 2 := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := apply_nonneg _ _
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hpi := Real.pi_pos
  have h1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cutErr_le c y).trans ?_
    have hc2 : c ^ 2 ≤ |c| := by rw [← sq_abs]; nlinarith
    have hy2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    calc Real.pi * c ^ 2 * ‖y‖ ^ 2 ≤ Real.pi * |c| * (1 + ‖y‖) ^ 2 := by gcongr
      _ = |c| * Real.pi * (1 + ‖y‖) ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  · refine (norm_iteratedFDeriv_cutErr_le c hj.ne' y).trans ?_
    have hcj : |c| ^ j ≤ |c| := pow_le_of_le_one hc0 hc hj.ne'
    calc |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)
        ≤ |c| * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by gcongr
      _ ≤ |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * 1 := by
          rw [mul_one]; gcongr; linarith
      _ ≤ _ := by gcongr

theorem cut_bound (h : 𝓢(E, ℂ)) (k n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 → ∀ y : E,
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖ ≤ |c| * K := by
  set S : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (GroundTheory.Global.gaussianSchwartz E) with hS
  set P := (Finset.Iic (k + 2, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hP_def
  have hP : 0 ≤ P := apply_nonneg _ _
  have hS0 : ∀ i, 0 ≤ S i := fun i => apply_nonneg _ _
  have hpi := Real.pi_pos
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P),
    Finset.sum_nonneg fun i _ => by have := hS0 i; positivity, fun c hc y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cutErr (E := E) c) (h.smooth ⊤) y (n := n)
    (by exact_mod_cast le_top)
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          ‖iteratedFDeriv ℝ (n - i) h y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) *
          ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_iteratedFDeriv_cutErr_le' c hc i y
        have h0 : 0 ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖ := by positivity
        have e : |c| * (Real.pi + S i) * ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) =
          (|c| * (Real.pi + S i) * (1 + ‖y‖) ^ 2) * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
        rw [e]; gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) * (2 ^ (k + 2) * P)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hS0i := hS0 i
        have hX : (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) ≤ 2 ^ (k + 2) * P := by
          calc (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)
              ≤ (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by
                gcongr; linarith
            _ = (1 + ‖y‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) h y‖ := by ring
            _ ≤ 2 ^ (k + 2) * P :=
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, n)) le_rfl
                  (Nat.sub_le n i) h y
        gcongr
    _ = |c| * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

def cutMap (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) : 𝓢(E, ℂ) where
  toFun y := cutErr c y * h y
  smooth' := (contDiff_cutErr c).mul (h.smooth ⊤)
  decay' k n := by
    obtain ⟨K, -, hK⟩ := cut_bound h k n
    exact ⟨|c| * K, hK c hc⟩

theorem cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl

end GlobalTheory.GaussCutoff


open GlobalTheory.GaussCutoff in
theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
end
end

section

open NumberField

namespace GlobalTheory

theorem differentIdeal_int_le_differentIdeal (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] :
    differentIdeal ℤ (𝓞 K') ≤ differentIdeal (𝓞 K) (𝓞 K') := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 K')]
  exact Ideal.mul_le_left

theorem span_rational_le_span_and_different_smul_le :
    ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  intro K K' L _ _ _ _ _ _ _ _ _ n M hM
  set φ : (Fin n → K') → (Fin n → L) := fun x i => algebraMap K' L (x i) with hφ
  set P := Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) with hP
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  ·
    have himg : ∀ y ∈ Submodule.span (𝓞 K') {y : Fin n → K' | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K K' (y0 i)}, φ y ∈ P := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨hyM, y0, rfl⟩ := hy
        exact Submodule.subset_span ⟨y0, hyM, rfl⟩
      | zero =>
        have h0 : φ 0 = 0 := by funext i; simp [hφ]
        rw [h0]; exact P.zero_mem
      | add a b _ _ ha hb =>
        have : φ (a + b) = φ a + φ b := by funext i; simp [hφ]
        rw [this]; exact P.add_mem ha hb
      | smul c a _ ha =>
        have : φ (c • a) = algebraMap (𝓞 K') (𝓞 L) c • φ a := by
          funext i
          change algebraMap K' L ((c : K') * a i) = ((algebraMap (𝓞 K') (𝓞 L) c : 𝓞 L) : L) * φ a i
          rw [map_mul]; rfl
        rw [this]; exact P.smul_mem _ ha
    rw [Ideal.map, Submodule.span_smul_span, Submodule.span_le]
    intro z hz
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul.mp hz
    have hdK : d ∈ differentIdeal (𝓞 K) (𝓞 K') := differentIdeal_int_le_differentIdeal K K' hd
    have hmem := differentIdeal_smul_mem_span_rational K K' n M hM d hdK x hx
    have h := himg _ hmem
    have : φ (d • x) = algebraMap (𝓞 K') (𝓞 L) d • φ x := by
      funext i
      change algebraMap K' L ((d : K') * x i) = ((algebraMap (𝓞 K') (𝓞 L) d : 𝓞 L) : L) * φ x i
      rw [map_mul]; rfl
    rw [this] at h
    exact h

end GlobalTheory
end

section

universe u

theorem _root_.GlobalTheory.T.quotient_retract_pi_quotient_of_summand : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
    r ∘ₗ s = LinearMap.id := by
  first | exact @GlobalTheory.quotient_retract_pi_quotient | exact GlobalTheory.quotient_retract_pi_quotient | (intros; apply GlobalTheory.quotient_retract_pi_quotient <;> assumption)
end
