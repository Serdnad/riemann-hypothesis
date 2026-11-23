module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKA
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle001
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Analysis.Convex.Cone.Extension
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def posCone : PointedCone ℝ C_c(X, ℝ) where
  carrier := {g | ∀ x, 0 ≤ g x}
  zero_mem' := fun x => by simp
  add_mem' := fun hf hg x => by simpa using add_nonneg (hf x) (hg x)
  smul_mem' := fun ⟨c, hc⟩ g hg x => by simpa using mul_nonneg hc (hg x)

theorem im_L (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (L : A →ₗ[ℂ] ℂ) (hpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0)
    (f : AR A) : (L ⟨f.1, f.2.1⟩).im = 0 := by
  obtain ⟨b, hbA, hb0, M, hM, hMb⟩ := dom A hbump (y := fun x => (f.1 x).re)
    (Complex.continuous_re.comp (hA _ f.2.1).1) ((hA _ f.2.1).2.comp_left Complex.zero_re)
  set F : A := ⟨f.1, f.2.1⟩
  set Bb : A := ⟨b, hbA⟩
  have h1 := hpos ((M : ℂ) • Bb - F) (fun x => by
    have := f.2.2 x
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Bb, F, (hb0 x).2, this]
    constructor <;> linarith [(hMb x).2])
  have h2 := hpos ((M : ℂ) • Bb) (fun x => by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Bb, (hb0 x).2]
    constructor <;> nlinarith [(hb0 x).1])
  have : L F = L ((M : ℂ) • Bb) - L ((M : ℂ) • Bb - F) := by rw [map_sub]; ring
  rw [this, Complex.sub_im, h1.2, h2.2, sub_zero]

theorem extend (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (L : A →ₗ[ℂ] ℂ) (hpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0) :
    ∃ Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ, ∀ a : AR A, Λ (reC A hA a) = (L ⟨a.1, a.2.1⟩).re := by
  set φ := reC A hA
  let e := LinearEquiv.ofInjective φ (reC_inj A hA)
  let fP : C_c(X, ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range φ, reL A L ∘ₗ e.symm.toLinearMap⟩
  have he : ∀ a : AR A, e.symm ⟨φ a, LinearMap.mem_range_self φ a⟩ = a := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm
  have hnonneg : ∀ x : fP.domain, (x : C_c(X, ℝ)) ∈ posCone → 0 ≤ fP x := by
    rintro ⟨y, hy⟩ hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
    change 0 ≤ reL A L (e.symm ⟨φ a, _⟩)
    rw [he]
    exact (hpos ⟨a.1, a.2.1⟩ (fun x => ⟨hx x, a.2.2 x⟩)).1
  have hdense : ∀ y : C_c(X, ℝ), ∃ x : fP.domain, (x : C_c(X, ℝ)) + y ∈ posCone := by
    intro y
    obtain ⟨b, hbA, hb0, M, hM, hMb⟩ := dom A hbump y.continuous y.hasCompactSupport
    let bR : AR A := ⟨b, hbA, fun x => (hb0 x).2⟩
    refine ⟨⟨M • φ bR, Submodule.smul_mem _ _ (LinearMap.mem_range_self φ bR)⟩, fun x => ?_⟩
    simpa [φ, reC, bR] using (hMb x).1
  obtain ⟨g, hg, hgpos⟩ := riesz_extension posCone fP hnonneg hdense
  refine ⟨PositiveLinearMap.mk₀ g (fun x hx => hgpos x (fun z => hx z)), fun a => ?_⟩
  change g (φ a) = _
  rw [hg ⟨φ a, LinearMap.mem_range_self φ a⟩]
  change reL A L (e.symm ⟨φ a, _⟩) = _
  rw [he]
  rfl

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end

section

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_smul {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (r : R) (M : Matrix m p R) :
    cj s (r • M) = s r • cj s M := by
  ext i j; simp [cj]

theorem map_cj {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (s : S →+* S) (π : R →+* S)
    (h : ∀ x, π (σ x) = s (π x)) {m p : Type} (M : Matrix m p R) : (cj σ M).map π = cj s (M.map π) := by
  ext i j; simp [cj, h]

theorem det_jacobi {R : Type} [CommRing R] (σ : R →+* R) (a b0 c d b : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (hb : cj σ b = b) :
    (fromBlocks a (a * b + b0) c (d + c * b)).det * (cj σ (d + c * b)).det = (d + c * b).det := by
  have hu : cj σ (d + c * b) = cj σ d + b * cj σ c := by rw [cj_add, cj_mul, hb]
  have e : fromBlocks a (a * b + b0) c (d + c * b) * fromBlocks (cj σ (d + c * b)) 0 (-cj σ c) 1 =
      fromBlocks 1 (a * b + b0) 0 (d + c * b) := by
    rw [fromBlocks_multiply, hu]
    congr 1
    · rw [← R1]; noncomm_ring
    · simp
    · calc c * (cj σ d + b * cj σ c) + (d + c * b) * -cj σ c = c * cj σ d - d * cj σ c := by noncomm_ring
        _ = 0 := by rw [R2, sub_self]
    · simp
  have := congrArg Matrix.det e
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at this
  simpa using this

theorem core {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsMaximal]
    (h2 : IsUnit (2 : R)) (hU : ∀ x, x ∉ 𝔭 → σ x ∉ 𝔭 → IsUnit x) (a b0 c d : Matrix n n R)
    (R1 : a * cj σ d - b0 * cj σ c = 1) (R2 : c * cj σ d = d * cj σ c) (R3 : d * cj σ a - c * cj σ b0 = 1) :
    ∃ b : Matrix n n R, cj σ b = b ∧ IsUnit (d + c * b).det := by
  letI : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  set π : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  set lift : R ⧸ 𝔭 → R := Function.surjInv hsurj with hlift
  have hl : ∀ y, π (lift y) = y := Function.surjInv_eq hsurj
  have hXY : c * (-cj σ b0) + d * cj σ a = 1 := by rw [← R3]; noncomm_ring
  have hXY' : c.map π * (-cj σ b0).map π + d.map π * (cj σ a).map π = 1 := by
    have := congrArg π.mapMatrix hXY
    simpa only [map_add (f := _), map_mul, map_one, RingHom.mapMatrix_apply] using this
  have key : ∃ b : Matrix n n R, cj σ b = b ∧ (d + c * b).det ∉ 𝔭 := by
    have hdet : ∀ b : Matrix n n R, ((d + c * b).map π).det ≠ 0 → (d + c * b).det ∉ 𝔭 := by
      intro b hb hm
      apply hb
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
      rw [← hm, RingHom.map_det]; rfl
    by_cases hst : ∀ x ∈ 𝔭, σ x ∈ 𝔭
    · set s : R ⧸ 𝔭 →+* R ⧸ 𝔭 := Ideal.quotientMap 𝔭 σ (fun x hx => hst x hx) with hs
      have hsπ : ∀ x, π (σ x) = s (π x) := fun x => (Ideal.quotientMap_mk).symm
      have hss : ∀ y, s (s y) = y := by
        intro y; obtain ⟨x, rfl⟩ := hsurj y; rw [← hsπ, ← hsπ, hσ]
      have hlag : c.map π * cj s (d.map π) = d.map π * cj s (c.map π) := by
        rw [← map_cj σ s π hsπ, ← map_cj σ s π hsπ]
        have := congrArg π.mapMatrix R2
        simpa only [map_mul, RingHom.mapMatrix_apply] using this
      obtain ⟨B, hBh, hBd⟩ := fieldA s hss _ _ _ _ hXY' hlag
      set B' := B.map lift with hB'
      refine ⟨(↑h2.unit⁻¹ : R) • (B' + cj σ B'), ?_, hdet _ ?_⟩
      · have hinv : σ (↑h2.unit⁻¹ : R) = ↑h2.unit⁻¹ := by
          have e1 : σ (↑h2.unit⁻¹ : R) * 2 = 1 := by
            have : σ ((↑h2.unit⁻¹ : R) * 2) = 1 := by
              rw [show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl, Units.inv_mul, map_one]
            rwa [map_mul, map_ofNat] at this
          calc σ (↑h2.unit⁻¹ : R) = σ (↑h2.unit⁻¹ : R) * (2 * ↑h2.unit⁻¹) := by
                rw [show (2 : R) * ↑h2.unit⁻¹ = ↑h2.unit * ↑h2.unit⁻¹ from rfl, Units.mul_inv, mul_one]
            _ = ↑h2.unit⁻¹ := by rw [← mul_assoc, e1, one_mul]
        rw [cj_smul, cj_add, cj_cj σ hσ, hinv, add_comm]
      · have hmap : ((↑h2.unit⁻¹ : R) • (B' + cj σ B')).map π = B := by
          ext i j
          have hij := congrFun (congrFun hBh i) j
          rw [cj_apply] at hij
          have h2π : π (↑h2.unit⁻¹ : R) * 2 = 1 := by
            rw [← map_ofNat π 2, ← map_mul, show (↑h2.unit⁻¹ : R) * 2 = ↑h2.unit⁻¹ * ↑h2.unit from rfl,
              Units.inv_mul, map_one]
          simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add (f := _), cj_apply,
            hB', hsπ, hl, hij]
          linear_combination (B i j) * h2π
        have : (d + c * ((↑h2.unit⁻¹ : R) • (B' + cj σ B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
    · push_neg at hst
      obtain ⟨y, hy, hσy⟩ := hst
      obtain ⟨r, i, hi, hri⟩ := h𝔭.exists_inv hσy
      obtain ⟨B, hBd⟩ := fieldB _ _ _ _ hXY'
      set B' := B.map lift with hB'
      set x := r * σ y with hx
      have hπx : π x = 1 := by
        have : π (x + i) = 1 := by rw [hx, hri, map_one]
        rwa [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hi, add_zero] at this
      have hπσx : π (σ x) = 0 := by
        rw [hx, map_mul, hσ, map_mul, (Ideal.Quotient.eq_zero_iff_mem).2 hy, mul_zero]
      refine ⟨x • B' + cj σ (x • B'), ?_, hdet _ ?_⟩
      · rw [cj_add, cj_cj σ hσ, add_comm]
      · have hmap : (x • B' + cj σ (x • B')).map π = B := by
          ext i j
          simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cj_apply, map_add (f := _), map_mul,
            hπx, hπσx, hB', hl]
          ring
        have : (d + c * (x • B' + cj σ (x • B'))).map π = d.map π + c.map π * B := by
          rw [← hmap]; simp [Matrix.map_add (f := _), Matrix.map_mul]
        rw [this]; exact hBd
  obtain ⟨b, hb, hb𝔭⟩ := key
  refine ⟨b, hb, hU _ hb𝔭 fun hσ𝔭 => hb𝔭 ?_⟩
  rw [← det_jacobi σ a b0 c d b R1 R2 hb, det_cj]
  exact Ideal.mul_mem_left _ _ hσ𝔭

end PositivityTheory.Rg.Rsw.L.LGenK
end

section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

theorem schMajor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) :
    ∃ F₀ : SchwartzMap V ℂ, (∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : V → ℂ, c.HasTemperateGrowth ∧ HasCompactSupport c ∧
        ∀ i y, ‖f i y‖ * ‖1 - c y‖ ≤ ε * (F₀ y).re := by
  classical
  set e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean with he
  set q : V → ℝ := fun y => ‖e y‖ ^ 2 with hqdef
  have hqy : ∀ y, q y = ‖e y‖ ^ 2 := fun y => rfl
  have hq0 : ∀ y, 0 ≤ q y := fun y => by rw [hqy]; positivity
  have hq : q.HasTemperateGrowth :=
    (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).comp
      e.hasTemperateGrowth
  have hq_upper : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖q y‖) ^ k := by
    refine ⟨1, ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖, fun y => ?_⟩
    have h1 : ‖y‖ ≤ ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖ * ‖e y‖ := by
      have := (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V).le_opNorm (e y)
      simpa using this
    have h2 : ‖e y‖ ≤ 1 + ‖q y‖ := by
      rw [Real.norm_of_nonneg (hq0 y), hqy]
      nlinarith [sq_nonneg (‖e y‖ - 1), norm_nonneg (e y)]
    rw [pow_one]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hqA : ∀ y, q y ≤ ‖(e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ ^ 2 * ‖y‖ ^ 2 := by
    intro y
    rw [hqy, ← mul_pow]
    have := (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))).le_opNorm y
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using this) 2
  obtain ⟨b, hb0, hbs, hbε⟩ := lmajASeq f q hq0 _ (sq_nonneg _) hqA
  obtain ⟨h, hh0, hhb⟩ := lmajASeqSchwartz b hb0 hbs
  set F₀ : SchwartzMap V ℂ := SchwartzMap.compCLM ℝ hq hq_upper h with hF₀
  have hF : ∀ y, F₀ y = h (q y) := fun y => rfl
  refine ⟨F₀, fun y => by rw [hF]; exact hh0 _, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hbε ε hε
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    ⟨(N : ℝ) + 1, (N : ℝ) + 2, by positivity, by linarith⟩
  set c : V → ℂ := fun y => ((β (e y) : ℝ) : ℂ) with hc
  have hcd : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp ((β.contDiff).comp e.contDiff)
  have hcs : HasCompactSupport c :=
    (β.hasCompactSupport.comp_homeomorph e.toHomeomorph).comp_left Complex.ofReal_zero
  refine ⟨c, hcs.hasTemperateGrowth hcd, hcs, fun i y => ?_⟩
  have hF0 : 0 ≤ (F₀ y).re := by rw [hF]; exact (hh0 _).1
  by_cases hy : ‖e y‖ ≤ (N : ℝ) + 1
  · have hβ : β (e y) = 1 :=
      β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hy)
    have hc1 : c y = 1 := by simp [hc, hβ]
    rw [hc1, sub_self, norm_zero, mul_zero]
    exact mul_nonneg hε.le hF0
  · push Not at hy
    have hqN : (N : ℝ) ≤ q y := by
      rw [hqy]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have h1c : ‖1 - c y‖ ≤ 1 := by
      have : (1 : ℂ) - c y = ((1 - β (e y) : ℝ) : ℂ) := by simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [β.nonneg (x := e y), β.le_one (x := e y)]
    have hqn : |q y - (⌊q y⌋₊ : ℝ)| ≤ 1 := by
      have h1 := Nat.floor_le (hq0 y)
      have h2 := Nat.lt_floor_add_one (q y)
      rw [abs_le]; constructor <;> linarith
    calc ‖f i y‖ * ‖1 - c y‖ ≤ ‖f i y‖ := mul_le_of_le_one_right (norm_nonneg _) h1c
      _ ≤ ε * b ⌊q y⌋₊ := hN i y hqN
      _ ≤ ε * (F₀ y).re := by rw [hF]; exact mul_le_mul_of_nonneg_left (hhb _ _ hqn) hε.le

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
