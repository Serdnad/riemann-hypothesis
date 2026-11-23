module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem ballMat_ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) (τ : Ψ) :
    ballMat q (ballPt q W) τ = (W τ)ᵀ := by
  ext a b
  simp [ballMat, ballPt]

theorem sgI_form (a : Fin j → ℂ) (b : Fin j' → ℂ) :
    star (Sum.elim a b : Sg j j' → ℂ) ⬝ᵥ (sgI j j' *ᵥ Sum.elim a b) = star a ⬝ᵥ a - star b ⬝ᵥ b := by
  simp [sgI, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, sub_eq_add_neg,
    neg_mulVec, Finset.sum_neg_distrib]

theorem form_mulVec {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) (z : Sg j j' → ℂ) :
    star (v *ᵥ z) ⬝ᵥ (sgI j j' *ᵥ (v *ᵥ z)) = star z ⬝ᵥ (sgI j j' *ᵥ z) := by
  have hv' : vᴴ * sgI j j' * v = sgI j j' := hv
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hv']

theorem norm_lt_of_ball {W : Matrix (Fin j') (Fin j) ℂ} (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) {y : Fin j' → ℂ}
    (hy : y ≠ 0) : (star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y)).re < (star y ⬝ᵥ y).re := by
  have hc : star y ≠ 0 := by simpa using hy
  have h := hW.dotProduct_mulVec_pos hc
  have hw : Wᵀ *ᵥ star y = star (Wᴴ *ᵥ y) := by
    rw [star_mulVec, conjTranspose_conjTranspose, mulVec_transpose]
  have e : star (star y) ⬝ᵥ ((1 - (Wᵀ)ᴴ * Wᵀ) *ᵥ star y) =
      star y ⬝ᵥ y - star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hw, dotProduct_sub, star_star, dotProduct_comm y (star y)]
    congr 1
    rw [dotProduct_mulVec, vecMul_conjTranspose, hw, star_star, dotProduct_comm]
  rw [e] at h
  have := (Complex.lt_def.1 h).1
  simpa using this

theorem isUnit_det_P {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det := by
  by_contra hne
  have h0 : (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det = 0 := by simpa using hne
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : v *ᵥ Sum.elim x (W *ᵥ x) =
      Sum.elim (0 : Fin j → ℂ) ((v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks v]
    rw [fromBlocks_mulVec]
    have h1 : v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x) = 0 := by
      rw [← hPx, add_mulVec, mulVec_mulVec]
    show Sum.elim (v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x))
      (v.toBlocks₂₁ *ᵥ x + v.toBlocks₂₂ *ᵥ (W *ᵥ x)) = _
    rw [h1, add_mulVec, mulVec_mulVec]
  have hen := form_mulVec hv (Sum.elim x (W *ᵥ x))
  rw [hz, sgI_form, sgI_form] at hen
  set y := W *ᵥ x with hy
  set Qx := (v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x
  have hxx : 0 < (star x ⬝ᵥ x).re := by
    have := (Complex.lt_def.1 (dotProduct_star_self_pos_iff.2 hx)).1
    simpa using this
  have hQ : 0 ≤ (star Qx ⬝ᵥ Qx).re := (Complex.le_def.1 (dotProduct_star_self_nonneg Qx)).1
  have hre := congrArg Complex.re hen
  simp only [Complex.sub_re, star_zero, dotProduct_zero, Complex.zero_re] at hre
  have hyy : (star x ⬝ᵥ x).re ≤ (star y ⬝ᵥ y).re := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyy
    simp at hyy
    linarith
  have hlt := norm_lt_of_ball hW hy0
  set w := Wᴴ *ᵥ y with hw
  have hnn : 0 ≤ (star (x - w) ⬝ᵥ (x - w)).re :=
    (Complex.le_def.1 (dotProduct_star_self_nonneg (x - w))).1
  have h1 : star x ⬝ᵥ w = star y ⬝ᵥ y := by
    rw [hw, dotProduct_mulVec, hy, star_mulVec]
  have h2 : star w ⬝ᵥ x = star y ⬝ᵥ y := by
    rw [hw, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hexp : star (x - w) ⬝ᵥ (x - w) = star x ⬝ᵥ x - star x ⬝ᵥ w - star w ⬝ᵥ x + star w ⬝ᵥ w := by
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, h1, h2] at hnn
  simp only [Complex.add_re, Complex.sub_re] at hnn
  linarith

theorem moebW_mul (u v : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ)
    (hP : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det) :
    moebW (u * v) W = moebW u (moebW v W) := by
  set P := v.toBlocks₁₁ + v.toBlocks₁₂ * W with hPd
  set Q := v.toBlocks₂₁ + v.toBlocks₂₂ * W with hQd
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hv : moebW v W = Q * P⁻¹ := rfl
  have huv : u * v = fromBlocks
      (u.toBlocks₁₁ * v.toBlocks₁₁ + u.toBlocks₁₂ * v.toBlocks₂₁)
      (u.toBlocks₁₁ * v.toBlocks₁₂ + u.toBlocks₁₂ * v.toBlocks₂₂)
      (u.toBlocks₂₁ * v.toBlocks₁₁ + u.toBlocks₂₂ * v.toBlocks₂₁)
      (u.toBlocks₂₁ * v.toBlocks₁₂ + u.toBlocks₂₂ * v.toBlocks₂₂) := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks]
  have e1 : (u * v).toBlocks₁₁ + (u * v).toBlocks₁₂ * W =
      (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P = u.toBlocks₁₁ * P + u.toBlocks₁₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₁₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 : (u * v).toBlocks₂₁ + (u * v).toBlocks₂₂ * W =
      (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P = u.toBlocks₂₁ * P + u.toBlocks₂₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₂₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hv]
  unfold moebW
  rw [e1, e2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul]

theorem moebBall_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  intro Ψ _ j j' n q u v hu hv t ht
  unfold moebBall
  congr 1
  funext τ
  rw [ballMat_ballPt, transpose_transpose]
  refine moebW_mul _ _ _ (isUnit_det_P (hv τ) ?_)
  simpa using ht τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ)

open Classical in
theorem pPart_add (y y' : Fin (j + j') → ℂ) : C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add (f := _), smul_sub]
  abel

open Classical in
theorem pPart_real_smul (r : ℝ) (y : Fin (j + j') → ℂ) : C.pPart R τ (r • y) = (r : ℂ) • C.pPart R τ y := by
  have h1 : ∀ y : Fin (j + j') → ℂ, C.perExt R (Pi.single τ (r • y)) = (r : ℂ) • C.perExt R (Pi.single τ y) := by
    intro y
    rw [Pi.single_smul, map_smul]
    ext i; simp
  have h2 : Complex.I • r • y = r • Complex.I • y := smul_comm _ _ _
  simp only [LatEmb.pPart, h2, h1, smul_sub]
  simp only [smul_smul]
  congr 2 <;> ring_nf

open Classical in
theorem pPart_I_smul (y : Fin (j + j') → ℂ) : C.pPart R τ (Complex.I • y) = Complex.I • C.pPart R τ y := by
  have h : Complex.I • Complex.I • y = -y := by simp [smul_smul]
  have h2 : C.perExt R (Pi.single τ (-y)) = - C.perExt R (Pi.single τ y) := by
    rw [Pi.single_neg, map_neg]
  simp only [LatEmb.pPart, h, h2]
  ext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (1 / 2 * (C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

def pPartL : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := C.pPart R τ
  map_add' := pPart_add C R τ
  map_smul' a y := by
    have ha : a • y = a.re • y + a.im • Complex.I • y := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      conv_lhs => rw [← Complex.re_add_im a]
      ring
    rw [ha, pPart_add, pPart_real_smul, pPart_real_smul, pPart_I_smul]
    simp only [RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im a]
    rw [add_smul, mul_smul]

theorem pPart_elim (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (v : Fin j → ℂ) (x : Fin j' → ℂ) :
    C.pPart R τ (A *ᵥ Sum.elim v x) =
      ∑ i, v i • C.pPart R τ (A *ᵥ Sum.elim (Pi.single i 1) 0) +
      ∑ b, x b • C.pPart R τ (A *ᵥ Sum.elim 0 (Pi.single b 1)) := by
  have hs : Sum.elim v x = ∑ i, v i • (Sum.elim (Pi.single i 1) 0 : Sg j j' → ℂ) +
      ∑ b, x b • (Sum.elim 0 (Pi.single b 1) : Sg j j' → ℂ) := by
    ext (i | b)
    · simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, Pi.single_apply]
  change pPartL C R τ _ = ∑ i, v i • pPartL C R τ _ + ∑ b, x b • pPartL C R τ _

  rw [hs, Matrix.mulVec_add, map_add (f := _), Matrix.mulVec_sum, Matrix.mulVec_sum, map_sum, map_sum]
  simp [Matrix.mulVec_smul]

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

theorem apply_eq_re (l : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    l z = (((l 1 : ℂ) - Complex.I * (l Complex.I : ℂ)) * z).re := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add (f := _), map_smul, map_smul]
  simp
  ring

theorem coeff_eq_zero {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (c : Ψ → ℂ) (h : ∀ x, ∑ τ, (c τ * s τ x).re = 0) (τ : Ψ) : c τ = 0 := by
  classical
  let m : Ψ ⊕ Ψ → (E →* ℂ) := Sum.elim (fun τ => (s τ : E →* ℂ))
    (fun τ => (((starRingEnd ℂ).comp (s τ) : E →+* ℂ) : E →* ℂ))
  have hm : Function.Injective m := by
    rintro (a | a) (b | b) hab
    · have : s a = s b := RingHom.ext fun x => DFunLike.congr_fun hab x
      rw [hs this]
    · exact absurd (RingHom.ext fun x => DFunLike.congr_fun hab x) (hc a b)
    · exact absurd (RingHom.ext fun x => (DFunLike.congr_fun hab x).symm) (hc b a)
    · have h1 : (starRingEnd ℂ).comp (s a) = (starRingEnd ℂ).comp (s b) :=
        RingHom.ext fun x => DFunLike.congr_fun hab x
      have : s a = s b := by
        ext x
        exact RingHom.injective (starRingEnd ℂ) (DFunLike.congr_fun h1 x)
      rw [hs this]
  have hli := (linearIndependent_monoidHom E ℂ).comp m hm
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (Sum.elim c (fun τ => (starRingEnd ℂ) (c τ))) (by
    funext x
    rw [Fintype.sum_sum_type]
    have h2 : ∑ τ, ((c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x)) = 0 := by
      have : ∀ τ, (c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x) = 2 * (((c τ * s τ x).re : ℝ) : ℂ) := by
        intro τ
        rw [Complex.add_conj]
        push_cast
        ring
      simp_rw [this]
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, h x]
      simp
    rw [Finset.sum_add_distrib] at h2
    simpa [m, Finset.sum_apply, map_mul] using h2)
  simpa using key (Sum.inl τ)

theorem span_eq_top {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (N : ℕ) (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ')) :
    Submodule.span ℝ (Set.range fun (v : Fin N → E) => (fun τ i => s τ (v i) : Ψ → Fin N → ℂ)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨L, hL0, hL⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hL0
  let l : Fin N → Ψ → (ℂ →ₗ[ℝ] ℝ) := fun i τ =>
    L ∘ₗ LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ ∘ₗ LinearMap.single ℝ (fun _ : Fin N => ℂ) i
  have hl : ∀ i τ, l i τ = 0 := by
    intro i τ
    have hc0 := coeff_eq_zero s hs hc (fun τ => ((l i τ 1 : ℝ) : ℂ) - Complex.I * ((l i τ Complex.I : ℝ) : ℂ)) (by
      intro x
      simp_rw [← apply_eq_re]
      have hmem : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) ∈ LinearMap.ker L :=
        hL (Submodule.subset_span ⟨_, rfl⟩)
      have hsum : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) =
          ∑ τ, LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ
            (LinearMap.single ℝ (fun _ : Fin N => ℂ) i (s τ x)) := by
        funext τ' j
        rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single τ'
          (fun b _ hb => by simp [Pi.single_apply, hb.symm]) (by simp)]
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_apply, hj]

      rw [LinearMap.mem_ker, hsum, map_sum] at hmem
      exact hmem) τ
    have h1 : l i τ 1 = 0 := by
      have := congrArg Complex.re hc0
      simpa using this
    have h2 : l i τ Complex.I = 0 := by
      have := congrArg Complex.im hc0
      simpa using this
    apply LinearMap.ext
    intro z
    rw [apply_eq_re, h1, h2]
    simp
  refine LinearMap.pi_ext' fun τ => LinearMap.pi_ext' fun i => ?_
  exact hl i τ

def vecOf {E : Type} [Field E] {Ψ : Type} (N : ℕ) (s : Ψ → (E →+* ℂ)) :
    (Fin N → E) →+ (Ψ → Fin N → ℂ) where
  toFun v τ i := s τ (v i)
  map_zero' := by funext τ i; simp
  map_add' a b := by funext τ i; simp

theorem exists_basis {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] {g N : ℕ} (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (hg : g = Fintype.card Ψ * N) {Λ : Type} [AddCommGroup Λ] (e : Λ →+ (Fin N → E))
    (hspan : ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (lam : Module.Basis (Fin (2 * g)) ℤ Λ) :
    ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = s τ (e (lam k) i) := by
  classical
  have hlat : ∀ x : Λ, vecOf N s (e x) ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro x

    rw [← lam.sum_repr x, map_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hall : ∀ v, vecOf N s v ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro v
    obtain ⟨k, x, hk, hx⟩ := hspan v
    have h2 := hlat x
    rw [hx, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hk)).1 h2
  have htop : (⊤ : Submodule ℝ (Ψ → Fin N → ℂ)) ≤
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    rw [← span_eq_top N s hs hc]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hall v
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Ψ → Fin N → ℂ) := by
    rw [Fintype.card_fin, Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, hg]
    ring
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ htop hcard, fun k τ i => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem exists_realBasis_of_latBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g N : ℕ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → g = Fintype.card Ψ * N → ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin N → E)), (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ lam : Module.Basis (Fin (2 * g)) ℤ Λ, ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = embOf (σ τ) (e (lam k) i) := by
  intro E _ _ _ Ψ _ g N σ hσ hg Λ _ e hspan lam
  have hres : ∀ τ a, embOf (σ τ) (algebraMap (𝓞 E) E a) = σ τ a := fun τ a =>
    IsFractionRing.lift_algebraMap (intEmb_injective (σ τ)) a
  have hs : Function.Injective fun τ => embOf (σ τ) := by
    intro a b hab
    apply hσ.1
    ext x
    rw [← hres a x, ← hres b x]
    exact DFunLike.congr_fun hab _
  have hc : ∀ τ τ', embOf (σ τ) ≠ (starRingEnd ℂ).comp (embOf (σ τ')) := by
    intro τ τ' h
    have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := by
      ext x
      rw [RingHom.comp_apply, ← hres τ x, ← hres τ' x]
      exact DFunLike.congr_fun h _
    exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩
  exact LatBas.exists_basis (fun τ => embOf (σ τ)) hs hc hg e hspan lam

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem ballPot_ballPt_eq : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ), ballPot q (ballPt q W) = -∑ τ, Real.log (1 - W τ * (W τ)ᴴ).det.re := by
  intro Ψ _ j j' n q W
  unfold ballPot
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hm : ballMat q (ballPt q W) τ = (W τ)ᵀ := by
    ext a b
    simp [ballMat, ballPt]
  have key : 1 - ((W τ)ᵀ)ᴴ * (W τ)ᵀ = (starRingEnd ℂ).mapMatrix (1 - W τ * (W τ)ᴴ) := by
    ext a b

    simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, map_sub, map_sum, map_mul]
    congr 1
    · by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp
  rw [hm, key, ← RingHom.map_det, Complex.conj_re]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

namespace LatEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem perExt_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R' y = k (C.perExt R y) := by
  have h : C.perExt R' = (k.toLinearMap.restrictScalars ℝ) ∘ₗ C.perExt R := by
    refine C.bas.ext fun i => ?_
    simp [perExt, Module.Basis.constr_basis, hk]
  rw [h]
  rfl

theorem pPart_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R' τ y = k (C.pPart R τ y) := by
  simp only [pPart, C.perExt_of_coord k hk, map_smul, map_sub]

theorem pBar_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pBar R' τ y = k (C.pBar R τ y) := by
  simp only [pBar, C.perExt_of_coord k hk, map_smul, map_add (f := _)]

end LatEmb

theorem isAdapted_of_eqvBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted R A → R.EqvBy R' 1 → C.IsAdapted R' A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R R' A hA hE
  obtain ⟨k, hk⟩ := hE
  have hk' : ∀ x, R'.P x = k (R.P x) := fun x => hk x
  refine ⟨hA.unit, fun τ v => ?_, fun τ v => ?_⟩
  · rw [C.pPart_of_coord k hk', hA.ker, map_zero]
  · rw [C.pBar_of_coord k hk', hA.kerBar, map_zero]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end
