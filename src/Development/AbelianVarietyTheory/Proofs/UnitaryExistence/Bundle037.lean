module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsoExt

theorem exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by
  obtain ⟨A, hA⟩ := GlobalTheory.FrameFibre.exists_matrix φ hφ hspan (φ' ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := GlobalTheory.FrameFibre.exists_matrix φ' hφ' hspan' (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ' (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ' v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan' fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA',
      Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem exists_unitary_of_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]

end GlobalTheory.IsoExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_model_pushInvertible_under_cdvr : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  intro hI hN E _ _ _ H Dw l Xo c hpos T io p hp hpT hg
  classical
  obtain ⟨Xf, hXf⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo :=
    ⟨Function.update (fun l' => (hN E H Dw l' hpos).some) l Xo, Function.update_self ..⟩
  subst hXf
  let U₀ : ValuationSubring T.Fr := (ValuationRing.valuation T.V T.Fr).valuationSubring
  have hU₀ : ∀ x : T.Fr, x ∈ U₀ ↔ ∃ a : T.V, algebraMap T.V T.Fr a = x := fun x =>
    ValuationRing.mem_integer_iff T.V T.Fr x
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hpU : (p : c.F) ∈ (U₀.comap io).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro h
    rw [ValuationSubring.mem_comap, hU₀] at h
    obtain ⟨a, ha⟩ := h
    have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h1 : a * (p : T.V) = 1 := by
      apply hinj
      rw [map_mul, ha, map_natCast, map_one, ← map_natCast io p, ← map_mul, inv_mul_cancel₀ hp0, map_one]
    exact (IsLocalRing.mem_maximalIdeal _).1 hpT (IsUnit.of_mul_eq_one_right a h1)
  obtain ⟨W, hW, hWU⟩ := GlobalTheory.T.exists_valuationSubring_complex_comap_eq c.F (U₀.comap io) p hpU
  obtain ⟨Y, hY, -⟩ := hI.2 E H Dw hpos Xf
  have hmem : ∀ x : c.V W, ∃ a : T.V, algebraMap T.V T.Fr a = io x := by
    intro x
    have hx : (x : c.F) ∈ U₀.comap io := hWU ▸ x.2
    exact (hU₀ _).1 (ValuationSubring.mem_comap.1 hx)
  choose f hf using hmem
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y p W hp hW ⟨l, c, hg⟩,
    ((hY p W hp hW).1.1 ⟨l, c, hg⟩).2.2.1, ?_⟩
  refine ⟨{ toFun := f
            map_one' := hinj (by simp [hf])
            map_mul' := fun x y => hinj (by simp [hf])
            map_zero' := hinj (by simp [hf])
            map_add' := fun x y => hinj (by simp [hf]) }, ?_⟩
  ext x
  exact hf x

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem uMat_conj_eq_diagonal {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ d : Fin n → ℝ, (∀ k : Fin n, 0 < sgn p0 k * d k) ∧
      (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) = Matrix.diagonal fun a => ((d a : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := hs ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  refine ⟨fun k => (B k k).re, fun k => ?_, ?_⟩
  · have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
      rw [hprod k.succ, hprod k.castSucc]
      exact prod_castLE_succ (f := fun k => B k k) k.isLt
    have h1 := hs k.succ
    have h0 := hs k.castSucc
    rw [hsucc, Complex.mul_re, hre, mul_zero, sub_zero, Fin.val_succ, psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (pos_iff_pos_of_mul_pos (a := psgn p0 k * (lminor A k.castSucc).re) ?_).1 h0
    exact h1.trans_eq (by ring)
  · rw [hdiag]
    congr 1
    funext k
    apply Complex.ext <;> simp [hre]

theorem exists_upper_conj_eq_signature {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, b.det ≠ 0 ∧ b.BlockTriangular id ∧
      bᵀ * A * b.map (starRingEnd ℂ)
        = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨d, hd, hA'⟩ := uMat_conj_eq_diagonal p0 A hA hs
  refine ⟨uMat A * Matrix.diagonal fun k : Fin n => (((√(sgn p0 k * d k))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_uMat, one_mul, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hd k)).ne')
  · exact (uMat_upper A).mul (Matrix.blockTriangular_diagonal _)
  · rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.diagonal_transpose,
      Matrix.diagonal_map (map_zero _), ← Matrix.mul_assoc, Matrix.mul_assoc _ (uMat A)ᵀ,
      Matrix.mul_assoc _ ((uMat A)ᵀ * A), hA',
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    have h1 := Real.mul_self_sqrt (hd k).le
    have h2 := (Real.sqrt_pos.2 (hd k)).ne'
    set s := √(sgn p0 k * d k)
    have h3 : d k = sgn p0 k * (s * s) := by
      rw [h1]
      rcases sgn_sq p0 k with h | h <;> simp [h]
    rw [h3]
    field_simp

theorem frame_mul_triangular_orthonormal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ x₀ = rmul x b) ∧ ∀ (τ : E →+* ℂ) (x₀ x₁ : Matrix (Fin r) (Fin r) ℂ), gram τ Gm x₀ = (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → gram τ Gm x₁ = gram τ Gm x₀ → ∃ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ ∧ x₁ = u * x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx => ?_, fun τ x₀ x₁ h0 h1 => ?_⟩
  · choose b hb using fun τ : Ψ => exists_upper_conj_eq_signature p0 (gram τ.1 Gm (mat x τ))
      (gram_isHermitian τ.1 hG _) (hx τ).2
    refine ⟨rmul x fun τ => b τ, fun τ => b τ,
      fun τ => ⟨(hb τ).1, fun a c hca => (hb τ).2.1 hca⟩, fun τ => ?_, rfl⟩
    show gram τ.1 Gm (mat x τ * b τ) = _
    rw [FrameDegreeData.gram_mul]
    exact (hb τ).2.2
  · have hdet : IsUnit x₀.det := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have h2 := congrArg Matrix.det h0
      rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul,
        zero_mul, Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
      rcases sgn_sq p0 k with h' | h' <;> simp [h']
    refine ⟨x₁ * x₀⁻¹, ?_, (Matrix.nonsing_inv_mul_cancel_right _ _ hdet).symm⟩
    rw [← FrameDegreeData.gram_eq, FrameDegreeData.gram_mul, h1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hdet,
      FrameDegreeData.gram_eq]
    simp

end GlobalTheory.UnitFrames
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  first | exact @GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | exact GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | (intros; apply GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular <;> assumption)
end

end

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  first | exact @GlobalTheory.IsoExt.exists_unitary_of_isometry | exact GlobalTheory.IsoExt.exists_unitary_of_isometry | (intros; apply GlobalTheory.IsoExt.exists_unitary_of_isometry <;> assumption)

end
end
