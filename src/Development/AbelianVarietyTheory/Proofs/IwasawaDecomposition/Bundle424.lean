module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle396
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle408
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle409
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle410
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem descend_exists (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ Φ : S.WL j →+ FmT D T S i j b, (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) ∧
      (∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x)) ∧
      ∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  exact GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form D.LL0 S.kKs S.kKs_spec (WKr D S j) bs (fun k => hW ▸ hb k) (hW ▸ hKs) hLi hLs
    (KT := KT D T i b) (readK D T i b) (fun s => rfl)

theorem descend_actL (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (g : G0g D.nd) (x : S.WL j) :
    Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x) := by
  have hcR : cR D S In.chi j (S.eG.symm g) = chiL S j (In.chi j h1 h2) (S.eG.symm g) := by
    unfold cR; rw [dite_eq_left ⟨h1, h2⟩]
  change _ = ((readK D T i b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g))) (Φ x)
  rw [hcR]
  have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
      (S.A j).ρ (S.eG.symm g) x := by
    simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
  rw [e1, hc, hf ((S.A j).ρ (S.eG.symm g)) (rhoR D S In.rho j (S.eG.symm g)) (fun w => rfl), map_inv₀]
  rfl

theorem descend_eSum (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) :
    Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x) := by
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _

  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  unfold eGT
  rw [MonoidAlgebra.lift_apply]
  simp only [eAlgT, MonoidAlgebra.coeff_ofCoeff]
  rw [Finsupp.sum_fintype _ _ (by intro; simp), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, hc, ha]
  simp

theorem descend_mem_V0T (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (he : ∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x))
    (x : S.WL j) (hx : x ∈ goodL D S In.θ j) : Φ x ∈ V0T D T S In.rho In.chi In.θ i j b := by
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨Φ x, ?_, ?_⟩
  · rw [SetLike.mem_coe, Fm0T, Submodule.mem_iInf]
    intro u
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    have h := hx2 u
    rw [Module.End.mem_eigenspace_iff] at h
    rw [LinearEquiv.coe_coe, ← ha, h, hc]
    simp [psiUT]
  · rw [Module.End.mem_eigenspace_iff, one_smul] at hx1
    rw [← he, hx1]

theorem descend_mem_eigenspace (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (k : ℕ) (P : PlE D.host) (μ : ↥D.LL0) (x : S.WL j)
    (hx : x ∈ Module.End.eigenspace (In.hL j k P) (μ : D.what₂.LL)) :
    Φ x ∈ Module.End.eigenspace (hkT D T S In i j b k P)
      (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hw : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  change ((show KT D T i b from algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k •
    LinearMap.baseChange (KT D T i b) (hLr D S In j k P) (Φ x) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = _
  rw [← hf _ _ hw, hx, hc]
  exact smul_smul _ _ _

end GlobalTheory.HeightCounting.FormsStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.TameTau

theorem tauTame : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  intro _ D cf b0 b1 Sx T Sp i j b kv _ _ hl
  have hg := D.host.g_prime kv.1
  have hover := D.naut.plGw_over kv.1 kv.2
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field (E := D.host.E) (Ω := D.nd.Om) (NX.pG D kv) (D.host.g kv.1) hg
    (GlobalTheory.Proof.EigenvalueCoprimeConjugation.normV_plGw D kv.1 kv.2) (by simpa [placesOver] using hover) (T.twistBaseCoefficientRing_isAdic i) (T.chi1 i j b)
    (T.twistCharacterFamily_continuous i j b) (fun A hA σ hσ => T.twistCharacterFamily_tame i j b kv.1 _ hover hl A hA σ hσ)
  refine ⟨(Units.map (baseCoeffToFractionRing D T i).toMonoidHom).comp τ, fun x u hu => ?_⟩
  rw [MonoidHom.comp_apply, Units.coe_map, hτ x u hu]
  rfl

end GlobalTheory.TameTau
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HuaQuadric

variable {p q : ℕ}

theorem exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R.det ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, ?_, hR⟩
  have h := hA.det_pos.ne'
  rw [hR, det_mul] at h
  exact (right_ne_zero_of_mul h).isUnit

theorem shear_fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin q) ℂ) (c : Matrix (Fin q) (Fin p) ℂ)
    (d : Matrix (Fin q) (Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (fromBlocks a b c d) Z = fromBlocks a (a * Z + b) (Zᴴ * a + c) ((Zᴴ * a + c) * Z + (Zᴴ * b + d)) := by
  simp [shear, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem exists_square {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) :
    ∃ (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ),
      IsUnit R.det ∧ IsUnit T.det ∧ A.det = (Complex.normSq R.det * Complex.normSq T.det : ℝ) ∧
      ∀ Z, (shear A Z).toBlocks₂₂ = Tᴴ * (1 + (R * Z * T⁻¹ + C)ᴴ * (R * Z * T⁻¹ + C)) * T := by
  obtain ⟨R, hR, ha⟩ := exists_factor (posDef_blocks hA).1
  have e : A.toBlocks₂₁ = A.toBlocks₁₂ᴴ := by
    ext a b
    exact (hA.1.apply _ _).symm
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hR.star
  obtain ⟨c, hc⟩ : ∃ c, A.toBlocks₁₂ = Rᴴ * R * c :=
    ⟨R⁻¹ * (Rᴴ⁻¹ * A.toBlocks₁₂), by
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hR, mul_nonsing_inv_cancel_left _ _ hRh]⟩
  have hA' : A = fromBlocks (Rᴴ * R) (Rᴴ * R * c) (cᴴ * (Rᴴ * R)) A.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks A, e, ha, hc]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  generalize A.toBlocks₂₂ = d at hA'
  have hs : shear A (-c) = fromBlocks (Rᴴ * R) 0 0 (d - cᴴ * (Rᴴ * R * c)) := by
    rw [hA', shear_fromBlocks]
    simp [sub_eq_neg_add]
  have hS := (posDef_blocks (posDef_shear hA (-c))).2.1
  rw [hs, toBlocks_fromBlocks₂₂] at hS
  obtain ⟨T, hT, ht⟩ := exists_factor hS
  have hTh : IsUnit Tᴴ.det := by rw [det_conjTranspose]; exact hT.star
  refine ⟨R, T, R * c * T⁻¹, hR, hT, ?_, fun Z => ?_⟩
  · rw [← det_shear A (-c), hs, ht, det_fromBlocks_zero₂₁, det_mul, det_mul, det_conjTranspose, det_conjTranspose]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    rfl
  · rw [hA', shear_fromBlocks, toBlocks_fromBlocks₂₂, eq_add_of_sub_eq ht]
    simp only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      conjTranspose_nonsing_inv, mul_nonsing_inv_cancel_left _ _ hTh,
      nonsing_inv_mul _ hT, Matrix.mul_one, Matrix.one_mul]
    abel

theorem quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  intro p q A hA
  obtain ⟨R, T, C, hR, hT, hd, hZ⟩ := exists_square hA
  have hr : 0 < Complex.normSq R.det := Complex.normSq_pos.2 hR.ne_zero
  have ht : 0 < Complex.normSq T.det := Complex.normSq_pos.2 hT.ne_zero
  let f : (Fin p × Fin q → ℂ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal ((1 + (toMat v)ᴴ * toMat v).det.re ^ (-((p + q : ℕ) : ℤ)))
  have hf : Measurable f :=
    ((Complex.continuous_re.comp (continuous_const.add
      (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det).measurable.pow_const
        _).ennreal_ofReal
  have h1 : ∀ v : Fin p × Fin q → ℂ,
      ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) =
        ENNReal.ofReal (Complex.normSq T.det ^ (-((p + q : ℕ) : ℤ))) * f (vecOf (R * toMat v * T⁻¹ + C)) := by
    intro v
    simp only [f, toMat_vecOf]
    rw [← ENNReal.ofReal_mul (zpow_pos ht _).le, ← mul_zpow, hZ, det_mul, det_mul, det_conjTranspose, mul_right_comm,
      ← Complex.re_ofReal_mul, Complex.normSq_eq_conj_mul_self]
    rfl
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    GlobalTheory.FlagFibre.lintegral_affine p q R T⁻¹ C hR (isUnit_nonsing_inv_det _ hT) f hf]
  have h2 : ∫⁻ v, f v = ENNReal.ofReal (grassConst p q)⁻¹ := GlobalTheory.HuaIntegral.dual_mass p q
  have h3 : Complex.normSq T⁻¹.det = (Complex.normSq T.det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
  rw [h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos ht _).le, ← ENNReal.ofReal_mul (by positivity), hd,
    Complex.ofReal_re, div_eq_mul_inv]
  congr 2
  simp only [_root_.zpow_neg, _root_.zpow_natCast, pow_add, mul_pow, inv_pow]
  field_simp

end GlobalTheory.HuaQuadric
end

section

noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

def lowPos {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : (Fin p × Fin q) ⊕ Low q ⊕ Low p → Low r
  | .inl s => ⟨(e.symm (.inl s.1), e.symm (.inr s.2)), by
      rw [Fin.lt_def]; simp only [he.1, he.2]; have := s.2.2; omega⟩
  | .inr (.inl s) => ⟨(e.symm (.inr s.1.1), e.symm (.inr s.1.2)), by
      rw [Fin.lt_def]; simp only [he.2]; exact s.2⟩
  | .inr (.inr s) => ⟨(e.symm (.inl s.1.1), e.symm (.inl s.1.2)), by
      rw [Fin.lt_def]; simp only [he.1]; have : (s.1.2 : ℕ) < s.1.1 := s.2; omega⟩

theorem lowPos_bijective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Bijective (lowPos he) := by
  constructor
  · rintro (⟨a, b⟩ | ⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) (⟨c, d⟩ | ⟨⟨c, d⟩, h'⟩ | ⟨⟨c, d⟩, h'⟩) hx <;>
      simp_all [lowPos]
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    obtain ⟨b, rfl⟩ := e.symm.surjective b
    have h : (e.symm b : ℕ) < e.symm a := hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at h
    · exact ⟨.inr (.inr ⟨(a, b), by rw [Fin.lt_def]; simp only; omega⟩), rfl⟩
    · exact ⟨.inl (a, b), rfl⟩
    · have := a.2; omega
    · exact ⟨.inr (.inl ⟨(a, b), h⟩), rfl⟩

theorem measurePreserving_mul_uni (y : Low q → ℂ) :
    MeasurePreserving (fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y)) volume volume := by
  have hc : Continuous fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y) :=
    continuous_pi fun s => (continuous_toMat.matrix_mul continuous_const).matrix_elem s.1 s.2
  refine ⟨hc.measurable, Measure.ext fun s hs => ?_⟩
  have h := GlobalTheory.FlagFibre.lintegral_affine p q 1 (uni y) 0 (by simp) (by simp [det_uni]) (s.indicator 1)
    (measurable_one.indicator hs)
  simp only [Matrix.one_mul, add_zero, det_uni, det_one, map_one, one_pow, mul_one, inv_one,
    ENNReal.ofReal_one, one_mul] at h
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hc.measurable, h]

theorem measurePreserving_shear_uni :
    MeasurePreserving (fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) =>
      (vecOf (toMat w.1 * uni w.2.1), w.2)) volume volume := by
  have hc : Continuous (Function.uncurry fun (y : (Low q → ℂ) × (Low p → ℂ)) (v : Fin p × Fin q → ℂ) =>
      vecOf (toMat v * uni y.1)) :=
    continuous_pi fun s => ((continuous_toMat.comp continuous_snd).matrix_mul
      (continuous_uni.comp (continuous_fst.comp continuous_fst))).matrix_elem s.1 s.2
  have h := (MeasurePreserving.id (volume : Measure ((Low q → ℂ) × (Low p → ℂ)))).skew_product
    (μc := volume) (μd := volume) hc.measurable
    (Filter.Eventually.of_forall fun y => (measurePreserving_mul_uni y.1).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem measurePreserving_glue (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q) (he : IsBlockSL2Embedding e) :
    MeasurePreserving (glue e) volume volume := by
  let σ := Equiv.ofBijective _ (lowPos_bijective he)
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Low r => ℂ) σ
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin p × Fin q) ⊕ Low q ⊕ Low p => ℂ)
  have h3 := (MeasurePreserving.id (volume : Measure (Fin p × Fin q → ℂ))).prod
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Low q ⊕ Low p => ℂ))
  have h := h1.comp (h2.comp (h3.comp measurePreserving_shear_uni))
  convert h using 1
  funext w s
  obtain ⟨x, rfl⟩ := σ.surjective s
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rcases x with ⟨a, b⟩ | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩
  · simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₂]
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₂₂, uni,
      of_apply, dif_pos hab']
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₁, uni,
      of_apply, dif_pos hab']
    rfl

end GlobalTheory.FlagFibre
end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_pos_of_posDef {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (k : Fin (m + 1)) :
    0 < lminor M k :=
  (h.submatrix (Fin.castLE_injective _)).det_pos

theorem lminor_neg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) :
    lminor (-M) k = (-1) ^ (k : ℕ) * lminor M k := by
  unfold lminor
  rw [submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg, Fintype.card_fin]

theorem psgn_of_le' {q i : ℕ} (h : i ≤ q) : psgn q i = 1 :=
  Finset.prod_eq_one fun a ha => by
    have := Finset.mem_range.1 ha
    simp [sgn, show a < q by omega]

theorem psgn_add' (q k : ℕ) : psgn q (q + k) = (-1) ^ k := by
  induction k with
  | zero => simpa using psgn_of_le' (le_refl q)
  | succ k ih =>
    have : psgn q (q + (k + 1)) = psgn q (q + k) * sgn q (q + k) := Finset.prod_range_succ _ _
    rw [this, ih]
    simp [sgn, pow_succ]

theorem signs_of_blocks {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (H : Matrix (Fin r) (Fin r) ℂ)
    (h2 : (reindex e e H).toBlocks₂₂.PosDef) (hs : (-schur (reindex e e H)).PosDef) (i : Fin (r + 1)) :
    0 < psgn q i * (lminor H i).re := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.FlagFibre.lminor_block r p q e he H h2.det_pos.ne'.isUnit
  have hr := he.card
  by_cases hi : (i : ℕ) ≤ q
  · rw [psgn_of_le' hi, one_mul, h₁ i ⟨i, by omega⟩ rfl]
    exact (Complex.pos_iff.1 (lminor_pos_of_posDef h2 _)).1
  · have hi2 := i.2
    obtain ⟨k, hk⟩ : ∃ k : Fin (p + 1), (i : ℕ) = q + k := ⟨⟨i - q, by omega⟩, by simp only; omega⟩
    have h3 := mul_pos h2.det_pos (lminor_pos_of_posDef hs k)
    rw [lminor_neg'] at h3
    rw [h₂ i k hk, hk, psgn_add', ← Complex.re_ofReal_mul]
    have h4 := (Complex.pos_iff.1 h3).1
    convert h4 using 2
    push_cast
    ring

theorem signs_over_dom : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ),
    reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q →
    ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  intro r p q e he A hA y hy i
  obtain ⟨w, rfl⟩ := glue_surjective he y
  rw [base_glue he] at hy
  have hy' : (1 - (toMat w.1)ᴴ * toMat w.1).PosDef := hy
  have hinj : ∀ {m : ℕ} (u : Low m → ℂ), Function.Injective (uni u).mulVec := fun u =>
    mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_uni]; exact isUnit_one))
  set Z := toMat w.1 with hZ
  set a := uni w.2.2 with ha
  set b := uni w.2.1 with hb
  have hH : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      fromBlocks (-(aᴴ * a)) (-(aᴴ * Z * b)) (-(aᴴ * Z * b))ᴴ (bᴴ * (1 - Zᴴ * Z) * b) := by
    have : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
        (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
      simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [this, reindex_uni_glue he, hA, Jpq, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply]
    congr 1
    · simp [ha]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [hb, hZ, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]
  have h2 : (bᴴ * (1 - Zᴴ * Z) * b).PosDef := hy'.conjTranspose_mul_mul_same (hinj _)
  refine signs_of_blocks he _ ?_ ?_ i
  · rw [hH, toBlocks_fromBlocks₂₂]; exact h2
  · rw [hH, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      neg_sub, sub_neg_eq_add, add_comm]
    refine PosDef.add_posSemidef ?_ (h2.inv.posSemidef.mul_mul_conjTranspose_same _)
    simpa using (PosDef.one (n := Fin p) (R := ℂ)).conjTranspose_mul_mul_same (hinj w.2.2)

end GlobalTheory.FlagFibre
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1) → (∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 → muF X (x0F X) (proj X hj κ ⁻¹' N) = 0) → ∀ F, IsFD (gammaU X hj κ) F → ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧ IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  first | exact @GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | exact GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | (intros; apply GlobalTheory.FlagFibre.FundPre.isFundSet_preimage <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∃ κ : ℕ → ℝ≥0, (∀ M, κ M ≠ 0) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ψ : AddChar (AF F) ℂ) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 1 ≤ M → IsHermND σ J → β ≠ 0 → IsCharAF F ψ → IsStdX s σ J β ν → ∀ νX, IsXbetaMeasure F E σ M J ψ β νX ↔ νX = κ M • ν := by
  first | exact @GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std | exact GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std | (intros; apply GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeLocN.heckeIntTw_base | exact GlobalTheory.HeckeLocN.heckeIntTw_base | (intros; apply GlobalTheory.HeckeLocN.heckeIntTw_base <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  first | exact @GlobalTheory.HeckeLiftN.heckeLift | exact GlobalTheory.HeckeLiftN.heckeLift | (intros; apply GlobalTheory.HeckeLiftN.heckeLift <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.parahoricTypeRC_mul_inv_mem : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F), k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  first | exact @GlobalTheory.ParGroup.parJ_mul_inv | exact GlobalTheory.ParGroup.parJ_mul_inv | (intros; apply GlobalTheory.ParGroup.parJ_mul_inv <;> assumption)
end
