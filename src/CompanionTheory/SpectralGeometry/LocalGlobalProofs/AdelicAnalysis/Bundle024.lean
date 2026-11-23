module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.AutomorphicTheory.ThetaDilations.WeilImplicationNonarchQuadratic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle010
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.FouSB

theorem fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_fou_sb

end GlobalTheory.CompanionTheory.SW.FouSB
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.reduction_to_siegel_domain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  first | exact @GlobalTheory.CompanionTheory.SW.Red.reduction | exact GlobalTheory.CompanionTheory.SW.Red.reduction | (intros; apply GlobalTheory.CompanionTheory.SW.Red.reduction <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GaussFou

def g1 {ι : Type} [Fintype ι] (S P : Matrix ι ι ℝ) (τ : ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) -
    (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_eq_prod (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ) :
    gauss B ρ P τ x = ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w) := by
  simp only [gauss, g1, Complex.exp_sum]

theorem neg_inv_im_pos {τ : ℂ} (h : 0 < τ.im) : 0 < (-τ⁻¹).im := by
  have hne : τ ≠ 0 := fun h0 => by simp [h0] at h
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos h (Complex.normSq_pos.2 hne)

theorem abs_norm_eq_prod (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : F) :
    |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w, |ρ w a| := by
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hF.isReal w⟩
  rw [hw, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]

theorem sqrt_prod_abs {α : Type} (s : Finset α) (f : α → ℝ) :
    Real.sqrt (∏ w ∈ s, |f w|) = ∏ w ∈ s, Real.sqrt |f w| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (abs_nonneg _), ih]

theorem sqrt_norm_det (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (hF : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| = ∏ w, Real.sqrt |(B.map (ρ w)).det| := by
  rw [abs_norm_eq_prod hF ρ hρ, sqrt_prod_abs]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [RingHom.map_det]
  rfl

theorem gauss_fourier : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Integrable (gauss B ρ P τ) ∧ ‖cG B ρ P τ‖ = (∏ w, ‖τ w‖ ^ M)⁻¹ ∧ cG B ρ P τ * cG B ρ P (fun w => -(τ w)⁻¹) = 1 ∧ ∀ y : InfinitePlace F → ι → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P τ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) y := by
  intro F _ _ ι _ _ M B ρ P hQ τ hτ
  obtain ⟨hF, hcard, hsym, hdet, hρ, hP, hrel⟩ := hQ
  have hdetw : ∀ w, (B.map (ρ w)).det ≠ 0 := fun w => by
    have : (B.map (ρ w)).det = ρ w B.det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact (map_ne_zero (ρ w)).2 hdet
  have one := fun w => GlobalTheory.T.real_gaussian_fourier_transform ι (B.map (ρ w)) (P w) (hsym.map _) (hdetw w) (hP w) (hrel w)
  choose c hc using one
  have hfou : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → ∀ y : InfinitePlace F → ι → ℝ,
      ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
      ∏ w, (c w (σ w) * g1 (B.map (ρ w)) (P w) (-(σ w)⁻¹) (y w)) := by
    intro σ hσ y
    have hint : ∀ x : InfinitePlace F → ι → ℝ, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
        ∏ w, (g1 (B.map (ρ w)) (P w) (σ w) (x w) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
      intro x
      rw [gauss_eq_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]
    simp_rw [hint]
    rw [integral_fintype_prod_volume_eq_prod
      (f := fun w (x : ι → ℝ) => g1 (B.map (ρ w)) (P w) (σ w) x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))),
      sqrt_norm_det B ρ hF hρ, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact (hc w (σ w) (hσ w)).2.2.2 (y w)
  have hcG : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → cG B ρ P σ = ∏ w, c w (σ w) := by
    intro σ hσ
    have h0 := hfou σ hσ 0
    simpa [cG, g1] using h0
  have hσ' : ∀ w, 0 < (-(τ w)⁻¹).im := fun w => neg_inv_im_pos (hτ w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : gauss B ρ P τ = fun x => ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w) :=
      funext fun x => gauss_eq_prod B ρ P τ x
    rw [this]
    exact Integrable.fintype_prod (f := fun w => g1 (B.map (ρ w)) (P w) (τ w))
      fun w => (hc w (τ w) (hτ w)).2.2.1
  · rw [hcG τ hτ, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(hc w (τ w) (hτ w)).1, hcard, pow_mul, Real.sq_sqrt (norm_nonneg _)]
  · rw [hcG τ hτ, hcG _ hσ', ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w _ => (hc w (τ w) (hτ w)).2.1
  · intro y
    rw [hfou τ hτ y, hcG τ hτ, gauss_eq_prod, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.SW.GaussFou
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HypSplit

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_dot (u v : Fin M → E) :
    hE σ J u v = Matrix.vecMul (fun i => σ (u i)) J ⬝ᵥ v := by
  simp only [hE, hform, Matrix.vecMul, dotProduct, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_comm

def hLin (u : Fin M → E) : (Fin M → E) →ₗ[E] E where
  toFun := hE σ J u
  map_add' v w := by simp only [hE_eq_dot, dotProduct_add]
  map_smul' a v := by simp only [hE_eq_dot, dotProduct_smul, RingHom.id_apply]

@[simp] theorem hLin_apply (u v : Fin M → E) : hLin σ J u v = hE σ J u v := rfl

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin M → E) :
    σ (hE σ J u v) = hE σ J v u := by

  simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem exists_partner (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by
  have hr : Matrix.vecMul (fun i => σ (x i)) J ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h0
    apply hx
    funext i
    have h3 := congrFun h1 i
    simpa using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have hj' : Matrix.vecMul (fun i => σ (x i)) J j ≠ 0 := hj
  obtain ⟨y₀, h1⟩ : ∃ y₀, hE σ J x y₀ = 1 := by
    refine ⟨Pi.single j (Matrix.vecMul (fun i => σ (x i)) J j)⁻¹, ?_⟩
    rw [hE_eq_dot, dotProduct_single, mul_inv_cancel₀ hj']
  have conj := hE_conj (J := J) hσ hJ.1
  have h1' : hE σ J y₀ x = 1 := by rw [← conj, h1, map_one]
  have hc : σ (hE σ J y₀ y₀) = hE σ J y₀ y₀ := conj _ _
  set c := hE σ J y₀ y₀ with hcdef
  have hc2 : σ (c / 2) = c / 2 := by rw [map_div₀, hc, map_ofNat]
  have hxy : hE σ J x (y₀ - (c / 2) • x) = 1 := by
    have := (hLin σ J x).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, hxx, h1] at this
    simpa using this
  have hy₀y : hE σ J y₀ (y₀ - (c / 2) • x) = c / 2 := by
    have := (hLin σ J y₀).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, h1', ← hcdef] at this
    rw [this]; field_simp; ring
  refine ⟨y₀ - (c / 2) • x, hxy, ?_⟩
  have := (hLin σ J (y₀ - (c / 2) • x)).map_sub y₀ ((c / 2) • x)
  simp only [map_smul, hLin_apply, smul_eq_mul] at this
  rw [this, ← conj y₀, hy₀y, hc2, ← conj x, hxy, map_one]
  ring

theorem finrank_perp (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    {x y : Fin M → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0) (hxy : hE σ J x y = 1) :
    Module.finrank E (LinearMap.ker ((hLin σ J x).prod (hLin σ J y))) + 2 = M := by
  have hyx : hE σ J y x = 1 := by rw [← hE_conj hσ hJ, hxy, map_one]
  have hs : Function.Surjective ((hLin σ J x).prod (hLin σ J y)) := by
    rintro ⟨a, b⟩
    refine ⟨a • y + b • x, Prod.ext ?_ ?_⟩
    · change hLin σ J x (a • y + b • x) = a
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hxy, hxx, mul_one, mul_zero, add_zero]
    · change hLin σ J y (a • y + b • x) = b
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hyy, hyx, mul_one, mul_zero, zero_add]
  have h := LinearMap.finrank_range_add_finrank_ker ((hLin σ J x).prod (hLin σ J y))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

theorem gram_eq {n : ℕ} (c : Fin n → Fin M → E) :
    cT (σ : E →+* E) (Matrix.of c)ᵀ * J * (Matrix.of c)ᵀ = gramE σ J c := by
  ext a b
  simp only [Matrix.mul_apply, cT, gramE, hE, hform, Finset.sum_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_comm

theorem det_ne_zero_of_hypJ {M₁ : ℕ} (A : Matrix (Fin M₁) (Fin M₁) E) (h : (hypJ A).det ≠ 0) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
  · intro h1
    apply hv
    funext i
    simpa using congrFun h1 i.succ.succ
  · funext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · have := congrFun hAv a
      simpa [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ] using this

theorem selfDualLattice_projection_mem_of_unit_length (hσ : ∀ a, σ (σ a) = a) (h2 : (2 : E) ≠ 0) {M₁ : ℕ}
    {J : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E} (hJ : IsHermND σ J)
    {x y : Fin (M₁ + 2) → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0)
    (hxy : hE σ J x y = 1) :
    ∃ (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧
      hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * J *
        (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  have conj := hE_conj (J := J) hσ hJ.1
  have hyx : hE σ J y x = 1 := by rw [← conj, hxy, map_one]
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  set W := LinearMap.ker ((hLin σ J x).prod (hLin σ J y)) with hW
  have hfr' : Module.finrank E W = M₁ := by omega
  let b : Module.Basis (Fin M₁) E W := Module.finBasisOfFinrankEq E W hfr'
  have hbx : ∀ i, hE σ J x (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.fst h3
  have hby : ∀ i, hE σ J y (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.snd h3
  have hbx' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) x = 0 := fun i => by
    rw [← conj, hbx, map_zero]
  have hby' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) y = 0 := fun i => by
    rw [← conj, hby, map_zero]
  let c : Fin (M₁ + 2) → Fin (M₁ + 2) → E :=
    Fin.cons x (Fin.cons y fun i => (b i : Fin (M₁ + 2) → E))
  have hli : LinearIndependent E c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at ha
    simp only [c, Fin.cons_zero, Fin.cons_succ] at ha
    have e1 := congrArg (hLin σ J x) ha
    have e2 := congrArg (hLin σ J y) ha

    simp only [map_add (f := _), map_smul, map_sum, hLin_apply, smul_eq_mul, hxx, hyy, hxy, hyx, hbx, hby,
    map_zero, mul_zero, zero_add, add_zero, mul_one, Finset.sum_const_zero] at e1 e2
    rw [e1, e2] at ha
    simp only [zero_smul, zero_add] at ha
    have e3 : ∑ i, a i.succ.succ • b i = 0 := by
      apply Subtype.ext
      simpa using ha
    have e4 := Fintype.linearIndependent_iff.mp b.linearIndependent _ e3
    intro i
    refine Fin.cases e2 (fun i => Fin.cases e1 e4 i) i
  have hunit : IsUnit (Matrix.of c)ᵀ := by
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := (Matrix.of c)ᵀ)).mp hli
  let J₁ : Matrix (Fin M₁) (Fin M₁) E := gramE σ J fun i => (b i : Fin (M₁ + 2) → E)
  have hgram : hypJ J₁ = gramE σ J c := by
    ext a b'
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b' => Fin.cases ?_ (fun b' => ?_) b') b' <;>
      simp [hypJ, gramE, c, J₁, hxx, hyy, hxy, hyx, hbx, hby, hbx', hby']
  have hdet : (hypJ J₁).det ≠ 0 := by
    rw [hgram, ← gram_eq, Matrix.det_mul, Matrix.det_mul]
    have hu : (Matrix.of c)ᵀ.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    have hcT : (cT (σ : E →+* E) (Matrix.of c)ᵀ).det ≠ 0 := by
      rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using hu
    exact mul_ne_zero (mul_ne_zero hcT hJ.2) hu
  refine ⟨hunit.unit, J₁, ⟨fun i j => conj _ _, det_ne_zero_of_hypJ J₁ hdet⟩, ?_⟩
  rw [hgram, ← gram_eq]
  rfl

end Alg

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem splitHyp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  intro F E _ _ _ _ _ σ hcm M J hJ x hx hxx
  have hσ := sigma_invol σ hcm
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨y, hxy, hyy⟩ := exists_partner hσ hJ h2 x hx hxx
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨_, hfr.symm⟩
  obtain ⟨g, J₁, h1, h3⟩ := selfDualLattice_projection_mem_of_unit_length hσ h2 hJ hxx hyy hxy
  exact ⟨M₁, rfl, g, J₁, h1, h3⟩

end GlobalTheory.CompanionTheory.SW.HypSplit
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem continuous_tmul_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (fun a : AF F => a ⊗ₜ[F] (1 : E)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  let φ : AF F →ₗ[AF F] AF F ⊗[F] E :=
    (TensorProduct.AlgebraTensorModule.mk F (AF F) (AF F) E).flip (1 : E)
  exact IsModuleTopology.continuous_of_linearMap φ

theorem exists_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨θ, hθ⟩ := (GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles F hCM.1).1
  let g : ℝ → AF F ⊗[F] E := fun x => pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)
  have g0 : g 0 = 1 := by
    simp only [g, Real.exp_zero, map_one]
    rfl
  have gadd : ∀ x y, g (x + y) = g x * g y := by
    intro x y
    have h : pairA F (θ (Real.exp x) * θ (Real.exp y)) 1 =
        pairA F (θ (Real.exp x)) 1 * pairA F (θ (Real.exp y)) 1 :=
      Prod.ext rfl (mul_one (1 : Af F)).symm
    simp only [g, Real.exp_add, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h]
  have gc : Continuous g := by
    refine (continuous_tmul_one F E).comp ?_
    show Continuous fun x : ℝ => ((θ (Real.exp x), 1) : AF F)
    exact (hθ.comp Real.continuous_exp).prodMk continuous_const
  let f : Multiplicative ℝ →* AF F ⊗[F] E :=
    { toFun := fun x => g x.toAdd
      map_one' := g0
      map_mul' := fun x y => gadd x.toAdd y.toAdd }
  refine ⟨f.toHomUnits, ?_, θ, hθ, fun x => rfl⟩
  rw [Units.continuous_iff]
  constructor
  · exact gc.comp continuous_toAdd
  · have : (fun x : Multiplicative ℝ => (((f.toHomUnits x)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
        fun x => g (-x.toAdd) := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact gc.comp (continuous_neg.comp continuous_toAdd)

end GlobalTheory.CompanionTheory.SW.Flow
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.unit_product_closure_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0) (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e → a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧ IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧ IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧ (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | exact GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | (intros; apply GlobalTheory.CompanionTheory.SW.UnitProdAlg.main <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.scalar_hermitian_trace_and_unit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det | exact GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_unitary_group_locally_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopH.topH_props | exact GlobalTheory.CompanionTheory.SW.TopH.topH_props | (intros; apply GlobalTheory.CompanionTheory.SW.TopH.topH_props <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measures_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | exact GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | (intros; apply GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lattice_stable_almost_everywhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | exact GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | (intros; apply GlobalTheory.CompanionTheory.SW.LatRat.latV_rational <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.rank_zero_gram_fiber_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | exact GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | (intros; apply GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_right_action_identities : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra | exact GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra | (intros; apply GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra <;> assumption)
end
