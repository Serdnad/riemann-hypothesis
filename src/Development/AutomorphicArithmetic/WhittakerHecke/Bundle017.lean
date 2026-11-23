module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.embedGL2_diag_mul_unipotent_theta_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (x : A ℚ),
        em E (aE y) * gl (nU (D.mkE 0 x)) = nE D ![0, (y : A ℚ) * x] * em E (aE y) := by
  intro E _ _ D y x
  have hm : ∀ (h : GL (Fin 2) (A ℚ)) (i j : Fin 2), (em E h).val i j = AdeleBaseChange.adeleMap ℚ E (h.val i j) := fun _ _ _ => rfl
  have hn : ∀ (q : A E), (nU q).val = !![1, q; 0, 1] := fun _ => rfl
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  refine Units.ext ?_
  ext i j
  simp only [nE, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hm]
  fin_cases i <;> fin_cases j <;> simp [aE, hn, hk, map_mul, mul_assoc]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

theorem UpperTheory.exists_rat_heightOneSpectrum_normV_eq_prime_bad_iff_dvd :
    ∀ (p N : ℕ), p.Prime → ∃ v : H.P ℚ, normV v = p ∧ (Bad N v ↔ p ∣ N) := by
  intro p N hp
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpr.ne_zero
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr, hne⟩, ?_, ?_⟩
  · have h : ∀ w : HeightOneSpectrum (𝓞 ℚ), normV w = Ideal.absNorm w.asIdeal := fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [h]
    change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · change (N : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ p ∣ N
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
      Int.natCast_dvd_natCast]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_aE {K : Type} [Field K] [NumberField K] : Continuous (aE : (A K)ˣ → GL (Fin 2) (A K)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_val, continuous_const, continuous_const, continuous_const]
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_coe_inv, continuous_const, continuous_const, continuous_const]

theorem UpperTheory.measurable_whittaker_idele_diagTorus_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Measurable (fun p : IdeleGroup ℚ × G1 ℚ => Wo D φ (em E (aE p.1 * gl p.2))) := by
  intro E _ _ D ω φ h
  have hem : Continuous (em E) := Continuous.units_map _
    (continuous_matrix fun i j => AdeleBaseChange.continuous_adeleMap.comp (continuous_id.matrix_elem i j))
  have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => em E (aE p.1 * gl p.2) :=
    hem.comp ((cont_aE.comp continuous_fst).mul (M.continuous_gl.comp continuous_snd))
  have hn : Continuous (nE D) :=
    M.continuous_gl.comp (M.continuous_nU.comp
      ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have h2 : Continuous fun q : (IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ) => φ (nE D q.2 * em E (aE q.1.1 * gl q.1.2)) * ψ (q.2 1) :=
    (h.cont.comp ((hn.comp continuous_snd).mul (h1.comp continuous_fst))).mul
      (hψ.comp ((continuous_apply 1).comp continuous_snd))
  have : BorelSpace ((IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ)) := inferInstance
  exact (h2.measurable.stronglyMeasurable.integral_prod_right' (ν := (adeleMeasurePi ℚ).restrict (FS2 ℚ))).measurable
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem vm_mul_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* γ.1) ᵥ* (γ⁻¹).1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private theorem vm_inv_mul (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* (γ⁻¹).1) ᵥ* γ.1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private def rowE (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨ξ.1 ᵥ* γ.1, fun h => ξ.2 (by
    have := vm_mul_inv γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  invFun ξ := ⟨ξ.1 ᵥ* (γ⁻¹).1, fun h => ξ.2 (by
    have := vm_inv_mul γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  left_inv ξ := Subtype.ext (vm_mul_inv γ ξ.1)
  right_inv ξ := Subtype.ext (vm_inv_mul γ ξ.1)

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (fun i => rt (x i)) ᵥ* (ratS ℚ γ).1 = fun i => rt ((x ᵥ* γ.1) i) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ratS, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_add, map_mul]

theorem UpperTheory.thetaSeries_ratSL2_mul_invariant :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)),
        ThR Φ t (gl (ratS ℚ γ * g) * h) = ThR Φ t (gl g * h) := by
  intro Φ t γ g h
  unfold ThR
  rw [← (rowE γ).tsum_eq (fun ξ : Rw ℚ => Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (gl g * h).val) j)]
  refine tsum_congr fun ξ => ?_
  have key : (fun i => rt (ξ.1 i)) ᵥ* (gl (ratS ℚ γ * g) * h).val
      = (fun i => rt ((rowE γ ξ).1 i)) ᵥ* (gl g * h).val := by
    have e : (gl (ratS ℚ γ * g) * h).val = (ratS ℚ γ).1 * (gl g * h).val := by
      simp [gl, Matrix.SpecialLinearGroup.toGL, Matrix.mul_assoc]
    rw [e, ← Matrix.vecMul_vecMul, row_rat]
    rfl
  rw [key]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (x : IdeleGroup ℚ) (g : GL (Fin 2) (A E)),
        Wo D φ (em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) * g) = ((ω.1 x : ℂˣ) : ℂ) ^ 2 * Wo D φ g := by
  intro E _ _ D ω φ hφ x g
  have h1 : em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E x) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change AdeleBaseChange.adeleMap ℚ E (Matrix.scalar (Fin 2) (x : A ℚ) i j) =
      Matrix.scalar (Fin 2) (AdeleBaseChange.adeleMap ℚ E (x : A ℚ)) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h2 : ∀ (z : (A E)ˣ) (n : GL (Fin 2) (A E)),
      n * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = Matrix.GeneralLinearGroup.scalar (Fin 2) z * (n * g) := by
    intro z n
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext (Matrix.scalar_commute (z : A E) (fun _ => Commute.all _ _) n.val).symm.eq
  have h3 : ideleNorm ℚ E (ideleEmbedding ℚ E x) = x ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  unfold Wo
  rw [h1, ← integral_const_mul]
  congr 1
  funext u
  rw [h2, hφ.cen, h3, map_pow, Units.val_pow_eq_pow_val, mul_assoc]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.EmbeddingGeneralLinear

variable {E : Type} [Field E] [NumberField E]

private theorem ab_emb (D : Dat ℚ E) (a : (A ℚ)ˣ) :
    ab (ideleEmbedding ℚ E a : (A E)ˣ) = ab a ^ 2 := by
  have hfr : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  have h := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E)
    (ideleEmbedding ℚ E a)
  rw [ideleNorm_ideleEmbedding, hfr, map_pow] at h
  simp only [ab]
  rw [← h]
  rfl

private theorem em_gl (b : A ℚ) (a : (A ℚ)ˣ) :
    em E (gl (nU b * mD a)) =
      gl (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ)) := by
  have hinv : (((ideleEmbedding ℚ E a : (A E)ˣ)⁻¹ : (A E)ˣ) : A E) =
      AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rw [← map_inv]; rfl
  apply Units.ext
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((nU b * mD a : G1 ℚ).1 i j) =
    (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 i j
  have hL : (nU b * mD a : G1 ℚ).1 = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  have hR : (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 =
      !![1, AdeleBaseChange.adeleMap ℚ E b; 0, 1] *
        !![AdeleBaseChange.adeleMap ℚ E (a : A ℚ), 0; 0, AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := by
    rw [← hinv]; rfl
  rw [hL, hR]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem continuous_em : Continuous (em E) :=
  Continuous.units_map _ (continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap)

end UpperTheory.EmbeddingGeneralLinear

open UpperTheory.EmbeddingGeneralLinear in
theorem UpperTheory.norm_admissible_baseChange_siegelSet_le :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ r : ℕ,
        ∃ B : ℝ, ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a → ‖φ (em E (gl (nU b * mD a) * k))‖ ≤ B * (ab a)⁻¹ ^ r := by
  intro E _ _ D ω φ hφ C hC c hc r
  obtain ⟨B, hB⟩ := hφ.decay (em E '' C) (hC.image continuous_em) (c ^ 2) (by positivity) r
  refine ⟨|B| * c⁻¹ ^ r, fun b a k hk hca => ?_⟩
  have ha : 0 < ab a := hc.trans_le hca
  have h1 := hB (AdeleBaseChange.adeleMap ℚ E b) (ideleEmbedding ℚ E a : (A E)ˣ) (em E k) ⟨k, hk, rfl⟩
    (by rw [ab_emb D]; gcongr)
  rw [ab_emb D] at h1
  rw [map_mul, em_gl]
  refine h1.trans ?_
  have h2 : ((ab a ^ 2)⁻¹) ^ r = (ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r := by
    rw [← mul_pow, sq, mul_inv]
  have h3 : (ab a)⁻¹ ^ r ≤ c⁻¹ ^ r := by gcongr
  have h4 : 0 ≤ (ab a)⁻¹ ^ r := by positivity
  rw [h2]
  calc B * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) ≤ |B| * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) := by
        gcongr; exact le_abs_self B
    _ ≤ |B| * (c⁻¹ ^ r * (ab a)⁻¹ ^ r) := by gcongr
    _ = |B| * c⁻¹ ^ r * (ab a)⁻¹ ^ r := by ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private theorem sc_comm {R : Type} [CommRing R] (y : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) y * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
  Units.ext (Matrix.scalar_commute (y : R) (fun _ => Commute.all _ _) g.val).eq

private theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hn : ∀ {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)),
      normV u = Ideal.absNorm u.asIdeal := by
    intro F _ _ u
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [hn] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log hy,
    WithZero.toAdd_unzero_eq_log hx, h2]

private theorem norm_loc {E : Type} [Field E] [NumberField E] (w : H.P E) (x : (H.Kv w)ˣ) (f : ℕ)
    (hf : normV w = normV (w.under (𝓞 ℚ)) ^ f) :
    ∃ y : (H.Kv (w.under (𝓞 ℚ)))ˣ, ideleNorm ℚ E (localIdele E w x) = localIdele ℚ (w.under (𝓞 ℚ)) y ∧
      Valued.v (y : H.Kv (w.under (𝓞 ℚ))) = Valued.v (x : H.Kv w) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := ℚ) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, h, val_of_norm _ w _ x hm' _ hf⟩

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) (hb : ((n : 𝓞 K)) ∉ v.asIdeal) :
    Valued.v ((n : ℕ) : H.Kv v) = 1 := by
  have h1 : v.valuation K (((n : 𝓞 K)) : K) = 1 := by
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h => hb ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v _).1 h
  have h2 : Valued.v (algebraMap K (H.Kv v) (((n : 𝓞 K)) : K)) = v.valuation K (((n : 𝓞 K)) : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1] at h2
  rw [← h2]
  simp

private theorem unr_of_ok {ω : HChar ℚ} {L : ℕ} (hc : ChOk ω⁻¹ L) {v : H.P ℚ} (hb : ¬ Bad L v) : ω.UnrAt v := by
  intro x hx
  have hL : Valued.v ((L : ℕ) : H.Kv v) = 1 := val_nat v L hb
  have hs : ∀ w : H.P ℚ, w ≠ v → (localIdele ℚ v x).val.2 w = 1 := fun w h => Pi.mulSingle_eq_of_ne h _
  have he : (localIdele ℚ v x).val.2 v = x := Pi.mulSingle_eq_same v _
  have hU : (localIdele ℚ v x : (A ℚ)ˣ) ∈ UU := by
    refine ⟨rfl, fun w => ?_⟩
    by_cases h : w = v
    · subst h
      exact (congrArg Valued.v he).trans hx
    · exact (congrArg Valued.v (hs w h)).trans (map_one _)
  have hD : ∀ w, Dv L w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) := fun w => by
    unfold Dv
    by_cases h : w = v
    · subst h
      have e : H.cp w (((localIdele ℚ w x : (A ℚ)ˣ) : A ℚ) - 1) = (x : H.Kv w) - 1 := by
        rw [map_sub, map_one]
        exact congrArg (· - 1) he
      rw [e, hL]
      have h1 := Valuation.map_sub (Valued.v (R := H.Kv w)) (x : H.Kv w) 1
      have hx' : Valued.v (x : H.Kv w) = 1 := hx
      rwa [hx', map_one, max_self] at h1
    · have e : H.cp w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) = 0 := by
        rw [map_sub, map_one, sub_eq_zero]
        exact hs w h
      rw [e, map_zero]
      exact zero_le'
  have h : (ω.1 (localIdele ℚ v x))⁻¹ = 1 := hc _ hU hD
  exact inv_eq_one.1 h

theorem UpperTheory.satake_param_mul_eq_central_char_pow_inertiaDeg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ) (L : ℕ), CenN P ω → ChOk ω⁻¹ L →
        ∀ (w : H.P E) (α β : ℂˣ) (f : ℕ), ¬ Bad L (w.under (𝓞 ℚ)) → normV w = normV (w.under (𝓞 ℚ)) ^ f →
          (CG.mk P).HasSat w {α, β} → α * β = ω.val (w.under (𝓞 ℚ)) ^ f := by
  intro E _ _ _ P ω L hC hO w α β f hb hf hS
  have hU := unr_of_ok hO hb
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hϖ : H.IsU (Units.mk0 p hp0) := hp
  have hB := (CG.hasSat_mk P w _).1 hS
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  obtain ⟨g, hg⟩ : ∃ g, x.1.1 g ≠ 0 := by
    by_contra! hn
    exact hx.1 (Subtype.ext (Subtype.ext (funext hn)))
  have hfix : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := 2), x.1.1 (g * finGL E 2 (locGL E 2 w k)) = x.1.1 g := fun g k hk =>
    congrFun (congrArg (fun y : P.V => y.1.1) (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)) g
  have hEig : UpperTheory.V.Af.Smo.EigAt w {α, β} x.1.1 := by
    intro g
    refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
    · rw [map_mul, map_mul, ← mul_assoc, hfix _ k hk]
    · have he := (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk =>
        Subtype.ext (Subtype.ext (funext fun z => hfix z k hk))) hx.1).2.2.2 ϖ hϖ j hj
      let ev : P.V →+ ℂ :=
        { toFun := fun ψ => ψ.1.1 (g * finGL E 2 (locGL E 2 w y))
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2)
        (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (P.locRep w) x)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
      rw [map_mul, map_mul, ← mul_assoc]
      rfl
  obtain ⟨R, -, -, hR⟩ := H.heckeExpl E w _ hϖ
  have hc := (hR α β _ (hEig g) 1).2
  have hc' : x.1.1 (g * Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl w (Units.mk0 p hp0))) = (α : ℂ) * β * x.1.1 g := by
    simp only [one_mul, map_one, mul_one] at hc
    rw [← (H.lcLaws E w).2.2.2.2.1]
    exact hc
  have h2 := hC x.1 x.2 (H.idl w (Units.mk0 p hp0)) g
  rw [sc_comm, hc'] at h2
  have h3 := mul_right_cancel₀ hg h2
  obtain ⟨y, hy, hv⟩ := norm_loc w (Units.mk0 p hp0) f hf
  have hu : IsUnitAt (w.under (𝓞 ℚ)) (y * (atFin (w.under (𝓞 ℚ)) (unif (w.under (𝓞 ℚ))) ^ f)⁻¹) := by
    have hun := unif_spec (w.under (𝓞 ℚ))
    have hp' : Valued.v ((Units.mk0 p hp0 : (H.Kv w)ˣ) : H.Kv w) = WithZero.exp (-1 : ℤ) := hp
    unfold IsUnitAt
    unfold IsUnifAt at hun
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, hp', hun]
    exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
  have h4 := hU _ hu
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h4
  have h5 : ω.1 (ideleNorm ℚ E (H.idl w (Units.mk0 p hp0))) = ω.val (w.under (𝓞 ℚ)) ^ f :=
    (congrArg ω.1 hy).trans h4
  rw [h5] at h3
  exact Units.ext (by simpa using h3)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasLevel_of_unitIdele_congruent_one :
    ∀ (L : ℕ), 0 < L → ∀ t : (A ℚ)ˣ, t ∈ UU → (∀ v, Dv L v ((t : A ℚ) - 1)) → Lev L (aE t) := by
  intro L _ t ht hD
  have h1 : (t : A ℚ).1 = 1 := ht.1
  have hu : ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1 := ht.2
  have hi : ∀ v : H.P ℚ, Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) = 1 := by
    intro v
    have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, hu v, one_mul, map_one] at this
  have hz : ∀ v : H.P ℚ, Dv L v 0 := by
    intro v
    simp [Dv]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [aE, h1] <;> rfl
  · rw [H.KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
    have e1 : (1 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := one_mem _
    have e0 : (0 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := zero_mem _
    have et : H.cp v (t : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hu v).le
    have ei : H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hi v).le
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa [aE, Matrix.GeneralLinearGroup.map] using et
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
    · fin_cases i <;> fin_cases j
      · exact ei
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
  · fin_cases i <;> fin_cases j
    · simpa [aE] using hD v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
end
