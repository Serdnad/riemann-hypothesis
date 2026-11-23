module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle069
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_isQGroup | exact GlobalTheory.ClassFin.cf_of_isQGroup | (intros; apply GlobalTheory.ClassFin.cf_of_isQGroup <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnit_mem_globalNorm_of_mem_localNorms : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ sUnits F S, x ∈ locNorm F δ S → x ∈ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm | exact GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm | (intros; apply GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_unitary_adelic_decomposition_split_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)), IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧ (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_rep_suppSplit | exact GlobalTheory.UnRep.exists_rep_suppSplit | (intros; apply GlobalTheory.UnRep.exists_rep_suppSplit <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm | exact GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm | (intros; apply GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.OrientedChar

theorem map_inv_field {E : Type} [Field E] (τ : E →+* ℂ) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map τ)⁻¹ = G⁻¹.map τ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h),
    Matrix.map_one _ τ.map_zero τ.map_one]

theorem ringHom_map_quadrupleSum_products {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ}
    (P : Fin n → Fin n → A) (y : Fin m → Fin n → A) (Q : Fin m → Fin m → A) (x : Fin m → Fin n → A) :
    φ (∑ a, ∑ b, ∑ c, ∑ d, P a b * y c b * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, φ (P a b) * φ (y c b) * φ (Q c d) * φ (x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul]

theorem trace_four {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (Q : Matrix (Fin m) (Fin m) ℂ) (x : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ c, ∑ d, P a b * starRingEnd ℂ (y c b) * Q c d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

variable {D : D7}

theorem comp_hO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    θ τ (infPart D (hO S T x y)) = hAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  have hc : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = starRingEnd ℂ (((θ τ).comp (infPart D)) z) := comp_cA hθ τ
  have hg : (gramAt D S τ)⁻¹ = S.gram⁻¹.map (tauE D τ) := map_inv_field _ _ (Formalism.L2.Theta.gram_det_ne S)
  unfold hO hAt
  refine (ringHom_map_quadrupleSum_products ((θ τ).comp (infPart D)) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  rw [hg]
  refine Eq.trans ?_ (trace_four _ _ _ _).symm
  simp only [hi, hc]
  rfl

theorem valTau_symplO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    valTau θ τ (symplO S T x y) = omAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  unfold valTau symplO omAt
  rw [SymplVal.trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul,
    comp_incA hθ, comp_hO hθ, Complex.add_re, Complex.conj_re, two_mul]

theorem finPart_cA_eq_zero {z : AE D} (hz : finPart D z = 0) : finPart D (cA D z) = 0 := by
  have h : ∀ w : AE D, finPart D (cA D w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e => rfl
  rw [h, hz, map_zero]

theorem finPart_hO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    finPart D (hO S T x y) = 0 := by
  unfold hO
  refine (ringHom_map_quadrupleSum_products (finPart D) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases h with h | h
  · have e : finPart D (x d a) = 0 := congrFun (congrFun h d) a
    rw [e, mul_zero]
  · have e : finPart D (y c b) = 0 := congrFun (congrFun h c) b
    rw [finPart_cA_eq_zero e, mul_zero, zero_mul, zero_mul]

theorem sndA_symplO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplO S T x y) = 0 := by
  have h0 : finPart D (incA D D.host.xi0 * hO S T x y) = 0 := by
    rw [RingHom.map_mul, finPart_hO S T h, mul_zero]
  have h1 : finPart D (algebraMap (AF D.host.F) (AE D) (symplO S T x y)) = 0 := by
    unfold symplO
    rw [SymplVal.trace_AE, RingHom.map_add (f := _), h0, finPart_cA_eq_zero h0, add_zero]
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F)
    (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  apply hinj
  rw [map_zero]
  exact h1

theorem char_symplOH : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) →
      ψ (symplOH S T x y) =
        Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  intro D θ ψ hθ hψ S T x y h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (real_adele_ext_and_char D θ σ hσ _ (sndA_symplO S T h)).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => valTau_symplO hθ S T τ x y] at e
  exact e

end GlobalTheory.OrientedChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem _root_.GlobalTheory.T.realSymplecticForm_alternating_invariant_definite : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  first | exact @GlobalTheory.RealSymplForm.form_alt_inv_def | exact GlobalTheory.RealSymplForm.form_alt_inv_def | (intros; apply GlobalTheory.RealSymplForm.form_alt_inv_def <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac.RatDual

open Formalism.L2.Pj

variable {D : D7}

theorem mem_mul_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) :
    z ∈ D.host.AA * D.host.AAbar := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hz : D.host.xi0 * z ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mem_dual
      (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨n, hn⟩ := h c
    rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
    exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
  rw [← dual_eq hP D] at hz
  have h4 := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
  have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
      D.host.AA * D.host.AAbar := by
    rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem mem_AA_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (star a * z)) = n) :
    z ∈ D.host.AA := by
  have hAb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z *
      D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro b hb
    refine mem_mul_of_trace D _ fun c => ?_
    have hcb : (c : D.host.E) * b ∈ D.host.AAbar :=
      Submodule.smul_mem (D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) c hb
    have := h _ (conj_mem_AA D hcb)
    have hs : star (D.host.conj ((c : D.host.E) * b)) = (c : D.host.E) * b :=
      (bridge_star_holds D.R D.host _).trans (conj_conj D _)
    rwa [hs, mul_assoc, mul_comm b] at this
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
            z * D.host.AAbar) := by
          rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
      _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
  exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)

theorem form_smul (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    ∑ c, ∑ d, star (t c) * T.gram c d * (e • y) d = e * ∑ c, ∑ d, star (t c) * T.gram c d * y d := by
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s' s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    genMap S T a s' t *ᵥ s = (a * ∑ c, ∑ d, star (s' c) * S.gram c d * s d) • t := by
  funext i
  rw [Finset.sum_comm]
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hRat_add_left (S T : HSp D) (x x' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (x + x') y = hRat S T x y + hRat S T x' y := by
  simp only [hRat, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hRat_add_right (S T : HSp D) (x y y' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (y + y') = hRat S T x y + hRat S T x y' := by
  simp only [hRat, Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hRat_neg_left (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (-x) y = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hRat_neg_right (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (-y) = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, star_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem hRat_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {ρ ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hρ : ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)))
    (hℓ : ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    hRat S T ρ ℓ ∈ NAA D := by
  induction hρ using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a', ha', s', hs', t', ht', rfl⟩ := hw
    induction hℓ using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨p, hp⟩ := (hS.2 s).1 hs s' hs'
      obtain ⟨q, hq⟩ := (hT.2 t').1 ht' t ht
      rw [hRat_genMap, genMap_mulVec, form_smul, ← hp, ← hq]
      have hs : star a = D.host.conj a := bridge_star_holds D.R D.host a
      have e : star a * (a' * (p : D.host.E) * (q : D.host.E)) = (p * q) • (a' * D.host.conj a) := by
        rw [hs, Algebra.smul_def, map_mul]
        change _ = (p : D.host.E) * (q : D.host.E) * _
        ring
      rw [e]
      exact Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha' (conj_mem_AAbar D ha))
    | zero => simp [hRat]
    | add x y _ _ hx hy => rw [hRat_add_right]; exact add_mem hx hy
    | neg x _ hx => rw [hRat_neg_right]; exact neg_mem hx
  | zero => simp [hRat]
  | add x y _ _ hx hy => rw [hRat_add_left]; exact add_mem hx hy
  | neg x _ hx => rw [hRat_neg_left]; exact neg_mem hx

end GlobalTheory.LatVac.RatDual

namespace GlobalTheory.LatVac

open RatDual Formalism.L2.Pj

theorem latRat_selfDual : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ ΛS ∧ s' i ∈ ΛS) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) → ∀ ρ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔ ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)), ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T ρ ℓ) = n := by
  intro D S T ΛS ΛT hS hT ⟨n, s, s', hss, hdual⟩ ρ
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  refine ⟨fun hρ ℓ hℓ => trace_int_of_mem hP D (hRat_mem S T ΛS ΛT hS hT hρ hℓ), fun h => ?_⟩
  have h5 : ∀ v ∈ ΛS, ∀ t ∈ ΛT, ∑ c, ∑ d, star (t c) * T.gram c d * (ρ *ᵥ v) d ∈ D.host.AA := by
    intro v hv t ht
    refine mem_AA_of_trace D _ fun a ha => ?_
    rw [← hRat_genMap]
    exact h _ (AddSubgroup.subset_closure ⟨a, ha, v, hv, t, ht, rfl⟩)
  have h6 : ∀ v ∈ ΛS, ∀ b ∈ D.host.AA⁻¹, b • (ρ *ᵥ v) ∈ ΛT := by
    intro v hv b hb
    refine (hT.2 _).2 fun t ht => ?_
    rw [form_smul]
    have := FractionalIdeal.mul_mem_mul hb (h5 v hv t ht)
    rw [inv_mul_cancel₀ hAA, FractionalIdeal.mem_one_iff] at this
    exact this
  have h7 : ∀ v ∈ ΛS, ∀ v' ∈ ΛS, ∀ e ∈ D.host.AA * D.host.AA⁻¹, genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro v hv v' hv' e he
    refine FractionalIdeal.mul_induction_on (C := fun e => genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) he
      (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · refine AddSubgroup.subset_closure ⟨a, ha, v', hv', c • (ρ *ᵥ v), h6 v hv c hc, ?_⟩
      ext i j
      simp only [genMap, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · have e : genMap S T (u + w) v' (ρ *ᵥ v) = genMap S T u v' (ρ *ᵥ v) + genMap S T w v' (ρ *ᵥ v) := by
        ext i j
        simp only [genMap, Matrix.of_apply, Matrix.add_apply, add_mul]
      show genMap S T (u + w) v' (ρ *ᵥ v) ∈ _
      rw [e]
      exact add_mem hu hw
  have e : ρ = ∑ i, genMap S T 1 (s' i) (ρ *ᵥ s i) := by
    refine Matrix.ext fun a j => ?_
    have h8 : ρ a j = ∑ b, ρ a b * ∑ i, s i b * ∑ k, star (s' i k) * S.gram k j := by
      simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h8, Matrix.sum_apply]
    simp only [genMap, Matrix.of_apply, one_mul, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum (s := Finset.univ (α := Fin n))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← mul_assoc]
    exact (Finset.sum_mul _ _ _).symm
  rw [e]
  exact sum_mem fun i _ => h7 _ (hss i).1 _ (hss i).2 1
    (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)

end GlobalTheory.LatVac
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTranslate

open GlobalTheory.SplitScalar GlobalTheory.LatVac

theorem differentiable_of_char (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : Differentiable ℝ χ := by
  first
  | exact @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | (apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable ..)

variable {D : D7}

theorem differentiable_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (L : ℝ →+ WO S T) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPart D) = 0)
    (w : WO S T) : Differentiable ℝ fun t : ℝ => heisO ψ S T (L t) f w := by
  have h1 : Differentiable ℝ fun t : ℝ => ψ (symplOH S T w (L t)) := by
    refine differentiable_of_char _ (hψ.comp (continuous_const.mul (continuous_symplO S T continuous_const hL))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add (f := _), symplOH_add_right, AddChar.map_add_eq_mul]
  have h2 := hf.smooth 1 (L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)) (hL.comp (continuous_apply 0))
    (fun t => hfin _) w
  have h3 : Differentiable ℝ fun t : ℝ => f (w + L t) :=
    (h2.differentiable (by simp)).comp (differentiable_pi.2 fun _ : Fin 1 => differentiable_id)
  exact h1.mul h3

theorem dRho_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ) (ha : ∀ i ∈ s, (a i).map (infPart D) = 0) :
    dRho (heisO ψ S T) θ τ z (∑ i ∈ s, c i • heisO ψ S T (a i) f) =
      ∑ i ∈ s, c i • heisO ψ S T (a i) (dRho (heisO ψ S T) θ τ z f) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) =
      fun t : ℝ => ∑ i ∈ s, (c i * ψ (symplOH S T x (a i))) * heisO ψ S T (lineAt θ τ z t) f (x + a i) := by
    funext t
    rw [heisO_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_smul, heisO_comm, symplO_real_fin S T (hL.2.1 t) (ha i hi), AddChar.map_zero_eq_one, one_smul,
      mul_assoc]
    rfl
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) 0 = _
  rw [e, deriv_fun_sum fun i _ => ((differentiable_heisO hψ hf _ hL.1 hL.2.1 (x + a i)).const_mul _) 0,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_const_mul_field, mul_assoc]
  rfl

theorem isFockVacAt_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsCharAF D.host.F ψ → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ), IsFockVacAt (heisO ψ S T) θ τ J f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ θ S T hψ hθ f hf τ J hv ι s a c ha z
  have hc : Continuous ψ := hψ.1
  have h0 : dRho (heisO ψ S T) θ τ z f + Complex.I • dRho (heisO ψ S T) θ τ (J z) f = 0 := hv z
  rw [annih, dRho_sum hc hθ hf τ z s a c ha, dRho_sum hc hθ hf τ (J z) s a c ha, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_comm, ← smul_add, ← heisO_smul, ← heisL_apply, ← heisL_apply, ← map_add (f := _), h0, map_zero, smul_zero]

end GlobalTheory.FockTranslate

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_rational_points_completed_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  first | exact @GlobalTheory.CompletedLatticeFinite.finite_rational_points | exact GlobalTheory.CompletedLatticeFinite.finite_rational_points | (intros; apply GlobalTheory.CompletedLatticeFinite.finite_rational_points <;> assumption)
end
