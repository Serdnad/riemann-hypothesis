module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import GroundTheory.GlobalFields.Artin.Bundle001
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

end GlobalTheory.AdTh
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem newton_charpolyRev {R r : Type} [CommRing R] [Fintype r] [DecidableEq r] (M : Matrix r r R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | k
  · simp
  · have h := congrArg (PowerSeries.coeff k) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, mul_comm (M.charpolyRev : PowerSeries R),
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    rw [mul_comm]
    simpa using h

theorem chernAt_newton (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) :
    chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j =
      -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  refine ⟨?_, fun j => ?_⟩
  · have h : (Matrix.charpolyRev (-curvPoly G v)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    rw [chernAt, chernPoly, h, map_one, pow_zero, one_smul]
  · have h := congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (newton_charpolyRev (-curvPoly G v) j)
    have hp (k : ℕ) : MvPolynomial.aeval (R := ℂ) (sym (n := n)) ((-curvPoly G v) ^ k).trace =
        (-1 : ℂ) ^ k • powAt G v k := by
      have e : curvEv G v ^ k = (curvPoly G v ^ k).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))) :=
        (map_pow (MvPolynomial.aeval (R := ℂ) (sym (n := n))).mapMatrix (curvPoly G v) k).symm
      rw [← neg_one_smul ℂ (curvPoly G v), smul_pow, Matrix.trace_smul, map_smul, powAt, e]

      simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

    rw [map_mul, map_natCast, map_neg, map_sum] at h
    simp only [map_mul, hp] at h
    simp only [chernAt, chernPoly]
    rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, h, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - (i + 1), by omega⟩
    rw [show i + 1 + m - 1 - i = m by omega, neg_pow kappa]
    ring

end GlobalTheory.ChernCalc
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.ChernCalc
open scoped Matrix ComplexOrder

namespace GlobalTheory.LeadingMinorPositivity

section Lin

variable {s : ℕ}

theorem submatrix_mul_lower {κ : Type} (T : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0)
    (M : Matrix (Fin s) κ ℂ) (j : ℕ) :
    (T * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id =
      T.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id := by
  ext a b
  change ∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp)
    (fun l => T a l * M l b)]
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra h
  refine hl ?_
  rw [hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]

theorem leadMinor_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (j : ℕ) :
    leadMinor (T * G * Tᴴ) j =
      ((∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < j, ‖T a a‖ ^ 2 : ℝ) : ℂ) * leadMinor G j := by
  let v : {a : Fin s // (a : ℕ) < j} → Fin s := Subtype.val
  have h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ := by
    have := submatrix_mul_lower T hT (G.submatrix v id)ᴴ j
    have h2 := (congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)
    refine Eq.trans ?_ (h2.trans ?_)
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rfl
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
      rfl
  have h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ) := by
    have := submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j
    rw [← h1, Matrix.mul_assoc]
    exact this
  have h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a) :=
    Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab
  unfold leadMinor
  change ((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4,
    Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]
  congr 1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

theorem leadMinor_re_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re :=
  (Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1

theorem grD_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (i : Fin s) : 0 < grD G i :=
  div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)

theorem grD_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (hd : ∀ a, T a a ≠ 0) (i : Fin s) :
    grD (T * G * Tᴴ) i = ‖T i i‖ ^ 2 * grD G i := by
  have e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))
  rw [grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e,
    Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]

theorem diag_mul_lower {K : Type} [Field K] (S T : Matrix (Fin s) (Fin s) K) (hS : ∀ a b, a < b → S a b = 0)
    (hT : ∀ a b, a < b → T a b = 0) (i : Fin s) : (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hT l i h, mul_zero]
  · rw [hS i l h, zero_mul]

end Lin

theorem green_frame_indep (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H)
    (B : Mat m X.Fn) (hB : B ∈ E.S (genericPoint X.X)) (y : GlobalTheory.CxPts X.str σ)
    (A : Mat m X.Fn) (hA : A ∈ E.S (under y)) (A' : Mat m X.Fn) (hA' : A' ∈ E.S (under y))
    (x : Root m) (f : X.Fn) (hu : UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f)) :
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
      -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  obtain ⟨τ, i⟩ := x
  have hT := (Fr.mem_iff hA).1 hA'
  have hS := (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hV := hT.map_of (ratVal · y) ψ hψ τ
  have hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0 := fun a b h => hV.2.2.2 a b a.2 h
  have hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0 := by
    have h := hV.2.1
    rw [Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
    rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
  have e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i := by
    rw [e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h)
      (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]
  have hu0 := ratVal_ne_zero hu
  have hur : RegAt (under y) ((B * A'⁻¹) τ i i / f) := by
    by_contra h
    exact hu0 (dif_neg h)
  have ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0 := hd i
  have hg := (grD_pos (hH.posDef y A hA τ) i).ne'
  have e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i := by
    rw [hH.trans y A hA A' hA' τ]
    exact grD_conj _ _ hlow hd i
  have n1 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
  have n2 := pow_ne_zero 2 (norm_ne_zero_iff.2 ht)
  dsimp only at n1 ⊢
  rw [e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2,
    Real.log_mul n2 hg]
  ring

end GlobalTheory.LeadingMinorPositivity
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ConjCartan


open scoped ComplexOrder in
theorem exists_conj_cartan_matrix : ∀ (n : ℕ) (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ), Mᴴ = M → IsCartan M θ₁ → IsCartan M θ₂ →
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  intro n M θ₁ θ₂ hM h1 h2
  have key : ∀ θ, IsCartan M θ → θ.map star * θ.map star = 1 ∧ (θ.map star)ᴴ * M * θ.map star = M ∧
      (M * θ.map star).PosDef := by
    rintro θ ⟨hθ, hu, hp⟩
    have hS : θ.map star = θᵀᴴ := rfl
    have hT : (θ.map star)ᴴ = θᵀ := by rw [hS, Matrix.conjTranspose_conjTranspose]
    have hSS : θ.map star * θ.map star = 1 := by
      rw [hS, ← Matrix.conjTranspose_mul, ← Matrix.transpose_mul, hθ, Matrix.transpose_one, Matrix.conjTranspose_one]
    have hMS : M * θ.map star = θᵀ * M := by
      calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [hu]
        _ = θᵀ * M := by rw [Matrix.mul_assoc _ (θ.map star), hSS, Matrix.mul_one]
    have hH : (M * θ.map star)ᴴ = M * θ.map star := by
      rw [Matrix.conjTranspose_mul, hT, hM, hMS]
    refine ⟨hSS, by rw [hT]; exact hu, ?_⟩
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x hx => ?_⟩
    have hx' : star x ≠ 0 := by simpa using hx
    have hre := hp (star x) hx'
    have e1 : star x ⬝ᵥ (M * θ.map star) *ᵥ x = (θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x) := by
      rw [star_star, hMS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : star (star x ⬝ᵥ (M * θ.map star) *ᵥ x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
      conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [Complex.lt_def]
    refine ⟨by rw [e1]; simpa using hre, ?_⟩
    have h3 := congrArg Complex.im e2
    have h4 : (star (star x ⬝ᵥ (M * θ.map star) *ᵥ x)).im = -(star x ⬝ᵥ (M * θ.map star) *ᵥ x).im :=
      Complex.conj_im _
    rw [Complex.zero_im]; linarith
  obtain ⟨hs1, hs2, hs3⟩ := key θ₁ h1
  obtain ⟨ht1, ht2, ht3⟩ := key θ₂ h2
  set S₁ := θ₁.map star
  set S₂ := θ₂.map star
  obtain ⟨p, q, B, B', hBB, hB'B, hBG, hBs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n M S₁ hs1 hs2 hs3
  set D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hDh : Dᴴ = D := by simp [D, Matrix.fromBlocks_conjTranspose]
  have hDD : D * D = 1 := by simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set T := B' * S₂ * B
  have hTT : T * T = 1 := by
    calc T * T = B' * S₂ * (B * B') * S₂ * B := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, Matrix.mul_assoc B', ht1, Matrix.mul_one, hB'B]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    have := congrArg (B'.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hB'B] using this
  have hDT : (D * T).PosDef := by
    have h := ht3.conjTranspose_mul_mul_same hinj
    have e : Bᴴ * (M * S₂) * B = D * T := by
      calc Bᴴ * (M * S₂) * B = Bᴴ * M * (B * B') * S₂ * B := by rw [hBB]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = D * T := by rw [← hBG]; simp only [T, Matrix.mul_assoc]
    rwa [e] at h
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.cartanInvolution_conj_of_posDef _ D T hDh hDD hTT hDT

  have haL : (D * aᴴ * D) * a = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc aᴴ, ha1, hDD]
  set U := B * a * B'
  set V := B * (D * aᴴ * D) * B'
  have hVU : V * U = 1 := by
    calc V * U = B * (D * aᴴ * D) * (B' * B) * a * B' := by simp only [V, U, Matrix.mul_assoc]
      _ = 1 := by rw [hB'B, Matrix.mul_one, Matrix.mul_assoc B, haL, Matrix.mul_one, hBB]
  have hUU : Uᴴ * M * U = M := by
    have hBh : B'ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc Uᴴ * M * U = B'ᴴ * (aᴴ * (Bᴴ * M * B) * a) * B' := by
          simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * (Bᴴ * M * B) * B' := by rw [hBG, ha1]
      _ = (B'ᴴ * Bᴴ) * M * (B * B') := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBh, hBB, Matrix.one_mul, Matrix.mul_one]
  have hB'S : B' * S₁ = D * B' := by
    calc B' * S₁ = B' * S₁ * (B * B') := by rw [hBB, Matrix.mul_one]
      _ = B' * (S₁ * B) * B' := by simp only [Matrix.mul_assoc]
      _ = B' * (B * D) * B' := congrArg (fun Z => B' * Z * B') hBs
      _ = (B' * B) * D * B' := by simp only [Matrix.mul_assoc]
      _ = D * B' := by rw [hB'B, Matrix.one_mul]
  have hUS : U * S₁ = S₂ * U := by
    calc U * S₁ = B * (a * D) * B' := by simp only [U, Matrix.mul_assoc, hB'S]
      _ = B * (T * a) * B' := by rw [ha2]
      _ = (B * B') * S₂ * (B * a * B') := by simp only [T, Matrix.mul_assoc]
      _ = S₂ * U := by rw [hBB, Matrix.one_mul]
  refine ⟨U.map star, V.map star, ?_, ?_, ?_⟩
  · have hUV : U * V = 1 := mul_eq_one_comm.1 hVU
    have : (U * V).map star = (1 : Matrix (Fin n) (Fin n) ℂ).map star := by rw [hUV]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).map star by simp, ← this]; ext i j; simp [Matrix.mul_apply, star_sum]
  · have e : (U.map star)ᵀ = Uᴴ := rfl
    rw [e, show (U.map star).map star = U by ext i j; simp, hUU]
  · have : (U * S₁).map star = (S₂ * U).map star := by rw [hUS]
    have e1 : (U * S₁).map star = U.map star * θ₁ := by ext i j; simp [S₁, Matrix.mul_apply, star_sum]
    have e2 : (S₂ * U).map star = θ₂ * U.map star := by ext i j; simp [S₂, Matrix.mul_apply, star_sum]
    rw [← e1, ← e2, this]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]


variable (F E) in
def archIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c z hz u hu => by
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem cA_mem_archIdeal (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ archIdeal F E) : cA σ z ∈ archIdeal F E :=
  fun u hu => by rw [← map_smul, hz u hu, map_zero]

end GlobalTheory.ConjCartan

namespace GlobalTheory.ConjCartan

theorem mapMatrix_transpose {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : f.mapMatrix Aᵀ = (f.mapMatrix A)ᵀ := rfl

theorem conj_cartan_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have cm := hB.cm
  have hM : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← cm.2.2.2 (B.emb w).1, hX.herm]
  have hU := fun w => exists_conj_cartan_matrix n _ (X.θ w) (Y.θ w) (hM w) (hX.cartan w) (hY.cartan w)
  choose u v huv hun hint using hU
  choose lift hlat hlev using GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents F E σ cm B.emb
  let π := Ideal.Quotient.mk (archIdeal F E)
  let Dm : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (u w - 1) i j
  let Dv : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (v w - 1) i j
  have hDm : π.mapMatrix Dm = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDv : π.mapMatrix Dv = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDc : π.mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (cA_mem_archIdeal σ (hlat _))
  have hDmw : ∀ w, (piInf (B.emb w)).mapMatrix Dm = u w - 1 := fun w => by
    ext i j; exact hlev _ w
  have hDvw : ∀ w, (piInf (B.emb w)).mapMatrix Dv = v w - 1 := fun w => by
    ext i j; exact hlev _ w
  have zero : ∀ Z : Matrix (Fin n) (Fin n) (AE F E), π.mapMatrix Z = 0 → (∀ w, (piInf (B.emb w)).mapMatrix Z = 0) → Z = 0 := by
    intro Z h1 h2; ext i j
    exact GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents F E σ cm B.emb _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j))
      (fun w => congrFun (congrFun (h2 w) i) j)
  have hGH : (1 + Dm) * (1 + Dv) = 1 := by
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_add (f := _), map_add (f := _), map_one, hDm, hDv]; simp
    · rw [map_sub, map_mul, map_add (f := _), map_add (f := _), map_one, hDmw, hDvw, add_sub_cancel, add_sub_cancel, huv w, sub_self]
  let g0 : GL (Fin n) (AE F E) := ⟨1 + Dm, 1 + Dv, hGH, mul_eq_one_comm.1 hGH⟩
  have hcw : ∀ w, (piInf (B.emb w)).mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = (u w).map star - 1 := fun w => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (cA σ).toRingHom (Dm i j) = cA σ (Dm i j) from rfl, GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj F E σ cm w (B.emb w)]
    simp only [Dm, Matrix.of_apply]
    rw [hlev]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, star_sub]
    split_ifs <;> simp
  have hJw : ∀ w, (piInf (B.emb w)).mapMatrix (incM F X.J) = X.J.map (B.emb w).1 := fun w => by
    ext i j; simp [incM, piInf_inclR]
  have hUG : g0 ∈ UG (cA σ) (incM F X.J) := by
    change (1 + Dm)ᵀ * incM F X.J * (cA σ).toRingHom.mapMatrix (1 + Dm) = incM F X.J
    rw [map_add (f := _), map_one]
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add (f := _), map_add (f := _), map_one, hDm, hDc]; simp
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add (f := _), map_add (f := _), map_one, hDmw, hcw, hJw,
        add_sub_cancel, add_sub_cancel, hun w, sub_self]
  refine ⟨⟨g0, hUG⟩, ?_, fun w => ?_⟩
  · intro a ha
    show a • ((1 + Dm) - 1) = 0
    ext i j
    simp only [add_sub_cancel_left, Matrix.smul_apply, Matrix.zero_apply]
    exact hlat _ a ha
  · have : (mat (⟨g0, hUG⟩ : UA σ X.J)).map (piInf (B.emb w)) = u w := by
      show (piInf (B.emb w)).mapMatrix (1 + Dm) = u w
      rw [map_add (f := _), map_one, hDmw]; abel
    rw [this]; exact hint w

end GlobalTheory.ConjCartan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  first | exact @GlobalTheory.FockConj.pureTensorO_negSp_monomial | exact GlobalTheory.FockConj.pureTensorO_negSp_monomial | (intros; apply GlobalTheory.FockConj.pureTensorO_negSp_monomial <;> assumption)
end
