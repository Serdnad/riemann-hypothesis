module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTwConjMemCentMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle312
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.Algebra.MvPolynomial.Variables
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDepthLowerBoundSaturatedEvenType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertUniq

section Fixed
variable {L : Type} [Field L]

abbrev fixF (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

abbrev starOfInv (σ : L →+* L) (h : ∀ x, σ (σ x) = x) : StarRing L where
  star := σ
  star_involutive := h
  star_mul x y := by rw [map_mul]; exact mul_comm _ _
  star_add := map_add σ

theorem finrank_fixF (σ : L →+* L) (h : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Module.finrank (fixF σ) L = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx₀)
  have hli : LinearIndependent (fixF σ) ![(1 : L), x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : σ (s : L) = s := s.2
    have ht : σ (t : L) = t := t.2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    change (s : L) + (t : L) * x₀ = 0 at hst
    have h2 : (s : L) + (t : L) * σ x₀ = 0 := by
      have := congrArg σ hst
      rwa [map_add, map_mul, hs, ht, map_zero] at this
    have ht0 : (t : L) = 0 := by
      have : (t : L) * (x₀ - σ x₀) = 0 := by linear_combination hst - h2
      exact (mul_eq_zero.1 this).resolve_right hd
    refine ⟨Subtype.ext ?_, Subtype.ext ht0⟩
    simpa [ht0] using hst
  have hsp : ⊤ ≤ Submodule.span (fixF σ) (Set.range ![(1 : L), x₀]) := by
    intro y _
    set b := (y - σ y) / (x₀ - σ x₀) with hbdef
    have hb : σ b = b := by
      rw [hbdef, map_div₀, map_sub, map_sub, h, h, ← neg_sub y (σ y), ← neg_sub x₀ (σ x₀), neg_div_neg_eq]
    set a := y - b * x₀ with hadef
    have hbm : b * (x₀ - σ x₀) = y - σ y := div_mul_cancel₀ _ hd
    have ha : σ a = a := by
      rw [hadef, map_sub, map_mul, hb]
      linear_combination hbm
    have hy : y = (⟨a, ha⟩ : fixF σ) • (1 : L) + (⟨b, hb⟩ : fixF σ) • x₀ := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change y = a * 1 + b * x₀
      rw [hadef]; ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
  simp

end Fixed

theorem eq_twCent_mul_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  intro E _ _ _ hU n w hs y g hy hbez hyg
  obtain ⟨hc, hinv, hval, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hϖ, -⟩, -⟩ := hns hs
  obtain ⟨-, -, hϖf, hϖv, ⟨x₀, -, hx₀⟩, -⟩ := hϖ
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  letI : StarRing (w.adicCompletion E) := starOfInv (cj w) hinv
  have hle1 : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  have hneq : ∀ x y : w.adicCompletion E, Valued.v x = Valued.v y → ‖x‖ = ‖y‖ := fun x y h =>
    le_antisymm (Valued.toNormedField.norm_le_iff.2 h.le) (Valued.toNormedField.norm_le_iff.2 h.ge)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖi : cj w ϖ⁻¹ = ϖ⁻¹ := by rw [map_inv₀, hϖf]
  have hϖn : 1 < ‖ϖ⁻¹‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, hϖv]
    exact one_lt_inv₀ (by simp) |>.2 (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  letI nF : NontriviallyNormedField (fixF (cj w)) :=
    { (inferInstance : NormedField (fixF (cj w))) with non_trivial := ⟨⟨ϖ⁻¹, hϖi⟩, hϖn⟩ }
  letI : NormedAlgebra (fixF (cj w)) (w.adicCompletion E) :=
    { (inferInstance : Algebra (fixF (cj w)) (w.adicCompletion E)) with
      norm_smul_le := fun r x => by rw [Algebra.smul_def, norm_mul]; exact le_of_eq rfl }
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI hUn : GlobalTheory.JR.Unram (fixF (cj w)) (w.adicCompletion E) :=
    { charZero := ⟨fun a b h => Nat.cast_injective (R := w.adicCompletion E) (by simpa using congrArg (algebraMap (fixF (cj w)) (w.adicCompletion E)) h)⟩
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := (isClosed_eq hc continuous_id).isClosedEmbedding_subtypeVal.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixF (cj w) hinv ⟨x₀, fun h => by rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      star_fix := fun x => x.2
      star_ne := ⟨x₀, fun h => by change cj w x₀ = x₀ at h; rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      norm_star := fun x => hneq _ _ (hval x)
      unram := by
        intro x
        by_cases hx : x = 0
        · exact ⟨0, by rw [hx]; rfl⟩
        · have hv0 : Valued.v x ≠ 0 := by simpa using hx
          refine ⟨⟨ϖ ^ (-WithZero.log (Valued.v x)), by
            change cj w (ϖ ^ (-WithZero.log (Valued.v x))) = ϖ ^ (-WithZero.log (Valued.v x)); rw [map_zpow₀, hϖf]⟩, ?_⟩
          change ‖x‖ = ‖ϖ ^ (-WithZero.log (Valued.v x))‖
          apply hneq
          rw [map_zpow₀, hϖv, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) from rfl,
            ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hv0] }
  have hcs : cj w = starRingEnd (w.adicCompletion E) := RingHom.ext fun _ => rfl
  have hth : ∀ h : GLw n w, (thL n w h).val = GlobalTheory.Tw.theta h.val := by
    intro h
    rw [thL, if_neg hs, hcs, thetaGL_val]
  have hnr : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
    rw [nrmL, if_neg hs, Units.val_mul, hcs, thetaGL_val]; rfl

  have hmem (O : Subring (w.adicCompletion E)) (h : GLw n w) :
      h ∈ GLint (Fin n) O ↔
        (∀ i j, h.val i j ∈ O) ∧ ∀ i j, (h⁻¹).val i j ∈ O := by
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.mul_inv
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.inv_mul
  have hint : ∀ h : GLw n w, h ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ i j, ‖h.val i j‖ ≤ 1) ∧ ‖h.val.det‖ = 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (hmem (Ov E w) h).1 hh
    have hdet : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, M i j ∈ Ov E w) → M.det ∈ Ov E w := by
      intro M hM
      let M₀ : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨M i j, hM i j⟩
      have hM₀ : M = (Ov E w).subtype.mapMatrix M₀ := by ext i j; rfl
      rw [hM₀, ← RingHom.map_det]
      exact (M₀.det).2
    have d1 : ‖h.val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h1)
    have d2 : ‖(h⁻¹).val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h2)
    have hprod : ‖h.val.det‖ * ‖(h⁻¹).val.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    refine ⟨fun i j => (hle1 _).2 (h1 i j), ?_⟩
    nlinarith [norm_nonneg h.val.det, norm_nonneg (h⁻¹).val.det]
  have hintR : ∀ h : GLw n w, (∀ i j, ‖h.val i j‖ ≤ 1) → ‖h.val.det‖ = 1 → h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    intro h h1 h2
    refine (hmem (Ov E w) h).2 ⟨fun i j => (hle1 _).1 (h1 i j), fun i j => ?_⟩
    rw [Matrix.coe_units_inv]
    exact (hle1 _).1 (GlobalTheory.TwIntegral.intg_inv h1 h2 i j)
  obtain ⟨hy1, hy2⟩ := hint y hy
  obtain ⟨hg1, hg2⟩ := hint _ hyg
  have htw : GlobalTheory.Tw.twConj g.val y.val = (g⁻¹ * y * thL n w g).val := by
    rw [Units.val_mul, Units.val_mul, hth, Matrix.coe_units_inv]; rfl
  obtain ⟨u, v, hu, hv, huv⟩ := hbez
  rw [hnr] at huv
  obtain ⟨t, ⟨htu, htc⟩, k, hk1, hk2, hx⟩ := GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul (fixF (cj w)) (w.adicCompletion E) n
    y.val g.val hy1 hy2 ⟨u, v, fun i => (hle1 _).2 (hu i), fun i => (hle1 _).2 (hv i), huv⟩ g.isUnit
    (by rw [htw]; exact hg1) (by rw [htw]; exact hg2)
  have hku : IsUnit k := GlobalTheory.TwIntegral.isUnit_of_norm_det hk2
  refine ⟨htu.unit, ?_, hku.unit, hintR _ (by simpa using hk1) (by simpa using hk2), Units.ext ?_⟩
  · show htu.unit * y = y * thL n w htu.unit
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hth, IsUnit.unit_spec]
    exact htc
  · rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    exact hx

end GlobalTheory.InertUniq
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem ordL_mul [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {d : K} (hd : d ≠ 0) (x : K) : (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul (mul_ne_zero hσd hd) hx, ordL_mul hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem li_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    LinearIndependent K (fun i => (b i : Fin n → K)) :=
  b.linearIndependent.map' W.subtype W.ker_subtype

theorem span_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    Submodule.span K (Set.range fun i => (b i : Fin n → K)) = W := by
  have : (Set.range fun i => (b i : Fin n → K)) = W.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem gram_change (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = W) (hu' : LinearIndependent K u')
    (hsu' : Submodule.span K (Set.range u') = W) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det =
      σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det :=
  GlobalTheory.T.gram_det_change_of_basis' σ W u u' hu hsu hu' hsu'

theorem csr_orth (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K) (hx : aeval γ Q *ᵥ x = 0) :
    ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 :=
  GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal σ γ hγ Q hQ x z hx

theorem gram_ne_zero (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A))
    (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0)
    (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 :=
  GlobalTheory.T.gram_det_ne_zero_of_ker_orth' σ A u hu hsu horth hdec

theorem conj_ker (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
      Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
      (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) =
        Matrix.of fun i j => ∑ k, σ (u i k) * u j k :=
  GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram σ γ g hg Q u hu hsu

end GlobalTheory.KapSignMul

namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem dec_of_dvd {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (Q : K[X]) (hsep : γ.charpoly.Separable)
    (hQ : Q ∣ γ.charpoly) : ∀ v, ∃ z y, aeval γ Q *ᵥ y = 0 ∧ v = aeval γ Q *ᵥ z + y := by
  obtain ⟨R, hR⟩ := hQ
  have hcop : IsCoprime Q R := Polynomial.Separable.isCoprime (by rw [← hR]; exact hsep)
  obtain ⟨a, c, hac⟩ := hcop
  intro v
  refine ⟨aeval γ a *ᵥ v, aeval γ (c * R) *ᵥ v, ?_, ?_⟩
  · rw [mulVec_mulVec, ← map_mul, show Q * (c * R) = c * (Q * R) by ring, ← hR, map_mul, aeval_self_charpoly,
      mul_zero, zero_mulVec]
  · rw [mulVec_mulVec, ← map_mul, ← add_mulVec, ← map_add (f := _), show Q * a + c * R = a * Q + c * R by ring, hac, map_one,
      one_mulVec]

theorem mem_im_of_coprime {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) {Q₁ Q₂ : K[X]} (hcop : IsCoprime Q₁ Q₂)
    {y : Fin n → K} (hy : aeval γ Q₂ *ᵥ y = 0) : ∃ z, y = aeval γ Q₁ *ᵥ z := by
  obtain ⟨a, c, hac⟩ := hcop
  refine ⟨aeval γ a *ᵥ y, ?_⟩
  have : y = aeval γ (a * Q₁ + c * Q₂) *ᵥ y := by rw [hac, map_one, one_mulVec]
  rw [mulVec_mulVec, ← map_mul, mul_comm Q₁ a]
  conv_lhs => rw [this]
  rw [map_add (f := _), add_mulVec, map_mul (aeval γ) c, ← mulVec_mulVec, hy, mulVec_zero, add_zero]

theorem ker_toLin' {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (P : K[X]) :
    LinearMap.ker (Matrix.toLin' (aeval M P)) = LinearMap.ker (aeval (Matrix.toLin' M) P) := by
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).toAlgHom M P).symm

theorem mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hs : ¬ IsSplitAt w) (γ : UL n w) :
    (((γ.1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (γ.1 : GLw n w) = 1 := by
  have := γ.2
  simp only [UL, if_neg hs] at this
  simpa [UJ, cT] using this

theorem mul_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : (M.map σ)ᵀ * M = 1) {Q₁ Q₂ : K[X]} (hsep : M.charpoly.Separable)
    (hdvd : Q₁ * Q₂ ∣ M.charpoly) (hcop : IsCoprime Q₁ Q₂) (hQ₁ : C (σ (Q₁.coeff 0)) * Q₁ = (Q₁.map σ).reverse)
    (hQ₂ : C (σ (Q₂.coeff 0)) * Q₂ = (Q₂.map σ).reverse) {ι₁ ι₂ ι : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι]
    (b₁ : Module.Basis ι₁ K (LinearMap.ker (Matrix.toLin' (aeval M Q₁))))
    (b₂ : Module.Basis ι₂ K (LinearMap.ker (Matrix.toLin' (aeval M Q₂))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k).det *
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k).det := by
  have hsup : LinearMap.ker (Matrix.toLin' (aeval M Q₁)) ⊔ LinearMap.ker (Matrix.toLin' (aeval M Q₂)) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    simp only [ker_toLin']
    exact sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop
  have hdis : Disjoint (LinearMap.ker (Matrix.toLin' (aeval M Q₁))) (LinearMap.ker (Matrix.toLin' (aeval M Q₂))) := by
    simp only [ker_toLin']
    exact disjoint_ker_aeval_of_isCoprime _ hcop
  have hli : LinearIndependent K (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K))) :=
    (li_coe b₁).sum_type (li_coe b₂) (by rw [span_coe, span_coe]; exact hdis)
  have hsp : Submodule.span K (Set.range (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)))) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_coe, span_coe, hsup]
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ (fun i => (b i : Fin n → K)) hli hsp (li_coe b) (span_coe b)
  have hblk : (Matrix.of fun i j => ∑ k, σ ((Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) i) k) *
      (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) j) k) =
      fromBlocks (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k)
        (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₂ j : Fin n → K) k) 0
        (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply, of_apply, Sum.elim_inr, Sum.elim_inl]
      have hy : aeval M Q₂ *ᵥ (b₂ i : Fin n → K) = 0 := by
        have := (b₂ i).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hx : aeval M Q₁ *ᵥ (b₁ j : Fin n → K) = 0 := by
        have := (b₁ j).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      obtain ⟨z, hz⟩ := mem_im_of_coprime M hcop hy
      rw [hz]
      exact csr_orth σ M hM Q₁ hQ₁ _ z hx
    · rfl
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  have h1 := gram_ne_zero σ (aeval M Q₁) _ (li_coe b₁) (span_coe b₁)
    (fun x z hx => csr_orth σ M hM Q₁ hQ₁ x z hx) (dec_of_dvd M Q₁ hsep (dvd_trans (dvd_mul_right _ _) hdvd))
  have h2 := gram_ne_zero σ (aeval M Q₂) _ (li_coe b₂) (span_coe b₂)
    (fun x z hx => csr_orth σ M hM Q₂ hQ₂ x z hx) (dec_of_dvd M Q₂ hsep (dvd_trans (dvd_mul_left _ _) hdvd))
  rw [hdet, sign_norm σ hσ hd, ordL_mul h1 h2, zpow_add₀ (by norm_num)]

theorem conj_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1) (Q : K[X])
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b' : Module.Basis ι' K (LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b' i : Fin n → K) k) * (b' j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det := by
  obtain ⟨hli, hsp, hgr⟩ := conj_ker σ γ g hg Q _ (li_coe b') (span_coe b')
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ _ (li_coe b) (span_coe b) hli hsp
  rw [hgr] at hdet
  rw [hdet, sign_norm σ hσ hd]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  intro E _ _ _ hU n _ w Q₁ Q₂ Q₃ γ g hsep hdvd hcop hc1 hc2
  by_cases hs : IsSplitAt w
  · simp [kapSign, hs]
  have hv := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hQ₁ : C (cj w (Q₁.coeff 0)) * Q₁ = (Q₁.map (cj w)).reverse := hc1.resolve_left hs
  have hQ₂ : C (cj w (Q₂.coeff 0)) * Q₂ = (Q₂.map (cj w)).reverse := hc2.resolve_left hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [kapSign, if_neg hs]
    exact mul_sign (cj w) hv _ (mem_UL hs γ) hsep hdvd hcop hQ₁ hQ₂ _ _ _
  · simp only [kapSign, if_neg hs]
    have hg' : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * γ * g := by simp
    rw [hg']
    exact conj_sign (cj w) hv γ.1 g.1 (mem_UL hs g) Q₃ _ _
  · simp only [kapSign, if_neg hs]
    rcases Int.even_or_odd (ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) i).1 k) * (Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) j).1 k).det) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow

end GlobalTheory.KapSignMul
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C), (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) → depth G u (P * Q) = depth G u P + depth G u Q := by
  first | exact @GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | exact GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | (intros; apply GlobalTheory.FGDepth.depth_mul_of_disjoint_columns <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.detDepth_lower_bound_saturated_even_type : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → 3 ≤ p → ∀ (d h : ℕ), 0 < h → Even h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j : ℕ), (∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ j) → ∀ (τ : ZMod h), Even τ.val → ∀ (i c : ℕ), 1 ≤ c → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ cr : ℕ, cr ≤ i ∧ (cr : ℝ) ≤ j * (3 / 2 + Real.logb p c / 2) ∧ ((((i : ℝ) - cr) * c * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p c + 1) : ℝ) : EReal) ≤ detDepth G u c := by
  first | exact @GlobalTheory.DepthLow.detDepth_lower | exact GlobalTheory.DepthLow.detDepth_lower | (intros; apply GlobalTheory.DepthLow.detDepth_lower <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors : ∀ {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n), StdPsi hF Q → ∀ (π : Formalism.L2.NG.FinTyp D.host.E n) Pr d B, SphOp V Pr d B → ∃ a : ℂ, ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → principalLevelFrame.Hecke₃ Q B x = a • x := by
  first | exact @GlobalTheory.SphScalar.spherical_scalar | exact GlobalTheory.SphScalar.spherical_scalar | (intros; apply GlobalTheory.SphScalar.spherical_scalar <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_identity_unconditional :
    ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
      (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ :=
  GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis GlobalTheory.T.jacquetRallisUnitMatch_all_ranks).1

end GlobalTheory.UnitLemma
end
