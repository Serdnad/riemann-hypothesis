module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)

namespace GlobalTheory.HeckeOne

theorem exists_eq_circleExp_mul (f : ℝ → Circle) (hf : Continuous f) (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ x, f x = Circle.exp (a * x) := by
  have h0 : f 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ⟨f, hf⟩ 0 0
    (by simp [h0])
  have hF' : ∀ x, Circle.exp (F x) = f x := fun x => congrFun hF x
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y : ℝ => F (x + y) - F x - F y := by fun_prop
    have := Circle.isCoveringMap_exp.const_of_comp hc (fun y y' => by
      simp only [Circle.exp_sub, hF', hadd]
      simp) y 0
    simp only [add_zero, hF0, sub_self] at this
    linarith
  refine ⟨F 1, fun x => ?_⟩
  have := map_real_smul (AddMonoidHom.mk' F hFadd) F.continuous x 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at this
  rw [← hF', this, mul_comm]

variable (K : Type) [Field K] [NumberField K]

theorem extensionEmbedding_mixedSymm_of_isReal (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩

theorem extensionEmbedding_mixedSymm_of_isComplex (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsComplex) :
    InfinitePlace.Completion.extensionEmbedding v
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y => (extensionEmbedding_mixedSymm_of_isReal K y v hv).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y => (extensionEmbedding_mixedSymm_of_isComplex K y v hv).symm

def mixedIdele : (mixedSpace K)ˣ →* Ideles K :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.toMonoidHom)

theorem continuous_mixedIdele : Continuous (mixedIdele K) :=
  Continuous.units_map _ ((continuous_ringEquiv_mixedSpace_symm K).prodMk continuous_const)

theorem mixedIdele_mixedEmbedding (k : Kˣ) :
    mixedIdele K (Units.map (mixedEmbedding K).toMonoidHom k) = Formalism.L2.Host.infDiag k := by
  rw [GlobalTheory.CMVal.infDiag_eq]
  apply Units.ext
  apply Prod.ext
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K (k : K)) = algebraMap K _ (k : K)
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
  · rfl

def expScalar (x : ℝ) : (mixedSpace K)ˣ :=
  ⟨algebraMap ℝ _ (Real.exp x), algebraMap ℝ _ (Real.exp (-x)),
    by rw [← map_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, map_one],
    by rw [← map_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, map_one]⟩

theorem expScalar_add (x y : ℝ) : expScalar K (x + y) = expScalar K x * expScalar K y :=
  Units.ext (by
    change algebraMap ℝ (mixedSpace K) (Real.exp (x + y)) = algebraMap ℝ _ (Real.exp x) * algebraMap ℝ _ (Real.exp y)
    rw [Real.exp_add, map_mul])

theorem continuous_expScalar : Continuous (expScalar K) :=
  Units.continuous_iff.2 ⟨(continuous_algebraMap ℝ (mixedSpace K)).comp Real.continuous_exp,
    (continuous_algebraMap ℝ (mixedSpace K)).comp (Real.continuous_exp.comp continuous_neg)⟩

theorem ideleNorm_expScalar (x : ℝ) :
    ideleNorm (mixedIdele K (expScalar K x)) = Real.exp ((Module.finrank ℚ K : ℝ) * x) := by
  have h : ∀ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ = Real.exp x := by
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isReal]
      change ‖Real.exp x‖ = _
      exact Real.norm_of_nonneg (Real.exp_pos x).le
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isComplex K _ v hv]
      change ‖((Real.exp x : ℝ) : ℂ)‖ = _
      exact Complex.norm_of_nonneg (Real.exp_pos x).le
  change (∏ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖) = _
  simp only [h, norm_one, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, Real.exp_nat_mul]

variable {K}

theorem exists_trivial_on_expScalar (χ : HChar K) (hχ : χ.IsUnitary) :
    ∃ t : ℝ, ∀ x : ℝ, (χ * normChar K (-t)).1 (mixedIdele K (expScalar K x)) = 1 := by
  let f : ℝ → Circle := fun x => ⟨(χ.1 (mixedIdele K (expScalar K x)) : ℂ),
    mem_sphere_zero_iff_norm.2 (hχ _)⟩
  have hf : Continuous f := Continuous.subtype_mk
    (Units.continuous_val.comp (χ.2.1.comp ((continuous_mixedIdele K).comp (continuous_expScalar K)))) _
  obtain ⟨a, ha⟩ := exists_eq_circleExp_mul f hf fun x y => Circle.ext (by
    change (χ.1 (mixedIdele K (expScalar K (x + y))) : ℂ) =
      (χ.1 (mixedIdele K (expScalar K x)) : ℂ) * (χ.1 (mixedIdele K (expScalar K y)) : ℂ)
    rw [expScalar_add, map_mul, map_mul, Units.val_mul])
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨a / Module.finrank ℚ K, fun x => Units.ext ?_⟩
  change (f x : ℂ) * (((normChar K _).1 (mixedIdele K (expScalar K x)) : ℂˣ) : ℂ) = 1
  rw [normChar_apply, ideleNorm_expScalar, Real.log_exp, ha, ← Circle.coe_mul, ← Circle.exp_add]
  have : a * x + -(a / (Module.finrank ℚ K : ℝ)) * ((Module.finrank ℚ K : ℝ) * x) = 0 := by
    field_simp
    ring
  rw [this, Circle.exp_zero, Circle.coe_one]

theorem exists_normChar_smooth_homogeneous_inf : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (t : ℝ) (φ : mixedSpace K → ℂ), (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (r : ℝ) x, 0 < r → φ (r • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ k : Kˣ, φ (mixedEmbedding K (k : K)) = ((((χ * GlobalTheory.HeckeOne.normChar K (-t)).inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  obtain ⟨t, ht⟩ := exists_trivial_on_expScalar χ hχ
  let ξ : HChar K := χ * normChar K (-t)
  have hξ : ξ.IsUnitary := fun x => by
    change ‖((χ.1 x : ℂˣ) : ℂ) * (((normChar K (-t)).1 x : ℂˣ) : ℂ)‖ = 1
    rw [norm_mul, hχ x, isUnitary_normChar (-t) x, mul_one]
  obtain ⟨φ, hmul, hsm, hu, hiff⟩ := GlobalTheory.exists_smooth_mul_extension_of_continuous_char K ((ξ⁻¹).1.comp (mixedIdele K))
    ((ξ⁻¹).2.1.comp (continuous_mixedIdele K))
  have hu' : ∀ u : (mixedSpace K)ˣ, φ u = ((ξ.1 (mixedIdele K u) : ℂˣ) : ℂ)⁻¹ := fun u => by
    rw [hu, ← Units.val_inv_eq_inv_val]
    rfl
  refine ⟨t, φ, hmul, fun r x hr => ?_, hsm, fun x hx => ?_, fun k => ?_⟩
  · have h1 : r • x = (expScalar K (Real.log r) : mixedSpace K) * x := by
      change _ = algebraMap ℝ (mixedSpace K) (Real.exp (Real.log r)) * x
      rw [Real.exp_log hr, Algebra.smul_def]
    rw [h1, hmul, hu', ht]
    simp
  · obtain ⟨u, rfl⟩ := (hiff x).1 hx
    rw [hu', norm_inv, hξ, inv_one]
  · have := hu' (Units.map (mixedEmbedding K).toMonoidHom k)
    rw [mixedIdele_mixedEmbedding] at this
    exact this

end GlobalTheory.HeckeOne
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem AlmostNorm.exists_basis_sq (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (b : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ b 0 = 1 ∧
      b 1 * b 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hr
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hr
  haveI : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by rw [← sq, ← hc]; exact pow_card_eq_one'
  obtain ⟨δ, b, h1, h0, -, h3⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by
      have := congrArg (fun τ : L ≃ₐ[K] L => τ x) h2
      simpa using this)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h))
  exact ⟨δ, b, h1, h0, h3⟩

theorem almostNorm_finDiag :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ t : Kˣ, AlmostNorm K L (finDiag K t) := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine (((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ0))).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K t)).subset ?_
  intro v hv
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Units.val_mk0] at hn
  obtain ⟨⟨h2, hd⟩, ht⟩ := hn
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  obtain ⟨x, -, y, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v
    (algebraMap K _ δ) (algebraMap K _ (t : K))
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2) (by rw [key, hd]) (by rw [key, ht])
  exact hv ((mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩)

end GlobalTheory.QuadSymbol
end

section

noncomputable section

namespace GlobalTheory.HermitianFormLinearity

open NumberField

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_add_left (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (x + x') y =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (y + y') =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (c • x) y =
      starRingEnd E c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (c • y) =
      c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem hform_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem hform_span_eq_zero (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd E) J y z = 0) :
    ∀ x ∈ Submodule.span E S, ∀ y ∈ Submodule.span E S,
      Formalism.UG.hform (starRingEnd E) J x y = 0 := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span E S, Formalism.UG.hform (starRingEnd E) J x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS x hx z hz
    | zero => exact hform_zero_right J x
    | add a b _ _ ha hb => rw [hform_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [hform_smul_right, ha, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem z hz => exact h1 z hz y hy
  | zero => exact hform_zero_left J y
  | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hform_smul_left, ha, mul_zero]

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst)
    (R : Submodule (NumberField.RingOfIntegers (Formalism.MainNotions.S.AutInst.E I))
      (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I)),
    R ≠ ⊥ →
    (∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd (Formalism.MainNotions.S.AutInst.E I)) (Formalism.MainNotions.S.AutInst.J I) y z
      = (0 : Formalism.MainNotions.S.AutInst.E I)) →
    Formalism.MainNotions.S.AutInst.IsIsot I (Submodule.span (Formalism.MainNotions.S.AutInst.E I)
      (↑R : Set (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I))) := by
  intro I R hR hiso
  refine ⟨?_, hform_span_eq_zero I.J _ hiso⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  intro h
  apply hr0
  have : r ∈ Submodule.span I.E (↑R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [h] at this
  exact (Submodule.mem_bot _).1 this

end GlobalTheory.HermitianFormLinearity
end
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tensor_eq_top_or_le_ker_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hloc₀ hRel₀ hK₀ hL hloc hRel hK
    N hN₀ hNi hS₀ hSi
  classical
  have hS : Stab (tensOps Op₀ (piOps Op)) N := by
    rintro f (⟨g, hg, rfl⟩ | ⟨h, ⟨i, g, hg, rfl⟩, rfl⟩) t ht
    · exact hS₀ g hg t ht
    · exact hSi i g hg t ht
  by_cases h0 : LinearMap.ker p₀ = ⊤
  · right
    intro t _
    have : p₀ = 0 := LinearMap.ker_eq_top.mp h0
    rw [LinearMap.mem_ker, this, TensorProduct.map_zero_left, LinearMap.zero_apply]
  by_cases hi : ∃ i, LinearMap.ker (p i) = ⊤
  · right
    obtain ⟨i, hi⟩ := hi
    have hpi : p i = 0 := LinearMap.ker_eq_top.mp hi
    have hmap : PiTensorProduct.map p = 0 := by
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.zero_apply]
      exact MultilinearMap.map_coord_zero _ i (by simp [hpi])
    intro t _
    rw [LinearMap.mem_ker, hmap, TensorProduct.map_zero_right, LinearMap.zero_apply]
  push_neg at hi
  by_cases hN : N = ⊤
  · exact Or.inl hN
  have hSimple₀ : SimpleOver Op₀ (LinearMap.ker p₀) := fun U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc₀ U (hRel₀.trans hKU) hU hUt) hKU)
  have hSimple : ∀ i, SimpleOver (Op i) (LinearMap.ker (p i)) := fun i U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc i U ((hRel i).trans hKU) hU hUt) hKU)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_finset_generating_operator_stable_bounded Op₀ Rel₀ hL₀
  choose F hF using fun i => GlobalTheory.T.exists_finset_generating_operator_stable_bounded (Op i) (Rel i) (hL i)
  let G : Finset (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :=
    (F₀ ×ˢ Fintype.piFinset F).image (fun q => q.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ q.2)
  have hgen : ∀ U, N ≤ U → Stab (tensOps Op₀ (piOps Op)) U → (↑G : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) ⊆ (U : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) → U = ⊤ := by
    intro U hNU hU hGU
    refine GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators Op₀ Op Rel₀ Rel F₀ F hF₀ hF U (fun x hx y => hNU (hN₀ x hx y))
      (fun i x hx x₀ y => hNU (hNi i x hx x₀ y)) hU ?_
    intro x₀ hx₀ y hy
    apply hGU
    simp only [G, Finset.coe_image]
    exact ⟨(x₀, y), by simp [hx₀, Fintype.mem_piFinset, hy], rfl⟩
  obtain ⟨N', hNN', hS', hN'top, hmax⟩ := GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating _ N G hgen N le_rfl hS hN
  have h0' := GlobalTheory.T.tensor_maximalStable_contains_leftKernel Op₀ (piOps Op) Rel₀ (LinearMap.ker p₀) hL₀ hloc₀ h0 hK₀ N'
    (fun x hx y => hNN' (hN₀ x hx y)) hS' hmax
  have hi' : ∀ i, ∀ x ∈ LinearMap.ker (p i), ∀ (x₀ : M₀) (y : ∀ j, M j),
      x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := fun i =>
    GlobalTheory.T.piTensor_maximalStable_contains_positionKernel Op₀ Op i (Rel i) (LinearMap.ker (p i)) (hL i) (hloc i) (hi i) (hK i) N'
      (fun x hx x₀ y => hNN' (hNi i x hx x₀ y)) hS' hmax
  have hKT : tensKer (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) ≤ N' := by
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · exact h0' x hxy y
    · refine Submodule.span_induction (p := fun y _ => x ⊗ₜ[ℂ] y ∈ N') ?_ ?_ ?_ ?_ hxy
      · rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
        have := hi' i (z i) hzi x z
        rwa [Function.update_eq_self] at this
      · simp
      · intro a b _ _ ha hb
        rw [TensorProduct.tmul_add]
        exact N'.add_mem ha hb
      · intro c a _ ha
        rw [TensorProduct.tmul_smul]
        exact N'.smul_mem c ha
  have hPi := GlobalTheory.T.simpleOverStableSubmodule_piTensor Op (fun i => LinearMap.ker (p i)) hr hK hSimple
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan Op₀ (piOps Op) (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) hr₀ hK₀
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan Op _ hK) hSimple₀ hPi
  rcases hT N' hS' hKT with h | h
  · right
    rw [h] at hNN'
    refine hNN'.trans ?_
    have hle : piKer (fun i => LinearMap.ker (p i)) ≤ LinearMap.ker (PiTensorProduct.map p) := by
      rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, PiTensorProduct.map_tprod]
      exact MultilinearMap.map_coord_zero _ i (LinearMap.mem_ker.mp hzi)
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp hxy]
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp (hle hxy)]
  · exact absurd h hN'top

end GlobalTheory.TensHead
end
