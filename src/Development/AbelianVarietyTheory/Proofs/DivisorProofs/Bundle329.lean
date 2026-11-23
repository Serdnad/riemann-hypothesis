module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle284
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
import ReciprocityTheory.Chebotarev.Bundle001
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  first | exact @GlobalTheory.SubLen.exists_relLen_of_smul_le | exact GlobalTheory.SubLen.exists_relLen_of_smul_le | (intros; apply GlobalTheory.SubLen.exists_relLen_of_smul_le <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.finrank_int0_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X → finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  first | exact @GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | exact GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | (intros; apply GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ), v (c : C) = r → RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  first | exact @GlobalTheory.ScalLen.relLen_map_lsmul | exact GlobalTheory.ScalLen.relLen_map_lsmul | (intros; apply GlobalTheory.ScalLen.relLen_map_lsmul <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.relLen_trans_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ), RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  first | exact @GlobalTheory.relLen_chain_add | exact GlobalTheory.relLen_chain_add | (intros; apply GlobalTheory.relLen_chain_add <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.hasLatticeRelativeLength_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  first | exact @GlobalTheory.LenMap.relLen_map_iff | exact GlobalTheory.LenMap.relLen_map_iff | (intros; apply GlobalTheory.LenMap.relLen_map_iff <;> assumption)
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussSum

open GlobalTheory.GaussExt

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem eq_zero_of_add_mul_ii {x y : F}
    (h : algebraMap F (Ext F) x + algebraMap F (Ext F) y * ii F = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hy' : algebraMap F (Ext F) y ≠ 0 := (_root_.map_ne_zero _).2 hy
    have hi : ii F = algebraMap F (Ext F) (-x / y) := by
      rw [map_div₀, map_neg, eq_div_iff hy']
      linear_combination h
    have h2 : algebraMap F (Ext F) ((-x / y) ^ 2 + 1) = 0 := by
      rw [map_add (f := _), map_pow, ← hi, ii_sq, map_one]; ring
    have h3 : (-x / y) ^ 2 + 1 = 0 := (map_eq_zero _).1 h2
    obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
      exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
    have h4 := congrArg τ h3
    rw [map_add (f := _), map_pow, map_one, map_zero] at h4
    nlinarith [sq_nonneg (τ (-x / y))]
  refine ⟨?_, hy⟩
  rw [hy, map_zero, zero_mul, add_zero] at h
  exact (map_eq_zero _).1 h

theorem isIntegral_ii : IsIntegral ℤ (ii F) :=
  ⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩



theorem summable_norm_rpow (𝔞 𝔟 : Frac F) {t : ℝ} (ht : 1 < t)
    (hQ : Finite ((𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range)) :
    Summable (fun c : Quotient (latRel 𝔞 𝔟) => |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := APart.exists_den (latM 𝔞)
  obtain ⟨d₂, hd₂, h₂⟩ := APart.exists_den (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  have hd : ((d₁ : F) * (d₂ : F)) ≠ 0 := mul_ne_zero (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  choose ga hga using fun c : Quotient (latRel 𝔞 𝔟) => h₁ c.out.1.1 c.out.2.1
  choose gb hgb using fun c : Quotient (latRel 𝔞 𝔟) => h₂ c.out.1.2 c.out.2.2.1
  let iO : 𝓞 (Ext F) := ⟨ii F, isIntegral_ii⟩
  let y : Quotient (latRel 𝔞 𝔟) → 𝓞 (Ext F) := fun c =>
    algebraMap (𝓞 F) (𝓞 (Ext F)) (d₂ * ga c) + algebraMap (𝓞 F) (𝓞 (Ext F)) (d₁ * gb c) * iO
  have hy : ∀ c, ((y c : 𝓞 (Ext F)) : Ext F) = algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) * gEmb F c.out.1 := by
    intro c
    have e : ((y c : 𝓞 (Ext F)) : Ext F) =
        algebraMap F (Ext F) ((d₂ * ga c : 𝓞 F) : F) + algebraMap F (Ext F) ((d₁ * gb c : 𝓞 F) : F) * ii F := rfl
    have ea : ((d₂ * ga c : 𝓞 F) : F) = (d₂ : F) * (ga c : F) := rfl
    have eb : ((d₁ * gb c : 𝓞 F) : F) = (d₁ : F) * (gb c : F) := rfl
    rw [e, ea, eb, hga, hgb, gEmb]
    simp only [map_mul]
    ring

  let rep : Ideal (𝓞 (Ext F)) → 𝓞 (Ext F) := fun J =>
    if h : ∃ x, J = Ideal.span {x} then h.choose else 0
  have hrep : ∀ c, Associated (rep (Ideal.span {y c})) (y c) := by
    intro c
    have hex : ∃ x, Ideal.span {y c} = Ideal.span {x} := ⟨y c, rfl⟩
    refine Ideal.span_singleton_eq_span_singleton.1 ?_
    simp only [rep, dif_pos hex]
    exact hex.choose_spec.symm
  choose u hu using hrep
  let Q := (𝓞 (Ext F))ˣ ⧸ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range
  let φ : Quotient (latRel 𝔞 𝔟) → Ideal (𝓞 (Ext F)) × Q := fun c =>
    (Ideal.span {y c}, (QuotientGroup.mk (u c) : Q))
  have hinj : Function.Injective φ := by
    intro c c' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hJ, hq⟩ := h
    obtain ⟨η, hη⟩ := QuotientGroup.eq.1 hq
    have hu' : ((u c' : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) = (u c : 𝓞 (Ext F)) * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      have : u c' = u c * Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom η := by
        rw [hη]; group
      rw [this]; simp
    have key : y c' = y c * algebraMap (𝓞 F) (𝓞 (Ext F)) (η : 𝓞 F) := by
      rw [← hu c', ← hu c, ← hJ, hu']; ring
    have h3 : ((y c' : 𝓞 (Ext F)) : Ext F) = (y c : Ext F) * algebraMap F (Ext F) ((η : 𝓞 F) : F) := by
      rw [key]; rfl
    rw [hy, hy] at h3
    have h4 : gEmb F c'.out.1 = gEmb F c.out.1 * algebraMap F (Ext F) ((η : 𝓞 F) : F) :=
      mul_left_cancel₀ ((_root_.map_ne_zero _).2 hd) (by rw [h3]; ring)
    unfold gEmb at h4
    have h5 : algebraMap F (Ext F) (c'.out.1.1 - ((η : 𝓞 F) : F) * c.out.1.1) +
        algebraMap F (Ext F) (c'.out.1.2 - ((η : 𝓞 F) : F) * c.out.1.2) * ii F = 0 := by
      simp only [map_sub, map_mul]
      linear_combination h4
    obtain ⟨e1, e2⟩ := eq_zero_of_add_mul_ii h5
    exact (Quotient.out_equiv_out.1 ⟨η, by linear_combination e1, by linear_combination e2⟩)
  haveI := hQ
  have hS : Summable (fun p : Ideal (𝓞 (Ext F)) × Q => ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-t) * (fun _ : Q => (1 : ℝ)) p.2) :=
    (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (Ext F) ht).mul_of_nonneg (Summable.of_finite)
      (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => zero_le_one)
  have hS' := hS.comp_injective hinj
  set K : ℝ := |((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ)| with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h0 : algebraMap F (Ext F) ((d₁ : F) * (d₂ : F)) ≠ 0 := (_root_.map_ne_zero _).2 hd
    have h1 : Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    exact abs_pos.2 (by exact_mod_cast h1)
  refine (hS'.mul_left (K ^ t)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (y c) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) * Algebra.norm ℚ (gEmb F c.out.1) := by
    rw [Algebra.coe_norm_int, hy, map_mul]
  have e2 : ((Algebra.norm ℤ (y c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (algebraMap F (Ext F) ((d₁ : F) * (d₂ : F))) : ℚ) : ℝ) * ((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({y c} : Set (𝓞 (Ext F)))) : ℕ) : ℝ) =
      K * |((Algebra.norm ℚ (gEmb F c.out.1) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply, φ, mul_one]
  rw [hN, Real.mul_rpow hK0.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel,
    Real.rpow_zero, one_mul]

end GlobalTheory.GaussSum

theorem GlobalTheory.GaussSum.summable_gauss_norm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  intro F _ _ _ 𝔞 𝔟 t ht hQ
  exact GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))

theorem hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2

theorem hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this

theorem hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z :=
  ((hasFDerivAt_expo (a σ) hz).cexp).const_mul (c σ)

open Classical in
theorem wirt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, 0 < (z τ).im) (τ₀ : Φ) (b : Bool) :
    wirt τ₀ b (mono c a σ) z =
      mono (fun σ => (if b then I else -I) / 2 * c σ * a σ τ₀) (fun σ => a σ - Pi.single τ₀ 1) σ z := by
  have hz' : ∀ τ, (z τ).im ≠ 0 := fun τ => (hz τ).ne'
  rw [wirt, (hasFDerivAt_mono c a σ hz').fderiv]
  simp [mono, Pi.single_apply]
  have hy := hz τ₀
  have e1 : ∀ x, ((if x = τ₀ then (1:ℂ) else 0).im) = 0 := fun x => by split_ifs <;> simp
  have e2 : ∀ x, ((if x = τ₀ then I else 0).im) = if x = τ₀ then 1 else 0 := fun x => by split_ifs <;> simp
  simp only [e1, e2, ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : ∑ x, (a σ x - if x = τ₀ then 1 else 0) * ((Real.log (z x).im : ℝ) : ℂ) =
      ∑ x, a σ x * ((Real.log (z x).im : ℝ) : ℂ) - ((Real.log (z τ₀).im : ℝ) : ℂ) := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [he, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hy]
  have hy' : ((z τ₀).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp <;> field_simp <;> ring

theorem wirtWord_mono (U : Set (Φ → ℂ)) (hU : IsOpen U) (hUpos : ∀ z ∈ U, ∀ τ, 0 < (z τ).im) (w : List (Φ × Bool)) :
    ∀ (c : ℂ → ℂ) (a : ℂ → Φ → ℂ), Differentiable ℂ c → (∀ τ, Differentiable ℂ (fun σ => a σ τ)) →
      ∃ (c' : ℂ → ℂ) (a' : ℂ → Φ → ℂ), Differentiable ℂ c' ∧ (∀ τ, Differentiable ℂ (fun σ => a' σ τ)) ∧
        ∀ σ, Set.EqOn (wirtWord w (mono c a σ)) (mono c' a' σ) U := by
  induction w with
  | nil => exact fun c a hc ha => ⟨c, a, hc, ha, fun σ z _ => rfl⟩
  | cons l w ih =>
    intro c a hc ha
    obtain ⟨c₁, a₁, hc₁, ha₁, h₁⟩ := ih c a hc ha
    classical
    refine ⟨fun σ => (if l.2 then I else -I) / 2 * c₁ σ * a₁ σ l.1, fun σ => a₁ σ - Pi.single l.1 1,
      ((differentiable_const _).mul hc₁).mul (ha₁ l.1), fun τ => ?_, fun σ z hz => ?_⟩
    · simp only [Pi.sub_apply]
      exact (ha₁ τ).sub (differentiable_const _)
    · rw [wirtWord_cons, GoodAdd.wirt_congr hU (h₁ σ) _ _ hz]
      convert wirt_mono c₁ a₁ σ (hUpos z hz) l.1 l.2

theorem mono_differentiable {c : ℂ → ℂ} {a : ℂ → Φ → ℂ} (hc : Differentiable ℂ c)
    (ha : ∀ τ, Differentiable ℂ (fun σ => a σ τ)) (z : Φ → ℂ) : Differentiable ℂ (fun σ => mono c a σ z) := by
  unfold mono
  refine hc.mul (Differentiable.cexp ?_)
  exact Differentiable.fun_sum fun τ _ => (ha τ).mul (differentiable_const _)

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons l w ih => intro y hy; rw [wirtWord_cons, wirtWord_cons]; exact GoodAdd.wirt_congr hU ih _ _ hy

end GlobalTheory.HeckeTwo.ProdImWirt

theorem GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.QFiber

open FractionalIdeal

variable {F : Type} [Field F] [NumberField F]

def toIdeal (K : FractionalIdeal (𝓞 F)⁰ F) : Ideal (𝓞 F) :=
  open Classical in if h : K ≤ 1 then (le_one_iff_exists_coeIdeal.mp h).choose else ⊥

theorem coe_toIdeal {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by
  unfold toIdeal
  rw [dite_eq_left h]
  exact (le_one_iff_exists_coeIdeal.mp h).choose_spec

theorem nrm_nonneg (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by
  unfold nrm; exact_mod_cast absNorm_nonneg _

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem card_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F)
    (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) →
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  intro F _ _ _ 𝔞 𝔟 ξ s hs
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))
  have hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔞.ne_zero
  have hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔟.ne_zero
  have hξ : ξ ≠ 0 := by
    obtain ⟨τ⟩ := emb_nonempty (F := F)
    have h := c0.out.2.2.2 τ
    rw [hs c0 hc0] at h
    intro h0
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hle : ∀ c : Quotient (qRel 𝔞 𝔟),
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := fun c => by
    calc _ ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.1
      _ = 1 := mul_inv_cancel₀ hA
  have hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    intro c hc
    have hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
      calc _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
            by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.2.1
        _ = 1 := mul_inv_cancel₀ hB
    rw [← hs c hc, ← spanSingleton_mul_spanSingleton]
    calc spanSingleton (𝓞 F)⁰ c.out.1.1 * spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
          (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
          (spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ring
      _ ≤ (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  have hI1 := (hIle c0 hc0).trans (hle c0)
  set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef
  let f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F) := fun c =>
    toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
  have hIJ : ∀ c ∈ s, I ≤ f c := by
    intro c hc
    rw [← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]
    exact hIle c hc
  have hI0 : I ≠ ⊥ := by
    intro h
    have h' := coe_toIdeal hI1
    rw [← hIdef, h, coeIdeal_bot] at h'
    have := h'.symm
    simp only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this
    tauto
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hcc
    have h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
        spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
      rw [← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]
      exact congrArg _ hcc
    have h2 := mul_right_cancel₀ (inv_ne_zero hA) h1
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp h2
    rw [Units.smul_def, Algebra.smul_def] at hu
    have hν : c.out.1.1 ≠ 0 := left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)
    have hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact u.ne_zero
    have h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      rw [mul_comm]; exact unit_inv_mul u
    have e1 := hs c hc
    have e2 := hs c' hc'
    rw [← hu] at e2
    have hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2 := by
      apply mul_left_cancel₀ (mul_ne_zero hu0 hν)
      linear_combination e2 - e1 - c.out.1.1 * c.out.1.2 * h4
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨u⁻¹, ?_, hb⟩
    rw [inv_inv, ← hu]
  have key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) =
      |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) *
        FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]
    ring
  rw [coeIdeal_absNorm] at key
  calc (s.card : ℝ) = ((s.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast GlobalTheory.T.card_divisors_le_absNorm_numberField F I hI0 (s.image f) (by
        intro J hJ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hJ
        exact hIJ c hc)
    _ = _ := by
      unfold nrm
      have := congrArg (Rat.cast : ℚ → ℝ) key
      push_cast at this
      exact this

end GlobalTheory.QFiber
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), rootSum θ k (P.map t) = rootSum θ (k * ringChar F ^ j) P := by
  first | (exact @GlobalTheory.Shin.rootSum_map_frobeniusPow) | (exact GlobalTheory.Shin.rootSum_map_frobeniusPow) | (intros; apply GlobalTheory.Shin.rootSum_map_frobeniusPow  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ) (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 → rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  first | (exact @GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (exact GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (intros; apply GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.natDegree_mul_esymm_roots_pow' : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  first | exact @GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | exact GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | (intros; apply GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow <;> assumption)
end
