module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle048
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMField
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnRep.StdInhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem bar_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  apply GlobalTheory.QuadTrace.bar_rt <;> assumption

theorem bar_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h4 : (2 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  rw [h2, bar_rt]
  linear_combination H.two_weight_eq_one_add_root

theorem w_norm (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ m : ℕ, 2 ≤ m ∧ H.w0 * H.bar H.w0 = (m : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  refine ⟨m, by have := H.d_mod; omega, ?_⟩
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [bar_w]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem w_not_unit (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ¬ IsUnit H.w0 := by
  intro hu
  obtain ⟨m, hm, e⟩ := w_norm H
  have h1 : IsUnit (m : 𝓞 E) := e ▸ hu.mul (hu.map H.bar)
  have h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) (m : ℤ))) := by
    apply IsUnit.map
    simpa using h1
  rw [Algebra.norm_algebraMap] at h2
  have h3 : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff h3, Int.isUnit_iff] at h2
  omega

theorem w_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.w0 ≠ 0 := by
  obtain ⟨m, hm, e⟩ := w_norm H
  intro h
  rw [h, zero_mul] at e
  have : m = 0 := by exact_mod_cast e.symm
  omega

theorem moved_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (P : Ideal (𝓞 E)) :
    Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P := by
  constructor
  · rintro ⟨a, ha, b, hb, hbP⟩ e
    apply hbP
    have : b = H.bar a := by
      apply Subtype.ext
      show (b : E) = ((H.bar a : 𝓞 E) : E)
      rw [hb, H.bar_eq]
    rw [this, ← e]
    exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha
  · intro hne
    by_contra hm
    have key : ∀ a ∈ P, H.bar a ∈ P := by
      intro a ha
      by_contra hb
      exact hm ⟨a, ha, H.bar a, H.bar_eq a, hb⟩
    apply hne
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact key a ha
    · intro a ha
      rw [← bar_bar H a]
      exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (key a ha)

theorem splitOff_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : SplitOff (IsCMField.complexConj E) 1 H.w0 := by
  refine ⟨w_ne_zero H, fun P hP hw => ?_⟩
  have h1 : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top
  refine ⟨⟨H.w0, hw, H.bar H.w0, H.bar_eq _, fun hb => h1 ?_⟩, by simpa using h1⟩
  have := P.add_mem hw hb
  rwa [bar_w, add_sub_cancel] at this

omit [IsCMField E] in
theorem single_mem (n : ℕ) (i : Fin n) : (Pi.single i (1 : E) : Fin n → E) ∈ stdLat E n := by
  intro j _
  by_cases h : j = i
  · subst h
    exact Submodule.mem_one.2 ⟨1, by simp⟩
  · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

omit [IsCMField E] in
theorem stdLat_eq_span (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : Fin n → E)) := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i => Submodule.mem_one.1 (hx i trivial)
    choose r hr using hx'
    have : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem n i

theorem hermE_one {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (x y : Fin n → E) :
    hermE c 1 x y = ∑ a, x a * c (y a) := by
  unfold hermE
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

theorem isUnE_one_iff {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c 1 γ ↔ ∀ i j, ∑ b, c (γ b i) * γ b j = if i = j then 1 else 0 := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [hermE_one, hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [mul_comm (c _)]
    rw [this]
    by_cases e : i = j
    · subst e; simp [Pi.single_apply]
    · simp [Pi.single_apply, e, Ne.symm e]
  · intro h x y
    rw [hermE_one, hermE_one]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc ∑ a, ∑ i, ∑ j, γ a j * x j * (c (γ a i) * c (y i))
        = ∑ i, ∑ j, (∑ a, c (γ a i) * γ a j) * (x j * c (y i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by simp [h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ), IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) ∧ Module.finrank (maximalRealSubfield E) E = 2 ∧ (stdLat E n).FG ∧ Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ ∧ SplitOff (IsCMField.complexConj E) 1 H.w0 ∧ ¬ IsUnit H.w0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → (Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P)) ∧ ∀ γ : Matrix (Fin n) (Fin n) E, IsUnE (IsCMField.complexConj E) 1 γ ↔ ∀ i j, ∑ b, (IsCMField.complexConj E) (γ b i) * γ b j = if i = j then 1 else 0 := by
  intro E _ _ _ H n
  refine ⟨⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => ?_, by simp⟩,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, ?_, ?_, splitOff_w H, w_not_unit H,
    fun P _ => moved_iff H P, isUnE_one_iff _⟩
  · by_cases e : a = b
    · subst e; simp
    · simp [Matrix.one_apply, e, Ne.symm e]
  · rw [stdLat_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simpa using single_mem (E := E) n i

end GlobalTheory.UnRep.StdInhab
end
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_leftTranslation_reynoldsOperator : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  first | exact @GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds | exact GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds | (intros; apply GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ 2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ 2 ^ (tFin F δ S + tReal F δ) := by
  first | exact @GlobalTheory.QNorm.first_inequality_sUnits | exact GlobalTheory.QNorm.first_inequality_sUnits | (intros; apply GlobalTheory.QNorm.first_inequality_sUnits <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  first | exact @GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | exact GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | (intros; apply GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_subst {σ : Type} (s : σ → MvPolynomial σ ℚ) (l : ℂ →ₗ[ℚ] ℚ)
    (b : MvPolynomial σ ℂ) :
    ∃ b' : MvPolynomial σ ℚ, ∀ m, AddMonoidAlgebra.coeff (MvPolynomial.aeval s b') m =
      l (AddMonoidAlgebra.coeff (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)
        m) := by
  induction b using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨MvPolynomial.monomial u (l a), fun m => ?_⟩
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    have h : (u.prod fun i k => (MvPolynomial.map (algebraMap ℚ ℂ) (s i)) ^ k) =
        MvPolynomial.map (algebraMap ℚ ℂ) (u.prod fun i k => s i ^ k) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [h, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm a, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', fun m => ?_⟩
    rw [map_add (f := _), map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, map_add (f := _), hp', hq']

theorem exists_poly_blk {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ s : ι × ι → MvPolynomial (ι × ι) ℚ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      ev (s ij) x = blk e x ij.1 ij.2 := by
  refine ⟨fun ij => blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) ij.1 ij.2,
    fun x ij => ?_⟩
  set φ : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hφ
  have h1 : φ.mapMatrix (e.map (algebraMap ℚ (MvPolynomial (ι × ι) ℚ))) = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, AlgHom.commutes]
  have h2 : φ.mapMatrix (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) = x := by
    ext i j
    simp [hφ]
  have h3 : φ.mapMatrix (blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)))
      = blk e x := by
    unfold blk
    simp only [map_add (f := _), map_mul, map_sub, map_one, h1, h2]
  rw [← h3]
  rfl

theorem descend_blk_rat : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  intro ι _ _ Γ e hΓ he hpar f hf
  have hmap : ∀ (p : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι ℂ),
      evC (MvPolynomial.map (algebraMap ℚ ℂ) p) x = ev p x := by
    intro p x
    unfold evC ev
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_complexPoly_blockDiagPart_of_fibre_const ι Γ e hΓ he hpar (MvPolynomial.map (algebraMap ℚ ℂ) f)
    (fun x hx x' hx' h => by rw [hmap, hmap]; exact hf x hx x' hx' h)
  obtain ⟨s, hs⟩ := exists_poly_blk e
  obtain ⟨l, hl⟩ : ∃ l : ℂ →ₗ[ℚ] ℚ, l 1 = 1 := by
    obtain ⟨l, hl⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
    refine ⟨l, ?_⟩
    have := LinearMap.congr_fun hl 1
    simpa using this
  obtain ⟨b', hb'⟩ := exists_component_subst s l b
  have hsubC : ∀ x : Matrix ι ι ℂ,
      evC (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b) x = evC b (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (MvPolynomial.map (algebraMap ℚ ℂ) (s ij)) := by
      funext ij
      rw [← hs, ← hmap]
      rfl
    unfold evC
    rw [h, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe, RingHom.coe_coe,
      ← MvPolynomial.comp_aeval]
    rfl
  have hsub : ∀ x : Matrix ι ι ℂ, ev (MvPolynomial.aeval s b') x = ev b' (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (s ij) := by
      funext ij
      rw [← hs]
      rfl
    unfold ev
    rw [h, ← MvPolynomial.comp_aeval]
    rfl
  have hvan := GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet ι Γ hΓ.aut_mem
    (MvPolynomial.map (algebraMap ℚ ℂ) f -
      MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)
    (fun g hg => by
      have h1 := hb g hg
      rw [← hsubC] at h1
      unfold evC at h1 ⊢
      rw [map_sub, h1, sub_self])
    l (f - MvPolynomial.aeval s b')
    (fun m => by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, map_sub, hb', MvPolynomial.coeff_map,
        Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one])
  refine ⟨b', fun x hx => ?_⟩
  have h1 := hvan x hx
  rw [← hsub]
  unfold ev at h1 ⊢
  rw [map_sub] at h1
  exact sub_eq_zero.mp h1

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → sUnits F S ⊔ finNorm p F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top | exact GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top | (intros; apply GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_primeIdempotent_CMField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  first | exact @GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | exact GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | (intros; apply GlobalTheory.PrimeIdemExists.exists_isPrimeIdem <;> assumption)
end
