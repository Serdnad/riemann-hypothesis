module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
end

section

noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Lev (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f

def IntC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V

def SmallC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V.nonunits

def Prim (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop :=
  IntC X V f ∧ ∃ r : ℚ, V.valuation ((X.exp f).coeff r) = 1

def Dom (X : Tower Ω ε) (V : ValuationSubring Ω) (W : ValuationSubring X.K) : Prop :=
  (∀ f, IntC X V f → f ∈ W) ∧ (∀ f, SmallC X V f → W.valuation f < 1) ∧ ∀ f, Prim X V f → W.valuation f = 1

def Gauss {F L : Type} [Field F] [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1

def FrobV (V : ValuationSubring Ω) (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Nq (X : Tower Ω ε) (M q : ℕ) (f : X.K) : X.K :=
  ∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f

def DiagMod (M q : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = q

def levF (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω (AlgebraicClosure X.K) :=
  IntermediateField.adjoin Ω (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f})

def rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) : IntermediateField (levF X M₀) (AlgebraicClosure X.K) :=
  IntermediateField.adjoin (levF X M₀) (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f} ∪
    {y | ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) U)})

theorem lev_jK (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ

end GlobalTheory.KZ.ES
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem kummer_root_mem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → ∃ g : X.Kˣ, f = g ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f a b M hM ha hb hb0 hfab hinv
  have hHs_open : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hHs_conn : IsPreconnected Hs :=
    (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  have hbne : ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
    rcases (hb.analyticOnNhd hHs_open).eqOn_zero_or_eventually_ne_zero_of_preconnected hHs_conn with h | h
    · exfalso; apply hb0
      exact Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h hz))
    · exact h
  have hrep : ∀ x : Mero, ∃ φ : ℂ → ℂ, x = (φ : Mero) := fun x =>
    Filter.Germ.inductionOn x (fun φ => ⟨φ, rfl⟩)
  obtain ⟨φ, hφ⟩ := hrep (X.an (f : X.K))
  rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul] at hfab
  have h1 : ∀ᶠ z in Filter.codiscreteWithin Hs, φ z * b z ^ m = a z ^ m :=
    (Filter.Germ.coe_eq.1 hfab).mono fun z hz => by simpa using hz
  have h2 : ∀ᶠ z in Filter.codiscreteWithin Hs, (a z / b z) ^ m = φ z := by
    filter_upwards [h1, hbne] with z hz hbz
    rw [div_pow, div_eq_iff (pow_ne_zero _ hbz), hz]
  have hpoly : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ m - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hm _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ, ← Filter.Germ.coe_pow, sub_eq_zero]
    exact Filter.Germ.coe_eq.2 (h2.mono fun z hz => by simpa using hz)
  obtain ⟨g0, hg0⟩ := X.sat a b M hM ha hb hb0 hinv hpoly
  obtain ⟨ψ, hψ⟩ := hrep (X.an g0)
  rw [hψ, ← Filter.Germ.coe_mul] at hg0
  have h3 : ∀ᶠ z in Filter.codiscreteWithin Hs, ψ z * b z = a z :=
    (Filter.Germ.coe_eq.1 hg0).mono fun z hz => by simpa using hz
  haveI : Nontrivial Mero := ⟨⟨_, _, hb0⟩⟩
  have hpow : g0 ^ m = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ, hφ, ← Filter.Germ.coe_pow]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [h2, h3, hbne] with z hz2 hz3 hbz
    have : ψ z = a z / b z := by rw [eq_div_iff hbz, hz3]
    simp only [Pi.pow_apply]
    rw [this, hz2]
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hpow
    exact f.ne_zero hpow.symm
  refine ⟨Units.mk0 g0 hg0ne, ?_⟩
  ext
  simp [hpow]

end GlobalTheory.KZ
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exp_two_pi_rat_mem_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (r : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero r.den := ⟨r.den_nz⟩
  haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den
  have hζ' : IsPrimitiveRoot (ε ζ) r.den := hζ.map_of_injective ε.injective
  have he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have h1 : ((r.den : ℚ) * r : ℚ) = r.num := Rat.den_mul_eq_num r
    have h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1
    rw [← h2]; ring
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one he
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem Tower.exponent_integral_of_translation_invariant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (hh : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  have e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ) := fun _ _ _ => rfl
  have e10 : ent (ofSL ModularGroup.T) 1 0 = 0 := by rw [e]; simp [ModularGroup.T]
  have e00 : ent (ofSL ModularGroup.T) 0 0 = 1 := by rw [e]; simp [ModularGroup.T]
  have e01 : ent (ofSL ModularGroup.T) 0 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have e11 : ent (ofSL ModularGroup.T) 1 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have key := X.exp_upper _ e10 h r
  rw [hh, e00, e01, e11, mul_one, div_one] at key
  have h1 : eOm ε r = 1 := by
    have : eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r := by rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hr this
  have h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) :=
    Function.invFun_eq (exp_two_pi_rat_mem_range ε r)
  rw [h1, map_one] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2.symm
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = (n : ℂ) := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulFam_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l),
    ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  intro N l _ hl _ γ
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp γ.2
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  rw [CongruenceSubgroup.Gamma0_mem] at hγ0
  obtain ⟨ha1, hd1, hcN⟩ := hγ1
  set a : ℤ := mat γ 0 0 with ha
  set b : ℤ := mat γ 0 1 with hb
  set c : ℤ := mat γ 1 0 with hc
  set d : ℤ := mat γ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := (γ : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at h
    exact h
  have hmat : mat γ = !![a, b; c, d] := Matrix.eta_fin_two _
  have hcl : (c : ZMod l) = 0 := hγ0
  have hcN' : (c : ZMod N) = 0 := hcN
  have ha1' : (a : ZMod N) = 1 := ha1
  have hd1' : (d : ZMod N) = 1 := hd1
  have had : (d : ZMod l) * a = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  let f : Fin l → Fin l := fun i => ⟨(((b + (i : ℕ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩
  have hf : ∀ i, (((f i : ℕ) : ℤ) : ZMod l) = (((b + (i : ℕ) * d) * d : ℤ) : ZMod l) := by
    intro i
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hinj : Function.Injective f := by
    intro i i' h
    have h2 := congrArg (fun x : Fin l => (((x : ℕ) : ℤ) : ZMod l)) h
    simp only [hf] at h2
    push_cast at h2
    have h3 : ((i : ℕ) : ZMod l) = ((i' : ℕ) : ZMod l) := by
      linear_combination (a * a) * h2 - ((i : ℕ) - (i' : ℕ) : ZMod l) * (d * a + 1) * had
    have h4 := congrArg ZMod.val h3
    rw [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt i'.2] at h4
    exact Fin.ext h4
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  set j : ℤ := ((f i : ℕ) : ℤ) with hj
  set x : ℤ := ((i : ℕ) : ℤ) with hx
  have hdvd : (l : ℤ) ∣ b + x * d - j * (a + x * c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp
    have hj' := hf i
    rw [← hj] at hj'
    have hxc : (x : ZMod l) = ((i : ℕ) : ZMod l) := by rw [hx, Int.cast_natCast]
    push_cast
    rw [hj', hcl, hxc]
    push_cast
    linear_combination (-(b : ZMod l) - x * d) * had + (d : ZMod l) * (d * a - 1) * hxc
  obtain ⟨e, he⟩ := hdvd
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a + x * c, e; l * c, d - j * c]
  have hMdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨M, hMdet⟩
  have hg : g ∈ Lev N l := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · show ((a + x * c : ℤ) : ZMod N) = 1
        push_cast; rw [ha1', hcN']; ring
      · show ((d - j * c : ℤ) : ZMod N) = 1
        push_cast; rw [hd1', hcN']; ring
      · show (((l : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast; rw [hcN']; ring
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((l : ℤ) * c : ℤ) : ZMod l) = 0
      push_cast; simp
  refine ⟨⟨g, hg⟩, ?_⟩
  show ulFam l i * mat γ = M * ulFam l (f i)
  rw [hmat]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [ulFam, M, Matrix.mul_apply, Fin.sum_univ_two, ← hj, ← hx] <;>
    first | ring1 | linear_combination he

end GlobalTheory.HeckeFamilyMatrices
end
