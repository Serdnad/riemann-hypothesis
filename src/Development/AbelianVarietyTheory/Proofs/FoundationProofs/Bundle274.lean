module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle269
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
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
public import Mathlib.GroupTheory.Schreier
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem smul_cls_eq_cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) (f : X.Kˣ) :
    r • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n r).val) := by
  have hker : r - ((PadicInt.toZModPow n r).val : ℤ_[l]) ∈ idl l ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  unfold Tower.cls
  have hk : ∀ (k : ℕ) (y : Additive X.Kˣ), (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • y) = k • ((1 : ℤ_[l]) ⊗ₜ[ℤ] y) :=
    fun k y => map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) k y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ofMul_pow, hk,
    ← Nat.cast_smul_eq_nsmul ℤ_[l], ← sub_smul]
  exact Submodule.smul_mem_smul hker Submodule.mem_top

theorem isRoot_pow (X : Tower Ω ε) {m : ℕ} {f : X.Kˣ} {a b : ℂ → ℂ} (h : H3.IsRoot X m f a b) (k : ℕ) :
    H3.IsRoot X m (f ^ k) (a ^ k) (b ^ k) := by
  obtain ⟨ha, hb, hb0, hab⟩ := h
  refine ⟨ha.pow k, hb.pow k, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI := hs_codiscrete_neBot
      rw [pow_zero] at h0
      exact one_ne_zero (α := Mero) h0
    · apply hb0
      have h1 : (b ^ k) =ᶠ[Filter.codiscreteWithin Hs] 0 := Filter.Germ.coe_eq.1 h0
      have h2 : b =ᶠ[Filter.codiscreteWithin Hs] 0 := by
        filter_upwards [h1] with z hz
        exact pow_eq_zero_iff hk.ne' |>.1 hz
      exact Filter.Germ.coe_eq.2 h2
  · rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul,
      mul_comm k m, pow_mul, pow_mul, ← mul_pow, hab]

theorem exp_val_mul (l n : ℕ) [Fact l.Prime] (s t : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * ((s * t).val : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / ((l : ℂ) ^ n)) ^ s.val := by
  have hl : (l : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((s.val * t.val / l ^ n : ℕ) : ℤ), ?_⟩
  have h : (((s * t).val : ℕ) : ℂ) + (l : ℂ) ^ n * ((s.val * t.val / l ^ n : ℕ) : ℂ) = (s.val : ℂ) * t.val := by
    rw [ZMod.val_mul]
    exact_mod_cast Nat.mod_add_div (s.val * t.val) (l ^ n)
  rw [Int.cast_neg, Int.cast_natCast]
  field_simp
  linear_combination h

theorem kum_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) {x : X.Khat l}
    {χ : SL(2, ℤ) → ZMod (l ^ n)} (h : H3.Kum X l n x χ) :
    H3.Kum X l n (r • x) (fun δ => PadicInt.toZModPow n r * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, hroot, hδ⟩ := h
  refine ⟨f ^ (PadicInt.toZModPow n r).val, a ^ (PadicInt.toZModPow n r).val, b ^ (PadicInt.toZModPow n r).val,
    M, hM, ?_, isRoot_pow X hroot _, fun δ hd z hz => ?_⟩
  · rw [map_smul, hx, smul_cls_eq_cls_pow]
  · rw [exp_val_mul]
    simp only [Pi.pow_apply]
    rw [← mul_pow, ← mul_pow, ← mul_pow, hδ δ hd z hz]

theorem btZ_smul (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) (h : BtZ X N l b c) : BtZ X N l (r • b) (r • c) := by
  intro n u
  obtain ⟨χ, hχ, M, hM, hc⟩ := h n u
  refine ⟨fun δ => PadicInt.toZModPow n r * χ δ, kum_smul X l n r hχ, M, hM, fun δ hd => ?_⟩
  have := hc δ hd
  simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  rw [this]

end GlobalTheory.KZ.BettiB
end
end

section

open scoped MatrixGroups TensorProduct Pointwise
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gam_fg (N l : ℕ) [Fact l.Prime] (hN : 0 < N) : Group.FG (Gam N l) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  exact Subgroup.fg_of_index_ne_zero _

theorem module_finite_z1_padicInt : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  intro N l w _ hN
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.1 (gam_fg N l hN)
  let t : Set (Gam N l) := insert 1 (s ∪ s⁻¹)
  have ht : t.Finite := (hfin.union hfin.inv).insert 1
  haveI : Finite t := ht.to_subtype
  haveI : Module.Finite ℤ_[l] (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  let L : Z1 N l w →ₗ[ℤ_[l]] (t → MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    { toFun := fun c i => ⟨c.1 i.1, c.2.1 i.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun c hc => ?_)
  have h0 : ∀ γ ∈ t, c.1 γ = 0 := fun γ hγ => congrArg Subtype.val (congrFun hc ⟨γ, hγ⟩)
  apply Subtype.ext
  funext γ
  have hγ : γ ∈ Submonoid.closure (s ∪ s⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hs]; trivial
  show c.1 γ = 0
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact h0 x (Set.mem_insert_of_mem _ hx)
  | one => exact h0 1 (Set.mem_insert _ _)
  | mul x y _ _ hx hy => rw [c.2.2 x y, hx, hy, map_zero, add_zero]

end GlobalTheory.KZ.BettiB
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB.Add

theorem mem_gamma_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem exp_val_add (l n : ℕ) [Fact l.Prime] (x y : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl⟩
  have hm : (l : ℂ) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.2 hl)
  have hs := Nat.mod_add_div (x.val + y.val) (l ^ n)
  rw [ZMod.val_add, ← Complex.exp_add]
  generalize (x.val + y.val) % l ^ n = r at hs ⊢
  generalize (x.val + y.val) / l ^ n = q at hs
  have hc : (r : ℂ) + (l : ℂ) ^ n * (q : ℂ) = (x.val : ℂ) + (y.val : ℂ) := by exact_mod_cast hs
  have key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (l : ℂ) ^ n + 2 * Real.pi * Complex.I * (y.val : ℂ) / (l : ℂ) ^ n =
      2 * Real.pi * Complex.I * (r : ℂ) / (l : ℂ) ^ n + (q : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← add_div, ← mul_add, ← hc]
    field_simp
  rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected
  rcases (hb.analyticOnNhd hopen).eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h0 | h0
  · refine absurd ?_ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h0 hz
  · exact h0

theorem germ_mul_ne_zero {b b' : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (h : (b : Mero) ≠ 0) (h' : (b' : Mero) ≠ 0) : ((b * b' : ℂ → ℂ) : Mero) ≠ 0 := by
  haveI := hs_codiscrete_neBot
  intro H
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at H
  obtain ⟨z, h1, h2, h3⟩ := ((eventually_ne_zero hb h).and ((eventually_ne_zero hb' h').and H)).exists
  exact mul_ne_zero h1 h2 h3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ) :
    X.cls l n (f * f') = X.cls l n f + X.cls l n f' := by
  unfold Tower.cls
  rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

theorem kum_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {x x' : X.Khat l} {χ χ' : SL(2, ℤ) → ZMod (l ^ n)}
    (h : H3.Kum X l n x χ) (h' : H3.Kum X l n x' χ') : H3.Kum X l n (x + x') (χ + χ') := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ := h
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩ := h'
  refine ⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_,
    ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩
  · rw [map_add (f := _), hx, hx', cls_mul]
  · rw [Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']
    ring
  · intro δ hδM z hz
    have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM) z hz
    have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM) z hz
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [exp_val_add]
    linear_combination (a' (mob (ofSL δ) z) * b' z) * e1 +
      (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        (a z * b (mob (ofSL δ) z))) * e2

theorem btZ_add : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (b b' : X.Fn l) (c c' : Gam N l → MvPolynomial (Fin 2) ℤ_[l]),
    BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := by
  intro Ω _ _ ε X N l _ b b' c c' h h' n u
  obtain ⟨χ, hχ, M, hM, hδ⟩ := h n u
  obtain ⟨χ', hχ', M', hM', hδ'⟩ := h' n u
  refine ⟨χ + χ', kum_add X l n hχ hχ', M * M', Nat.mul_pos hM hM', fun δ hδM => ?_⟩
  have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM)
  have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM)
  simp only [Pi.add_apply, map_add (f := _)]
  rw [e1, e2]

end GlobalTheory.KZ.BettiB.Add
end
end

section

set_option autoImplicit false

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.DIV NumberField GlobalTheory.PresBasic

namespace GlobalTheory.TraceIncl

section Scalar

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem exists_int_smul (f : V →ₛₗ[σ] W) (hinj : Function.Injective f)
    (hs : ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c) {x y : V} {c : ℂˣ} (hc : IsOfFinOrder c)
    (h : f x = (c : ℂ) • f y) : ∃ a : 𝓞 K, x = (a : K) • y := by
  rcases hs x y c h with rfl | ⟨a, ha⟩
  · exact ⟨0, hinj (by rw [h]; simp)⟩
  · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have h1 : a ^ n = 1 := σ.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one])
    refine ⟨⟨a, IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)⟩, hinj ?_⟩
    rw [h, map_smulₛₗ, ← ha]
    rfl

theorem inj_and_rat_of_li (f : V →ₛₗ[σ] W)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => f (b k)) :
    Function.Injective f ∧ ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c := by
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra h0
    have := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0
    exact this hx
  refine ⟨hinj, fun x y c h => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  have hy' : f y ≠ 0 := fun h0 => hy (hinj (by rw [h0, map_zero]))
  by_cases hl : LinearIndependent K ![y, x]
  · have h2 : LinearIndependent ℂ ![f y, f x] := by
      convert hli 2 _ hl using 1
      funext k
      fin_cases k <;> rfl
    exact absurd h.symm ((LinearIndependent.pair_iff' hy').1 h2 c)
  · rw [LinearIndependent.pair_iff' hy] at hl
    push Not at hl
    obtain ⟨a, rfl⟩ := hl
    rw [map_smulₛₗ] at h
    exact Or.inr ⟨a, smul_left_injective ℂ hy' h⟩

end Scalar

variable {G Γ W K X : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] [AddCommGroup X] [Module ℂ X] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ) (k : G → W →ₗ[ℂ] X)

theorem coef_rat (x y : S.V) (c : ℂ) (h : P.coef x = c • P.coef y) : y = 0 ∨ ∃ a, σ a = c := by
  by_cases hy : y = 0
  · exact Or.inl hy
  obtain ⟨j, hj⟩ : ∃ j, S.bV.repr y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (S.bV.repr.injective (by ext j; simp [hn j]))
  have e := congrArg (fun w => (bW P).repr w j) h
  simp only [map_smul, Finsupp.smul_apply, repr_coef, smul_eq_mul] at e
  refine Or.inr ⟨S.bV.repr x j / S.bV.repr y j, ?_⟩
  rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hj)]

theorem card_stab (γ : Γ) (y : G) (j : J) : Nat.card (stab ι J (ι γ * y * j)) = Nat.card (stab ι J y) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  rw [mem_stab, mem_stab]
  have e : (ι γ * y * j)⁻¹ * ι δ * (ι γ * y * j) = (j : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * j := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right j.2, J.mul_mem_cancel_left (J.inv_mem j.2)]

theorem sum_translate (κ : G) (h1 : ∀ j ∈ J, κ * j * κ⁻¹ ∈ J) (h2 : ∀ j ∈ J, κ⁻¹ * j * κ ∈ J) (Φ : G → X)
    (hΦ : ∀ γ h (j : J), Φ (ι γ * h * j) = Φ h) :
    ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c * κ) = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c) := by
  have hinj : Function.Injective fun c => P.decC (P.y c * κ) := by
    intro c c' e
    have e1 := P.dec_spec (P.y c * κ)
    have e2 := P.dec_spec (P.y c' * κ)
    simp only at e
    rw [← e] at e2
    generalize P.decC (P.y c * κ) = d at e1 e2
    generalize P.decG (P.y c * κ) = γ at e1
    generalize P.decK (P.y c * κ) = j at e1
    generalize P.decG (P.y c' * κ) = γ' at e2
    generalize P.decK (P.y c' * κ) = j' at e2
    refine (P.reps (P.y c')).unique ⟨γ' * γ⁻¹, ⟨_, h1 _ (j⁻¹ * j').2⟩, ?_⟩ ⟨1, 1, by simp⟩
    rw [eq_mul_inv_of_mul_eq e1, eq_mul_inv_of_mul_eq e2]
    simp [mul_assoc]
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun c => ?_
  have e1 := P.dec_spec (P.y c * κ)
  have e2 : stab ι J (P.y c * κ) = stab ι J (P.y c) := by
    ext δ
    rw [mem_stab, mem_stab]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · convert h1 _ h using 1
      group
    · convert h2 _ h using 1
      group
  rw [← e2]
  conv_lhs => rw [e1, card_stab, hΦ]

def clSum : S.Forms →ₛₗ[σ] X where
  toFun f := ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.extL f (P.y c))
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [map_smulₛₗ, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _

theorem clSum_apply (f : S.Forms) :
    clSum P k f = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.coef ((f : S.Cl → S.V) c)) :=
  Finset.sum_congr rfl fun c _ => by rw [ClassPres.extL_apply, ext_y]

structure KernelLaws (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J : Subgroup G} (χ : J →* ℂˣ) (k : G → W →ₗ[ℂ] X) : Prop where
  aut : ∀ γ h w, k (ι γ * h) (ρ γ w) = k h w
  typ : ∀ h (j : J) w, k (h * j) w = (((χ j)⁻¹ : ℂˣ) : ℂ) • k h w

variable {k}

theorem KernelLaws.dec (hk : KernelLaws ι ρ χ k) (γ : Γ) (h : G) (j : J) (w : W) :
    (χ j : ℂ) • k (ι γ * h * j) (ρ γ w) = k h w := by
  rw [hk.typ, hk.aut, smul_smul, Units.mul_inv, one_smul]

theorem KernelLaws.form (hk : KernelLaws ι ρ χ k) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (γ : Γ) (h : G) (j : J) :
    k (ι γ * h * j) (F (ι γ * h * j)) = k h (F h) := by
  rw [hF γ h j, map_smul, hk.dec]

theorem clSum_avgForm (hk : KernelLaws ι ρ χ k) (c : S.Cl) (x : S.V) :
    clSum P k (avgForm S c x) = k (P.y c) (P.coef x) := by
  classical
  rw [clSum_apply, Finset.sum_eq_single c]
  · have hg : ∀ g : S.Gam c, k (P.y c) (P.coef (S.ρ c g x)) = k (P.y c) (P.coef x) := fun g => by
      have := hk.dec (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g)) (P.coef x)
      rwa [stabK_spec, ← map_smul, ← P.coef_act] at this

    simp only [avgForm, Pi.single_eq_same, map_sum, hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  · intro c' _ hc
    simp [avgForm, Pi.single_eq_of_ne hc]
  · simp

theorem clSum_act (hk : KernelLaws ι ρ χ k) {Q : Subgroup G} {ch : Q →* ℂˣ} {G0 : Type} [Group G0]
    {act : Representation K G0 S.Forms} (T : ActTie ι P Q ch act) (hJ : J ≤ Q) (a : G0 → X →ₗ[ℂ] X)
    (ha : ∀ (q : Q) h w, a (T.red q) (k (h * q) w) = (((ch q)⁻¹ : ℂˣ) : ℂ) • k h w) (g : G0) (f : S.Forms) :
    clSum P k (act g f) = a g (clSum P k f) := by
  obtain ⟨q, rfl⟩ := T.red_surj g
  have hn : ∀ (q : Q), ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J := fun q j hj =>
    (T.red_ker (q * ⟨j, hJ hj⟩ * q⁻¹)).1 (by
      rw [map_mul, map_mul, (T.red_ker ⟨j, hJ hj⟩).2 hj, mul_one, ← map_mul, mul_inv_cancel, map_one])
  have key := sum_translate P (q : G) (hn q) (fun j hj => by simpa using hn q⁻¹ j hj)
    (fun h => k h (P.ext f h)) (hk.form (extMem P f))
  change ∑ c, _ • k (P.y c) (P.ext _ (P.y c)) = a _ (∑ c, _ • k (P.y c) (P.ext _ (P.y c)))

  rw [← key, map_sum, T.act_eq _ q rfl]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ha, g0Act, map_smul]

structure LatSys (r : Γ → S.V →ₗ[K] S.V) (L : G → Submodule (𝓞 K) S.V) : Prop where
  coef : ∀ γ x, P.coef (r γ x) = ρ γ (P.coef x)
  move : ∀ γ h (j : J), ∀ x ∈ L h, r γ x ∈ L (ι γ * h * j)
  nab : ∀ c, L (P.y c) = S.Nab c

variable {P} {r : Γ → S.V →ₗ[K] S.V} {L : G → Submodule (𝓞 K) S.V}

theorem LatSys.avg_mem (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) {c : S.Cl} {x : S.V} (hx : x ∈ S.Nab c) (c' : S.Cl) :
    (avgForm S c x : S.Cl → S.V) c' ∈ S.Nab c' := by
  classical
  by_cases h : c' = c
  · subst h
    simp only [avgForm, Pi.single_eq_same]
    refine Submodule.sum_mem _ fun g _ => ?_
    have h1 := hL.move (P.stabI c' g : Γ) (P.y c') (stabK ι (P.stabI c' g)) x (hL.nab c' ▸ hx)
    rw [stabK_spec, hL.nab] at h1
    obtain ⟨a, ha⟩ := exists_int_smul P.coef (coef_injective P) (coef_rat P) (hχ _)
      ((P.coef_act c' g x).trans (by rw [← hL.coef]))
    rw [ha]
    have h2 := Submodule.smul_mem _ a h1
    rwa [← algebraMap_smul K a] at h2
  · simp [avgForm, Pi.single_eq_of_ne h]

theorem LatSys.exists_trace (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) (hk : KernelLaws ι ρ χ k) {h : G} {x : S.V}
    (hx : x ∈ L h) : ∃ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) ∧
      ∃ j : J, k h (P.coef x) = (((χ j)⁻¹ : ℂˣ) : ℂ) • clSum P k f := by
  obtain ⟨c, ⟨γ, j, rfl⟩, -⟩ := P.reps h
  have h1 := hL.move γ⁻¹ _ j⁻¹ x hx
  rw [show ι γ⁻¹ * (ι γ * P.y c * j) * (j⁻¹ : J) = P.y c by simp [mul_assoc], hL.nab] at h1
  refine ⟨avgForm S c (r γ⁻¹ x), hL.avg_mem hχ h1, j, ?_⟩
  rw [clSum_avgForm P hk, ← hk.dec γ (P.y c) j, smul_smul, Units.inv_mul, one_smul, hL.coef, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.TraceIncl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | exact GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | (intros; apply GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul <;> assumption)
end
