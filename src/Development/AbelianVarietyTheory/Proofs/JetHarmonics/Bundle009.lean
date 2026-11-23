module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
public import Mathlib.Analysis.Normed.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle006
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
import Mathlib.RingTheory.PicardGroup
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
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace


set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add (f := _), map_add (f := _), h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩


set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)

end Comparison₂

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
end
end

section

noncomputable section

namespace GlobalTheory.ConvSer.Bridge

def unitExp : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun ν := ν ()
  left_inv n := by simp
  right_inv ν := by ext; simp

variable {K : Type} [NormedField K]

theorem powerSeriesConvergentSubstMv_eq_mv {τ : Type} (s : MvPowerSeries τ K) (f : PowerSeries K) :
    csub1 s f = csub (fun _ : Unit => s) f := by
  ext μ
  change ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n) =
    ∑' ν : Unit →₀ ℕ, MvPowerSeries.coeff ν f * MvPowerSeries.coeff μ (∏ i : Unit, s ^ ν i)
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum (f : PowerSeries K) (t : K) : ev1 f t = ev f (fun _ : Unit => t) := by
  unfold ev1 ev
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt (f : PowerSeries K) (t a : K) : PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a := by
  unfold PowerSeriesHasSumAt HS
  rw [← unitExp.hasSum_iff]
  have h : (fun ν : Unit →₀ ℕ => MvPowerSeries.coeff ν f * ∏ i : Unit, t ^ ν i) ∘ unitExp =
      fun n : ℕ => PowerSeries.coeff n f * t ^ n := by
    funext n
    simp [unitExp]
  rw [h]

theorem csub_C {σ τ : Type} [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K) :
    csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x) := by
  have hC : ∀ ν : σ →₀ ℕ, (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) =
      MvPowerSeries.C (∏ i, x i ^ ν i) := fun ν => by simp [map_prod, map_pow]
  ext μ
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) = _
  simp only [hC]
  by_cases h : μ = 0
  · subst h
    simp only [MvPowerSeries.coeff_zero_C]
    rfl
  · simp only [MvPowerSeries.coeff_C_of_ne_zero h, mul_zero, tsum_zero]

theorem shift1_eq_csub (F : MvPowerSeries (Fin 2) K) (y : K) :
    shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F := by
  ext m
  have hc : ∀ p : PowerSeries K, MvPowerSeries.coeff (unitExp m) p = PowerSeries.coeff m p :=
    fun p => by simp [unitExp]
  change PowerSeries.coeff m (shift1 F y) = ∑' ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F *
    MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i)
  have hterm : ∀ ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F * MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i) =
      MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0) := by
    intro ν
    rw [hc, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_pow, mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_C_mul_X_pow]
  simp only [hterm]
  rw [shift1, PowerSeries.coeff_mk]
  have hinj : Function.Injective
      (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro b b' h
    have h1 := congrArg (fun ν : Fin 2 →₀ ℕ => ν 1) h
    simpa using h1
  have hsupp : Function.support
      (fun ν : Fin 2 →₀ ℕ => MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0)) ⊆
      Set.range (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro ν hν
    have h0 : m = ν 0 := by
      by_contra h
      exact hν (by simp [h])
    refine ⟨ν 1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  refine Eq.trans ?_ (hinj.tsum_eq hsupp)
  refine tsum_congr fun b => ?_
  simp

theorem csub_eq_subst {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    csub a S = MvPowerSeries.subst a S := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  ext μ
  rw [MvPowerSeries.coeff_subst hs, ← tsum_eq_finsum (L := SummationFilter.unconditional (σ →₀ ℕ))
    (MvPowerSeries.coeff_subst_finite hs S μ)]
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, a i ^ ν i) = _
  refine tsum_congr fun ν => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

theorem powerSeriesConvergentSubstMv_eq_subst {τ : Type} (a : MvPowerSeries τ K) (f : PowerSeries K)
    (ha : MvPowerSeries.constantCoeff a = 0) : csub1 a f = f.subst a := by
  rw [powerSeriesConvergentSubstMv_eq_mv, csub_eq_subst _ _ (fun _ => ha)]
  rfl

theorem csub_bridge : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  intro K _
  exact ⟨fun _ s f => powerSeriesConvergentSubstMv_eq_mv s f, fun f t => powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum f t, fun f t a => powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt f t a,
    fun _ _ _ S x => csub_C S x, fun F y => shift1_eq_csub F y,
    fun _ _ _ a S ha => csub_eq_subst a S ha, fun _ a f ha => powerSeriesConvergentSubstMv_eq_subst a f ha⟩

end GlobalTheory.ConvSer.Bridge
end
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.SubstSum

variable {K : Type} [NormedField K] [IsUltrametricDist K] {τ : Type}

def Decay (θ : ℝ) (m : ℕ) (S : MvPowerSeries τ K) : Prop :=
  ∀ μ : τ →₀ ℕ, ‖MvPowerSeries.coeff μ S‖ ≤ θ ^ (m - μ.degree)

omit [IsUltrametricDist K] in
theorem decay_one (θ : ℝ) : Decay θ 0 (1 : MvPowerSeries τ K) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem Decay.mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {m n : ℕ} {S T : MvPowerSeries τ K}
    (hS : Decay θ m S) (hT : Decay θ n T) : Decay θ (m + n) (S * T) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 _) fun p hp => ?_
  have hp' : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 S‖ * ‖MvPowerSeries.coeff p.2 T‖
      ≤ θ ^ (m - p.1.degree) * θ ^ (n - p.2.degree) :=
        mul_le_mul (hS _) (hT _) (norm_nonneg _) (pow_nonneg h0 _)
    _ = θ ^ ((m - p.1.degree) + (n - p.2.degree)) := (pow_add _ _ _).symm
    _ ≤ θ ^ (m + n - μ.degree) := by
        apply pow_le_pow_of_le_one h0 h1
        rw [← hp', map_add (f := _)]
        omega

theorem Decay.pow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {S : MvPowerSeries τ K}
    (hS : Decay θ 1 S) (n : ℕ) : Decay θ n (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact decay_one θ
  | succ n ih => rw [pow_succ]; exact ih.mul h0 h1 hS

theorem decay_prod {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {σ : Type} (t : Finset σ)
    (s : σ → MvPowerSeries τ K) (hs : ∀ i, Decay θ 1 (s i)) (ν : σ → ℕ) :
    Decay θ (∑ i ∈ t, ν i) (∏ i ∈ t, s i ^ ν i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact decay_one θ
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Decay.pow h0 h1 (hs a) (ν a)).mul h0 h1 ih

omit [IsUltrametricDist K] in
theorem decay_of_small {θ : ℝ} {S : MvPowerSeries τ K} (hS : Intg S)
    (hθ : ‖MvPowerSeries.constantCoeff S‖ ≤ θ) : Decay θ 1 S := by
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hθ
  · have hd : μ.degree ≠ 0 := (Finsupp.degree_eq_zero_iff μ).not.2 hμ
    have : 1 - μ.degree = 0 := by omega
    rw [this, pow_zero]
    exact hS μ

theorem exists_decay {σ : Type} [Fintype σ] (s : σ → MvPowerSeries τ K) (hs : ∀ i, Small (s i)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (ν : σ →₀ ℕ) (μ : τ →₀ ℕ),
      ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ θ ^ (ν.degree - μ.degree) := by
  classical
  set θ : ℝ := ((Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊ : NNReal) : ℝ)
    with hθdef
  have hsi : ∀ i, Intg (s i) ∧ ‖MvPowerSeries.constantCoeff (s i)‖ < 1 := hs
  have h0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hlt : θ < 1 := by
    have : (Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊) < 1 :=
      (Finset.sup_lt_iff (by simp)).2 fun i _ => by
        have h := (hsi i).2
        rw [← coe_nnnorm] at h
        exact_mod_cast h
    exact_mod_cast this
  have hle : ∀ i, ‖MvPowerSeries.constantCoeff (s i)‖ ≤ θ := fun i => by
    rw [hθdef, ← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊)
      (Finset.mem_univ i)
  refine ⟨θ, h0, hlt, fun ν μ => ?_⟩
  have h := decay_prod h0 hlt.le Finset.univ s (fun i => decay_of_small (hsi i).1 (hle i)) ν μ
  rwa [← Finsupp.degree_eq_sum] at h

theorem tendsto_degree {σ : Type} [Fintype σ] :
    Filter.Tendsto (fun ν : σ →₀ ℕ => ν.degree) Filter.cofinite Filter.atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (0 : σ →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun _ => b)).subset
    fun ν hν => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hν
  refine Set.mem_Icc.2 ⟨zero_le, Finsupp.le_def.2 fun i => ?_⟩
  simpa using (Finsupp.le_degree i ν).trans hν.le

end GlobalTheory.ConvSer.SubstSum


open GlobalTheory.ConvSer.SubstSum in
theorem GlobalTheory.ConvSer.csub_hasSum_and_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  intro K _ _ _ σ τ _ s S hs hS
  obtain ⟨θ, h0, h1, hθ⟩ := exists_decay s hs
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C := hS
  set t : (τ →₀ ℕ) → (σ →₀ ℕ) → K := fun μ ν =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i) with ht
  have hprod1 : ∀ (ν : σ →₀ ℕ) μ, ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ 1 := fun ν μ =>
    (hθ ν μ).trans (pow_le_one₀ h0 h1.le)
  have hsum : ∀ μ, HasSum (t μ) (MvPowerSeries.coeff μ (csub s S)) := by
    intro μ
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have htend : Filter.Tendsto (t μ) Filter.cofinite (nhds 0) := by
      refine squeeze_zero_norm (a := fun ν => max C 0 * θ ^ (ν.degree - μ.degree))
        (fun ν => ?_) ?_
      · rw [ht, norm_mul]
        exact mul_le_mul ((hC ν).trans (le_max_left _ _)) (hθ ν μ) (norm_nonneg _) hC0
      · have h : Filter.Tendsto (fun ν : σ →₀ ℕ => θ ^ (ν.degree - μ.degree))
            Filter.cofinite (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
            ((Filter.tendsto_sub_atTop_nat μ.degree).comp tendsto_degree)
        simpa using h.const_mul (max C 0)
    have heq : MvPowerSeries.coeff μ (csub s S) = ∑' ν, t μ ν := rfl
    rw [heq]
    exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htend).hasSum
  have hbound : ∀ B : ℝ, 0 ≤ B → (∀ μ ν, ‖t μ ν‖ ≤ B) →
      ∀ μ, ‖MvPowerSeries.coeff μ (csub s S)‖ ≤ B := fun B hB h μ => by
    rw [← (hsum μ).tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB (h μ)
  have hterm : ∀ μ ν, ‖t μ ν‖ ≤ ‖MvPowerSeries.coeff ν S‖ := fun μ ν => by
    rw [ht, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hprod1 ν μ)
  have hintg : Intg S → Intg (csub s S) := fun hI =>
    hbound 1 zero_le_one fun μ ν => (hterm μ ν).trans (hI ν)
  refine ⟨hsum, ?_, hintg, fun hI h00 => ?_⟩
  · exact Exists.intro (max C 0) (hbound _ (le_max_right _ _) fun μ ν =>
      (hterm μ ν).trans ((hC ν).trans (le_max_left _ _)))
  · have hc : ‖MvPowerSeries.coeff 0 (csub s S)‖ ≤ θ := by
      rw [← (hsum 0).tsum_eq]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg h0 fun ν => ?_
      by_cases hν : ν = 0
      · subst hν
        simp [ht, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h00, h0]
      · rw [ht, norm_mul]
        have hd : 1 ≤ ν.degree - (0 : τ →₀ ℕ).degree := by
          have a := (Finsupp.degree_eq_zero_iff ν).not.2 hν
          rw [map_zero]
          omega
        calc ‖MvPowerSeries.coeff ν S‖ * ‖MvPowerSeries.coeff 0 (∏ i, s i ^ ν i)‖
            ≤ 1 * θ := mul_le_mul (hI ν)
              ((hθ ν 0).trans ((pow_le_pow_of_le_one h0 h1.le hd).trans_eq (pow_one θ)))
              (norm_nonneg _) zero_le_one
          _ = θ := one_mul θ
    exact And.intro (hintg hI)
      (by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc.trans_lt h1)
end

section

open Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.re_inner_le_on_image_of_intertwining' : ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T] [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T) (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) → (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) → ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  first | exact @GlobalTheory.re_inner_le_on_image_of_intertwining | exact GlobalTheory.re_inner_le_on_image_of_intertwining | (intros; apply GlobalTheory.re_inner_le_on_image_of_intertwining <;> assumption)
end

section

open Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  first | exact @GlobalTheory.sum_norm_add_sq_le_of_bounds | exact GlobalTheory.sum_norm_add_sq_le_of_bounds | (intros; apply GlobalTheory.sum_norm_add_sq_le_of_bounds <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem finite_augmented_connected_part_localisation :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by
  first
  | exact @_root_.GlobalTheory.MonicSeparableProduct.main
  | exact _root_.GlobalTheory.MonicSeparableProduct.main
  | (apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicSeparableProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicSeparableProduct.main ..)

end GlobalTheory
end
