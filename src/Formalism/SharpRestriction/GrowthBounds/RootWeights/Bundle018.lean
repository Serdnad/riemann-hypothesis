module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle015
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IrreducibleStableContainsEqTop
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
import Mathlib.RingTheory.LocalProperties.Reduced
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monomial_eq_smul_basis {K σ : Type} [CommRing K] (m : σ →₀ ℕ) (c : K) :
    monomial m c = c • (basisMonomials σ K m) := by
  rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem divided_power_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    divPow K LL S a b k (monomial m c) = c • divPowMono K LL S a b k m := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold divPow
  rw [Module.Basis.constr_basis]

theorem binomial_operator_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    binomPol K LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : K)) := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold binomPol
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

def dividedPowerTermCoefficient {ι : Type} {n : ℕ} (LL : Letters ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (l : ι) : ℤ :=
  if LL.vec l then ((m (l, b)).choose (f l) : ℤ) else (-1 : ℤ) ^ (f l) * ((m (l, a)).choose (f l) : ℤ)

open Classical in
theorem divided_power_monomial_expansion {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    c • divPowMono K LL S a b k m =
      ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
        monomial ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
          + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l))
          (c * ((∏ l ∈ f.support, dividedPowerTermCoefficient LL a b m f l : ℤ) : K)) := by
  unfold divPowMono
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.smul_monomial, smul_eq_mul, Int.cast_prod]
  congr 2
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold dividedPowerTermCoefficient
  split_ifs <;> push_cast <;> rfl

theorem integral_formula_stability_holds {p : ℕ} (hp : p.Prime) (hV : ValuationProperties p O) : PolynomialIntegralFormPreservesLattices p O := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S
  refine ⟨?_, ?_⟩
  · intro u hu x hx
    refine integral_poly_linear_map_closed u (fun m => ?_) x hx
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [one_mul]
      exact integer_monomial_mem_integral _ _
    · rw [binomial_operator_monomial, one_mul]
      exact integer_monomial_mem_integral _ _
  · intro u hu F hF
    refine fock_lattice_linear_map_closed hV u (fun m c hmc => ?_) F hF
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine fock_lattice_sum_mem hV _ _ fun f _ => ?_
      refine fock_lattice_monomial_rescale hV m _ c _ hmc ?_
      exact divided_power_padic_valuation_bound p (fun l => if LL.vec l then (l, b) else (l, a))
        (fun l => if LL.vec l then (l, a) else (l, b))
        (fun l => by split_ifs <;> rfl) (fun l => by split_ifs <;> rfl)
        (fun l => by split_ifs <;> simp [hab, Ne.symm hab]) m f (dividedPowerTermCoefficient LL a b m f)
        (fun l => by unfold dividedPowerTermCoefficient; split_ifs <;> simp [Int.natAbs_mul, Int.natAbs_pow])
    · rw [binomial_operator_monomial]
      exact fock_lattice_monomial_rescale hV m m c _ hmc (Or.inr (Nat.le_add_left _ _))

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ}

def cr_Pos (n : ℕ) : AddSubmonoid (Fin n → ℤ) :=
  AddSubmonoid.closure {β | ∃ a b : Fin n, a < b ∧ β = rootW a b}

def cr_h (ν : Fin n → ℤ) : ℤ := ∑ a : Fin n, ∑ b : Fin n, if a < b then ν a - ν b else 0

def cr_c (ν : Fin n → ℤ) : ℤ := ∑ a, ν a ^ 2 + cr_h ν

theorem cr_ht_add (x y : Fin n → ℤ) : weightHeight' (x + y) = weightHeight' x + weightHeight' y := by
  simp only [weightHeight', Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem cr_ht_zero : weightHeight' (0 : Fin n → ℤ) = 0 := by simp [weightHeight']

theorem cr_ht_root (a b : Fin n) (h : a < b) : 0 < weightHeight' (rootW a b) := by
  have := v2rep_ht_root (0 : Fin n → ℤ) a b h
  rwa [zero_add, cr_ht_zero] at this

theorem cr_h_eq (ν : Fin n → ℤ) : cr_h ν = ∑ a : Fin n, ((n : ℤ) - 1 - 2 * (a.val : ℤ)) * ν a := by
  classical
  have h1 : ∀ a : Fin n, (∑ b : Fin n, if a < b then ν a else 0) = ((n : ℤ) - 1 - (a.val : ℤ)) * ν a := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
    rw [this, Fin.card_Ioi, nsmul_eq_mul]
    have ha := a.isLt
    congr 1
    omega
  have h2 : ∀ b : Fin n, (∑ a : Fin n, if a < b then ν b else 0) = (b.val : ℤ) * ν b := by
    intro b
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b := by ext a; simp
    rw [this, Fin.card_Iio, nsmul_eq_mul]
  have h3 : cr_h ν = (∑ a : Fin n, ∑ b : Fin n, if a < b then ν a else 0) -
      ∑ a : Fin n, ∑ b : Fin n, if a < b then ν b else 0 := by
    rw [cr_h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [h3, Finset.sum_comm (f := fun a b : Fin n => if a < b then ν b else 0), Finset.sum_congr rfl fun a _ => h1 a,
    Finset.sum_congr rfl fun b _ => h2 b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_h_ht (ν : Fin n → ℤ) : cr_h ν = ((n : ℤ) - 1) * ∑ a, ν a + 2 * weightHeight' ν := by
  rw [cr_h_eq, weightHeight', Finset.mul_sum, mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_Pos_sum {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : ∑ a, β a = 0 := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, _, rfl⟩ := hx
    simp [rootW, Finset.sum_sub_distrib]
  | zero => simp
  | add x y _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]

theorem cr_Pos_ht {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : 0 ≤ weightHeight' β := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact (cr_ht_root a b hab).le
  | zero => rw [cr_ht_zero]
  | add x y _ _ hx hy => rw [cr_ht_add]; omega

theorem cr_Pos_pair {ν β : Fin n → ℤ} (hν : Dominant ν) (h : β ∈ cr_Pos n) : 0 ≤ ∑ a, ν a * β a := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    have : ∑ c, ν c * rootW a b c = ν a - ν b := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [this]
    have := hν hab.le
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    omega

theorem cr_root_mem (a b : Fin n) (h : a < b) : rootW a b ∈ cr_Pos n :=
  AddSubmonoid.subset_closure ⟨a, b, h, rfl⟩

theorem cr_c_lt {lam mu : Fin n → ℤ} (hl : Dominant lam) (hm : Dominant mu) (h : lam - mu ∈ cr_Pos n)
    (hpos : 0 < weightHeight' (lam - mu)) : cr_c mu < cr_c lam := by
  have h1 := cr_Pos_pair hl h
  have h2 := cr_Pos_pair hm h
  have h3 := cr_Pos_sum h
  have e1 : cr_h lam - cr_h mu = 2 * weightHeight' (lam - mu) := by
    have hh : cr_h (lam - mu) = 2 * weightHeight' (lam - mu) := by rw [cr_h_ht, h3]; ring
    rw [← hh, cr_h_eq, cr_h_eq, cr_h_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  have e2 : ∑ a, lam a ^ 2 - ∑ a, mu a ^ 2 = ∑ a, lam a * (lam - mu) a + ∑ a, mu a * (lam - mu) a := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  unfold cr_c
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def nablaToDeltaMaps (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O (Module.End (KK O) V) where
  carrier := {f | ∀ x ∈ Nabla (O := O) E lam v, f x ∈ Delta (O := O) E v}
  zero_mem' := fun x _ => by simp
  add_mem' := fun {f g} hf hg x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (hf x hx)

theorem nabla_integral_enveloping_stable (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) :
    UZStable (O := O) E (NablaSub (O := O) E lam v) := by
  intro u hu x hx u' hu'
  exact hx (u' * u) (Submonoid.mul_mem _ hu' (Submonoid.subset_closure hu))

theorem delta_integral_enveloping_stable (E : GLOps n (KK O) V) (v : V) : UZStable (O := O) E (Delta (O := O) E v) := by
  intro u hu x hx
  have hle : Delta (O := O) E v ≤ (Delta (O := O) E v).comap (u.restrictScalars O) := by
    unfold Delta
    rw [Submodule.span_le]
    rintro _ ⟨u', hu', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    exact Submodule.subset_span ⟨u * u', Submonoid.mul_mem _ (Submonoid.subset_closure hu) hu', rfl⟩
  exact hle hx

theorem adjoint_divided_power_expansion [CharZero (KK O)] (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) (f : Module.End (KK O) V) :
    divPowE (adjointEndAction E) a b k f =
      ∑ m ∈ range (k + 1), ((-1 : KK O) ^ (k - m)) • (divPowE E a b m * f * divPowE E a b (k - m)) := by
  have hc : Commute (LinearMap.mulLeft (KK O) (E a b)) ((-1 : KK O) • LinearMap.mulRight (KK O) (E a b)) :=
    (LinearMap.commute_mulLeft_right _ _).smul_right _
  have hsub : adjointEndAction E a b =
      LinearMap.mulLeft (KK O) (E a b) + (-1 : KK O) • LinearMap.mulRight (KK O) (E a b) := by
    rw [adjointEndAction, neg_one_smul, sub_eq_add_neg]
  simp only [divPowE]
  rw [hsub, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by simp at hm; omega
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_nsmul, map_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← Nat.cast_smul_eq_nsmul (KK O), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose (KK O) hmk]
  have h1 : ((m.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (((k - m).factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - m)
  have h3 : ((k.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem nabla_to_delta_maps_stable [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    (lam : Fin n → ℤ) (v : V) : UZStable (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := by
  intro u hu f hf x hx
  have hN := nabla_integral_enveloping_stable (O := O) E lam v
  have hD := delta_integral_enveloping_stable (O := O) E v
  have htop : ∀ z : V, z ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    intro z
    simp only [iSup_true]
    rw [hE.2.2]
    exact Submodule.mem_top
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · rw [adjoint_divided_power_expansion, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : divPowE E a b (k - m) x ∈ NablaSub (O := O) E lam v := hN _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) x hx
    have h2 : f (divPowE E a b (k - m) x) ∈ Delta (O := O) E v := hf _ h1
    have h3 := hD _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ h2
    have h4 := intCast_smul_mem_submodule (Delta (O := O) E v) ((-1 : ℤ) ^ (k - m)) h3
    simpa using h4
  · have hR : ∀ (m : ℕ) (μ ν : Fin n → ℤ) (z : V), z ∈ weightSp E μ →
        (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) z =
          (∏ j ∈ range m, ((μ a : KK O) - ((ν a : KK O) + j))) • z := by
      intro m μ ν z hz
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          (mem_weightSpace_iff_diag_scalar.1 hz) a, ← sub_smul, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]
    have hw : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        (binomE (adjointEndAction E) a k f) y = ∑ ij ∈ antidiagonal k,
          (((Ring.choose (-(ν a)) ij.2 : ℤ) : KK O)) • binomE E a ij.1 (f y) := by
      intro ν y hy
      have hadx : ∀ (g : Module.End (KK O) V) (c : KK O),
          ((adjointEndAction E a a - c • (1 : Module.End (KK O) (Module.End (KK O) V))) g) y =
            (E a a - ((ν a : KK O) + c) • (1 : Module.End (KK O) V)) (g y) := by
        intro g c
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, adjointEndAction_apply,
          Module.End.mul_apply, (mem_weightSpace_iff_diag_scalar.1 hy) a, map_smul, add_smul, LinearMap.add_apply]
        abel
      have hprod : ∀ (m : ℕ) (g : Module.End (KK O) V),
          (((List.range m).map fun j : ℕ => adjointEndAction E a a - (j : KK O) •
            (1 : Module.End (KK O) (Module.End (KK O) V))).prod g) y =
          (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) (g y) := by
        intro m
        induction m with
        | zero => intro g; simp
        | succ m ih =>
          intro g
          rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
            List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
          simp only [Module.End.mul_apply]
          rw [ih, hadx]
      obtain ⟨G, h, hh, hfy⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop (f y))

      rw [binomE, LinearMap.smul_apply, LinearMap.smul_apply, hprod, hfy, map_sum, Finset.smul_sum]

      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμw := (hh μ hμ).2
      rw [hR k μ ν _ hμw, smul_smul]
      simp only [binomial_diagonal_on_weight hμw, map_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      calc ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, ((μ a : KK O) - ((ν a : KK O) + j))
          = ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, (((μ a + -(ν a) : ℤ) : KK O) - (j : KK O)) := by
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            push_cast
            ring
        _ = ((Ring.choose (μ a + -(ν a)) k : ℤ) : KK O) := inv_factorial_prod_eq_choose _ _
        _ = _ := by
            rw [Ring.add_choose_eq k (Commute.all _ _)]
            push_cast
            refine Finset.sum_congr rfl fun ij _ => ?_
            ring
    obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Module.End (KK O) V,
        S = fun j : ℕ => ((((j : ℤ).negOnePow : ℤˣ) : ℤ) : KK O) • shiftedBinomialOperator E a ((j : ℤ) - 1) j := ⟨_, rfl⟩
    have hS : ∀ (j : ℕ) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        S j y = ((Ring.choose (-(ν a)) j : ℤ) : KK O) • y := by
      intro j ν y hy
      rw [hSdef, LinearMap.smul_apply, shifted_binomial_on_weight hy, smul_smul]
      congr 1
      rw [Ring.choose_neg, Units.smul_def, smul_eq_mul, add_sub_assoc]
      push_cast
      ring
    have hop : binomE (adjointEndAction E) a k f = ∑ ij ∈ antidiagonal k, binomE E a ij.1 * f * S ij.2 := by
      apply LinearMap.ext
      intro z
      obtain ⟨F, g, hg, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop z)

      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hw ν _ (hg ν hν).2, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hS _ _ _ (hg ν hν).2, map_smul, map_smul]
    rw [hop, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun ij _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have h1 : S ij.2 x ∈ NablaSub (O := O) E lam v := by
      rw [hSdef, LinearMap.smul_apply]
      exact intCast_smul_mem_submodule _ _ (shifted_binomial_preserves_lattice hN a _ _ hx)
    have h2 : f (S ij.2 x) ∈ Delta (O := O) E v := hf _ h1
    exact hD _ (Or.inr ⟨a, ij.1, rfl⟩) _ h2

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end
