module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

noncomputable section

open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.WachTie

def Laur (L M : Type) [Field L] [AddCommGroup M] [Module L M] : Type := HahnModule ℤ L M

namespace Laur

variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']

instance : AddCommGroup (Laur L M) := inferInstanceAs (AddCommGroup (HahnModule ℤ L M))

instance : Module L⟦X⟧ (Laur L M) :=
  Module.compHom (HahnModule ℤ L M) (HahnSeries.ofPowerSeries ℤ L)

def co : Laur L M →+ (ℤ → M) where
  toFun x := ((HahnModule.of L).symm x).coeff
  map_zero' := rfl
  map_add' _ _ := rfl

theorem co_injective : Function.Injective (co : Laur L M → ℤ → M) := by
  intro x y h
  exact HahnModule.ext x y h

theorem isLaurent_co (x : Laur L M) : IsLaurent (co x) := by
  exact ⟨((HahnModule.of L).symm x).order, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩

def mk (u : ℤ → M) (hu : IsLaurent u) : Laur L M :=
  HahnModule.of L (HahnSeries.ofSuppBddBelow u (by
    obtain ⟨m, hm⟩ := hu
    exact ⟨m, fun k hk => not_lt.1 fun h => hk (hm k h)⟩))

private theorem coeff_ofPowerSeries_smul_eq_serMul (f : L⟦X⟧) (y : HahnModule ℤ L M) (k : ℤ) :
    ((HahnModule.of L).symm (HahnSeries.ofPowerSeries ℤ L f • y)).coeff k =
      serMul f ((HahnModule.of L).symm y).coeff k := by
  set F := HahnSeries.ofPowerSeries ℤ L f with hFdef
  have hF : ∀ j : ℕ, F.coeff (j : ℤ) = PowerSeries.coeff j f := fun j =>
    HahnSeries.ofPowerSeries_apply_coeff f j
  have hneg : ∀ i : ℤ, F.coeff i ≠ 0 → 0 ≤ i := by
    intro i hi
    by_contra hlt
    apply hi
    rw [hFdef, HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨j, -, hj⟩
    change (j : ℤ) = i at hj
    omega
  have key : ∀ ij : ℤ × ℤ, F.coeff ij.1 ≠ 0 → ij.1 + ij.2 = k →
      ((ij.1.toNat : ℕ) : ℤ) = ij.1 ∧ k - ((ij.1.toNat : ℕ) : ℤ) = ij.2 := by
    intro ij h1 h3
    have := hneg _ h1
    constructor <;> omega
  have hlau : IsLaurent ((HahnModule.of L).symm y).coeff :=
    ⟨_, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩
  have hfin := serMul_finite f hlau k
  rw [HahnModule.coeff_smul]
  show _ = ∑ᶠ j : ℕ, PowerSeries.coeff j f • ((HahnModule.of L).symm y).coeff (k - (j : ℤ))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  apply Finset.sum_bij_ne_zero (fun ij _ _ => ij.1.toNat)
  · intro ij hij hne
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    rw [Set.Finite.mem_toFinset, Function.mem_support, e2, ← hF, e1]
    exact hne
  · intro a ha _ b hb _ hab
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at ha hb
    obtain ⟨ea1, ea2⟩ := key a ha.1 ha.2.2
    obtain ⟨eb1, eb2⟩ := key b hb.1 hb.2.2
    apply Prod.ext <;> omega
  · intro j _ hne
    refine ⟨((j : ℤ), k - j), ?_, ?_, ?_⟩
    · simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add]
      refine ⟨?_, right_ne_zero_of_smul hne, by omega⟩
      rw [hF]
      exact left_ne_zero_of_smul hne
    · show F.coeff (j : ℤ) • ((HahnModule.of L).symm y).coeff (k - j) ≠ 0
      rw [hF]
      exact hne
    · show ((j : ℤ)).toNat = j
      simp
  · intro ij hij _
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    show F.coeff ij.1 • ((HahnModule.of L).symm y).coeff ij.2 =
      PowerSeries.coeff ij.1.toNat f • ((HahnModule.of L).symm y).coeff (k - (ij.1.toNat : ℤ))
    rw [e2, ← hF, e1]

theorem co_smul (f : L⟦X⟧) (x : Laur L M) : co (f • x) = serMul f (co x) := by
  funext k
  exact coeff_ofPowerSeries_smul_eq_serMul f x k

private theorem co_smul_add_eq_coeff_smul_co (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (n : ℕ)
    (hf : ∀ j < n, PowerSeries.coeff j f = 0) (hx : ∀ k < m, co x k = 0) :
    co (f • x) (m + n) = PowerSeries.coeff n f • co x m := by
  rw [co_smul]
  show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (m + n - j) = _
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hf j h, zero_smul]
    · rw [hx (m + n - j) (by omega), smul_zero]

theorem co_smul_low (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (hx : ∀ k < m, co x k = 0) :
    (∀ k < m, co (f • x) k = 0) ∧ co (f • x) m = constantCoeff f • co x m := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [co_smul]
    show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j) = 0
    exact (finsum_congr fun j => by rw [hx (k - j) (by omega), smul_zero]).trans finsum_zero
  · have e := co_smul_add_eq_coeff_smul_co f x m 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hx
    simpa using e

def tw (c : L) (g : M →ₗ[L] M') : Laur L M →+ Laur L M' where
  toFun x := mk (fun k => c ^ k • g (co x k)) (by
    obtain ⟨m, hm⟩ := isLaurent_co x
    exact ⟨m, fun k hk => by simp [hm k hk]⟩)
  map_zero' := co_injective (by
    funext k
    simp
    rfl)
  map_add' x y := co_injective (by
    funext k
    simp
    rfl)

@[simp] theorem co_tw (c : L) (g : M →ₗ[L] M') (x : Laur L M) (k : ℤ) :
    co (tw c g x) k = c ^ k • g (co x k) := rfl

theorem tw_smul {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (f : L⟦X⟧) (x : Laur L M) :
    tw c g (f • x) = rescale c f • tw c g x := by
  apply co_injective
  funext k
  rw [co_tw, co_smul, co_smul]
  show (c ^ k • g) (∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j)) =
    ∑ᶠ j : ℕ, PowerSeries.coeff j (rescale c f) • co (tw c g x) (k - j)
  rw [map_finsum (c ^ k • g) (serMul_finite f (isLaurent_co x) k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.smul_apply, map_smul, co_tw, PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show c ^ k = c ^ (j : ℤ) * c ^ (k - j) by rw [← zpow_add₀ hc, add_sub_cancel], zpow_natCast]
  ring

end Laur

end GlobalTheory.WachTie
end
end

section

noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]

variable [TopologicalSpace G] [TopologicalSpace LL]

section Whole

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  {ρ : Representation LL G V} {ρ' : Representation LL G V'}

omit [TopologicalSpace G] [TopologicalSpace LL]

end Whole

end Generic

section At

variable (K LL : FinExt l)

end At

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_mapdR_eq {K LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {T T' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.mapdR P f = _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mapdR (Qp := ℚ_[l]) (BdR := P.R.BdR) f :=
  rfl

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem strictness_of_dualExactSequence_strict
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore
  · intro K s LL hg T₀ T₁ T₂ f g hf hg' hi he hs h₀ h₁ h₂ τ a
    obtain ⟨k₁, k₂, k₃⟩ := h K s LL hg T₀ T₁ T₂ f g ⟨hf, hg', hi, he, hs⟩ h₀ h₁ h₂ τ a
    simp only [dualExactSequence_mapdR_eq] at k₁ k₂ k₃
    refine ⟨k₁, ?_, ?_⟩
    · ext y
      simpa [Submodule.mem_inf] using k₂ y
    · ext z
      simpa using k₃ z

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_strict_of_strictness
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb
  · intro K s LL hg T₀ T₁ T₂ f g hfg h₀ h₁ h₂ τ a
    obtain ⟨hf, hg', hi, he, hs⟩ := hfg
    have k := h K s LL hg T₀ T₁ T₂ f g
    have k' := k hf hg' hi he hs
    have k'' := k' h₀ h₁ h₂
    have k3 := k'' τ
    have k4 := k3 a
    obtain ⟨k₁, k₂, k₃⟩ := k4
    refine ⟨k₁, fun y => ?_, fun z => ?_⟩
    · have := SetLike.ext_iff.mp k₂ y
      simpa [Submodule.mem_inf, dualExactSequence_mapdR_eq] using this
    · have := SetLike.ext_iff.mp k₃ z
      simpa [dualExactSequence_mapdR_eq] using this

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
theorem _root_.GlobalTheory.DeRhamCompare.strict_iff :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  ⟨strictness_of_dualExactSequence_strict P,
    dualExactSequence_strict_of_strictness P⟩

end GlobalTheory.DeRhamCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem exists_primRoot_pow (m : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ m) := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)

theorem padic_norm_sub_le_trans {x y z : ℚ_[l]} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) :
    ‖x - z‖ ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_nat_sub_one_le_iff (a m : ℕ) :
    ‖(a : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ↔ ((l : ℤ) ^ m) ∣ (a : ℤ) - 1 := by
  rw [← Padic.norm_int_le_pow_iff_dvd]
  push_cast
  rfl

theorem IsCyc.norm_sub_one_le_of_prim {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ)
    {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ m)) (hg : g ζ = ζ) :
    ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨a, ha, hga⟩ := h g m ζ hζ.pow_eq_one
  refine padic_norm_sub_le_trans ha ?_
  rw [norm_nat_sub_one_le_iff]
  have h0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, ← hga, hg, zpow_one, div_self h0]
  have := (hζ.zpow_eq_one_iff_dvd _).1 h1
  exact_mod_cast this

theorem IsCyc.fix_iff {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ) :
    (∀ ζ : Om l, ζ ^ (l ^ m) = 1 → g ζ = ζ) ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  constructor
  · intro hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
    exact h.norm_sub_one_le_of_prim g m hζ (hg ζ hζ.pow_eq_one)
  · intro hg ζ hζ
    obtain ⟨a, ha, hga⟩ := h g m ζ hζ
    rw [norm_sub_rev] at ha
    obtain ⟨c, hc⟩ := (norm_nat_sub_one_le_iff a m).1 (padic_norm_sub_le_trans ha hg)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
      exact zero_ne_one hζ
    have ha' : (a : ℤ) = ((l ^ m : ℕ) : ℤ) * c + 1 := by push_cast; linarith
    rw [hga, ← zpow_natCast, ha', zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul,
      zpow_one]

theorem IsCyc.norm_le_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := h g 0 1 (one_pow _)
  have h2 : ‖(a : ℚ_[l]) - 0‖ ≤ 1 := by
    rw [sub_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _
  simp only [Nat.cast_zero, neg_zero, zpow_zero] at ha
  simpa using padic_norm_sub_le_trans ha h2

theorem IsCyc.norm_eq_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 := h.norm_le_one g
  have h2 := h.norm_le_one g⁻¹
  have h3 : ‖(χ g : ℚ_[l])‖ * ‖(χ g⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]; simp
  have h4 := norm_nonneg (χ g : ℚ_[l])
  nlinarith

theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem IsCyc.continuous {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) :
    Continuous (fun g => (χ g : ℚ_[l])) := by
  change Continuous ((Units.coeHom ℚ_[l]).comp χ)
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hε
  obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
  rw [Filter.Eventually, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin ℚ_[l] {ζ},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ), ?_⟩
  intro g hg
  have hg' : g ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
    (IntermediateField.mem_adjoin_simple_self _ _)
  have := h.norm_sub_one_le_of_prim g m hζ hg'
  simp only [Set.mem_setOf_eq, map_one, dist_eq_norm]
  exact this.trans_lt hm

theorem mem_fixingSubgroup_adjoin_iff (S : Set (Om l)) (g : GQ l) :
    g ∈ (IntermediateField.adjoin ℚ_[l] S).fixingSubgroup ↔ ∀ x ∈ S, g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact hg x (IntermediateField.subset_adjoin _ _ hx)
  · intro hg x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap x => exact g.commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem cyc_basic : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  intro l _ χ h
  refine ⟨h.norm_eq_one, h.continuous, fun K g hg => ⟨fun j => ?_, ?_⟩⟩
  · rw [Gj, Ks, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff, ← h.fix_iff]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  · rw [Hinf, Kinf, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hne
      have hpos : 0 < ‖(χ g : ℚ_[l]) - 1‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun e => hne (Units.ext e)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd ((h.fix_iff g m).1 fun ζ hζ => h2 ζ ⟨m, hζ⟩) (not_le.2 hm)
    · intro h1
      refine ⟨hg, ?_⟩
      rintro x ⟨m, hx⟩
      refine (h.fix_iff g m).2 ?_ x hx
      rw [h1, Units.val_one, sub_self, norm_zero]
      positivity

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues

variable {l : ℕ} [Fact l.Prime]

theorem norm_galAlgCl (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

theorem isometry_galAlgCl (g : GQ l) : Isometry (g : Om l → Om l) :=
  AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)

noncomputable def galExtC (g : GQ l) : PadicComplex l ≃+* PadicComplex l :=
  UniformSpace.Completion.mapRingEquiv g.toRingEquiv (isometry_galAlgCl g).continuous
    (isometry_galAlgCl g.symm).continuous

theorem galExtC_coe (g : GQ l) (x : Om l) :
    galExtC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x

theorem galExtC_continuous (g : GQ l) : Continuous (galExtC g) :=
  UniformSpace.Completion.continuous_map

theorem norm_galExtC (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]

theorem galExtC_mul (g h : GQ l) : galExtC (g * h) = galExtC g * galExtC h := by
  ext y
  change galExtC (g * h) y = galExtC g (galExtC h y)
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))
  | ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]

noncomputable def galActC (l : ℕ) [Fact l.Prime] : GQ l →* (PadicComplex l ≃+* PadicComplex l) :=
  MonoidHom.mk' galExtC galExtC_mul

theorem isActC_galActC (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩

end GlobalTheory.InertiaEigenvalues
end
