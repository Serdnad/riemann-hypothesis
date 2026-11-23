module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
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
public import Mathlib.LinearAlgebra.Eigenspace.Zero
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.Field.GeomSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Member.TameDivOrd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma ord_vw_unit_mul_uniformiser_pow {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {ϖ : W} (hϖ : Irreducible ϖ) (h0 : ϖ ≠ 0) (u : Wˣ) (m : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun
      (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m) = m := by
  induction m with
  | zero =>
    rw [pow_zero, _root_.mul_one, Nat.cast_zero]
    exact (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).map_unit u
  | succ m ih =>
    rw [pow_succ, ← _root_.mul_assoc, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ih,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_uniformiser h0
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
    push_cast
    ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma eq_one_of_pow_eq_one_of_ne_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    {k : ℕ} (hk : k ≠ 0) (h : a ^ k = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hk).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hk).ne'

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma one_le_valuation_root_of_unity_sub_one {F : Type} [Field F] (O : ValuationSubring F) {k : ℕ}
    (hk : IsUnit (k : O)) {w : F} (hw : w ^ k = 1) (hw1 : w ≠ 1) : 1 ≤ O.valuation (w - 1) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hsum : ∑ i ∈ Finset.range k, w ^ i = 0 := by
    rw [geom_sum_eq hw1, hw, sub_self, zero_div]
  have hkF : (k : F) = (w - 1) * -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp_rw [mul_comm (w - 1), geom_sum_mul]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hvw : O.valuation w = 1 :=
    eq_one_of_pow_eq_one_of_ne_zero hk0 (by rw [← map_pow, hw, map_one])
  have hwO : w ∈ O := (O.valuation_le_one_iff w).1 hvw.le
  have hcO : -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j ∈ O :=
    neg_mem (sum_mem fun i _ => sum_mem fun j _ => pow_mem hwO j)
  have hvk : O.valuation (k : F) = 1 := by
    simpa using O.valuation_unit hk.unit
  rw [← hvk, hkF, map_mul]
  exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).2 hcO)


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
theorem _root_.GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  intro W _ _ _ F _ _ ϖ hϖ k O φ σ π hk _ hφ hσ hπ hζ d z hd hdz
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have h0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖF : algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).2 h0)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hπ
    exact hϖF hπ.symm
  set ζ := σ π / π with hζdef
  have hσπ : σ π = ζ * π := by rw [hζdef, div_mul_cancel₀ _ hπ0]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective W (z : FractionRing W)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap W (FractionRing W) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : (z : FractionRing W) * algebraMap W _ b = algebraMap W _ a := by
    rw [← hab, div_mul_cancel₀ _ hbF]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at key
    exact z.ne_zero (by simpa [hbF] using key)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ

  have hU : z * (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u' *
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m') =
      Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [show ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 : (FractionRing W)ˣ) : FractionRing W) =
      algebraMap W _ ϖ from rfl, ← map_pow, ← map_mul, ← map_pow, ← map_mul, key]
  have hord : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z + m' = m := by
    have := congrArg (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun hU
    rwa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul,
      ord_vw_unit_mul_uniformiser_pow hϖ, ord_vw_unit_mul_uniformiser_pow hϖ] at this

  have hφu : ∀ x : Wˣ, O.valuation (φ x : F) = 1 := fun x => by
    simpa using O.valuation_unit (Units.map (φ : W →* O) x)
  have keyF : algebraMap _ F (z : FractionRing W) * ((φ u' : F) * (φ ϖ : F) ^ m') =
      (φ u : F) * (φ ϖ : F) ^ m := by
    have := congrArg (algebraMap (FractionRing W) F) key
    simpa only [hφ, map_mul, map_pow] using this
  have hP : O.valuation (φ ϖ : F) = O.valuation π ^ k := by rw [hφ, ← hπ, map_pow]
  have hV : O.valuation d ^ k * O.valuation π ^ (k * m') = O.valuation π ^ (k * m) := by
    have := congrArg O.valuation keyF
    simp only [map_mul, map_pow, hφu, _root_.one_mul, hP] at this
    rw [hdz, pow_mul, pow_mul]
    exact this
  have hvπ : O.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  set y := d * π ^ m' / π ^ m with hydef
  have hvy : O.valuation y = 1 := by
    apply eq_one_of_pow_eq_one_of_ne_zero hk0
    rw [hydef, map_div₀, map_mul, map_pow, map_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm m' k, mul_comm m k, hV, div_self (pow_ne_zero _ hvπ)]
  set w := ζ ^ m' / ζ ^ m with hwdef
  have hσy : σ y = w * y := by
    rw [hydef, hwdef, map_div₀, map_mul, map_pow, map_pow, hd, hσπ]
    ring
  have hyO : y ∈ O := (O.valuation_le_one_iff y).1 hvy.le
  have hwk : w ^ k = 1 := by
    rw [hwdef, div_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, pow_mul, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, div_one]
  have hw : w = 1 := by
    by_contra hw1
    have h1 := one_le_valuation_root_of_unity_sub_one O hk hwk hw1
    have hlt := hσ y hyO
    rw [hσy, show w * y - y = (w - 1) * y by ring, map_mul, hvy, _root_.mul_one] at hlt
    exact absurd hlt (not_lt.2 h1)
  have hdvd : (k : ℤ) ∣ (m' : ℤ) - m := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hk0), zpow_natCast, zpow_natCast]
    exact hw
  have hn : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z = m - m' := by omega
  rw [hn, ← dvd_neg, neg_sub]
  exact hdvd

end GlobalTheory.Member.TameDivOrd
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_kur_of_actQ_fixed (K : FinExt l) (b : P.R.B) (hb : ∀ g ∈ GK K, P.actQ g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = b := by
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by rw [P.PD_actB]; exact hb g g.2
  exact ⟨_, hc⟩

theorem exists_kur_of_actSt_fixed (K : FinExt l)
    (hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (p : Bst P) (hp : ∀ g ∈ GK K, actSt P g p = p) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = p := by
  have hC : ∀ b : P.R.B, (∀ g ∈ GK K, actSt P g (C b) = C b) →
      ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = C b := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_kur_of_actQ_fixed P K b fun g hg =>
      C_injective (by rw [← actSt_C]; exact hb g hg)
    exact ⟨c, by rw [Polynomial.algebraMap_apply, hc]⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0] at hp ⊢
      exact hC _ hp
    · have hN : ∀ g ∈ GK K, actSt P g (monSt P p) = monSt P p := fun g hg => by
        rw [← monSt_actSt, hp g hg]
      obtain ⟨c, hc⟩ := ih (monSt P p).natDegree (by
        rw [monSt_apply, natDegree_neg, ← hn]; exact natDegree_derivative_lt h0) _ hN rfl
      rw [Polynomial.algebraMap_apply] at hc
      set a := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c with ha
      have hfa : ∀ g ∈ GK K, P.actQ g a = a := fun g hg =>
        C_injective (by rw [← actSt_C, hc]; exact hN g hg)
      obtain ⟨b, hb⟩ := (monSt_eq_zero_iff P (p + C a * X)).mp (by
        rw [map_add (f := _), ← hc]; simp)
      have hpb : p = C b - C a * X := by rw [← hb]; ring
      by_cases hc0 : c = 0
      · have : p = C b := by rw [hpb, ha, hc0]; simp
        rw [this] at hp ⊢
        exact hC _ hp
      · exfalso
        set a' := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c⁻¹ with ha'
        have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, inv_mul_cancel₀ hc0, map_one]
        refine hK (a' * b) fun g hg => ?_
        have h1 := hp g hg
        rw [hpb, map_sub, map_mul, actSt_C, actSt_C, actSt_X, hfa g hg] at h1
        have h2 : P.actQ g b - a * ((kummer P g : ℚ_[l]) • P.tB) = b :=
          C_injective (by rw [map_sub, map_mul]; linear_combination h1)
        have h3 : P.actQ g a' * a = 1 := by
          have := congrArg (P.actQ g) haa
          rwa [map_mul, map_one, hfa g hg] at this
        have h4 : P.actQ g a' = a' := by
          linear_combination a' * h3 - P.actQ g a' * haa
        rw [map_mul, h4]
        linear_combination a' * h2 + ((kummer P g : ℚ_[l]) • P.tB) * haa

end GlobalTheory.Pst
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
    _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ σ τ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg σ = _root_.GlobalTheory.WeilDeligne.deg τ →
      ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ σ τ hdeg
  let x : ℕ → _root_.GlobalTheory.WeilDeligne.Weil h := fun k ↦ (τ ^ k)⁻¹ * σ ^ k
  have hmem : ∀ k, ρ (x k) ∈ Set.range fun ι ↦ ρ (_root_.GlobalTheory.WeilDeligne.ineIncl h ι) := by
    intro k
    have h0 : _root_.GlobalTheory.WeilDeligne.deg (x k) = 0 := by
      simp only [x, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv, _root_.GlobalTheory.WeilDeligne.deg_pow, hdeg]
      ring
    refine ⟨⟨_, _root_.GlobalTheory.WeilDeligne.deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only
    congr 1
  obtain ⟨k, l, hkl, hρkl⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hmem hρ.finite_range
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hx : ρ (x k) = ρ (x (k + m + 1)) := hρkl
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have key : σ ^ (m + 1) = τ ^ (k + m + 1) * x (k + m + 1) * (x k)⁻¹ * (τ ^ k)⁻¹ := by
    simp only [x]
    group
  have key' : τ ^ (m + 1) = τ ^ (k + m + 1) * (τ ^ k)⁻¹ := by
    group
  have hinv : ρ (x k) * ρ (x k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← map_pow, ← map_pow, key, key']
  simp only [map_mul]
  rw [← hx, mul_assoc (ρ _) (ρ (x k)), hinv, mul_one]

end GlobalTheory.WeilDeligne
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}


variable (h) in
theorem lpDim_zero (h : IsPlaceOver A w) : lpDim (lpZero (h := h)) = 0 := by
  simp [lpZero]

theorem lpDim_sum (a b : WD h) : lpDim (lpSum a b) = lpDim a + lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_prod]

theorem lpDim_tw (a : WD h) (s : ℝ) : lpDim (lpTw a s) = lpDim a := by
  induction a using ind
  rw [lpTw_mk, lpDim_mk, lpDim_mk]

theorem lpDim_tensor (a b : WD h) : lpDim (lpChar a b) = lpDim a * lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpChar_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_tensorProduct]

theorem lpDim_char (a χ : WD h) (hχ : lpDim χ = 1) : lpDim (lpChar a χ) = lpDim a := by
  rw [lpDim_tensor, hχ, mul_one]

theorem lpSum_zero (a : WD h) : lpSum a (lpZero (h := h)) = a := by
  induction a using ind
  rw [lpZero, lpSum_mk]
  exact sound ⟨LinearEquiv.prodUnique, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_comm (a b : WD h) : lpSum a b = lpSum b a := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodComm _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_assoc (a b c : WD h) : lpSum (lpSum a b) c = lpSum a (lpSum b c) := by
  induction a using ind
  induction b using ind
  induction c using ind
  rw [lpSum_mk, lpSum_mk, lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodAssoc _ _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpTw_zero (a : WD h) : lpTw a 0 = a := by
  induction a using ind
  rw [lpTw_mk]
  exact sound ⟨.refl _ _, fun σ v => by simp, fun _ => rfl⟩

theorem lpTw_add (a : WD h) (s t : ℝ) : lpTw (lpTw a s) t = lpTw a (s + t) := by
  induction a using ind
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  rw [lpTw_mk, lpTw_mk, lpTw_mk]
  refine sound ⟨.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  simp only [WDRep.tw_ρ, smul_smul, LinearEquiv.refl_apply]
  rw [Complex.ofReal_add, Complex.cpow_add _ _ hq, mul_zpow, mul_comm]

theorem lpTw_sum (a b : WD h) (s : ℝ) : lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s) := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpTw_mk, lpTw_mk, lpTw_mk, lpSum_mk]
  exact sound ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem monomial_sum_iff (a b : WD h) : mono0 (lpSum a b) ↔ mono0 a ∧ mono0 b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
  refine ⟨fun h0 => ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h0 => ?_⟩
  · exact congrArg Prod.fst (LinearMap.congr_fun h0 (v, 0))
  · exact congrArg Prod.snd (LinearMap.congr_fun h0 (0, v))
  · rw [h0.1, h0.2, LinearMap.prodMap_zero]

theorem monomial_twist_iff (a : WD h) (s : ℝ) : mono0 (lpTw a s) ↔ mono0 a := by
  induction a using ind
  rw [lpTw_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tw_N]

theorem mono0_of_lpDim_eq_one {χ : WD h} (hχ : lpDim χ = 1) : mono0 χ := by
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff]
    have h1 := b.nilpotent.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly b.N
    rwa [h1, hχ, pow_one, aeval_X] at h2

theorem monomial_char_iff (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by
  have h0 := mono0_of_lpDim_eq_one hχ
  induction a using ind with
  | hP m a =>
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]
    refine ⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩
    let e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])
    have h2 := congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x))
      (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))
    simpa using h2

theorem charPol_lpSum (a b : WD h) (σ : Weil h) :
    charPol (lpSum a b) σ = charPol a σ * charPol b σ := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]

theorem inePol_sum (a b : WD h) (σ : G E Ω) :
    inePol (lpSum a b) σ = inePol a σ * inePol b σ := by
  by_cases hσ : σ ∈ Weil h
  · rw [inePol_of_mem _ hσ, inePol_of_mem _ hσ, inePol_of_mem _ hσ, charPol_lpSum]
  · rw [inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, mul_one]

theorem inePol_tw (a : WD h) (s : ℝ) :
    ∀ σ ∈ Ine (F := E) A, inePol (lpTw a s) σ = inePol a σ := by
  intro σ hσ
  induction a using ind
  rw [inePol_of_mem_Ine _ hσ, inePol_of_mem_Ine _ hσ, lpTw_mk, charPol_mk, charPol_mk]
  congr 1
  simp

end GlobalTheory.WeilDeligne.WD
end
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem reverse_map_of_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem normCoeff_map_of_isPushout {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  have hbc := @GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
  have hint := @GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed
  let ι : FractionRing A →+* FractionRing A' := IsLocalization.map (FractionRing A') α
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective α hα)
  have hι : ∀ a : A, ι (algebraMap A (FractionRing A) a) = algebraMap A' (FractionRing A') (α a) :=
    fun a => IsLocalization.map_eq _ _
  have hc := hbc φ α β φ' H hφ hφ' ι hι b
  have spec : ∀ {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] (ψ : R →+* S)
      (hψ : ψ.Finite) (s : S), algebraMap R (FractionRing R) (normCoeff ψ hψ s k) =
        (charK ψ hψ (FractionRing R) s).reverse.coeff k := by
    intro R S _ _ _ _ ψ hψ s
    obtain ⟨P, hP⟩ := hint (K := FractionRing R) ψ hψ s
    refine algebraMap_normCoeff ψ hψ s k ⟨P.reverse.coeff k, ?_⟩
    rw [← hP, reverse_map_of_injective _ (IsFractionRing.injective R (FractionRing R)), coeff_map]
  apply IsFractionRing.injective A' (FractionRing A')
  rw [← hι, spec, spec, hc, reverse_map_of_injective ι ι.injective, coeff_map]

end GlobalTheory.NormalDescent
end
