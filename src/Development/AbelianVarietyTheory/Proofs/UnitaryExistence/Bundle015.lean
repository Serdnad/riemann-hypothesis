module

public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

namespace GlobalTheory.LocalQuad

theorem landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt :=
  fun H => GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)

end GlobalTheory.LocalQuad
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.IntegralFrameAllCompare

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Valuations

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_nonneg_iff_le_one (x : K) (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  rw [← WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero, WithZero.log_one, vV]
  omega

theorem mem_range_iff (x : K) : x ∈ Set.range (algebraMap V K) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  rw [vV_nonneg_iff_le_one x hx]
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · exact fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K v) := by
  have h1 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 h0
  have h2 : valV V (algebraMap V K v) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 h2
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem vV_of_isUnit {v : V} (h : IsUnit v) : vV V (algebraMap V K v) = 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 := (mem_range_iff (V := V) (algebraMap V K (u : V))).1 ⟨_, rfl⟩
  have h2 := (mem_range_iff (V := V) (algebraMap V K ((u⁻¹ : Vˣ) : V))).1 ⟨_, rfl⟩
  rw [map_units_inv, ← zpow_neg_one, vV_zpow] at h2
  omega

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) : i.Finite := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (mem_range_iff _).2 (by rw [hi]; exact mul_nonneg (by positivity) ((mem_range_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := ((algebraMap W L).comp g).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun a => hg a
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_cases h0 : a = 0
    · simp [h0]
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    have h1 : vV W (algebraMap W L (g a)) = 0 := vV_of_isUnit hu
    have h3 : (0 : ℤ) < r * vV V (algebraMap V K a) := mul_pos (by exact_mod_cast hr) (vV_pos h0 ha)
    rw [← hi, ← hg, h1] at h3
    exact lt_irrefl _ h3
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  have : IsHausdorff ((maximalIdeal V).map (algebraMap V W)) W := IsHausdorff.of_isDomain _ htop
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have : Finite (W ⧸ (maximalIdeal V).map (algebraMap V W)) := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    have : Finite (W ⧸ maximalIdeal W) := h'
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have : Module.Finite V (W ⧸ (maximalIdeal V).map (algebraMap V W)) := Module.Finite.of_finite
  have : Module.Finite V W := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal V)
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

end Valuations

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.IntegralFrameAllCompare
end
end

section

noncomputable section

namespace GlobalTheory.CuspFormsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma zero_mem_SS_unitary_existence {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    (0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) ∈ X.SS la :=
  ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero X la, fun ξ _ x _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero X la ξ x 0⟩

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma add_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) (hQ : Q ∈ X.SS la) : P + Q ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add X hP.1 hQ.1 hξ hx 0, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma smul_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (a : ℂ) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : a • P ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul X la P ξ x 0 a, hP.2 ξ hξ x hx, mul_zero]


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS {r : ℕ} {Comp : Type}
    (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r)
    (P : _root_.Formalism.L2.PjFree.FDSec X) : P ∈ _root_.Formalism.L2.PjFree.holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  constructor
  · intro hP
    unfold _root_.Formalism.L2.PjFree.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ => exact hQ
    | zero => exact fun k => zero_mem_SS_unitary_existence (X k) (la k)
    | add Q R _ _ hQ hR => exact fun k => add_mem_SS (X k) (la k) (hQ k) (hR k)
    | smul a Q _ hQ => exact fun k => smul_mem_SS (X k) (la k) a (hQ k)
  · intro hP
    exact _root_.Formalism.L2.PjFree.holCusp_mem_holSub X la hP

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end GlobalTheory.CuspFormsCompare
end
end

section

open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.finite_normalisation_of_finite_over_normal (A S : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [CharZero S]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S] :
    Module.Finite S (integralClosure S (FractionRing S)) := by
  haveI : FaithfulSMul A (FractionRing S) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A S (FractionRing S)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective A S))
  letI : Algebra (FractionRing A) (FractionRing S) := FractionRing.liftAlgebra A _
  haveI := FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S _)
  haveI : CharZero (FractionRing A) := (algebraMap (FractionRing A) (FractionRing S)).charZero
  haveI : FiniteDimensional (FractionRing A) (FractionRing S) := inferInstance
  haveI : IsIntegralClosure (integralClosure S (FractionRing S)) A (FractionRing S) := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := A) (A := S) (y : FractionRing S) y.2
  haveI : Module.Finite A (integralClosure S (FractionRing S)) :=
    IsIntegralClosure.finite A (FractionRing A) (FractionRing S) _
  exact Module.Finite.of_restrictScalars_finite A S _

open IsLocalRing in
private theorem isPrecomplete_of_finite_module {R M : Type*} [CommRing R] {I : Ideal R} [hR : IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) →
      ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x := by
    intro n x hx
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, by simp [Finsupp.sum_fintype]⟩
  refine ⟨fun {f} hf => ?_⟩
  have hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := fun n => by
    have := (hf (Nat.le_succ n))
    rw [SModEq.sub_mem] at this
    simpa using neg_mem this
  choose c hcI hcsum using fun n => key n _ (hd n)
  have hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro j
    refine hR.prec' _ fun {m n} hmn => ?_
    rw [SModEq.sub_mem, hpow]
    have : ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j =
        -∑ i ∈ Finset.Ico m n, c i j := by
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))
  choose a ha using hs
  refine ⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩
  have hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]
      rw [← add_assoc, ← ih]
      abel
  rw [SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have := (SModEq.sub_mem.1 (ha j n))
  rw [hpow] at this
  exact Submodule.smul_mem_smul this Submodule.mem_top

open IsLocalRing in
open Polynomial in
private theorem isLocalRing_of_finite_domain_over_complete (S C : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] : IsLocalRing C := by
  set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI
  haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module
  haveI : IsAdicComplete (maximalIdeal S) C := {}
  haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  have hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) M)).ge
  haveI : IsArtinianRing (C ⧸ I) := by
    letI := Ideal.Quotient.field (maximalIdeal S)
    haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S _ _
    exact IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal C
  refine ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  obtain ⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁ := by
    by_contra! h
    exact hne (hM₂.eq_of_le hM₁.ne_top h)
  set u := Ideal.Quotient.mk I x with hu
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I)
    ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}),
      fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩
  set m := N + 1 with hmdef
  have hm : u ^ m ∈ Ideal.span {u ^ (m + 1)} := by
    have h₁ := hN m (by omega)
    have h₂ := hN (m + 1) (by omega)
    have : Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)} := by
      exact congrArg OrderDual.ofDual (h₁.symm.trans h₂)
    rw [← this]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hm
  have hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, pow_add u m j, ← hv]
      ring
  have he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m := by
    calc (u ^ m * v ^ m) * (u ^ m * v ^ m) = (u ^ (m + m) * v ^ m) * v ^ m := by ring
      _ = u ^ m * v ^ m := by rw [← hpow m]
  have hue : u ^ m = u ^ m * (u ^ m * v ^ m) := by
    calc u ^ m = u ^ (m + m) * v ^ m := hpow m
      _ = u ^ m * (u ^ m * v ^ m) := by ring
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  set a₀ := x ^ m * y ^ m with ha₀def
  have hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m := by
    simp [ha₀def, hu]
  have hmon : (X ^ 2 - X : C[X]).Monic := by monicity!
  have heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]
    rw [sq, he, sub_self]
  have hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀)) := by
    rw [hder, map_sub, map_mul, hmk, map_one, map_ofNat]
    exact (Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1)
      (by linear_combination 4 * he)).isUnit
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  have hx₂m : a₀ ∈ M₂ := M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))
  rcases mul_eq_zero.1 ha' with h0 | h1
  · subst h0
    have ha₀I : a₀ ∈ I := by simpa using neg_mem haa₀
    have hxm : x ^ m - x ^ m * a₀ ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue,
        sub_self]
    have : x ^ m ∈ M₁ := by
      have h := hIM M₁ hM₁ hxm
      have h' := M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)
      simpa using M₁.add_mem h h'
    exact hx₁ (hM₁.isPrime.mem_of_pow_mem m this)
  · have h1' : a = 1 := sub_eq_zero.1 h1
    subst h1'
    have : (1 : C) ∈ M₂ := by
      have h := hIM M₂ hM₂ haa₀
      simpa using M₂.add_mem h hx₂m
    exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)

open IsLocalRing in
theorem _root_.GlobalTheory.normalisation_finite_local_complete_of_mixedChar :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by
  intro S _ _ _ _ p hp hpm hS hSc
  obtain ⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩ :=
    _root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc
  letI : Algebra A S := i.toAlgebra
  haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  haveI : Module.Finite A S := hfin
  haveI := hAn
  haveI := hAic
  haveI := hS
  haveI := hSc
  haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _
  haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance
  exact ⟨hC, inferInstance, inferInstance,
    _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩

end GlobalTheory
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.signature_hermitian_model_of_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (0 < (τ ξ).im → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn D.q (a : ℕ) : ℝ) : ℂ))) ∧ ((τ ξ).im < 0 → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn D.p (a : ℕ) : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HermSign.signature_of_model | exact GlobalTheory.HermSign.signature_of_model | (intros; apply GlobalTheory.HermSign.signature_of_model <;> assumption)
end
