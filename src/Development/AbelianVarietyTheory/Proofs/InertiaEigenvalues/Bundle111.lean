module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Mathlib.RingTheory.Discriminant
public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle072
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle074
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Trace.Quotient
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.Adjoin.PowerBasis
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.IntBasis

open IsLocalRing

abbrev adicVal (K : UQ) : Valuation K.E (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem adicVal_le_one_iff (K : UQ) (x : K.E) : adicVal K x ≤ 1 ↔ ∃ a : K.O, algebraMap K.O K.E a = x :=
  ⟨IsDiscreteValuationRing.exists_lift_of_le_one, by
    rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩

theorem adicVal_eq_one_iff (K : UQ) (a : K.O) : adicVal K (algebraMap K.O K.E a) = 1 ↔ IsUnit a := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem adicVal_map (h : IsUnrExt K K' d φ) (x : K.E) : adicVal K' (φ x) = adicVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx
  have h1 := h.2.2.1 x
  unfold val at h1
  have h2 := neg_inj.1 h1
  have a1 : adicVal K' (φ x) ≠ 0 := (Valuation.ne_zero_iff _).2 hφ
  have a2 : adicVal K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← WithZero.exp_log a1, ← WithZero.exp_log a2]
  exact congrArg WithZero.exp h2

theorem exists_lift (h : IsUnrExt K K' d φ) :
    ∃ ι : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
  let S := (algebraMap K'.O K'.E).range
  have hS : ∀ a : K.O, (φ.comp (algebraMap K.O K.E)) a ∈ S := fun a => by
    obtain ⟨b, hb⟩ := (adicVal_le_one_iff K' (φ (algebraMap K.O K.E a))).1 (by
      rw [adicVal_map h]; exact (adicVal_le_one_iff K _).2 ⟨a, rfl⟩)
    exact ⟨b, hb⟩
  let e : K'.O ≃+* S := RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective K'.O K'.E (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict S hS), fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict S hS a))

theorem exists_key (h : IsUnrExt K K' d φ) :
    ∃ w : Fin d → K'.E, ∀ (a : Fin d → K.E) (m : Fin d), (∀ k, adicVal K (a k) ≤ adicVal K (a m)) →
      adicVal K' (∑ k, φ (a k) * w k) = adicVal K (a m) := by
  obtain ⟨ι, hι⟩ := exists_lift h
  haveI : IsLocalHom ι := ⟨fun a ha => by
    rw [← adicVal_eq_one_iff] at ha ⊢; rwa [hι, adicVal_map h] at ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ι).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hf : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have hc := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, K'.card_res, K.card_res, h.1, ← pow_mul,
      mul_comm, pow_mul] at hc
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← K.card_res]; exact Finite.one_lt_card
    exact (Nat.pow_right_injective h2 hc).symm
  haveI : Module.Finite (ResidueField K.O) (ResidueField K'.O) := Module.Finite.of_finite
  let bk := Module.finBasisOfFinrankEq _ _ hf
  choose w' hw' using fun i => residue_surjective (bk i)
  refine ⟨fun i => algebraMap K'.O K'.E (w' i), fun a m hm => ?_⟩
  by_cases ham : a m = 0
  · have h0 : ∀ k, a k = 0 := fun k => by
      have := hm k; rw [ham, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
    simp [h0]
  have hb : ∀ k, ∃ b : K.O, algebraMap K.O K.E b = a k / a m := fun k =>
    (adicVal_le_one_iff K _).1 (by rw [map_div₀]; exact div_le_one_of_le₀ (hm k) zero_le')
  choose b hb using hb
  have hbm : b m = 1 := IsFractionRing.injective K.O K.E (by rw [hb, div_self ham, map_one])
  set s : K'.O := ∑ k, ι (b k) * w' k with hs
  have hsum : ∑ k, φ (a k) * algebraMap K'.O K'.E (w' k) = φ (a m) * algebraMap K'.O K'.E s := by

    rw [hs, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hι, hb, map_div₀, ← mul_assoc, mul_div_cancel₀ _ ((map_ne_zero φ).2 ham)]
  have hres : residue K'.O s ≠ 0 := by
    have e1 : residue K'.O s = ∑ k, residue K.O (b k) • bk k := by

      rw [hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw', Algebra.smul_def, RingHom.algebraMap_toAlgebra, ResidueField.map_residue]
    rw [e1]; intro h0
    have := Fintype.linearIndependent_iff.1 bk.linearIndependent _ h0 m
    rw [hbm, map_one] at this; exact one_ne_zero this
  have hsu : IsUnit s := by
    by_contra hn
    exact hres ((residue_eq_zero_iff s).2 ((mem_maximalIdeal s).2 hn))
  rw [hsum, Valuation.map_mul, (adicVal_eq_one_iff K' s).2 hsu, mul_one, adicVal_map h]

theorem intBasis : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra;
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : ∀ a : Fin d → K.E, ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) := fun a =>
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]; intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k; have := hm k; rw [hgm, map_zero] at this
    exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k; rw [← adicVal_le_one_iff]; exact (hm k).trans (hv ▸ hzO)
  · intro hall; rw [hv]; exact (adicVal_le_one_iff K _).2 (hall m)

end GlobalTheory.UnitLemma.Unr.IntBasis
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma

theorem mem_range_of_val_nonneg (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0 := by simpa using hz
  have hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1 := by
    unfold val at h
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact ⟨a, ha⟩

theorem val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using ha
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_int_image {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by
  apply mem_range_of_val_nonneg
  rw [hU.2.2.1]
  exact val_algebraMap_nonneg K a

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_separable : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  intro K K' d φ _ B ψ hψ hσ hsep

  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hsep

  have hP : aeval B.g B.P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
    have h2 : aeval (LinearMap.mulLeft K.E B.g) B.P = Algebra.lmul K.E B.A (aeval B.g B.P) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    have h3 := congrArg (fun f : Module.End K.E B.A => f 1) (h2.symm.trans h1)
    simpa using h3
  set B' := overExt φ B ψ hψ hσ with hB'
  have hg : B'.g = B.g := rfl
  have hmap : ∀ x : K'.E, algebraMap K'.E B'.A x = ψ x := fun x => rfl
  have hint : IsIntegral K'.E B'.g := Algebra.IsIntegral.isIntegral _

  have htop : Algebra.adjoin K'.E {B'.g} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : (y : B.A) = ∑ i, (e.repr y i) • e i := (e.sum_repr y).symm
    change (y : B'.A) ∈ Algebra.adjoin K'.E {B'.g}
    have : (y : B'.A) = ∑ i, algebraMap K'.E B'.A (φ (e.repr y i)) * B'.g ^ (i : ℕ) := by
      refine hy.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hmap, hψ, he, Algebra.smul_def]; rfl
    rw [this]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hchar : B'.P = minpoly K'.E B'.g := by
    have h1 := charpoly_leftMulMatrix pb
    rw [PowerBasis.ofAdjoinEqTop_gen] at h1
    rw [← h1, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    rfl
  have hdvd : minpoly K'.E B'.g ∣ B.P.map φ := by
    refine minpoly.dvd _ _ ?_
    rw [aeval_def, eval₂_map]
    have : (algebraMap K'.E B'.A).comp φ = algebraMap K.E B.A := RingHom.ext fun x => hψ x
    rw [this]
    exact hP
  rw [hchar]
  exact (hsep.map).of_dvd hdvd

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResDisc

open IsLocalRing

theorem isUnit_discr_of_isMaximal_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field (Ideal.map (algebraMap R S) (maximalIdeal R))
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (basisQuotient b)
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    inferInstance
  have h1 : Ideal.Quotient.mk (maximalIdeal R) (Algebra.discr R b) =
      Algebra.discr (R ⧸ maximalIdeal R) (basisQuotient b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk]
  have h2 := Algebra.discr_not_zero_of_basis (R ⧸ maximalIdeal R) (basisQuotient b)
  rw [← h1] at h2
  by_contra h
  exact h2 (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 h))

theorem discr_trace_isUnit :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (π : K.O) (π' : K'.O),
      algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) →
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} →
      IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det) := by
  intro K K' d φ _ π π' hππ' hm hm'
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hφ : ∀ e : K.E, φ e = algebraMap K.E K'.E e := fun _ => rfl

  have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
    intro a
    apply (hw _).2
    intro k
    obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
    refine ⟨a * c, ?_⟩
    have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
  let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
    RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
      ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
  let ι : K.O →+* K'.O :=
    e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
  have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
  letI : Algebra K.O K'.O := ι.toAlgebra
  have hsm : ∀ (a : K.O) (y : K'.O),
      algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
    intro a y
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    exact congrArg (· * _) (hι a)
  have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
      algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
    intro g v

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _

  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    refine ⟨if m = k then 1 else 0, ?_⟩
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  choose bv hbv using hw1
  have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
    fun y => (hw _).1 ⟨y, rfl⟩
  choose c hc using hcoord
  have hli : LinearIndependent K.O bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h1 := congrArg (algebraMap K'.O K'.E) hg
    rw [hsum, map_zero] at h1
    simp only [hbv] at h1
    have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
    exact hi (by rw [h2, map_zero])
  have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
    intro y _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c y, hj ?_⟩
    rw [hsum]
    simp only [hbv, hc]
    exact w.sum_repr _
  let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
  have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
    rw [Module.Basis.mk_apply]; exact hbv k
  have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
    intro y k
    conv_rhs => rw [← b.sum_repr y, hsum]
    simp only [hb]
    rw [w.repr_sum_self]

  have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
      Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
    intro y

    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
    map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

  have hιπ : ι π = π' := hj (by rw [hι, hππ'])
  have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hm, Ideal.map_span, Set.image_singleton]
    have h1 : algebraMap K.O K'.O π = π' := hιπ
    rw [h1, ← hm']
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨Algebra.discr K.O b, isUnit_discr_of_isMaximal_map b hmax, ?_⟩
  rw [Algebra.discr_def, RingHom.map_det]
  congr 1
  ext k m
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]

end GlobalTheory.UnitLemma.Unr.ResDisc
end
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_invariants_of_smul_ne_one : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  intro O _ _ _ _ M _ _ e G _ ρ g a ha hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : a - 1 ≠ 0 := sub_ne_zero.2 ha
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0 := by
    intro m
    have hm : ρ g (m : M) = m := (Representation.mem_invariants ρ (m : M)).1 m.2 g
    have h1 : (a - 1) • (m : M) = 0 := by
      rw [sub_smul, one_smul, ← hg, hm, sub_self]
    rw [hu, mul_smul] at h1
    have h2 := congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1
    simp only [smul_zero, smul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  haveI := (lev_pow_card hϖ e c).1
  refine Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_
  intro x y hxy
  have := congrArg Lev.val hxy
  simp only [Lev.val_mk] at this
  exact Subtype.ext this

end GlobalTheory.ShapeNeg
end

section

open Formalism.L2.Pj

theorem _root_.GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  first | exact @GlobalTheory.isIntegral_adjoin_of_forall_cdvr | exact GlobalTheory.isIntegral_adjoin_of_forall_cdvr | (intros; apply GlobalTheory.isIntegral_adjoin_of_forall_cdvr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_gaussPoint' : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧ IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧ ∀ x, vV T'.V (i x) = vV T.V x := by
  exact @GlobalTheory.GaussPoint.exists_gaussPoint
end
