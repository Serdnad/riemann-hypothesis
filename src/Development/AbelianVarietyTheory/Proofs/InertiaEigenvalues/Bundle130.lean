module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle112
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem valuation_map_eq_of_unr (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hU.2.2.1 x
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  have h0' : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_log h0']
  congr 1
  omega

theorem exists_intMap_of_unr (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by
  choose f hf using exists_int_image hU
  have inj := IsFractionRing.injective K'.O K'.E
  let ψ : K.O →+* K'.O :=
    { toFun := f, map_one' := inj (by simp only [hf, map_one]),
      map_mul' := fun a b => inj (by simp only [hf, map_mul]),
      map_zero' := inj (by simp only [hf, map_zero]),
      map_add' := fun a b => inj (by simp only [hf, map_add (f := _)]) }
  exact ⟨ψ, hf⟩

theorem exists_int_basis_of_unr (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_intMap_of_unr hU
  have hv := valuation_map_eq_of_unr hU
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hvdef
  set v' := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv'def

  have memK : ∀ a : K.O, a ∈ maximalIdeal K.O ↔ v (algebraMap K.O K.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K.O) a).symm
  have memK' : ∀ a : K'.O, a ∈ maximalIdeal K'.O ↔ v' (algebraMap K'.O K'.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K'.O) a).symm
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal K.O := (mem_maximalIdeal a).2 hna
    have h2 : ψ a ∈ maximalIdeal K'.O := by
      rw [memK', hψ, hv]; exact (memK a).1 h1
    exact (mem_maximalIdeal _).1 h2 ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ψ).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hfr : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have h1 := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    have c1 : Fintype.card (ResidueField K.O) = K.q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact K.card_res
    have c2 : Fintype.card (ResidueField K'.O) = (K.q ^ 2) ^ d := by
      rw [← Nat.card_eq_fintype_card, K'.card_res, hU.1, ← pow_mul, ← pow_mul, mul_comm]
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← c1]; exact Fintype.one_lt_card
    rw [c1, c2] at h1
    exact (Nat.pow_right_injective h2 h1).symm
  let b := Module.finBasisOfFinrankEq (ResidueField K.O) (ResidueField K'.O) hfr
  choose u hu using fun i => IsLocalRing.residue_surjective (b i)

  have hres : ∀ c : Fin d → K.O, ∀ j, c j = 1 → ∑ i, ψ (c i) * u i ∉ maximalIdeal K'.O := by
    intro c j hj hmem
    have h0 : residue K'.O (∑ i, ψ (c i) * u i) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem

    rw [map_sum] at h0
    simp only [map_mul, ← ResidueField.map_residue, hu] at h0
    have h1 : ∑ i, residue K.O (c i) • b i = 0 := by
      simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h0
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 j
    rw [hj, map_one] at this
    exact one_ne_zero this

  set U : Fin d → K'.E := fun i => algebraMap K'.O K'.E (u i) with hUdef

  have key : ∀ e : Fin d → K.E, ∀ j, (∀ i, v (e i) ≤ v (e j)) → e j ≠ 0 →
      v (e j) ≤ v' (∑ i, φ (e i) * U i) := by
    intro e j hmax hj
    have hpos : 0 < v (e j) := zero_lt_iff.2 (by simpa using hj)
    have hc : ∀ i, ∃ a : K.O, algebraMap K.O K.E a = e i / e j := fun i =>
      IsDiscreteValuationRing.exists_lift_of_le_one (by
        rw [map_div₀]; exact (div_le_one₀ hpos).2 (hmax i))
    choose a ha using hc
    have haj : a j = 1 := IsFractionRing.injective K.O K.E (by rw [ha, div_self hj, map_one])
    have h1 := hres a j haj
    rw [memK', not_lt] at h1
    have h2 : algebraMap K'.O K'.E (∑ i, ψ (a i) * u i) = ∑ i, φ (e i / e j) * U i := by

      simp only [map_sum, map_mul, hψ, ha, hUdef]
    have h3 : ∑ i, φ (e i) * U i = φ (e j) * ∑ i, φ (e i / e j) * U i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hj]
    rw [h3, map_mul, hv, ← h2]
    exact le_mul_of_one_le_right' h1
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hsmul : ∀ (x : K.E) (y : K'.E), x • y = φ x * y := fun x y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent K.E U := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i)) ⟨i, Finset.mem_univ i⟩
    have hgi : 0 < v (g i) := zero_lt_iff.2 (by simpa using hi)
    have hgj : g j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd this (not_le.2 hgi)
    have := key g j (fun i => hj i (Finset.mem_univ i)) hgj
    simp only [← hsmul] at this
    rw [hg, map_zero] at this
    exact hgj ((map_eq_zero v).1 (le_antisymm this zero_le'))
  have hd : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : Nonempty (Fin d) := by
    have : 0 < d := hfr ▸ Module.finrank_pos
    exact ⟨⟨0, this⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hd])
  refine ⟨u, fun y => ?_⟩
  have hy : algebraMap K'.O K'.E y ∈ Submodule.span K.E (Set.range U) := hspan ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun K.E).1 hy
  have hint : ∀ i, v (e i) ≤ 1 := by
    intro i
    by_contra hi
    rw [not_le] at hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨i, Finset.mem_univ i⟩
    have hej : e j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd (lt_of_lt_of_le hi this) (not_lt.2 zero_le')
    have h1 := key e j (fun i => hj i (Finset.mem_univ i)) hej
    simp only [← hsmul] at h1
    rw [he] at h1
    have h2 := HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K'.O) (K := K'.E) y
    exact absurd (lt_of_lt_of_le hi (le_trans (hj i (Finset.mem_univ i)) (le_trans h1 h2))) (lt_irrefl _)
  choose a ha using fun i => IsDiscreteValuationRing.exists_lift_of_le_one (hint i)
  refine ⟨a, ?_⟩
  rw [← he]
  simp only [hsmul, ha, hUdef]

end GlobalTheory.UnitLemma.Unr
end
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

noncomputable section

namespace GlobalTheory.LiftCoker

theorem map_decomp_frob {O K : Type} [CommRing O] [NormedField K] [Algebra O K] (l : ℕ) [Fact l.Prime]
    {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
    PowerSeries.map (algebraMap O K) f =
      ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by

  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_X, map_expand]
  rfl

theorem colon_map_frob_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    colon (O := O) (K := K) (G.map (frob K l)) ≤
      (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _ (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l) (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob (K := K) l hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]

      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm

  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))

end GlobalTheory.LiftCoker
end
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
      [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ]
      (G : Matrix κ ι K⟦X⟧),
      colon (O := O) (K := K) (G.map (frob K l)) ≤
        (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have map_decomp_frob {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
      (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
      PowerSeries.map (algebraMap O K) f =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by

    rw [h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, map_X, map_expand]
    rfl
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _
      (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l)
      (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val *
          frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]

      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm
  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem colon_map_expand_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by

      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring

end GlobalTheory.LiftCoker
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type)
    [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by

      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem latProj_smul (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) :
    latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  rw [latPair_smul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).comap (LinearMap.inl O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.fst A₁ A₂) t : A₁ˣ) : A₁) ((M : Submodule O (A₁ × A₂)).comap (LinearMap.inl O A₁ A₂))
    ext y
    rw [Submodule.mem_comap, mem_mulLat_iff, mem_mulLat_iff, Submodule.mem_comap]
    have h : ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂) * (LinearMap.inl O A₁ A₂ y) =
        LinearMap.inl O A₁ A₂ (((Units.map (MonoidHom.fst A₁ A₂) t)⁻¹ : A₁ˣ) * y) := by
      ext <;> simp
    rw [h]
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).map (LinearMap.snd O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.snd A₁ A₂) t : A₂ˣ) : A₂) ((M : Submodule O (A₁ × A₂)).map (LinearMap.snd O A₁ A₂))
    unfold mulLat
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.Published

theorem _root_.GlobalTheory.T.induced_representation_character : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)
end
