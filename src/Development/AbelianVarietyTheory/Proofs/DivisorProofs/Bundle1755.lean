module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.LeftBasis

theorem isIntB_of_isIntB_of_repr {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) (v : HeightOneSpectrum ℤ)
    (h : ∀ k' k, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' k') k) ∈ v.adicCompletionIntegers ℚ)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) (hy : IsIntB v b' y) : IsIntB v b y := by
  intro k

  rw [eq_sum_tmul b' v y, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun k' _ => ?_
  rw [repr_tmul_apply]
  exact mul_mem (hy k') (h k' k)

theorem isIntB_iff_eventually {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ y, IsIntB v b y ↔ IsIntB v b' y := by
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ' × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ',
      algebraMap ℚ (v.adicCompletion ℚ) (b'.repr (b t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv y => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨isIntB_of_isIntB_of_repr b' b v (fun k k' => hv.2 (k, k')) y,
    isIntB_of_isIntB_of_repr b b' v (fun k' k => hv.1 (k', k)) y⟩

theorem isIntB_sum_leftBasis_iff_eventually : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  intro L _ _ C _ _ ι r e he κ ℓ κ' b
  let Φl : (Fin r → L) →ₗ[ℚ] C :=
    ∑ i, (LinearMap.mulRight ℚ (e i)) ∘ₗ ι.toLinearMap ∘ₗ LinearMap.proj i
  have hΦl : ∀ c, Φl c = ∑ i, ι (c i) * e i := fun c => by
    simp [Φl, LinearMap.sum_apply]
  have hbij : Function.Bijective Φl := by
    refine ⟨fun c c' hcc => ?_, fun x => ?_⟩
    · obtain ⟨d, -, hd⟩ := he (Φl c)
      exact (hd c (hΦl c)).trans (hd c' (hcc.trans (hΦl c'))).symm
    · obtain ⟨d, hd, -⟩ := he x
      exact ⟨d, (hΦl d).trans hd.symm⟩
  let Φ := LinearEquiv.ofBijective Φl hbij
  let b' : Module.Basis (Σ _ : Fin r, κ) ℚ C := (Pi.basis fun _ : Fin r => ℓ).map Φ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  haveI : FiniteDimensional ℚ C := Module.Finite.of_basis b'
  haveI : Fintype κ' := FiniteDimensional.fintypeBasisIndex b
  have hsingle : ∀ (j : Fin r) (l : L), Φ (Pi.single j l) = ι l * e j := by
    intro j l
    show Φl _ = _
    rw [hΦl, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrepr : ∀ (j : Fin r) (l : L) (i : Fin r) (a : κ),
      b'.repr (ι l * e j) ⟨i, a⟩ = ℓ.repr ((Pi.single j l : Fin r → L) i) a := by
    intro j l i a
    rw [← hsingle]
    simp [b', Module.Basis.map_repr, Pi.basis_repr]
  have hcoord : ∀ (v : HeightOneSpectrum ℤ) (j : Fin r) (z : v.adicCompletion ℚ ⊗[ℚ] L) (i : Fin r) (a : κ),
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
        (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι z * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr ((Pi.single j z : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) i) a := by
    intro v j z i a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, AlgHom.id_apply,
        repr_tmul_apply, hrepr]
      by_cases h : i = j
      · subst h; simp [repr_tmul_apply]
      · simp [h]
    | add x y hx hy =>
      rw [map_add (f := _), add_mul, LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy, Pi.single_add, Pi.add_apply,
        LinearEquiv.map_add, Finsupp.add_apply]
  obtain ⟨S, hS⟩ := isIntB_iff_eventually b b'
  refine ⟨S, fun v hv β => ?_⟩
  have hy : ∀ (i : Fin r) (a : κ), (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
      (∑ j, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β j) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr (β i) a := by
    intro i a

    rw [map_sum, Finsupp.finsetSum_apply]
    simp_rw [hcoord]

    rw [← Finsupp.finsetSum_apply, ← map_sum]
    congr 2
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hS v hv]
  constructor
  · intro h i a
    rw [← hy]
    exact h ⟨i, a⟩
  · rintro h ⟨i, a⟩
    rw [hy]
    exact h i a

end GlobalTheory.AdicSpan.LeftBasis
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicInt_iff (v : HeightOneSpectrum ℤ) (q : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [← this]
  rfl

theorem valuation_int_eq_one (v : HeightOneSpectrum ℤ) {s : ℤ} (hs : s ∉ v.asIdeal) :
    v.valuation ℚ (s : ℚ) = 1 := by
  have e : ((s : ℚ)) = algebraMap ℤ ℚ s := rfl
  rw [e]
  refine le_antisymm (v.valuation_le_one s) (not_lt.1 fun h => hs ?_)
  exact (Ideal.dvd_span_singleton).1 ((v.valuation_lt_one_iff_dvd s).1 h)

theorem den_not_mem (v : HeightOneSpectrum ℤ) (q : ℚ) (hq : v.valuation ℚ q ≤ 1) :
    ((q.den : ℤ)) ∉ v.asIdeal := by
  intro hd
  have hlt : v.valuation ℚ ((q.den : ℤ) : ℚ) < 1 := by
    have e : (((q.den : ℤ)) : ℚ) = algebraMap ℤ ℚ (q.den : ℤ) := rfl
    rw [e]; exact (v.valuation_lt_one_iff_dvd _).2 (Ideal.dvd_span_singleton.2 hd)
  have hn : v.valuation ℚ ((q.num : ℤ) : ℚ) < 1 := by
    have e : ((q.num : ℤ) : ℚ) = q * ((q.den : ℤ) : ℚ) := by
      rw [Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hq) hlt
  have hnm : q.num ∈ v.asIdeal := by
    have e : ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num := rfl
    rw [e] at hn
    exact Ideal.dvd_span_singleton.1 ((v.valuation_lt_one_iff_dvd _).1 hn)
  have hc : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using q.reduced
  obtain ⟨u, w, h⟩ := hc
  have h1 : (1 : ℤ) ∈ v.asIdeal := h ▸ add_mem (Ideal.mul_mem_left _ _ hnm) (Ideal.mul_mem_left _ _ hd)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem repr_via {K M ι κ : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] (c : Module.Basis κ K M)
    (d : Module.Basis ι K M) (z : M) (i : κ) :
    c.repr z i = ∑ j, d.repr z j * c.repr (d j) i := by
  conv_lhs => rw [← d.sum_repr z]

  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem isIntB_one_tmul_iff (v : HeightOneSpectrum ℤ) {L κ : Type} [Field L] [Algebra ℚ L]
    (ℓ : Module.Basis κ ℚ L) (z : L) :
    IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∀ i, v.valuation ℚ (ℓ.repr z i) ≤ 1 := by
  unfold IsIntB
  simp only [repr_tmul_apply, one_mul, rat_mem_adicInt_iff]

theorem isIntB_one_tmul_iff_exists_isIntegral : ∀ (L : Type) [Field L] [NumberField L] (κ : Type)
    (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  intro L _ _ κ ℓ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  set b := integralBasis L
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × Module.Free.ChooseBasisIndex ℤ (𝓞 L),
      algebraMap ℚ (v.adicCompletion ℚ) (ℓ.repr (b t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Module.Free.ChooseBasisIndex ℤ (𝓞 L) × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (ℓ t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv z => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨h1v, h2v⟩ := hv
  simp only [rat_mem_adicInt_iff] at h1v h2v
  rw [isIntB_one_tmul_iff]
  constructor
  · intro hz
    have hb : ∀ j, v.valuation ℚ (b.repr z j) ≤ 1 := fun j => by
      rw [repr_via b ℓ z j]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      exact mul_le_one' (hz i) (h2v (j, i))
    refine ⟨∏ j, ((b.repr z j).den : ℤ), ?_, ?_⟩
    · intro hd
      obtain ⟨j, _, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hd
      exact den_not_mem v _ (hb j) hj
    · set d : ℤ := ∏ j, ((b.repr z j).den : ℤ) with hd
      have hdv : ∀ j, ((b.repr z j).den : ℤ) ∣ d := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hmem : (d : L) * z ∈ Submodule.span ℤ (Set.range b) := by
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨fun j => d / ((b.repr z j).den : ℤ) * (b.repr z j).num, ?_⟩
        conv_rhs => rw [← b.sum_repr z]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hc : (((d / ((b.repr z j).den : ℤ) * (b.repr z j).num : ℤ)) : ℚ) = (d : ℚ) * b.repr z j := by
          have e1 := Int.ediv_mul_cancel (hdv j)
          conv_rhs => rw [← e1]
          rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, mul_comm ((b.repr z j).den : ℚ),
            Rat.mul_den_eq_num]
        rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, hc, mul_smul]
      obtain ⟨y, hy⟩ := (mem_span_integralBasis L).1 hmem
      rw [← hy]
      exact RingOfIntegers.isIntegral_coe y
  · rintro ⟨s, hs, hint⟩ i
    have hmem : (s : L) * z ∈ Submodule.span ℤ (Set.range b) := (mem_span_integralBasis L).2 ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
    have hsz : ℓ.repr ((s : L) * z) i = (s : ℚ) * ℓ.repr z i := by
      rw [← zsmul_eq_mul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    have hval : v.valuation ℚ (ℓ.repr ((s : L) * z) i) ≤ 1 := by

      rw [← hc, map_sum, Finsupp.finsetSum_apply]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, map_mul]
      have e : ((c j : ℤ) : ℚ) = algebraMap ℤ ℚ (c j) := rfl
      rw [e]
      exact mul_le_one' (v.valuation_le_one (c j)) (h1v (i, j))
    rwa [hsz, map_mul, valuation_int_eq_one v hs, one_mul] at hval

end GlobalTheory.AdicSpan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalCartan

theorem doubleCoset_of_hasDiv : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  intro D _ n P d x y hx hy hdx hdy
  obtain ⟨a, b, e⟩ := GlobalTheory.SphGal.HasDiv.exists_eq_mul_mul (O := Ov D.host.E P) (fun _ h => h) hdy hdx
  by_cases hs : IsSplitAt P
  · obtain ⟨φ, hφ⟩ := GlobalTheory.locU_equiv_GL D.host.E n P hs
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g := fun g => by rw [← hφ, φ.apply_symm_apply]
    refine ⟨φ.symm a, ⟨(φ.symm a).2, by rw [hc]; exact a.2⟩, φ.symm b, ⟨(φ.symm b).2, by rw [hc]; exact b.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm a * ⟨x, hx⟩ * φ.symm b := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply, hφ, hφ]
      exact e
    exact congrArg Subtype.val h
  · obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E P
      (GlobalTheory.ToricDistribution.host_unram P) hs
    obtain ⟨φ, hφ⟩ := GlobalTheory.DefU.Inert.locU_equiv D.host.E n P s hs hU.2.1
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g.1 := fun g => by rw [← hφ, φ.apply_symm_apply]
    obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := GlobalTheory.UnramDoubleCoset.doubleCoset_one hU _ (φ ⟨x, hx⟩).2 _ (φ ⟨y, hy⟩).2
      a a.2 b b.2 (by rw [hφ, hφ]; exact e)
    refine ⟨φ.symm ⟨k₁, hk₁.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₁.2⟩,
      φ.symm ⟨k₂, hk₂.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₂.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm ⟨k₁, hk₁.1⟩ * ⟨x, hx⟩ * φ.symm ⟨k₂, hk₂.1⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply]
      exact Subtype.ext e'
    exact congrArg Subtype.val h

end GlobalTheory.LocalCartan
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.map (pLoc E w) g).1 i j = pLoc E w (g.1 i j) := rfl

theorem loc_inv_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (pLoc E w) g)⁻¹).1 i j = pLoc E w ((g⁻¹).1 i j) := by
  rw [← map_inv]; rfl

theorem gl_ext {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g = Matrix.GeneralLinearGroup.map (pLoc E w) h) :
    g = h :=
  Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w =>
    congrArg (fun x : GLw n w => x.1 i j) (H w)))

theorem mem_KGL_iff {w : Pl E} {x : GLw n w} : x ∈ GlobalTheory.LFun.KGL w (n := n) ↔
    (∀ i j, x.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (x⁻¹).1 i j ∈ w.adicCompletionIntegers E :=
  GlobalTheory.AdelicU.mem_GLint_iff

theorem mem_Kglob {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    g ∈ Kglob E n ↔ ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp only [Kglob, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem coe_Kglob : (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    (PIW.ClassFinD.KGL E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  ext g
  change g ∈ Kglob E n ↔ PIW.ClassFinD.MatInt g.val ∧ PIW.ClassFinD.MatInt (g⁻¹).val
  rw [mem_Kglob]
  simp only [mem_KGL_iff, loc_val, loc_inv_val]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

theorem isCompact_Kglob : IsCompact (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  rw [coe_Kglob]; exact GlobalTheory.isCompact_KGL E n

theorem isOpen_Kglob : IsOpen (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  have hO : IsOpen ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} := by
    have e : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => M i j) ⁻¹'
          ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) := by
      ext M; simp [PIW.ClassFinD.MatInt]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((continuous_apply j).comp (continuous_apply i))
  rw [coe_Kglob]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage Units.continuous_coe_inv)

theorem mem_orb_iff (u w : Pl E) :
    w ∈ orb E u ↔ w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  rw [orb, Finset.mem_insert, Finset.mem_singleton, GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact GlobalTheory.SplitPts.conjPl_self_conjSrc u
  · have e := eq_conjSrc h
    change w = conjSrc (IsCMField.complexConj E).toRingEquiv u
    rw [e]
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm

end GlobalTheory.EulerTwRestr

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.EulerTwRestr

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | exact GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), s k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  first | exact @GlobalTheory.LeviDesc.LeviHoms.levi_homs | exact GlobalTheory.LeviDesc.LeviHoms.levi_homs | (intros; apply GlobalTheory.LeviDesc.LeviHoms.levi_homs <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.integers_act_integralChart_eigenDirections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), ∀ a : 𝓞 E, IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧ ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  first | exact @GlobalTheory.ChartAct.isIntHom_actX_and_eigen | exact GlobalTheory.ChartAct.isIntHom_actX_and_eigen | (intros; apply GlobalTheory.ChartAct.isIntHom_actX_and_eigen <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.embeddingReducedResidueField_bijective_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), UnramIn E p → Function.Bijective (red io X) := by
  first | exact @GlobalTheory.PrimePart.red_bijective | exact GlobalTheory.PrimePart.red_bijective | (intros; apply GlobalTheory.PrimePart.red_bijective <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_realPart_hom | exact GlobalTheory.CovTop.VolUp.exists_realPart_hom | (intros; apply GlobalTheory.CovTop.VolUp.exists_realPart_hom <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  first | exact @GlobalTheory.CovTop.VolUp.Proj.exists_proj | exact GlobalTheory.CovTop.VolUp.Proj.exists_proj | (intros; apply GlobalTheory.CovTop.VolUp.Proj.exists_proj <;> assumption)
end
