module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle003
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F mo) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : AddMonoidAlgebra.coeff F mo = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * AddMonoidAlgebra.coeff F mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := by
      have h1 := congrArg (AddMonoidAlgebra.coeff · mo) hQ
      rw [MvPolynomial.coeff_smul] at h1
      have h2 : AddMonoidAlgebra.coeff (toK K _ Q) mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (AddMonoidAlgebra.coeff Q mo)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IntAdeleComplete

open Formalism.UG Formalism.UG.P

variable {E : Type} [Field E] [NumberField E]

local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝒮" => tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ)

def ratBasis (E : Type) [Field E] [NumberField E] :
    Module.Basis (Fin (Module.finrank ℤ (𝓞 E))) ℚ E :=
  (Module.finBasis ℤ (𝓞 E)).localizationLocalization ℚ (nonZeroDivisors ℤ) E

theorem ratBasis_apply (j : Fin (Module.finrank ℤ (𝓞 E))) :
    ratBasis E j = algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) :=
  Module.Basis.localizationLocalization_apply _ _ _ _ _

def coord (i : Fin (Module.finrank ℤ (𝓞 E))) : E ⊗[ℚ] 𝔸 →ₗ[ℚ] 𝔸 :=
  (TensorProduct.lid ℚ 𝔸).toLinearMap ∘ₗ LinearMap.rTensor 𝔸 ((ratBasis E).coord i)

def comb : (Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) →+ E ⊗[ℚ] 𝔸 where
  toFun r := ∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem coord_comb (r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) (i : Fin (Module.finrank ℤ (𝓞 E))) :
    coord i (comb r) = r i := by
  change coord i (∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j) = r i

  rw [map_sum, Finset.sum_eq_single i]
  · rw [← ratBasis_apply]
    simp [coord]
  · intro j _ hj
    rw [← ratBasis_apply]
    simp [coord, hj]
  · simp

theorem comb_mem (r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) (hr : ∀ j, r j ∈ intAd ℚ) :
    comb r ∈ 𝒮 := by
  change (∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j) ∈ 𝒮
  exact sum_mem fun j _ => levelaf_tmul_mem _ (hr j)

theorem exists_comb {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) :
    ∃ r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸, (∀ j, r j ∈ intAd ℚ) ∧ s = comb r :=
  levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j) (Module.finBasis ℤ (𝓞 E)).span_eq hs

theorem coord_mem {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) (i : Fin (Module.finrank ℤ (𝓞 E))) :
    coord i s ∈ intAd ℚ := by
  obtain ⟨r, hr, rfl⟩ := exists_comb hs
  rw [coord_comb]
  exact hr i

theorem comb_coord {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) : comb (fun i => coord i s) = s := by
  obtain ⟨r, -, rfl⟩ := exists_comb hs
  simp only [coord_comb]

theorem tensInt_separated_complete (E : Type) [Field E] [NumberField E] :
    (∀ y : E ⊗[ℚ] 𝔸, (∀ N : ℕ, 0 < N →
      ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), y = (N : E ⊗[ℚ] 𝔸) * w) → y = 0) ∧
    ∀ x : ℕ → E ⊗[ℚ] 𝔸, (∀ N, x N ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ)) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ),
        x (N * m) = x N + (N : E ⊗[ℚ] 𝔸) * w) →
      ∃ y ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), ∀ N : ℕ, 0 < N →
        ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), y = x N + (N : E ⊗[ℚ] 𝔸) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.AdLat.integral_finiteAdele_complete_separated ℚ
  simp only [← nsmul_eq_mul]
  constructor
  · intro z hz
    have hz1 : z ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ) := by
      obtain ⟨w, hw, h⟩ := hz 1 one_pos
      rw [h, one_smul]; exact hw
    have : (fun i => coord i z) = 0 := by
      funext i
      refine hsep _ fun N hN => ?_
      obtain ⟨w, hw, h⟩ := hz N hN
      exact ⟨_, coord_mem hw i, by rw [h, map_nsmul]⟩
    rw [← comb_coord hz1, this, map_zero]
  · intro x hx hxx
    have key : ∀ i, ∃ y : 𝔸, ∀ N : ℕ, 0 < N → ∃ a : 𝔸,
        (∀ v, a v ∈ v.adicCompletionIntegers ℚ) ∧ y = coord i (x N) + N • a := by
      intro i
      refine hcpl (fun N => coord i (x N)) (fun N => coord_mem (hx N) i) fun N k hN hk => ?_
      obtain ⟨w, hw, h⟩ := hxx N k hN hk
      exact ⟨_, coord_mem hw i, by rw [h, map_add (f := _), map_nsmul]⟩
    choose y hy using key
    have main : ∀ N : ℕ, 0 < N → ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ),
        comb y = x N + N • w := by
      intro N hN
      choose a ha hya using fun i => hy i N hN
      refine ⟨comb a, comb_mem a ha, ?_⟩
      have : y = (fun i => coord i (x N)) + N • a := funext hya
      rw [this, map_add (f := _), map_nsmul, comb_coord (hx N)]
    refine ⟨comb y, ?_, main⟩
    obtain ⟨w, hw, h⟩ := main 1 one_pos
    rw [h]
    exact add_mem (hx 1) (nsmul_mem hw 1)


open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 in
theorem integral_separated_complete : ∀ (D : D7), (∀ y : AE D, (∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = (N : AE D) * w) → y = 0) ∧ ∀ x : ℕ → AE D, (∀ N, x N ∈ OhE D) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w) → ∃ y ∈ OhE D, ∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = x N + (N : AE D) * w :=
  fun D => tensInt_separated_complete D.host.E

end GlobalTheory.IntAdeleComplete
end
end
