module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassOfSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem vF_eq_emultiplicity {F : Type} [Field F] [NumberField F] (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) (α : 𝓞 F) (hα : α ≠ 0) :
    ((vF 𝔭 α : ℕ) : ℕ∞) = emultiplicity 𝔭 (Ideal.span {α}) := by
  have hs : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hfm : FiniteMultiplicity 𝔭 (Ideal.span {α}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime h0 h𝔭) hs
  rw [hfm.emultiplicity_eq_multiplicity]
  congr 1
  unfold vF
  have hset : {e : ℕ | α ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {α})) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← hfm.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset, csSup_Iic]

end

theorem countExt_single (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : 𝓞 F) (h𝔭 : 𝔭.IsMaximal)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭) (hα : α ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (α : F))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * vF 𝔭 α : ℕ) : ℤ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  haveI : P.asIdeal.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hP]⟩
  set β : 𝓞 K := algebraMap (𝓞 F) (𝓞 K) α
  have hβ : β ≠ 0 := by
    intro h
    apply hα
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [map_zero]; exact h)
  have hsβ : Ideal.span {β} ≠ ⊥ := by simpa using hβ
  have hsα : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hK : algebraMap F K (α : F) = algebraMap (𝓞 K) K β := rfl
  rw [hK, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P hsβ,
    Ideal.count_associates_factors_eq hsβ P.isPrime P.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hsβ P]
  congr 1
  have hfmP : FiniteMultiplicity P.asIdeal (Ideal.span {β}) :=
    FiniteMultiplicity.of_prime_left P.prime hsβ
  have hmap : Ideal.span {β} = (Ideal.span {α}).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hsα
    (Ideal.prime_of_isPrime h0 h𝔭.isPrime).irreducible P.irreducible P.ne_bot
  rw [← hmap, hfmP.emultiplicity_eq_multiplicity, ← vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 α hα,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P.asIdeal h0] at he
  exact_mod_cast he

theorem count_extension : CountExt := by
  intro K F _ _ _ _ _ n 𝔭 P α h𝔭 hP hα
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hprod : (∏ j, ((α j : 𝓞 F) : F)) = ((∏ j, α j : 𝓞 F) : F) := by simp
  have hne : (∏ j, α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hα j
  rw [hprod, countExt_single K F 𝔭 P _ h𝔭 hP hne]
  congr 2
  have key : ((vF 𝔭 (∏ j, α j) : ℕ) : ℕ∞) = ((∑ j, vF 𝔭 (α j) : ℕ) : ℕ∞) := by
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ hne, ← Ideal.prod_span_singleton, Nat.cast_sum]
    rw [Finset.emultiplicity_prod (Ideal.prime_of_isPrime h0 h𝔭.isPrime)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ (hα j)]
  exact_mod_cast key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem count_coe_eq_multiplicity {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K) = (multiplicity v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coeIdeal K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]

theorem eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I J : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

def belowP {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (P : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))
  isPrime := P.isPrime.comap _
  ne_bot := by
    intro h
    have hmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax (NumberField.RingOfIntegers.not_isField F) h

theorem exists_above {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 K), belowP P = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem norm_mass_assembly : NormAssembly := by
  intro K F _ _ _ _ _ h2 J w hJ0 hc
  classical
  set wv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => w v.asIdeal with hwv

  have hcJ : ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J =
      ((P.asIdeal.ramificationIdx (𝓞 F) * wv (belowP P) : ℕ) : ℤ) := fun P =>
    hc _ P (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal) rfl
  have he : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
    intro P
    haveI := P.isPrime
    exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'

  have hfinJ := FractionalIdeal.finite_factors (K := K) J
  have hsupp : {v : HeightOneSpectrum (𝓞 F) | wv v ≠ 0}.Finite := by
    refine (hfinJ.image belowP).subset ?_
    intro v hv
    obtain ⟨P, rfl⟩ := exists_above (K := K) v
    refine ⟨P, ?_, rfl⟩
    show FractionalIdeal.count K P J ≠ 0
    rw [hcJ P]
    exact_mod_cast Nat.mul_ne_zero (he P) hv

  have hmsF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  set IF : Ideal (𝓞 F) := ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ wv v with hIF
  have hIF0 : IF ≠ ⊥ := by
    rw [hIF, finprod_eq_prod _ hmsF]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  have hcF : ∀ v : HeightOneSpectrum (𝓞 F), multiplicity v.asIdeal IF = wv v := by
    intro v
    have h1 := count_coe_eq_multiplicity (K := F) v hIF0
    have h2 : ((IF : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ u : HeightOneSpectrum (𝓞 F), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ ((wv u : ℕ) : ℤ) := by
      rw [hIF, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 F)) F le_rfl]
      simp_rw [FractionalIdeal.coeIdeal_pow, zpow_natCast]
    rw [h2, FractionalIdeal.count_finprod] at h1
    · exact_mod_cast h1.symm
    · show {u | ¬ ((wv u : ℕ) : ℤ) = 0}.Finite
      simpa using hsupp

  have hJ : J = ((IF.map (algebraMap (𝓞 F) (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have hm0 : IF.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hIF0
    refine eq_of_count_eq hJ0 (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]) fun P => ?_
    rw [hcJ P, count_coe_eq_multiplicity P hm0]
    haveI : P.asIdeal.LiesOver (belowP (K := K) (F := F) P).asIdeal := ⟨rfl⟩
    have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hIF0
      (belowP (K := K) (F := F) P).irreducible P.irreducible P.ne_bot
    rw [(FiniteMultiplicity.of_prime_left P.prime hm0).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left (belowP (K := K) (F := F) P).prime hIF0).emultiplicity_eq_multiplicity,
      hcF, Ideal.ramificationIdx'_eq_ramificationIdx _ P.asIdeal (belowP (K := K) (F := F) P).ne_bot] at hem
    exact_mod_cast hem.symm

  have hfr : Module.finrank (𝓞 F) (𝓞 K) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
    exact h2
  have hNJ : (FractionalIdeal.absNorm J : ℝ) = ((Ideal.absNorm IF : ℕ) : ℝ) ^ 2 := by
    rw [hJ, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap, hfr]
    push_cast
    rfl
  have hNIF : Ideal.absNorm IF = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^ wv v := by
    rw [hIF, map_finprod Ideal.absNorm hmsF]
    simp only [map_pow]
  have hms2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show Ideal.absNorm v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  have hms3 : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  let e : HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    { toFun := fun v => ⟨v.asIdeal, v.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField p.2 (NumberField.RingOfIntegers.not_isField F)⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  have ht : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    rw [← e.tprod_eq]
    exact tprod_eq_finprod hms3
  have hcast := map_finprod (Nat.castRingHom ℝ) hms2
  simp only [map_pow, eq_natCast] at hcast
  rw [hNJ, hNIF, ht, hcast]

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adjust

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def IsDual0 (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ a b, (VS D).hT (F0.e a) (g b) = if a = b then 1 else 0

def AggOK (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ v ∈ Λ, ycL F0 g v ∈ Λ

variable {F0}

theorem int_smul_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E}
    (hc : c ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) {v : (VS D).V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ o hv

theorem hT_g_e {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a b : Fin D.R.rS) :
    (VS D).hT (g a) (F0.e b) = if b = a then 1 else 0 := by
  rw [hT_swap D, hg b a]
  split_ifs <;> simp

theorem hT_g_xc {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a : Fin D.R.rS) (v : (VS D).V) :
    (VS D).hT (g a) (xcL F0 g v) = (VS D).hT (g a) v := by

  rw [xcL_apply, map_sum]
  simp [hT_g_e hg]

theorem hT_xc_yc (g : Fin D.R.rS → (VS D).V) (l w : (VS D).V) :
    (VS D).hT l (xcL F0 g w) = (VS D).hT (ycL F0 g l) w := by

  rw [xcL_apply, ycL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_smul, smul_eq_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hT_swap D,
    mul_comm]

theorem xc_agg {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V}
    (hok : AggOK F0 Λ g) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {w : (VS D).V} (hw : w ∈ Λ) :
    xcL F0 g w ∈ Λ := by
  have h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hu
  rw [← h, mem_dual_iff]
  intro l hl
  rw [hT_xc_yc]
  exact int_of_unimod hu (hok l hl) hw

theorem isSplitF_of {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f : Fin D.R.rS → (VS D).V}
    (hf : IsDualF F0 f) (hz : ∀ a, (VS D).hT (f a) F0.z = 0) (hok : AggOK F0 Λ f)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) : IsSplitF F0 Λ f := by
  refine ⟨hf, hz, ?_⟩
  intro v hv
  have hy : ycL F0 f v ∈ Λ := hok v hv
  have hw : v - ycL F0 f v ∈ Λ := Submodule.sub_mem _ hv hy
  have hx : xcL F0 f (v - ycL F0 f v) ∈ Λ := xc_agg hok hu hw
  refine ⟨xcL F0 f (v - ycL F0 f v), v - ycL F0 f v - xcL F0 f (v - ycL F0 f v), ycL F0 f v,
    hx, xc_mem_X _, Submodule.sub_mem _ hw hx, ?_, ?_, hy, yc_mem_span _, by abel⟩
  · intro a
    rw [map_sub, map_sub, hT_e_yc hf, sub_self, zero_sub, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), neg_zero]
  · intro a
    rw [map_sub, hT_f_xc hf, sub_self]

end Adjust

def RowDualFrame : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ g : Fin D.R.rS → (VS D).V, IsDual0 F0 g ∧ AggOK F0 Λ g

def RowZUnit : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ l0 ∈ Λ, l0 ∈ perpS (VS D) F0.X ∧ (VS D).hT l0 F0.z = 1

def TraceOne : Prop :=
  ∀ D : D7, ∃ t : 𝓞 D.host.E, (t : D.host.E) + star (t : D.host.E) = 1

section Assembly

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}

def gz (g : Fin D.R.rS → (VS D).V) (l0 : (VS D).V) : Fin D.R.rS → (VS D).V :=
  fun b => g b - (VS D).hT F0.z (g b) • l0

def giso (F0 : FlagG (VS D) D.R.rS T) (g : Fin D.R.rS → (VS D).V) (t : D.host.E) : Fin D.R.rS → (VS D).V :=
  fun b => g b - t • xcL F0 g (g b)

theorem gz_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {l0 : (VS D).V}
    (hl : l0 ∈ perpS (VS D) F0.X) : IsDual0 F0 (gz (F0 := F0) g l0) := by
  intro a b
  rw [gz, map_sub, map_smul, hl _ (e_mem_X F0 a), smul_zero, sub_zero, hg a b]

theorem hermForm_shifted_vector_zero {g : Fin D.R.rS → (VS D).V} {l0 : (VS D).V} (hl1 : (VS D).hT l0 F0.z = 1) (b : Fin D.R.rS) :
    (VS D).hT (gz (F0 := F0) g l0 b) F0.z = 0 := by
  rw [gz, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hl1, starRingEnd_apply, smul_eq_mul,
    mul_one, ← hT_swap D, sub_self]

theorem yc_gz (g : Fin D.R.rS → (VS D).V) (l0 v : (VS D).V) :
    ycL F0 (gz (F0 := F0) g l0) v = ycL F0 g v - (VS D).hT F0.z (ycL F0 g v) • l0 := by

  rw [ycL_apply, ycL_apply, map_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [gz, smul_sub, map_smul, smul_eq_mul, smul_smul]

theorem gz_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (hzΛ : F0.z ∈ Λ) {l0 : (VS D).V} (hl0 : l0 ∈ Λ) :
    AggOK F0 Λ (gz (F0 := F0) g l0) := by
  intro v hv
  rw [yc_gz]
  exact Submodule.sub_mem _ (hok v hv) (int_smul_mem (int_of_unimod hu hzΛ (hok v hv)) hl0)

theorem giso_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (t : D.host.E) : IsDual0 F0 (giso F0 g t) := by
  intro a b
  rw [giso, map_sub, map_smul, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), smul_zero, sub_zero, hg a b]

theorem hT_giso_z_eq_zero_of_hT_z_eq_zero {g : Fin D.R.rS → (VS D).V} (hz : ∀ b, (VS D).hT (g b) F0.z = 0) (t : D.host.E) (b : Fin D.R.rS) :
    (VS D).hT (giso F0 g t b) F0.z = 0 := by
  rw [giso, map_sub, LinearMap.sub_apply, hz b, map_smulₛₗ, LinearMap.smul_apply,
    hX_perp F0 (xc_mem_X _) (z_mem_perp D F0), smul_zero, sub_zero]

theorem yc_giso (g : Fin D.R.rS → (VS D).V) (t : D.host.E) (v : (VS D).V) :
    ycL F0 (giso F0 g t) v = ycL F0 g v - t • xcL F0 g (ycL F0 g v) := by

  rw [ycL_apply, ycL_apply, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [giso, smul_sub, map_smul, smul_comm]

theorem giso_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (t : 𝓞 D.host.E) : AggOK F0 Λ (giso F0 g (t : D.host.E)) := by
  intro v hv
  rw [yc_giso]
  refine Submodule.sub_mem _ (hok v hv) ?_
  rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, algebraMap_smul]
  exact Submodule.smul_mem _ t (xc_agg hok hu (hok v hv))

theorem giso_iso {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {t : D.host.E} (ht : t + star t = 1) :
    ∀ a b, (VS D).hT (giso F0 g t a) (giso F0 g t b) = 0 := by
  intro a b
  have h1 : (VS D).hT (g a) (xcL F0 g (g b)) = (VS D).hT (g a) (g b) := hT_g_xc hg a (g b)
  have h2 : (VS D).hT (xcL F0 g (g a)) (g b) = (VS D).hT (g a) (g b) := by
    rw [hT_swap D, hT_g_xc hg b (g a), ← hT_swap D]
  have h3 : (VS D).hT (xcL F0 g (g a)) (xcL F0 g (g b)) = 0 := hX_X F0 (xc_mem_X _) (xc_mem_X _)
  simp only [giso, map_sub, LinearMap.sub_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, h1, h2, h3, mul_zero]
  linear_combination (-(VS D).hT (g a) (g b)) * ht

end Assembly

theorem rowSplitF_of (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowSplitF := by
  intro D u F0 Λ hΛ
  obtain ⟨g, hg, hok⟩ := h1 D u F0 Λ hΛ
  obtain ⟨l0, hl0, hlp, hl1⟩ := h2 D u F0 Λ hΛ
  obtain ⟨t, ht⟩ := h3 D
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hzΛ : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have hg' := gz_dual hg hlp
  have hok' := gz_ok hok hu hzΛ hl0
  have hz' := hermForm_shifted_vector_zero (F0 := F0) (g := g) hl1
  have hd := giso_dual hg' (t : D.host.E)
  exact ⟨giso F0 (gz (F0 := F0) g l0) (t : D.host.E),
    isSplitF_of ⟨hd, giso_iso hg' ht⟩ (hT_giso_z_eq_zero_of_hT_z_eq_zero hz' _) (giso_ok hok' hu t) hu⟩

theorem rowClass_of_three (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowClass :=
  rowClass_of_split (rowSplitF_of h1 h2 h3)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
