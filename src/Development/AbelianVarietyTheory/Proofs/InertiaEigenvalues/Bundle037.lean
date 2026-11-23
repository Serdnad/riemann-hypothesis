module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

namespace GlobalTheory.IntegralNormSmallIdeal

open NumberField

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (y : PadicAlgCl l)
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (PadicAlgCl l) NNReal)
  have h2 : IsIntegral (Valued.v : Valuation (PadicAlgCl l) NNReal).integer y :=
    IsIntegral.tower_top hy
  have h3 := hv.isIntegral_iff_v_le_one.mp h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

theorem norm_natCast_prime {l : ℕ} [Fact (Nat.Prime l)] :
    ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h0 := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h0
  rw [h0]
  exact Padic.norm_p_lt_one

theorem norm_map_le_one {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  apply norm_le_one_of_isIntegral
  have h0 := (NumberField.RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  simpa using h0

def smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := map_add (algebraMap (𝓞 E) E) a b
    rw [this, map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have : ((0 : 𝓞 E) : E) = 0 := map_zero (algebraMap (𝓞 E) E)
    rw [this, map_zero, norm_zero]
    exact zero_lt_one
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
    have : ((r * x : 𝓞 E) : E) = (r : E) * (x : E) := map_mul (algebraMap (𝓞 E) E) r x
    rw [this, map_mul, norm_mul]
    calc ‖c (r : E)‖ * ‖c (x : E)‖ ≤ 1 * ‖c (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one c r) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

theorem mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ smallIdeal c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : (smallIdeal c).IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨?_, fun {x y} hxy => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · rw [mem_smallIdeal, mem_smallIdeal]
    rw [mem_smallIdeal] at hxy
    by_contra hcon
    push_neg at hcon
    have h1 := norm_map_le_one c x
    have h2 := norm_map_le_one c y
    have e : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := map_mul (algebraMap (𝓞 E) E) x y
    rw [e, map_mul, norm_mul] at hxy
    nlinarith [hcon.1, hcon.2]

theorem natCast_mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ smallIdeal c := by
  rw [mem_smallIdeal]
  have e : (((l : ℕ) : 𝓞 E) : E) = ((l : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) l
  rw [e, map_natCast]
  exact norm_natCast_prime

theorem exists_place_of_embedding {l : ℕ} [inst : Fact (Nat.Prime l)] {E : Type} [inst_1 : Field E]
    [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)),
      (↑l : NumberField.RingOfIntegers E) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ∧
      ∀ (x : NumberField.RingOfIntegers E), x ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ↔
        ‖(c : E → PadicAlgCl l) (↑x : E)‖ < (1 : ℝ) := by
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers E) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨⟨smallIdeal c, smallIdeal_isPrime c, fun h => hl0 ?_⟩, natCast_mem_smallIdeal c, fun x => mem_smallIdeal c x⟩
  have h0 := natCast_mem_smallIdeal (E := E) c
  rw [h] at h0
  exact (Submodule.mem_bot _).1 h0

end GlobalTheory.IntegralNormSmallIdeal
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_partition_one_integral_at_places (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'

end GlobalTheory
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem locBasis_of_bounded {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (M : Set (Fin d → F)) (h0 : (0 : Fin d → F) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hsmul : ∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hstd : ∀ i, Pi.single i 1 ∈ M)
    (hbd : ∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) :
    ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧
      (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧
      LinearIndependent F b := by
  obtain ⟨D, hD, hDM⟩ := hbd
  set A : ValuationSubring F := p.valuationSubringAtPrime F with hA
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _
  have memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1 := by
    intro a
    rw [hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  let M' : Submodule A (Fin d → F) :=
    { carrier := M
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        have : c • x = (c : F) • x := rfl
        rw [this]
        exact hsmul _ ((memA _).1 c.2) x hx }
  let e : Fin d → Fin d → F := fun i => D⁻¹ • Pi.single i 1
  have heF : LinearIndependent F e := by
    have h1 := (Pi.basisFun F (Fin d)).linearIndependent.units_smul
      (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))
    convert h1 using 1
    ext i j
    simp [e, Pi.basisFun_apply]
  have heA : LinearIndependent A e := (LinearIndependent.iff_fractionRing A F).2 heF
  have hle : M' ≤ Submodule.span A (Set.range e) := by
    intro x hx
    have hx' : x = ∑ i, (D * x i) • e i := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      rw [mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : D * x i ∈ A := (memA _).2 (hDM x hx i)
    have : (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bas⟩ := Submodule.basisOfPidOfLE hle (Module.Basis.span heA)
  refine ⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩
  · intro x hx
    refine ⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩
    have h := congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · have h1 : LinearIndependent A (M'.subtype ∘ bas) :=
      bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
    exact (LinearIndependent.iff_fractionRing A F).1 h1

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.PlaceTransport

theorem eq_of_forall_le_exp_neg {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  have key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ)) := fun n => by
    simpa only [WithZero.exp_le_exp] using h n
  have hkm : k ≤ m := by
    have := (key (-m).toNat).1 (by omega)
    omega
  have hmk : m ≤ k := by
    have := (key (-k).toNat).2 (by omega)
    omega
  rw [le_antisymm hmk hkm]

theorem intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl

theorem exists_place_valuation_comp_equiv :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
      (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K),
        ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  intro K L _ _ _ _ e la
  set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  refine ⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c) := fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]

end GlobalTheory.PlaceTransport
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem exists_notMem_mul_valuation_le_one_of_ne : ∀ {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (𝓞 F)) {ι : Type} [Finite ι] (x : ι → F), ∃ s : 𝓞 F, s ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ≠ p → ∀ i, q.valuation F ((s : F) * x i) ≤ 1 := by
  intro F _ _ p ι _ x
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) x
  have hc : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJp : ¬ J ≤ p.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨s, hsp, fun q hq i => ?_⟩
  have hpow : ¬ p.asIdeal ^ multiplicity p.asIdeal (Ideal.span {(b : 𝓞 F)}) ≤ q.asIdeal := by
    intro h
    have h1 : p.asIdeal ≤ q.asIdeal := q.isPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hpow
  have hts : t * s ∈ Ideal.span {(b : 𝓞 F)} := by
    rw [hJ]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hts
  obtain ⟨a, ha⟩ := hb i
  replace ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F (b : 𝓞 F) * x i := by
    rw [ha]; exact Algebra.smul_def _ _
  have key : algebraMap (𝓞 F) F t * ((s : F) * x i) = algebraMap (𝓞 F) F (u * a) := by
    rw [map_mul, ha, RingOfIntegers.coe_eq_algebraMap, ← mul_assoc, ← map_mul, hu, map_mul]
    ring
  have h1 : q.valuation F (algebraMap (𝓞 F) F t) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := F) (r := t)).2 htq
  have h2 : q.valuation F (algebraMap (𝓞 F) F (u * a)) ≤ 1 := q.valuation_le_one (K := F) _
  rw [← key, map_mul, h1, one_mul] at h2
  exact h2

end GlobalTheory
end

section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem integral_of_sq_sub_integral (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (hbi : ∀ i, IsIntegral ℤ (b i))
    (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E'))
    (hw : w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal) (ε : E')
    (hε : ∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) : w''.valuation E' ε ≤ 1 := by
  have hunder : w''.under (𝓞 E) = w := HeightOneSpectrum.ext hw
  have hc : ∀ c : E, w.valuation E c ≤ 1 → w''.valuation E' (algebraMap E E' c) ≤ 1 := by
    intro c hc
    subst hunder
    have : w''.asIdeal.LiesOver (w''.under (𝓞 E)).asIdeal := ⟨rfl⟩
    rw [← HeightOneSpectrum.valuation_liesOver E' (w''.under (𝓞 E)) w'' c]
    exact pow_le_one' hc _
  have hb : ∀ i, w''.valuation E' (b i) ≤ 1 := by
    intro i
    have : b i = algebraMap (𝓞 E') E' (⟨b i, (mem_integralClosure_iff ℤ E').2 (hbi i)⟩ : 𝓞 E') := rfl
    rw [this]
    exact w''.valuation_le_one _
  have hu : w''.valuation E' (ε * ε - ε) ≤ 1 := by
    rw [← b.sum_repr (ε * ε - ε)]
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (hc _ (hε i)) (hb i)
  by_contra h
  push_neg at h
  have h2 : w''.valuation E' (ε * ε) ≤ w''.valuation E' ε := by
    have : ε * ε = ε + (ε * ε - ε) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hu.trans h.le))
  rw [map_mul] at h2
  have h0 : (0 : _) < w''.valuation E' ε := lt_trans zero_lt_one h
  have := mul_lt_mul_of_pos_left h h0
  rw [mul_one] at this
  exact absurd h2 (not_le.2 this)

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory

theorem natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal :
    ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal →
      ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) →
      ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) →
        la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  intro l c K L _ _ _ _ _ la hl hD y hy
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d₀ ∈ differentIdeal (𝓞 K) (𝓞 L), d₀ ∉ la.asIdeal ^ (c + 1) := by
    by_contra h
    push_neg at h
    exact hD (Ideal.dvd_iff_le.mpr h)
  have h1 : la.intValuation ((l : 𝓞 L) ^ c) ≤ WithZero.exp (-(c : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ c).mpr (Ideal.pow_mem_pow hl c)
  have h2 : WithZero.exp (-(c : ℤ)) ≤ la.intValuation d₀ := by
    rw [HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le]
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem la,
      HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity, not_le] at hd₀
    rw [← ENat.lt_natCast_add_one_iff]
    exact_mod_cast hd₀
  have hyd := hy d₀ hd₀D
  have e1 : la.valuation L (d₀ : L) = la.intValuation d₀ := la.valuation_of_algebraMap (K := L) d₀
  have e2 : la.valuation L ((l : L) ^ c) = la.intValuation ((l : 𝓞 L) ^ c) := by
    rw [← la.valuation_of_algebraMap (K := L)]
    simp
  rw [Valuation.map_mul] at hyd ⊢
  calc la.valuation L ((l : L) ^ c) * la.valuation L y
      ≤ la.valuation L (d₀ : L) * la.valuation L y := by
        gcongr
        rw [e1, e2]
        exact h1.trans h2
    _ = la.valuation L y * la.valuation L (d₀ : L) := mul_comm _ _
    _ ≤ 1 := hyd

end GlobalTheory
end
