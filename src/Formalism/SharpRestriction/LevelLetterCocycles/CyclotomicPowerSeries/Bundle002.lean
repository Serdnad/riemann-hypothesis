module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

@[expose] public section

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem expRescale_coeff (S : Type) [CommRing S] [Algebra ℚ S] (E : PowerSeries S)
    (h0 : constantCoeff E = 1) (hd : PowerSeries.derivative E = E) (n : ℕ) :
    coeff n E = algebraMap ℚ S (1 / (n.factorial : ℚ)) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have h := congrArg (coeff n) hd
    rw [PowerSeries.coeff_derivative, ih] at h
    have hn : ((n : S) + 1) = algebraMap ℚ S ((n : ℚ) + 1) := by simp
    rw [hn] at h
    have hu : coeff (n + 1) E =
        coeff (n + 1) E * algebraMap ℚ S ((n : ℚ) + 1) * algebraMap ℚ S (1 / ((n : ℚ) + 1)) := by
      rw [mul_assoc, ← map_mul, mul_one_div_cancel (by positivity), map_one, mul_one]
    rw [hu, h, ← map_mul, Nat.factorial_succ]
    congr 1
    push_cast
    field_simp

theorem expRescale : ExpRescaleStatement := by
  intro S _ _ E h0 hd
  have hE : E = PowerSeries.exp S := by
    ext n
    rw [expRescale_coeff S E h0 hd n, PowerSeries.coeff_exp]
  refine ⟨hE, fun a => ?_⟩
  rw [hE, PowerSeries.exp_pow_eq_rescale_exp]

end LevelStatements.Lv
end
end

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

theorem polynomial_coe_powerSeries_eq_aeval_X {O : Type*} [CommRing O] (P : Polynomial O) :
    (P : PowerSeries O) = Polynomial.aeval (X : PowerSeries O) P := by
  rw [Polynomial.aeval_def]
  exact Polynomial.eval₂_C_X_eq_coe.symm

theorem psCyclo_algHom_coe {O : Type*} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (P : Polynomial O) : φ (P : PowerSeries O) = Polynomial.aeval (φ X) P := by
  rw [polynomial_coe_powerSeries_eq_aeval_X P]
  exact (Polynomial.aeval_algHom_apply φ X P).symm

theorem psCyclo_step {O : Type*} [CommRing O] (l : ℕ) (hl : l.Prime)
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ X = (1 + X) ^ l - 1) (m : ℕ) (hm : l ∣ m) :
    φ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      (((Polynomial.cyclotomic (m * l) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
  rw [psCyclo_algHom_coe, polynomial_coe_powerSeries_eq_aeval_X,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic hl hm]
  simp only [Polynomial.aeval_comp, Polynomial.expand_aeval, hφ, map_add (f := _), Polynomial.aeval_X,
    map_one]
  exact congrArg (fun y => Polynomial.aeval y (Polynomial.cyclotomic m O)) (by ring)

theorem psCyclo : PsCycloStatement := by
  unfold PsCycloStatement
  intro O _ l hl φ hφ q w hq s
  induction s with
  | zero => exact ⟨w, by rw [Function.iterate_zero_apply, zero_add, pow_one]; exact hq⟩
  | succ s ih =>
    obtain ⟨w', hw'⟩ := ih
    refine ⟨Units.map (φ : PowerSeries O →* PowerSeries O) w', ?_⟩
    rw [Function.iterate_succ_apply', hw', map_mul,
      psCyclo_step l hl φ hφ (l ^ (s + 1)) (dvd_pow_self l (Nat.succ_ne_zero s)),
      ← pow_succ]
    all_goals simp

end LevelStatements.Lv
end
end

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_powerSeries_coe_eq_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (ρ : PowerSeries O →ₐ[O] PowerSeries S) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  have h : ρ.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (ρ X) := by
    apply Polynomial.algHom_ext
    simp [Polynomial.coeToPowerSeries.algHom_apply]
  have h2 := congrArg (fun f => f r) h
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using h2

theorem exists_pow_mul_add_polynomial {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O)) (k : ℕ) (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), a = (P : PowerSeries O) ^ k * q + (r : PowerSeries O) := by
  have hm : (P ^ k).Monic := hP.monic.pow k
  have hne : PowerSeries.map (residue O) ((P ^ k : Polynomial O) : PowerSeries O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
    exact (hm.map (residue O)).ne_zero
  obtain ⟨q, r, h⟩ := PowerSeries.exists_isWeierstrassDivision a hne
  refine ⟨q, r, ?_⟩
  rw [← Polynomial.coe_pow]
  exact h.2

theorem rhoUnique : RhoUniqueStatement := by
  intro O S _ _ _ _ _ P hP ρ ρ' hX h0
  have hpoly : ∀ r : Polynomial O, ρ (r : PowerSeries O) = ρ' (r : PowerSeries O) := by
    intro r
    rw [algHom_powerSeries_coe_eq_aeval, algHom_powerSeries_coe_eq_aeval, hX]
  have hdvd : X ∣ ρ (P : PowerSeries O) := by
    rw [PowerSeries.X_dvd_iff, algHom_powerSeries_coe_eq_aeval]
    exact h0
  apply AlgHom.ext
  intro a
  ext n
  obtain ⟨q, r, hqr⟩ := exists_pow_mul_add_polynomial P hP (n + 1) a
  have hd : ρ a - ρ' a = ρ (P : PowerSeries O) ^ (n + 1) * (ρ q - ρ' q) := by
    rw [hqr, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, hpoly r, ← hpoly P]
    ring
  have hX' : X ^ (n + 1) ∣ ρ a - ρ' a := by
    rw [hd]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdvd _) _
  have h1 := (PowerSeries.X_pow_dvd_iff.mp hX') n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h1
  exact h1

end LevelStatements.Lv
end
end

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_coe_eq_aeval {O T : Type} [CommRing O] [CommRing T] [Algebra O T]
    (ρ : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    all_goals first
      | exact ρ.commutes a

theorem constantCoeff_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    all_goals first
      | rfl
      | simp [PowerSeries.algebraMap_apply'']
      | (rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)

theorem eq_of_X_mul_eq {S : Type} [CommRing S] {f g : PowerSeries S}
    (h : (X : PowerSeries S) * f = X * g) : f = g := by
  first
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff (n + 1)) h)

private theorem map_coe_eq_X_pow_lemma {O K : Type} [CommRing O] [CommRing K] (I : Ideal O) (f : O →+* K)
    (hf : ∀ c ∈ I, f c = 0) (P : Polynomial O) (hP : P.IsDistinguishedAt I) :
    PowerSeries.map f (P : PowerSeries O) = X ^ P.natDegree := by
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have hmem : ∀ {n : ℕ}, n < P.natDegree → P.coeff n ∈ I := by
    intro n hn
    first | exact hP.mem hn | exact hP.1.mem hn | exact hP.toIsWeaklyEisensteinAt.mem hn
  ext n
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, PowerSeries.coeff_X_pow]
  split_ifs with hn
  · rw [hn, hmon.coeff_natDegree, map_one]
  · rcases Nat.lt_or_gt_of_ne hn with h | h
    · exact hf _ (hmem h)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]

private theorem exists_weierstrass_div_lemma_2 {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O))
    (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < P.natDegree ∧
      a = (P : PowerSeries O) * q + r := by
  have h1 : PowerSeries.map (residue O) (P : PowerSeries O) = X ^ P.natDegree :=
    map_coe_eq_X_pow_lemma _ _ (fun c hc => (residue_eq_zero_iff c).2 hc) P hP
  have h2 : (PowerSeries.map (residue O) (P : PowerSeries O)).order.toNat = P.natDegree := by
    rw [h1, PowerSeries.order_X_pow]; rfl
  have h3 : PowerSeries.map (residue O) (P : PowerSeries O) ≠ 0 := by
    rw [h1]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hr, he⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) h3
  have h2' : (PowerSeries.map (Ideal.Quotient.mk (maximalIdeal O)) (P : PowerSeries O)).order.toNat =
      P.natDegree := by
    first
      | exact h2
  refine ⟨q, r, ?_, he⟩
  first
    | (rw [h2'] at hr; exact hr)

theorem rhoCompl : RhoComplStatement := by
  intro O LL S _ _ _ _ _ _ _ _ _ _ _ P hP ρ hunit hann
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have key : ∀ a : PowerSeries O, (X : PowerSeries S) ∣ ρ a → (P : PowerSeries O) ∣ a := by
    intro a ha
    obtain ⟨q, r, hr, he⟩ := exists_weierstrass_div_lemma_2 P hP a
    obtain ⟨w, hw⟩ := hunit
    have hρa : ρ a = (w : PowerSeries S) * X * ρ q + Polynomial.aeval (ρ X) r := by
      rw [he, map_add (f := _), map_mul, hw, algHom_coe_eq_aeval]
    have h0 : constantCoeff (ρ a) = 0 := by
      obtain ⟨c, hc⟩ := ha
      rw [hc, map_mul, PowerSeries.constantCoeff_X, zero_mul]
    have hr0 : Polynomial.aeval (constantCoeff (ρ X)) r = 0 := by
      have h1 := congrArg constantCoeff hρa
      rw [h0, map_add (f := _), map_mul, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul, zero_add,
        constantCoeff_aeval] at h1
      exact h1.symm
    have hdvd : P.map (algebraMap O LL) ∣ r.map (algebraMap O LL) := by
      apply hann
      first | (rw [Polynomial.aeval_map_algebraMap]; exact hr0) | simpa [Polynomial.aeval_map_algebraMap] using hr0
    have hmap0 : r.map (algebraMap O LL) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
      calc (r.map (algebraMap O LL)).degree ≤ r.degree := by
            first | exact Polynomial.degree_map_le | exact Polynomial.degree_map_le _ _
        _ < P.natDegree := hr
        _ = P.degree := (Polynomial.degree_eq_natDegree hmon.ne_zero).symm
        _ = (P.map (algebraMap O LL)).degree := (hmon.degree_map _).symm
    have hr' : r = 0 := by
      apply Polynomial.map_injective (algebraMap O LL) (IsFractionRing.injective O LL)
      rw [hmap0, Polynomial.map_zero]
    rw [hr', Polynomial.coe_zero, add_zero] at he
    exact ⟨q, he⟩
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := key a (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) ha)
    obtain ⟨w, hw⟩ := hunit
    rw [map_mul, hw] at ha
    obtain ⟨c, hc⟩ := ha
    have h2 : (w : PowerSeries S) * ρ b = X ^ k * c := by
      apply eq_of_X_mul_eq
      linear_combination hc
    have hb : (X : PowerSeries S) ^ k ∣ ρ b := by
      refine ⟨(↑w⁻¹ : PowerSeries S) * c, ?_⟩
      calc ρ b = (↑w⁻¹ : PowerSeries S) * ((w : PowerSeries S) * ρ b) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = (↑w⁻¹ : PowerSeries S) * (X ^ k * c) := by rw [h2]
        _ = X ^ k * ((↑w⁻¹ : PowerSeries S) * c) := by ring
    obtain ⟨d, hd⟩ := ih b hb
    exact ⟨d, by rw [hd]; ring⟩

end LevelStatements.Lv
end
end

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

private theorem constantCoeff_aeval_eq_aeval_constantCoeff {S : Type} [CommRing S] (Q : Polynomial S) (y : PowerSeries S) :
    constantCoeff (Polynomial.aeval y Q) = Polynomial.aeval (constantCoeff y) Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1

theorem cycloSimple : CycloSimpleStatement := by
  intro LL S _ _ _ _ m hm ζ E hζ hE0 hE
  have hζm : ζ ^ m = 1 := by
    obtain ⟨q, hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m LL
    have h := congrArg (Polynomial.aeval ζ) hq
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.1 h
  have hζu : IsUnit ζ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hmul : ζ * ζ ^ k = 1 := by rw [← pow_succ']; exact hζm
    exact ⟨⟨ζ, ζ ^ k, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  set Φ := Polynomial.cyclotomic m LL with hΦ
  have hsep : Φ.Separable :=
    (Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hm.ne')).of_dvd
      (Polynomial.cyclotomic.dvd_X_pow_sub_one m LL)
  obtain ⟨a, b, hab⟩ := hsep
  have hu : IsUnit (Polynomial.aeval ζ (Polynomial.derivative Φ)) := by
    have h := congrArg (Polynomial.aeval ζ) hab
    simp only [map_add (f := _), map_mul, map_one, hζ, mul_zero, zero_add] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  set y : PowerSeries S := C ζ * E with hy
  have hy0 : constantCoeff y = ζ := by simp [hy, hE0]
  have hyd : derivative y = y := by
    simp [hy, Derivation.leibniz, derivative_C, hE, smul_eq_mul]
  have hF : Polynomial.aeval y Φ = Polynomial.aeval y (Φ.map (algebraMap LL S)) :=
    (Polynomial.aeval_map_algebraMap S y Φ).symm
  have h0 : constantCoeff (Polynomial.aeval y Φ) = 0 := by
    rw [hF, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.aeval_map_algebraMap, hζ]
  have h1 : constantCoeff (derivative (Polynomial.aeval y Φ)) =
      Polynomial.aeval ζ (Polynomial.derivative Φ) * ζ := by
    rw [hF, Derivation.map_aeval, hyd, smul_eq_mul, map_mul, constantCoeff_aeval_eq_aeval_constantCoeff, hy0,
      Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hGc : constantCoeff (derivative (Polynomial.aeval y Φ)) = constantCoeff G := by
    rw [hG]
    simp [Derivation.leibniz, derivative_X, smul_eq_mul]
  have hGu : IsUnit G := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← hGc, h1]
    exact hu.mul hζu
  refine ⟨hGu.unit, ?_⟩
  rw [IsUnit.unit_spec, hG, mul_comm]

end LevelStatements.Lv
end
end

section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem powerSeries_algHom_C' {O : Type} [CommRing O] (ψ : PowerSeries O →ₐ[O] PowerSeries O) (c : O) :
    ψ (C c) = C c := by
  first
  | exact ψ.commutes c
  | (have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by
       rw [PowerSeries.smul_eq_C_mul, mul_one]
     rw [e, map_smul, map_one])
  | simpa using ψ.commutes c

theorem psCoprime_dvdSub {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    (X * (X + C (l : O)) : PowerSeries O) ∣ φ a - C (constantCoeff a) := by
  obtain ⟨b, hb⟩ : (X : PowerSeries O) ∣ a - C (constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have e : φ (a - C (constantCoeff a)) = φ a - C (constantCoeff a) := by
    rw [map_sub, powerSeries_algHom_C']
  rw [← e, hb, map_mul]
  exact dvd_mul_of_dvd_left h _

private theorem constantCoeff_algHom_eq_of_X_mul_dvd {O : Type} [CommRing O] (l : ℕ)
    (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    constantCoeff (φ a) = constantCoeff a := by
  have h1 := psCoprime_dvdSub l φ h a
  have h2 : (X : PowerSeries O) ∣ φ a - C (constantCoeff a) :=
    dvd_trans (dvd_mul_right (X : PowerSeries O) _) h1
  rw [PowerSeries.X_dvd_iff] at h2
  first
  | simpa [sub_eq_zero] using h2
  | (rw [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h2; exact h2)

theorem psCoprime_cc {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s : ℕ) :
    constantCoeff ((⇑φ)^[s] (X + C (l : O))) = (l : O) := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', constantCoeff_algHom_eq_of_X_mul_dvd l φ h, ih]

theorem psCoprime_qdvd {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (t : ℕ) :
    (X + C (l : O) : PowerSeries O) ∣ (⇑φ)^[t + 1] (X + C (l : O)) - C (l : O) := by
  rw [Function.iterate_succ_apply']
  have h1 := psCoprime_dvdSub l φ h ((⇑φ)^[t] (X + C (l : O)))
  rw [psCoprime_cc l φ h t] at h1
  exact dvd_trans (dvd_mul_left _ _) h1

private theorem algHom_iterate_C_add_mul {O : Type} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (c : O) (s : ℕ) (b d : PowerSeries O) :
    (⇑φ)^[s] (C c + b * d) = C c + (⇑φ)^[s] b * (⇑φ)^[s] d := by
  induction s with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, map_add (f := _), map_mul, powerSeries_algHom_C']

theorem psCoprime_lt {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s s' : ℕ) (hs : s < s') :
    (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), (⇑φ)^[s'] (X + C (l : O))} := by
  obtain ⟨t, rfl⟩ : ∃ t, s' = s + (t + 1) := ⟨s' - s - 1, by omega⟩
  obtain ⟨q, hq⟩ := psCoprime_qdvd l φ h t
  have hq' : (⇑φ)^[t + 1] (X + C (l : O)) = C (l : O) + (X + C (l : O)) * q := by
    linear_combination hq
  have e : (⇑φ)^[s + (t + 1)] (X + C (l : O)) =
      C (l : O) + (⇑φ)^[s] (X + C (l : O)) * (⇑φ)^[s] q := by
    rw [Function.iterate_add_apply, hq', algHom_iterate_C_add_mul]
  rw [Ideal.mem_span_pair]
  exact ⟨-((⇑φ)^[s] q), 1, by linear_combination e⟩

theorem psCoprime : PsCoprimeStatement := by
  unfold PsCoprimeStatement
  intro O _ l φ h
  refine ⟨fun s => ?_, fun s s' hss => ?_⟩
  · have hc := psCoprime_cc l φ h s
    obtain ⟨r, hr⟩ : (X : PowerSeries O) ∣ (⇑φ)^[s] (X + C (l : O)) - C (l : O) := by
      rw [PowerSeries.X_dvd_iff, map_sub, hc]
      first
      | simp
      | rw [PowerSeries.constantCoeff_C, sub_self]
    rw [Ideal.mem_span_pair]
    exact ⟨1, -r, by linear_combination hr⟩
  · rcases Nat.lt_or_gt_of_ne hss with hlt | hlt
    · exact psCoprime_lt l φ h s s' hlt
    · rw [Set.pair_comm]
      exact psCoprime_lt l φ h s' s hlt

end LevelStatements.Lv
end
end
