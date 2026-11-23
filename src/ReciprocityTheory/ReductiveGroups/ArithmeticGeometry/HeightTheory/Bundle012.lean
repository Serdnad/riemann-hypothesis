module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle008
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle009
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

section
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

noncomputable abbrev algOTKT : Algebra (OT K D N) (KTf K D N) :=
  ((algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)).toAlgebra

noncomputable abbrev algOpKT (la : HeightOneSpectrum (𝓞 K)) : Algebra (Op D N la) (KTf K D N) :=
  (OpToKT D N la).toAlgebra

theorem isFractionRing_OT :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by
  set_option synthInstance.maxHeartbeats 200000 in
  letI := algOTKT (K := K) D N
  have hinj : Function.Injective (algebraMap (OT K D N) (KTf K D N)) :=
    (IsFractionRing.injective (KTp K D N) (KTf K D N)).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  haveI : FaithfulSMul (OT K D N) (KTf K D N) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (KTp K D N) z
  letI : Algebra (OT K D N) (KTp K D N) := MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := TVar D N) (nonZeroDivisors (𝓞 K)) K
  obtain ⟨⟨P, ⟨_, a, ha, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) p
  obtain ⟨⟨Q, ⟨_, b, hb, rfl⟩⟩, hQ⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) q
  refine ⟨P * MvPolynomial.C b, Q * MvPolynomial.C a, ?_⟩
  have e : ∀ X : OT K D N, algebraMap (OT K D N) (KTf K D N) X =
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) X) := fun X => rfl
  have hC : ∀ c ∈ nonZeroDivisors (𝓞 K),
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) (MvPolynomial.C c)) ≠ 0 := by
    intro c hc
    rw [← e]
    exact (map_ne_zero_iff _ hinj).mpr (by
      rw [Ne, MvPolynomial.C_eq_zero]; exact nonZeroDivisors.ne_zero hc)
  have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
      (nonZeroDivisors.ne_zero hq)
  simp only at hP hQ
  rw [e, e, map_mul, map_mul, map_mul, map_mul, ← hP, ← hQ, map_mul, map_mul]
  have ha := hC a ha
  have hb := hC b hb
  field_simp

theorem isFractionRing_Op (la : HeightOneSpectrum (𝓞 K)) :
    letI := algOpKT (K := K) D N la
    IsFractionRing (Op D N la) (KTf K D N) := by
  set_option synthInstance.maxHeartbeats 200000 in
  letI := algOTKT (K := K) D N
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_OT (K := K) D N
  haveI : IsScalarTower (OT K D N) (Op D N la) (KTf K D N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = OpToKT D N la (algebraMap _ _ x)
      rw [OpToKT, IsLocalization.lift_eq]
      rfl
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT D N la).primeCompl
    (Op D N la) (KTf K D N)

theorem OpToKT_injective (la : HeightOneSpectrum (𝓞 K)) : Function.Injective (OpToKT D N la) := by
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_Op (K := K) D N la
  exact IsFractionRing.injective (Op D N la) (KTf K D N)

omit [NumberField K] in
theorem unif_mem [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by
  have hex : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    refine ⟨π, ?_, ?_⟩
    · rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    · rw [← la.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]
      norm_num
  rw [Data.unif, dite_eq_left hex]
  exact hex.choose_spec

noncomputable def unifOp (la : HeightOneSpectrum (𝓞 K)) : Op D N la :=
  algebraMap (OT K D N) (Op D N la) (MvPolynomial.C (Data.unif la))

theorem unifOp_irreducible (la : HeightOneSpectrum (𝓞 K)) : Irreducible (unifOp D N la) := by
  classical
  haveI := Op_isDVR (K := K) D N la
  obtain ⟨hmem, hnot⟩ := unif_mem la
  have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
    IsLocalization.injective (Op D N la) (laT D N la).primeCompl_le_nonZeroDivisors
  have hne : unifOp D N la ≠ 0 := by
    intro h
    have h0 : MvPolynomial.C (Data.unif la) = (0 : OT K D N) := hinj (h.trans (map_zero _).symm)
    rw [MvPolynomial.C_eq_zero] at h0
    exact hnot (h0 ▸ zero_mem _)
  have hmax : unifOp D N la ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [unifOp, IsLocalization.AtPrime.to_map_mem_maximal_iff (Op D N la) (laT D N la)]
    exact Ideal.mem_map_of_mem _ hmem
  have hnu : ¬ IsUnit (unifOp D N la) := (IsLocalRing.mem_maximalIdeal _).mp hmax
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Op D N la)
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  rcases j with _ | _ | j
  · exact absurd (by rw [hu, pow_zero, mul_one]; exact u.isUnit) hnu
  · rw [hu, pow_one]
    exact (irreducible_isUnit_mul u.isUnit).mpr hϖ
  · exfalso
    have h2 : unifOp D N la ∈ (IsLocalRing.maximalIdeal (Op D N la)) ^ 2 := by
      have hpow : (u : Op D N la) * ϖ ^ (j + 1 + 1) = (u * ϖ ^ j) * (ϖ * ϖ) := by ring
      rw [hu, hpow, pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hϖm hϖm)
    have hL2 : laT D N la ^ 2 = Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) (la.asIdeal ^ 2) := by
      unfold laT
      rw [Ideal.map_pow]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, hL2,
      IsLocalization.mem_map_algebraMap_iff (laT D N la).primeCompl (Op D N la)] at h2
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := h2
    simp only [unifOp, ← map_mul] at hx
    have hx' := hinj hx
    rw [← hx', MvPolynomial.mem_map_C_iff] at ha
    have hs' : s ∉ Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal := hs
    rw [MvPolynomial.mem_map_C_iff, not_forall] at hs'
    obtain ⟨mm, hmm⟩ := hs'
    have h3 := ha mm
    rw [MvPolynomial.coeff_C_mul] at h3
    have v1 : la.intValuation (Data.unif la) = la.intValuation (Data.unif la) * la.intValuation (AddMonoidAlgebra.coeff s mm) := by
      have : la.intValuation (AddMonoidAlgebra.coeff s mm) = 1 := by
        apply le_antisymm (la.intValuation_le_one _)
        rw [← not_lt, la.intValuation_lt_one_iff_mem]
        exact hmm
      rw [this, mul_one]
    have h4 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [v1, ← map_mul]
      exact (la.intValuation_le_pow_iff_mem _ 2).mpr h3
    exact hnot ((la.intValuation_le_pow_iff_mem _ 2).mp h4)

theorem algK_unif (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by
  rw [unifOp, OpToKT, IsLocalization.lift_eq, RingHom.comp_apply, OTtoKT, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]

theorem exp_unique (la : HeightOneSpectrum (𝓞 K)) {m m' : ℤ} {u u' : Op D N la} (hu : IsUnit u)
    (hu' : IsUnit u')
    (h : (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u') : m = m' := by
  have key : ∀ {m m' : ℤ} {u u' : Op D N la}, IsUnit u → IsUnit u' →
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
        (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u' → m ≤ m' := by
    intro m m' u u' hu hu' h
    by_contra hlt
    push_neg at hlt
    have hϖ0 : algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
      rw [algK_unif]
      exact (map_ne_zero_iff _ (OpToKT_injective D N la)).mpr (unifOp_irreducible D N la).ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = m' + (k + 1 : ℕ) := ⟨(m - m' - 1).toNat, by omega⟩
    rw [hk, zpow_add₀ hϖ0, mul_assoc] at h
    have h' := mul_left_cancel₀ (zpow_ne_zero m' hϖ0) h
    rw [zpow_natCast, algK_unif, ← map_pow, ← map_mul] at h'
    have h'' := OpToKT_injective D N la h'
    have hunit : IsUnit (unifOp D N la ^ (k + 1) * u) := h'' ▸ hu'
    have := isUnit_of_mul_isUnit_left hunit
    exact (unifOp_irreducible D N la).not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp this)
  exact le_antisymm (key hu hu' h) (key hu' hu h.symm)

end

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem gOrd_eq (d : Data K ι Ω WT A) (la : HeightOneSpectrum (𝓞 K)) {q : KTf K d.D d.N} {m : ℤ}
    {u : Op d.D d.N la} (hu : IsUnit u)
    (hq : q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u) :
    d.gOrd la q = m := by
  classical
  have hex : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u :=
    ⟨m, u, hu, hq⟩
  rw [gOrd, dite_eq_left hex]
  obtain ⟨u', hu', hq'⟩ := hex.choose_spec
  exact exp_unique d.D d.N la hu' hu (hq'.symm.trans hq)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

abbrev PolyRingPositiveRowsBase : Type := MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K

abbrev PolyRingPositiveRowsOmega (c : ι) : Type := MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c)

abbrev FracFieldPositiveRowsBase : Type := FractionRing d.PolyRingPositiveRowsBase

abbrev FracFieldPositiveRowsOmega (c : ι) : Type := FractionRing (d.PolyRingPositiveRowsOmega c)

noncomputable def eLX4 : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) :=
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hL K d.D d.N)

noncomputable def eEX4 (c : ι) : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) :=
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c))

theorem eLX4_algebraMap (P : KTp K d.D d.N) :
    d.eLX4 (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1)) (FractionFieldVariableLift.hL K d.D d.N P) := by
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hL K d.D d.N) P

theorem eEX4_algebraMap (c : ι) (P : MvPolynomial (SVar d.D d.N) (Ω c)) :
    d.eEX4 c (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P) =
      FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1)) (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) P) := by
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c)) P

noncomputable def psiE (c : ι) : d.PolyRingPositiveRowsBase →+* d.FracFieldPositiveRowsOmega c :=
  (algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)).comp (d.offBaseSubstitution c).toRingHom

private theorem sumRingEquiv_X_inl' (R S₁ S₂ : Type) [CommSemiring R] (b : S₁) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
  MvPolynomial.sumRingEquiv_X_inl R S₁ S₂ b

private theorem sumRingEquiv_X_inr' (R S₁ S₂ : Type) [CommSemiring R] (q : S₂) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inr q)) =
      MvPolynomial.C (MvPolynomial.X q) :=
  MvPolynomial.sumRingEquiv_X_inr R S₁ S₂ q

private theorem sumRingEquiv_C' (R S₁ S₂ : Type) [CommSemiring R] (a : R) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) :=
  MvPolynomial.sumRingEquiv_C R S₁ S₂ a

theorem compat0 (c : ι) (P : KTp K d.D d.N) :
    d.eEX4 c (d.sH c P) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) _
      (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N P)) := by
  have hXlE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrE : ∀ q, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hXlL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrL : ∀ q, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hEX : ∀ p, FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) p =
      MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.rename (FractionFieldVariableLift.eS d.D d.N (d.jc c)) p) := fun p => rfl
  have hLX : ∀ p, FractionFieldVariableLift.hL K d.D d.N p =
      MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.rename (FractionFieldVariableLift.eT d.D d.N) p) := fun p => rfl
  have sac1 : ∀ {β : Type} (y : β) (p : Fin d.N → β),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p (d.jc c) = y :=
    fun y p => Fin.insertNth_apply_same (α := fun _ => _) _ y p
  have sac2 : ∀ {β : Type} (y : β) (p : Fin d.N → β) (k : Fin d.N),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p ((d.jc c).succAbove k) = p k :=
    fun y p k => Fin.insertNth_apply_succAbove (α := fun _ => _) _ y p k
  have hpsiC : ∀ a, d.offBaseSubstitution c (MvPolynomial.C a) = MvPolynomial.C (algebraMap K (Ω c) a) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, MvPolynomial.algebraMap_apply]
  have hpsiX : ∀ v, d.offBaseSubstitution c (MvPolynomial.X v) =
      Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
        (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2 := by
    intro v
    simp only [Data.offBaseSubstitution, MvPolynomial.aeval_X]
  have hpsi (p : d.PolyRingPositiveRowsBase) :
      d.psiE c p = algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)
        (d.offBaseSubstitution c p) := rfl
  have e1 : ∀ a, d.sH c (MvPolynomial.C a) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N) (MvPolynomial.C (algebraMap K (Ω c) a)) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, ← MvPolynomial.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have e2 : ∀ p, d.sH c (MvPolynomial.X p) = sImg (d.jc c) (d.x c) p := by
    intro p
    simp only [Data.sH, sHom, MvPolynomial.aeval_X]
  have key : (d.eEX4 c).toRingHom.comp (d.sH c).toRingHom =
      (algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))).comp
        ((MvPolynomial.map (d.psiE c)).comp (FractionFieldVariableLift.hL K d.D d.N).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show d.eEX4 c (d.sH c (MvPolynomial.C a)) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.C a)))
      simp [e1, d.eEX4_algebraMap, hEX, hLX, hCE, hCL, FractionFieldVariableLift.toFracY, hpsi, hpsiC]
    · rintro ⟨i, j⟩
      show d.eEX4 c (d.sH c (MvPolynomial.X (i, j))) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.X (i, j))))
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac1, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · set_option synthInstance.maxHeartbeats 100000 in
          simp [e2, sImg, sac1, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, hpsi, hpsiX, hpsiC]
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac2, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac2, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, hpsi, hpsiX]
  exact RingHom.congr_fun key P

theorem psiE_injective (h : d.S1) (c : ι) : Function.Injective (d.psiE c) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have e := d.compat0 c ((FractionFieldVariableLift.hL K d.D d.N).symm (MvPolynomial.C p))
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C, hp, map_zero, map_zero] at e
  have e2 := (RingEquiv.map_eq_zero_iff (d.eEX4 c)).mp e
  have e3 := h c (e2.trans (map_zero (d.sH c)).symm)
  have e4 : (MvPolynomial.C p : MvPolynomial (Fin (d.N + 1)) d.PolyRingPositiveRowsBase) = 0 := by
    rw [← RingEquiv.apply_symm_apply (FractionFieldVariableLift.hL K d.D d.N) (MvPolynomial.C p), e3, map_zero]
  exact MvPolynomial.C_eq_zero.mp e4

noncomputable def algLE (h : d.S1) (c : ι) : Algebra d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) :=
  (IsFractionRing.lift (A := d.PolyRingPositiveRowsBase) (K := d.FracFieldPositiveRowsBase) (d.psiE_injective h c)).toAlgebra

theorem algLE_algebraMap (h : d.S1) (c : ι) (p : d.PolyRingPositiveRowsBase) :
    letI := d.algLE h c;
    algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase p) = d.psiE c p := IsFractionRing.lift_algebraMap (d.psiE_injective h c) p

theorem fieldEquiv_compat_liftY (h : d.S1) (c : ι) (q : KTf K d.D d.N) :
    letI := d.algLE h c;
    d.eEX4 c (d.KTtoS h c q) = VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1)) (d.eLX4 q) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) q
  simp only [map_div₀]
  congr 1
  all_goals
    rw [show ∀ P : KTp K d.D d.N, d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      d.sH c P from fun P => IsFractionRing.lift_algebraMap _ _]
    rw [d.compat0 c, d.eLX4_algebraMap]
    unfold FractionFieldVariableLift.toFracY VariableBasisExtension.liftY
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.map_map]
    rw [show (@algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) _ _ (d.algLE h c)).comp (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase) =
      d.psiE c from RingHom.ext fun p => d.algLE_algebraMap h c p]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
