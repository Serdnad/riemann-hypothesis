module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle043
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle017
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit :
    {K V : Type} →
      [inst : Field K] →
        [inst_1 : StarRing K] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module K V] → Subring K → (V →ₗ⋆[K] V →ₗ[K] K) → Prop :=
    fun {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) ↦
      ∀ (w y : V),
        ((h : V → V →ₗ[K] K) y : V → K) w = (1 : K) →
          ((h : V → V →ₗ[K] K) w : V → K) w ∈ S →
            ((h : V → V →ₗ[K] K) y : V → K) y ∈ S →
              ∃ c ∈ S,
                ∃ d ∈ S, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (c • w + d • y) : V → K) (c • w + d • y))


open Formalism.HermitianLattices.Ext.L3.WA in
private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S)
    (hn : h.Nondegenerate) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) {v : V} (hv : v ≠ 0) :
    ∃ a : K, a • v ∈ L ∧ ∃ w ∈ L, h w (a • v) = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ L, h m v = a}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', L.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, L.neg_mem hm, by simp⟩ }
  have hmul : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨star s • m, hL.smul_mem _ (hS.star_mem s hs) _ hm, by
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]⟩
  have hne : ∃ a ∈ A, a ≠ 0 := by
    have hu : ∃ u, h u v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (hn.2 v hc)
    obtain ⟨u, hu⟩ := hu
    obtain ⟨t, ht, htu⟩ := hL.span u
    refine ⟨_, ⟨t • u, htu, rfl⟩, ?_⟩
    simp [map_smulₛₗ, ht, hu]
  have hbd : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htv⟩ := hL.span v
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hL.int m hm _ htv
  obtain ⟨α, ⟨w, hw, hα⟩, hα0, hdiv⟩ := hS.principal A hmul hne hbd
  refine ⟨α⁻¹, hL.dual _ fun m hm => ?_, w, hw, ?_⟩
  · simpa [mul_comm] using hdiv _ ⟨m, hm, rfl⟩
  · rw [map_smul, hα, smul_eq_mul, inv_mul_cancel₀ hα0]


open Formalism.HermitianLattices.Ext.L3.WA in
private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hS : IsHermSemilocal S) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hp : UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L)
    {k : ℕ} (hk : k < Module.finrank K V) (x : Fin k → V) (hxL : ∀ i, x i ∈ L)
    (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ z ∈ L, (∀ i, h (x i) z = 0) ∧ IsUnitIn S (h z z) := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let φ : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (x i)
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxv : ∀ i, h (x i) v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hvk) i
  obtain ⟨a, hyL, w₀, hw₀, hwy⟩ := UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive hS hn hL hv0
  have hxy : ∀ i, h (x i) (a • v) = 0 := fun i => by rw [map_smul, hxv, smul_zero]
  generalize a • v = y at hyL hwy hxy
  have hyx : ∀ i, h y (x i) = 0 := fun i => by rw [← hsym, hxy, star_zero]
  have hyw₀ : h y w₀ = 1 := by rw [← hsym, hwy, star_one]
  let w : V := w₀ - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) w₀) • x i
  have hwL : w ∈ L :=
    L.sub_mem hw₀ (L.sum_mem fun i _ =>
      hL.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hw₀)) _ (hxL i))
  have hyw : h y w = 1 := by

    simp [w, map_sub, map_sum, hyx, hyw₀]
  have hxw : ∀ j, h (x j) w = 0 := by
    intro j
    have hj := (hxu j).1

    simp only [w, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · field_simp
      ring
    · intro i _ hij
      rw [hxo j i hij.symm, mul_zero]
    · simp
  obtain ⟨c, hc, d, hd, hu⟩ := hp w y hyw (hL.int _ hwL _ hwL) (hL.int _ hyL _ hyL)
  refine ⟨c • w + d • y, L.add_mem (hL.smul_mem _ hc _ hwL) (hL.smul_mem _ hd _ hyL), fun i => ?_, hu⟩
  rw [map_add (f := _), map_smul, map_smul, hxw, hxy, smul_zero, smul_zero, add_zero]

theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit :
    ∀ {K V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} [FiniteDimensional K V],
      Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal S →
        h.IsSymm →
          h.Nondegenerate →
            UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h →
              ∀ {L : AddSubgroup V},
                Formalism.HermitianLattices.Ext.L3.WA.IsSelfDualMod S h L →
                  ∃ (x : Fin (Module.finrank K V) → V),
                    (∀ (i : Fin (Module.finrank K V)), x i ∈ L) ∧
                      (∀ (i j : Fin (Module.finrank K V)), i ≠ j → ((h : V → V →ₗ[K] K) (x i) : V → K) (x j) = (0 : K)) ∧
                        ∀ (i : Fin (Module.finrank K V)),
                          Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (x i) : V → K) (x i)) := by
  intro K V _ _ _ _ S h _ hS hs hn hp L hL
  have key : ∀ k : ℕ, k ≤ Module.finrank K V → ∃ x : Fin k → V, (∀ i, x i ∈ L) ∧
      (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
        ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxL, hxo, hxu⟩ := ih (by omega)
      obtain ⟨z, hzL, hxz, hzu⟩ :=
        UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend hS hs hn hp hL (by omega) x hxL hxo hxu
      have hzx : ∀ i, h z (x i) = 0 := fun i => by
        rw [← hs.eq, hxz, map_zero]
      refine ⟨Fin.cons z x, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzL
        · simpa using hxL i
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hzx j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hxz i
          | succ j => simpa using hxo i j fun e => hij (by rw [e])
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzu
        · simpa using hxu i
  exact key _ le_rfl
end

section

open IsDedekindDomain ValuativeRel nonZeroDivisors

namespace UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset

private lemma approx_one {F K : Type*} [Field F] [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsValuativeTopology K] (ι : F →+* K) (hd : DenseRange ι) (b c : K) (hc : c ≠ 0) :
    ∃ a : F, valuation K (ι a - b) ≤ valuation K c := by
  have hv : valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hn : {z | valuation K (z - b) < (Units.mk0 _ hv : (ValueGroupWithZero K)ˣ)} ∈ nhds b :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨_, subset_rfl⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds hn
  exact ⟨a, le_of_lt ha⟩

private lemma val_eq_exp {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (q : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    ∃ n : ℕ, q.valuation K (algebraMap R K r) = WithZero.exp (-(n : ℤ)) :=
  ⟨_, by rw [HeightOneSpectrum.valuation_of_algebraMap, q.intValuation_if_neg hr]⟩

private lemma val_le_of_mem {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (q : HeightOneSpectrum R) {r : R} {n : ℕ} (h : r ∈ q.asIdeal ^ n) :
    q.valuation K (algebraMap R K r) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (q.intValuation_le_pow_iff_mem r n).2 h

private lemma core {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (c : R) (hc : c ≠ 0)
    (a : HeightOneSpectrum R → K) :
    ∃ f : K, (∀ p ∈ S, p.valuation K (f - a p) ≤ p.valuation K (algebraMap R K c)) ∧
      ∀ p ∉ S, p.valuation K f ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples R⁰ S a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdK : algebraMap R K (d : R) ≠ 0 := by
    simpa using hd0
  have hcd : c * (d : R) ≠ 0 := mul_ne_zero hc hd0
  choose x hx using fun i : S => hd i.1 i.2
  choose m hm using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hcd
  choose m' hm' using fun q : HeightOneSpectrum R => val_eq_exp (K := K) q hd0
  have hI : (Ideal.span {(d : R)} : Ideal R) ≠ 0 := by
    simpa using hd0
  let T : Finset (HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : HeightOneSpectrum R → ℕ := fun q => if q ∈ S then m q else m' q
  let t : T → R := fun i => if h : i.1 ∈ S then x ⟨i.1, h⟩ else 0
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun q : HeightOneSpectrum R => q.asIdeal) e (fun q _ => q.prime)
    (fun q _ q' _ hne h => hne (HeightOneSpectrum.ext h)) t
  refine ⟨algebraMap R K y / algebraMap R K (d : R), fun p hp => ?_, fun p hp => ?_⟩
  · have hpT : p ∈ T := Finset.mem_union_left _ hp
    have h1 := hy p hpT
    have ht : t ⟨p, hpT⟩ = x ⟨p, hp⟩ := by simp [t, hp]
    have he : e p = m p := by simp [e, hp]
    rw [ht, he] at h1
    have h2 := val_le_of_mem (K := K) p h1
    rw [← hm p, map_mul, map_mul, map_sub] at h2
    have hxa : algebraMap R K (x ⟨p, hp⟩) = algebraMap R K (d : R) * a p := by
      rw [hx ⟨p, hp⟩, Algebra.smul_def]
    have hf : algebraMap R K y / algebraMap R K (d : R) - a p =
        (algebraMap R K y - algebraMap R K (x ⟨p, hp⟩)) / algebraMap R K (d : R) := by
      rw [hxa]; field_simp
    have hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0 := (Valuation.ne_zero_iff _).2 hdK
    rw [hf, map_div₀]
    exact div_le_of_le_mul₀ (zero_le') (zero_le') h2
  · rw [map_div₀]
    have hvd : p.valuation K (algebraMap R K (d : R)) ≠ 0 := (Valuation.ne_zero_iff _).2 hdK
    by_cases hpT : p ∈ T
    · have h1 := hy p hpT
      have ht : t ⟨p, hpT⟩ = 0 := by simp [t, hp]
      have he : e p = m' p := by simp [e, hp]
      rw [ht, he, sub_zero] at h1
      have h2 := val_le_of_mem (K := K) p h1
      rw [← hm' p] at h2
      exact div_le_one_of_le₀ h2 zero_le'
    · have hnd : ¬ (p.asIdeal ∣ Ideal.span {(d : R)}) := by
        intro h
        exact hpT (Finset.mem_union_right _ (by simpa using h))
      have hmem : (d : R) ∉ p.asIdeal := by
        intro h
        exact hnd (Ideal.dvd_span_singleton.2 h)
      have hone : p.valuation K (algebraMap R K (d : R)) = 1 :=
        le_antisymm (p.valuation_le_one _)
          (not_lt.1 (fun h => hmem ((p.valuation_lt_one_iff_mem _).1 h)))
      rw [hone, div_one]
      exact p.valuation_le_one _

end UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset

theorem UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {sig : E →ₐ[F] E}
      (A : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (c : NumberField.RingOfIntegers F),
      c ≠ (0 : NumberField.RingOfIntegers F) →
        ∀ (b : (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → (A p).Fp),
          ∃ (f : F),
            (∀ p ∈ S,
                (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp) f - b p) ≤
                  (ValuativeRel.valuation (A p).Fp : (A p).Fp → ValuativeRel.ValueGroupWithZero (A p).Fp)
                    (((A p).ιF : F → (A p).Fp)
                      ((Algebra.algebraMap (NumberField.RingOfIntegers F) F : NumberField.RingOfIntegers F → F) c))) ∧
              ∀ p ∉ S, ((A p).ιF : F → (A p).Fp) f ∈ (ValuativeRel.valuation (A p).Fp).integer := by
  intro F E _ _ _ _ _ sig A S c hc b
  have hc' : ∀ p, (A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c) ≠ 0 := fun p => by
    simpa using hc
  have happ : ∀ p, ∃ a : F, valuation (A p).Fp ((A p).ιF a - b p) ≤
      valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c)) := fun p => by
    haveI := (A p).lf
    exact UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approx_one (A p).ιF (A p).dense (b p) _ (hc' p)
  choose a ha using happ
  obtain ⟨f, hf1, hf2⟩ := UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.core (K := F) S c hc a
  refine ⟨f, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 := ((A p).val _ _).2 (hf1 p hp)
    rw [(valuation (A p).Fp).vle_iff_le, map_sub] at h1
    have h2 : (A p).ιF f - b p = ((A p).ιF f - (A p).ιF (a p)) + ((A p).ιF (a p) - b p) := by ring
    change valuation (A p).Fp ((A p).ιF f - b p) ≤
      valuation (A p).Fp ((A p).ιF (algebraMap (NumberField.RingOfIntegers F) F c))
    rw [h2]
    exact Valuation.map_add_le _ h1 (ha p)
  · have h1 : p.valuation F f ≤ p.valuation F 1 := by simpa using hf2 p hp
    have h2 := ((A p).val _ _).2 h1
    rw [(valuation (A p).Fp).vle_iff_le, map_one, map_one] at h2
    exact h2
end

section

theorem UpperTheory.Reformulated.B.Gka4.diag_hermitian :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] (σ : E →ₐ[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
        ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
          HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ T →
            ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ),
              HeckeCharacterZeroLocus.SiegelWeilU.cT (↑σ : E →+* E) (↑g : Matrix (Fin n) (Fin n) E) * T * (↑g : Matrix (Fin n) (Fin n) E) =
                Matrix.diagonal fun (i : Fin n) ↦ (Algebra.algebraMap F E : F → E) (↑(D i) : F) := by
  intro F E _ _ _ _ _ σ hCM n T hT
  obtain ⟨-, hC, h2, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ τ, hτ τ, star_star]
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal τ := by
    intro hr
    have := hC.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at this
    exact this hr
  obtain ⟨α, hα⟩ : ∃ α, σ α ≠ α := by
    by_contra hcon
    push_neg at hcon
    apply hnr
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ x
    rw [hcon x] at this
    exact this.symm
  have hfix := UpperTheory.fixed_quadratic_mem_base h2 σ α hα
  obtain ⟨g, D, h⟩ := UpperTheory.hermitian_diagonalisation σ hinv hfix n T hT.1 hT.2
  exact ⟨g, D, h⟩
end

section

theorem UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof.{u} :
    GroundTheory.Heights₂.Heights.GenericNoetherNormalisation.Statement.{u} := by
  intro A _ _ n q _ hq _
  classical
  obtain ⟨f, hfq, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨e, a, ha, hlc⟩ := UpperTheory.exists_monic_change_of_variables A n f hf
  have hg : e f ≠ 0 := fun h ↦ hf (e.injective (by simpa using h))
  let π : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ q :=
    (Ideal.Quotient.mkₐ A q).comp e.symm.toAlgHom
  have hπf : π (e f) = 0 := by
    simpa [π, Ideal.Quotient.eq_zero_iff_mem] using hfq
  have hsurj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective A q).comp e.symm.surjective
  let z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q :=
    fun i ↦ π (Polynomial.C (MvPolynomial.X i))
  have hz : ∀ c : MvPolynomial (Fin n) A, MvPolynomial.aeval z c = π (Polynomial.C c) := by
    intro c
    have : MvPolynomial.aeval z = π.comp (Polynomial.CAlgHom) := by
      ext i
      simp [z]
    rw [this]
    rfl
  let N := (e f).natDegree
  refine ⟨a, ha, z, (Finset.range N).image (fun j ↦ π Polynomial.X ^ j), fun d ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hsurj d
  obtain ⟨k, s, r, hk, hr⟩ := UpperTheory.pseudo_division (MvPolynomial (Fin n) A) (e f) p hg
  have h1 : a ^ k • π p = π r := by
    have := congrArg π hk
    rw [map_add (f := _), map_mul π (e f), hπf, zero_mul, zero_add, hlc, map_mul, ← hz, ← map_pow,
      MvPolynomial.aeval_C, ← Algebra.smul_def] at this
    exact this
  have h2 : r = ∑ j ∈ Finset.range N, Polynomial.C (r.coeff j) * Polynomial.X ^ j := by
    rw [Polynomial.degree_eq_natDegree hg] at hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        Polynomial.as_sum_range' r N ((Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hr)
  refine ⟨k, fun t ↦ ∑ j ∈ Finset.range N with π Polynomial.X ^ j = t, r.coeff j, ?_⟩

  rw [h1, h2, map_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun j ↦ π Polynomial.X ^ j)
  (fun j hj ↦ Finset.mem_image_of_mem _ hj), ← h2]
  refine Finset.sum_congr rfl fun t _ ↦ ?_

  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [map_mul, map_pow, hz, (Finset.mem_filter.mp hj).2]
end

section

theorem UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] (y : R →ₐ[ℤ_[l]] PadicAlgCl l),
    ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (O := ℤ_[l]) y a ha
end

section

theorem UpperTheory.Reformulated.B.Qf46.cover :
    ∀ {G Y : Type} [inst : Group G] [Countable G] [inst_2 : MeasurableSpace Y] [inst_3 : MulAction G Y]
      (μ : MeasureTheory.Measure Y),
      UpperTheory.Esk.Pres G μ →
        ∀ (b : Y → ℝ),
          UpperTheory.Esk.IsCut G b →
            ∀ (S : Set Y),
              MeasurableSet S →
                (∀ (y : Y), ∃ (g : G), g • y ∈ S) → ∫⁻ (y : Y), ENNReal.ofReal (b y) ∂μ ≤ (μ : Set Y → ENNReal) S := by
  intro G Y _ _ _ _ μ hP b hb S hS hc
  have hB : Measurable fun y => ENNReal.ofReal (b y) := hb.meas.ennreal_ofReal
  have hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y))) :=
    fun g => (hB.comp (hP g⁻¹).measurable).indicator hS
  have hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
    intro y
    have h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y)) :=
      (Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))
    rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq,
      ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (b y) ∂μ
      ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := by
        refine MeasureTheory.lintegral_mono fun y => ?_
        obtain ⟨g, hg⟩ := hc y
        refine le_trans ?_ (ENNReal.le_tsum g)
        rw [Set.indicator_of_mem hg, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ :=
        MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := by
        refine MeasureTheory.lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, hone, Pi.one_apply]
        · simp only [Set.indicator_of_notMem hy, tsum_zero]
    _ = μ S := MeasureTheory.lintegral_indicator_one hS
end
