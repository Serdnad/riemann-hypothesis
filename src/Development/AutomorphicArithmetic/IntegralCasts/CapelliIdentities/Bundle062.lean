module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Order.Fin.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.LocalizedModule.Basic

@[expose] public section

section

namespace UpperTheory.Reformulated.B.NormLtOne

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hx0 : y a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact absurd hx (by norm_num)
  have hu : ‖(y a)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hint : IsIntegral ℚ_[l] (y a)⁻¹ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly ℚ_[l] (y a)⁻¹).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] (y a)⁻¹).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmon]
    exact hu
  have hz := minpoly.aeval ℚ_[l] (y a)⁻¹
  generalize minpoly ℚ_[l] (y a)⁻¹ = P at hmon hc hz
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hz
  let c : ℕ → ℤ_[l] := fun i => ⟨P.coeff i, hc i⟩
  have hr : (∑ i ∈ Finset.range P.natDegree,
      algebraMap O R (algebraMap ℤ_[l] O (c i)) * a ^ (P.natDegree - i)) ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha _ ?_)
    have := Finset.mem_range.mp hi
    omega
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hr)
  apply (hunit.map y).ne_zero
  have hz' := congrArg (· * y a ^ P.natDegree) hz
  simp only [zero_mul, add_mul, Finset.sum_mul] at hz'
  rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow] at hz'

  rw [sub_neg_eq_add, map_add (f := _), map_one, map_sum, add_comm, ← hz']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := (Finset.mem_range.mp hi).le
  rw [map_mul, map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), Algebra.smul_def, mul_assoc,
    pow_sub₀ _ hx0 hi', inv_pow, mul_comm (y a ^ P.natDegree)]
  rfl

end UpperTheory.Reformulated.B.NormLtOne
end

section

theorem UpperTheory.Reformulated.B.FiniteModuleImageInFiniteExtension.qb_fdmod :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {M : Type}
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (f : M →ₗ[ℤ_[l]] PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      FiniteDimensional ℚ_[l] ↥K ∧ ∀ (x : M), (f : M → PadicAlgCl l) x ∈ K := by
  intro l _ M _ _ hM f
  obtain ⟨S, hS⟩ := hM.fg_top
  have hfin : (f '' (S : Set M)).Finite := S.finite_toSet.image _
  haveI : Finite (f '' (S : Set M)) := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro x
    have hx : x ∈ Submodule.span ℤ_[l] (S : Set M) := by
      rw [hS]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]
      exact IntermediateField.smul_mem _ ha
end

section

namespace UpperTheory.Reformulated.B.S4

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have hv : spectralValue (minpoly ℚ_[l] z) ≤ 1 := hz
  have hc : ∀ n, ‖(minpoly ℚ_[l] z).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hv
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 : Polynomial.aeval z (q.map (algebraMap ℤ_[l] ℚ_[l])) = 0 := by
    rw [hq]
    exact minpoly.aeval _ _
  rw [Polynomial.aeval_map_algebraMap] at h0
  exact h0

end UpperTheory.Reformulated.B.S4
end

section

theorem UpperTheory.padicAlgCl_isIntegral_of_norm_le_one :
    ∀ {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l), ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x := by
  intro l _ x hx
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] x) ≤ 1 := hx
  have hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hs
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]
  exact minpoly.aeval _ _
end

section

open scoped NNReal

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact PadicAlgCl.norm_extends l (a : ℚ_[l])

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one {l : ℕ} [Fact (Nat.Prime l)] {y : PadicAlgCl l}
    (hy : IsIntegral ℤ_[l] y) : ‖y‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) ℝ≥0 := NormedField.valuation
  have hv : ∀ z : PadicAlgCl l, z ∈ v.integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff]
    exact NNReal.coe_le_coe.symm
  let f : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => (hv _).2 (by
      rw [UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap]; exact a.norm_le_one)
  have h : IsIntegral v.integer y :=
    hy.map_of_comp_eq f (RingHom.id _) (by ext a; rfl)
  exact (hv y).1 ((Valuation.integer.integers v).mem_of_integral h)

theorem UpperTheory.Reformulated.B.NormOnValuationRing.mem_max_iff :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {T : Type}
    [inst_1 : CommRing T] [inst_2 : IsLocalRing T] [inst_3 : Algebra ℤ_[l] T] [Algebra.IsIntegral ℤ_[l] T]
    (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T), x ∈ IsLocalRing.maximalIdeal T ↔ ‖(φ : T → PadicAlgCl l) x‖ < (1 : ℝ) := by
  intro l _ T _ _ _ _ φ x
  have hle : ∀ t : T, ‖φ t‖ ≤ 1 := fun t =>
    UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) t).map φ)
  let P : Ideal T :=
    { carrier := {t | ‖φ t‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖φ (a + b)‖ < 1
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ t : T, t ∈ P ↔ ‖φ t‖ < 1 := fun _ => Iff.rfl
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra h
      rw [not_or, hP, hP, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)
  have hcomap : P.comap (algebraMap ℤ_[l] T) = IsLocalRing.maximalIdeal ℤ_[l] := by
    ext a
    rw [Ideal.mem_comap, hP, φ.commutes, UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hmax : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) P
    change (P.comap (algebraMap ℤ_[l] T)).IsMaximal
    rw [hcomap]
    exact IsLocalRing.maximalIdeal.isMaximal ℤ_[l]
  rw [← IsLocalRing.eq_maximalIdeal hmax, hP]
end

section

namespace UpperTheory.Reformulated.B.S6

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint

end UpperTheory.Reformulated.B.S6
end

section

namespace UpperTheory.Reformulated.B.NormLeOneOfIsIntegral

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l,
      y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l],
      algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer := by
    intro a
    rw [hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans_le a.2
  have hint : IsIntegral (PadicAlgCl.valued l).v.integer x :=
    hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)

end UpperTheory.Reformulated.B.NormLeOneOfIsIntegral
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Emb :
    {F : Type} → [inst : Field F] → [NumberField F] → (l : ℕ) → [Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.Qh13.Plc F → Type :=
    fun {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact (Nat.Prime l)] (w : UpperTheory.Reformulated.B.Qh13.Plc F) ↦
      { j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w →+* UpperTheory.Reformulated.B.Qh13.Qbar l //
        Continuous (⇑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w → UpperTheory.Reformulated.B.Qh13.Qbar l) }

theorem UpperTheory.Reformulated.B.Qh13.ec_field :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
      {w : UpperTheory.Reformulated.B.Qh13.Plc L} (j : UpperTheory.Reformulated.B.Qh13.Emb l w),
      ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
        FiniteDimensional ℚ_[l] ↥K ∧
          ∀ (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w),
            ((↑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w →+* UpperTheory.Reformulated.B.Qh13.Qbar l) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion L w → UpperTheory.Reformulated.B.Qh13.Qbar l)
                x ∈
              K := by
  intro L _ _ l _ w j
  obtain ⟨j, hj⟩ := j
  let f : L →+* PadicAlgCl l :=
    j.comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w))
  let b := Module.finBasis ℚ L
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => f (b i))
  have hK : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hf : ∀ y : L, f y ∈ K := by
    intro y

    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have hc : IsClosed (K : Set (PadicAlgCl l)) :=
    haveI : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hK
    K.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  refine ⟨K, hK, fun x => ?_⟩
  exact (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w).induction_on x
    (hc.preimage hj) hf
end

section

theorem UpperTheory.Reformulated.B.Qe12.killed :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (M : Type)
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Finite M],
    ∃ (r : ℕ), (0 : ℕ) < r ∧ ∀ (x : M), (↑l : ℤ_[l]) ^ r • x = (0 : M) := by
  intro l _ M _ _ _
  have hN : ((Nat.card M : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨((Nat.card M : ℕ) : ℤ_[l]).valuation + 1, Nat.succ_pos _, fun x => ?_⟩
  have h1 : ((Nat.card M : ℕ) : ℤ_[l]) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact card_nsmul_eq_zero'
  have h2 : ((PadicInt.unitCoeff hN : ℤ_[l]ˣ) : ℤ_[l]) •
      ((l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x) = 0 := by
    rw [← mul_smul, ← PadicInt.unitCoeff_spec hN]
    exact h1
  have h3 : (l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x = 0 :=
    ((PadicInt.unitCoeff hN).isUnit.smul_eq_zero).mp h2
  rw [pow_succ', mul_smul, h3, smul_zero]
end

section

theorem UpperTheory.Reformulated.B.Qk55.exists_kill.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {H : Type u_1}
    [inst_1 : AddCommGroup H] [inst_2 : _root_.Module ℤ_[l] H] (h : H),
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h = (0 : TensorProduct ℤ_[l] ℚ_[l] H) → ∃ (b : ℕ), l ^ b • h = (0 : H) := by
  intro l _ H _ _ h hh
  have h0 : TensorProduct.mk ℤ_[l] ℚ_[l] H 1 h = 0 := hh
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] H 1)).1 h0
  have hs0 : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hs' : (s : ℤ_[l]) • h = 0 := hs
  refine ⟨(s : ℤ_[l]).valuation, ?_⟩
  rw [PadicInt.unitCoeff_spec hs0, mul_smul] at hs'
  have h2 : ((l : ℤ_[l]) ^ (s : ℤ_[l]).valuation) • h = 0 :=
    (IsUnit.smul_eq_zero (Units.isUnit _)).1 hs'
  rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  exact h2
end

section

theorem UpperTheory.Reformulated.B.Yde3.continuous_toZModPow :
    ∀ {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by
  intro ℓ hℓ n
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n) ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-n : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  refine (continuousAt_const (y := (0 : ZMod (ℓ ^ n)))).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
  exact hx.symm
end

section

theorem UpperTheory.Reformulated.B.Yoa4.add_gap_le :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by
  intro r d hd k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hm : (i : ℕ) + k < r := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hm⟩ rfl
    have h2 : d j < d ⟨(i : ℕ) + k, hm⟩ := hd (by
      rw [Fin.lt_def]
      simp only
      omega)
    omega
end
