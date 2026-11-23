module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Idempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Mathlib.NumberTheory.Padics.Complex
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  first | exact @GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | exact GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | (intros; apply GlobalTheory.GoodCoeff.exists_trace_form_integral_iff <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.IntDual

theorem lattice_basis (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ_[l] LL),
      (∀ i, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (b i)) ∧
      ∀ x : LL, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x →
        ∀ i, ∃ z : ℤ_[l], b.repr x i = (z : ℚ_[l]) := by
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure ℤ_[l] LL
  haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S
  have hinj : Function.Injective (algebraMap ℤ_[l] LL) := by
    intro a c h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)
  haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by
    have hr0 : algebraMap ℤ_[l] LL r ≠ 0 := by
      intro h0; exact hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    apply Subtype.ext
    have h1 := congrArg (fun s : S => (s : LL)) hac
    simp only [Subalgebra.coe_smul, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hr0 h1⟩
  haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S
  let bO := (Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)
  let b := bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL
  have hb : ∀ i, b i = (bO i : LL) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i
  refine ⟨_, b, fun i => ?_, fun x hx i => ?_⟩
  · rw [hb]; exact (bO i).2
  · have := bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i
    exact ⟨bO.repr ⟨x, hx⟩ i, this⟩

theorem intDual_coef : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  intro l _ LL _ _ _ O _ _ hO
  have H := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩ := hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  haveI := hfd
  have hmem := H.1
  obtain ⟨n, b, hbint, hcoord⟩ := lattice_basis l LL
  let ι := algebraMap O LL
  have hιinj : Function.Injective ι := IsFractionRing.injective O LL
  let Tr := Algebra.trace ℚ_[l] LL
  let B := Algebra.traceForm ℚ_[l] LL
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ_[l] LL
  let f' := B.dualBasis hB b
  have hcoef : ∀ x i, Tr (f' i * x) = b.repr x i := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]

    rw [Finset.mul_sum, map_sum]
    have : ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0) := by
      intro j
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]
      rfl
    simp_rw [this, mul_ite, mul_one, mul_zero]
    simp

  let Zs : Subring ℚ_[l] := (algebraMap ℤ_[l] ℚ_[l]).range
  have hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l]) := by
    intro q; constructor
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
  have hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o) :=
    fun o => (hmem (ι o)).1 ⟨o, rfl⟩
  have hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs := by
    intro i s
    obtain ⟨z, hz⟩ := hcoord (ι s) (hintO s) i
    rw [hcoef, hZ]; exact ⟨z, hz⟩
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n)) f'
  let D := ι c
  have hD : D ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))
  have ho : ∀ i, ∃ o : O, ι o = D * f' i := by
    intro i
    obtain ⟨o, ho⟩ := hcint i (Finset.mem_univ i)
    exact ⟨o, by rw [ho, Algebra.smul_def]⟩
  choose o hoD using ho
  let I : Ideal O :=
    { carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs}
      add_mem' := by
        intro a a' ha ha' s
        have e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s := by
          rw [map_add (f := _)]; ring
        rw [e, map_add (f := _)]; exact Zs.add_mem (ha s) (ha' s)
      zero_mem' := by
        intro s; simp only [map_zero, mul_zero, zero_mul]; exact Zs.zero_mem
      smul_mem' := by
        intro r a ha s
        have e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s) := by
          rw [smul_eq_mul, map_mul, map_mul]; ring
        rw [e]; exact ha (r * s) }
  have hoI : ∀ i, o i ∈ I := by
    intro i s
    show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs
    rw [hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    exact hf'M i s
  let g := Submodule.IsPrincipal.generator I
  have hgI : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha : ∀ i, ∃ a : O, a * g = o i := by
    intro i
    have h := hoI i
    rw [← Submodule.IsPrincipal.span_singleton_generator I] at h
    exact Ideal.mem_span_singleton'.1 h
  choose a hag using ha
  let δ := D⁻¹ * ι g
  let lam : LL →ₗ[ℚ_[l]] ℚ_[l] := Tr.comp (LinearMap.mulLeft ℚ_[l] δ)
  have hlam : ∀ y, lam y = Tr (δ * y) := fun y => rfl
  have hδa : ∀ i, δ * ι (a i) = f' i := by
    intro i
    show D⁻¹ * ι g * ι (a i) = f' i
    rw [mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  have he : ∀ i, ∃ e : O, ι e = b i := fun i => (hmem (b i)).2 (hbint i)
  choose e he using he
  refine ⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩
  · have hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem
        (algebraMap ℚ_[l] LL (z : ℚ_[l])) := RingHom.isIntegralElem_map _
    exact (hmem _).2 hz
  · have h := hgI y
    rw [hZ] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [hlam]; exact hz⟩
  · conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam, ← mul_assoc, hδa, hcoef, he]
end GlobalTheory.IntDual
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_finset_primePow_torsion_quotient : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  first | exact @GlobalTheory.GoodCoeff.exists_finset_pow_torsion | exact GlobalTheory.GoodCoeff.exists_finset_pow_torsion | (intros; apply GlobalTheory.GoodCoeff.exists_finset_pow_torsion <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem adicSpan_smul_top_mem_iff {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (x : O) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule O O) ↔ ∃ b : O, x = ϖ ^ n * b := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩

theorem adicComplete_explicit_sums {O : Type} [CommRing O] (ϖ : O)
    [h : IsAdicComplete (Ideal.span {ϖ}) O] :
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (M := O)
      (fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j) (by
        intro m n hmn
        rw [SModEq.sub_mem, adicSpan_smul_top_mem_iff]
        refine ⟨-∑ j ∈ Finset.Ico m n, ϖ ^ (j - m) * x j, ?_⟩
        rw [← Finset.sum_range_add_sum_Ico _ hmn, mul_neg, Finset.mul_sum]
        have : ∑ j ∈ Finset.Ico m n, ϖ ^ m * (ϖ ^ (j - m) * x j)
            = ∑ j ∈ Finset.Ico m n, ϖ ^ j * x j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
        rw [this]; ring)
    refine ⟨L, fun n => ?_⟩
    have h1 := (SModEq.sub_mem.mp (hL n))
    rw [adicSpan_smul_top_mem_iff] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨-b, by rw [mul_neg, ← hb]; ring⟩
  · refine IsHausdorff.haus' (I := Ideal.span {ϖ}) a fun n => ?_
    rw [SModEq.zero, adicSpan_smul_top_mem_iff]
    exact ha n

theorem goodO_coeff_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O,
      a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  intro l _ LL _ _ _ O _ _ hG
  have hc := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.2.2
  exact adicComplete_explicit_sums (h := hc) ((l : ℕ) : O)

end GlobalTheory
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  first | exact @GlobalTheory.AlgRing.finite_and_isSemisimpleRing | exact GlobalTheory.AlgRing.finite_and_isSemisimpleRing | (intros; apply GlobalTheory.AlgRing.finite_and_isSemisimpleRing <;> assumption)
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

variable {k : Type} [Field k]

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → k) (j : ℕ) :
    (j : k) * (univ.val.map f).esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k j)

  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
  MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset k) (j : ℕ) :
    (j : k) * s.esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) j
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq [CharZero k] (s t : Multiset k)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) : ∀ j, s.esymm j = t.esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hj0 : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      apply mul_left_cancel₀ hj0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq [CharZero k] (s t : Multiset k) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext j
  by_cases hj : j ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hj, Multiset.prod_X_sub_C_coeff t (hc ▸ hj), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hj
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

theorem charpoly_eq_prod_of_trace_pow : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k), Multiset.card B = a → (∀ n : ℕ, 1 ≤ n → (M ^ n).trace = (B.map (· ^ n)).sum) → M.charpoly = (B.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro k _ _ _ a M B hB h
  have hR : Multiset.card M.charpoly.roots = a := GlobalTheory.CharpolyPow.card_roots_charpoly M
  have hsplit : M.charpoly = (M.charpoly.roots.map fun b => X - C b).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq M.charpoly_monic
      (by rw [hR, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    exact this.symm
  rw [hsplit]
  refine prod_eq_of_psum_eq _ _ (by rw [hR, hB]) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hR, hB]
  · rw [← h n hn, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]

end GlobalTheory.CharpolyNewton
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

open Filter Topology

namespace GlobalTheory.Cong

theorem extend_of_locallyCauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ J : Type) [TopologicalSpace Γ] (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → (∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε) → ∃ T : Γ → PadicAlgCl l, Continuous T ∧ ∀ j, T (x j) = θ j := by
  intro l _ Γ J _ x hx θ L hL hθL hC
  have hLc : IsComplete (L : Set (PadicAlgCl l)) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule L.toSubalgebra) := hL
    exact Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule L.toSubalgebra)
  have hnb : ∀ g : Γ, (comap x (𝓝 g)).NeBot := by
    intro g
    refine comap_neBot_iff.2 fun t ht => ?_
    obtain ⟨_, hyt, j, rfl⟩ := mem_closure_iff_nhds.1 (hx g) t ht
    exact ⟨j, hyt⟩
  have hex : ∀ g : Γ, ∃ t : PadicAlgCl l, Tendsto θ (comap x (𝓝 g)) (𝓝 t) := by
    intro g
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hcau : Cauchy (map θ (comap x (𝓝 g))) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
      refine ⟨θ '' (x ⁻¹' V), image_mem_map (preimage_mem_comap hV), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hVc i j hi hj) (by linarith)
    have hle : map θ (comap x (𝓝 g)) ≤ 𝓟 (L : Set (PadicAlgCl l)) :=
      le_principal_iff.2 (mem_map.2 (univ_mem' fun j => hθL j))
    obtain ⟨t, -, ht⟩ := hLc _ hcau hle
    exact ⟨t, ht⟩
  choose T hT using hex
  refine ⟨T, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
    filter_upwards [interior_mem_nhds.2 hV] with g' hg'
    have hV' : V ∈ 𝓝 g' := mem_interior_iff_mem_nhds.1 hg'
    haveI : (comap x (𝓝 g')).NeBot := hnb g'
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hlim : Tendsto (fun p : J × J => dist (θ p.1) (θ p.2))
        (comap x (𝓝 g') ×ˢ comap x (𝓝 g)) (𝓝 (dist (T g') (T g))) :=
      ((hT g').comp tendsto_fst).dist ((hT g).comp tendsto_snd)
    have hev : ∀ᶠ p : J × J in comap x (𝓝 g') ×ˢ comap x (𝓝 g), dist (θ p.1) (θ p.2) ≤ ε / 2 := by
      filter_upwards [prod_mem_prod (preimage_mem_comap hV') (preimage_mem_comap hV)] with p hp
      rw [dist_eq_norm]
      exact hVc p.1 p.2 hp.1 hp.2
    have := le_of_tendsto hlim hev
    linarith
  · intro j
    haveI : (comap x (𝓝 (x j))).NeBot := hnb (x j)
    refine tendsto_nhds_unique (hT (x j)) ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) (x j)
    filter_upwards [preimage_mem_comap hV] with i hi
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hVc i j hi (mem_of_mem_nhds hV)) (by linarith)

end GlobalTheory.Cong
end
