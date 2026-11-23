module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add (f := _)]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
end

section

noncomputable def UpperTheory.Reformulated.B.Qj9.Stable :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → Set (Module.End ℂ M) → Submodule ℂ M → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) ↦
      ∀ g ∈ Op, ∀ x ∈ P, (g : M → M) x ∈ P

theorem UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable :
    ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M),
      UpperTheory.Reformulated.B.Qj9.Stable Op P → ∀ e ∈ Algebra.adjoin ℂ Op, ∀ x ∈ P, (e : M → M) x ∈ P := by
  intro M _ _ Op P h e he
  induction he using Algebra.adjoin_induction with
  | mem g hg => exact h g hg
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
end

section

open TensorProduct in
private theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) c (AdicCompletion.of I M x)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

open Polynomial in
private theorem lift_idem {T : Type} [CommRing T] (I : Ideal T) [HenselianRing T I]
    (f : T ⧸ I) (hf : IsIdempotentElem f) :
    ∃ e : T, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = f := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hm : (X ^ 2 - X : T[X]).Monic := by
    nontriviality T
    apply monic_X_pow_sub
    simp
  have hf' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I a = Ideal.Quotient.mk I a := hf
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X : T[X]) hm a
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, pow_two, map_mul, eval_mul]
      rw [hf', sub_self])
    (by
      have h : eval a (derivative (X ^ 2 - X : T[X])) = 2 * a - 1 := by
        simp
        ring
      rw [h, map_sub, map_mul, map_one, map_ofNat]
      refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I a - 1) ?_
      linear_combination 4 * hf')
  refine ⟨e, ?_, Ideal.Quotient.eq.mpr hea⟩
  have : e ^ 2 - e = 0 := by simpa using he
  show e * e = e
  linear_combination this

private theorem artin_idem {A : Type} [CommRing A] [IsArtinianRing A] (J : Ideal A) :
    ∃ (e : A) (n : ℕ), IsIdempotentElem e ∧ 1 - e ∈ J ∧ ∀ x ∈ J, x ^ n * e = 0 := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (J ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have h1 : J ^ n = J ^ (n + 1) := hn (n + 1) (by omega)
  have h2 : J ^ n = J ^ (n + n) := hn (n + n) (by omega)
  have hid : IsIdempotentElem (J ^ n) := by
    show J ^ n * J ^ n = J ^ n
    rw [← pow_add, ← h2]
  obtain ⟨f, hf, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hid
  refine ⟨1 - f, n, hf.one_sub, ?_, ?_⟩
  · have : f ∈ J ^ (n + 1) := by
      rw [← h1, hJ]
      exact Submodule.mem_span_singleton_self f
    simpa using Ideal.pow_le_self (by omega) this
  · intro x hx
    have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
    rw [hJ] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have hf' : f * f = f := hf
    rw [← hc, smul_eq_mul]
    linear_combination (-c) * hf'

private theorem exists_scalar {Λ T : Type} [CommRing Λ] [CommRing T] [Algebra Λ T]
    {ι : Type} (t : ι → T) (a : ι → Λ) (h : Algebra.adjoin Λ (Set.range t) = ⊤) (J : Ideal T)
    (hJ : ∀ i, t i - algebraMap Λ T (a i) ∈ J) (s : T) :
    ∃ c : Λ, s - algebraMap Λ T c ∈ J := by
  have hs : s ∈ Algebra.adjoin Λ (Set.range t) := h ▸ Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i, hJ i⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, ?_⟩
    have := J.add_mem hc hd
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have := J.add_mem (J.mul_mem_right y hc) (J.mul_mem_left (algebraMap Λ T c) hd)
    convert this using 1
    rw [map_mul]; ring

private theorem maximal_of_scalar {Λ T : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing T]
    [Algebra Λ T] (J : Ideal T) (hne : J ≠ ⊤)
    (hm : Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ≤ J)
    (hs : ∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ J) : J.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hne ((Ideal.eq_top_iff_one J).mpr h), fun K x hJK hxJ hxK => ?_⟩
  obtain ⟨c, hc⟩ := hs x
  by_cases hu : IsUnit c
  · have h1 : algebraMap Λ T c ∈ K := by
      have := K.sub_mem hxK (hJK hc)
      simpa using this
    exact (Ideal.eq_top_iff_one K).mp (K.eq_top_of_isUnit_mem h1 (hu.map _))
  · exfalso
    have h1 : algebraMap Λ T c ∈ J := hm (Ideal.mem_map_of_mem _ hu)
    have := J.add_mem hc h1
    exact hxJ (by simpa using this)

theorem UpperTheory.Reformulated.B.Qe2.locAbs :
    ∀ (Λ T : Type) [inst : CommRing Λ] [inst_1 : IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] [inst_4 : CommRing T] [inst_5 : Algebra Λ T] [Module.Finite Λ T]
    (ι : Type) (t : ι → T) (a : ι → Λ),
    Algebra.adjoin Λ (Set.range t) = ⊤ →
      ∃ (e : T),
        IsIdempotentElem e ∧
          (∀ (i : ι),
              ∃ (n : ℕ),
                (t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ^ n * e ∈
                  Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ)) ∧
            (1 : T) - e ∈
                Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                  Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ∧
              (∀ (s : T),
                  ∃ (c : Λ),
                    s - (Algebra.algebraMap Λ T : Λ → T) c ∈
                      Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                        Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))) ∧
                (e ≠ (0 : T) →
                  (Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                      Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))).IsMaximal) := by
  intro Λ T _ _ _ _ _ _ _ ι t a h
  set I : Ideal T := Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) with hI
  set J : Ideal T := I ⊔ Ideal.span (Set.range fun i : ι ↦ t i - algebraMap Λ T (a i)) with hJ
  have hmem : ∀ i, t i - algebraMap Λ T (a i) ∈ J := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hs := exists_scalar t a h J hmem
  by_cases htop : J = ⊤
  · exact ⟨0, IsIdempotentElem.zero, fun i => ⟨0, by simp⟩, by simp [htop], hs,
      fun h0 => absurd rfl h0⟩
  have hmax : J.IsMaximal := maximal_of_scalar J htop le_sup_left hs
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal Λ) T := precomplete_of_finite _ T
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Λ) T := {}
  haveI : IsAdicComplete I T := (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  haveI : IsArtinianRing (T ⧸ I) := by
    letI : Field (Λ ⧸ IsLocalRing.maximalIdeal Λ) := Ideal.Quotient.field _
    haveI : Module.Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I) :=
      Module.Finite.of_restrictScalars_finite Λ _ _
    exact IsArtinianRing.of_finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I)
  obtain ⟨f, n, hf, hfJ, hfn⟩ := artin_idem (J.map (Ideal.Quotient.mk I))
  obtain ⟨e, he, rfl⟩ := lift_idem I f hf
  refine ⟨e, he, fun i => ⟨n, ?_⟩, ?_, hs, fun _ => hmax⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hfn _ (Ideal.mem_map_of_mem _ (hmem i))
  · have h1 : Ideal.Quotient.mk I (1 - e) ∈ J.map (Ideal.Quotient.mk I) := by
      rwa [map_sub, map_one]
    have h2 := Ideal.mem_quotient_iff_mem (I := I) (J := J) le_sup_left (x := 1 - e)
    exact h2.mp h1
end

section

namespace UpperTheory.Reformulated.B.Qi13

theorem aux1 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K], IsLocalRing ↥(ValuativeRel.valuation K).integer := by
  intro K _ _ _ _
  infer_instance

@[reducible] noncomputable def algRes : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Algebra (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    ZMod.algebra (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l

attribute [local instance] algRes

@[reducible] noncomputable def fdim : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [Fact (Nat.Prime l)] → [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] → ℕ :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    Module.finrank (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

theorem aux4 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Module.Free (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  letI := algRes K l
  exact Module.Free.of_divisionRing (ZMod l) _

theorem aux5 : ∀ (l : ℕ) [Fact (Nat.Prime l)], StrongRankCondition (ZMod l) := by
  intro l _
  infer_instance

theorem aux6 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Module.Finite (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  letI := algRes K l
  haveI : Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := inferInstance
  exact Module.Finite.of_finite

attribute [local instance] aux4 aux6

noncomputable def bb : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Module.Basis (Fin (fdim K l)) (ZMod l)
                  (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    Module.finBasis (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

theorem aux8 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l]
  (i : Fin (fdim K l)),
  ∃ a, (IsLocalRing.residue ↥(ValuativeRel.valuation K).integer) a = (bb K l) i := by
  intro K _ _ _ _ l _ _ i
  exact IsLocalRing.residue_surjective _

noncomputable def blift : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Fin (fdim K l) → ↥(ValuativeRel.valuation K).integer :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] i =>
    (aux8 K l i).choose

private theorem key {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    (O : Subring K) {k : Type} [CommRing k] [Algebra (ZMod l) k] (r : O →+* k)
    (hO : ∀ c : ℤ_[l], algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) {ι : Type} [Fintype ι] (x : ι → O)
    (h : LinearIndependent (ZMod l) (fun i => r (x i))) :
    LinearIndependent ℚ_[l] (fun i => (x i : K)) := by
  classical
  let φ : ℤ_[l] →+* O :=
    ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict O hO
  have hφ : ∀ c : ℤ_[l], r (φ c) = algebraMap (ZMod l) k (PadicInt.toZMod c) := by
    intro c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZMod c)
    have hker : c - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
    obtain ⟨d, hd⟩ := hker
    have hl : (l : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod l) k), ZMod.natCast_self, map_zero]
    have hc : c = n + l * d := by rw [← hd]; ring
    rw [← hn, hc]
    simp only [map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖g i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖g m‖ := (norm_pos_iff.mpr hi₀).trans_le (hm i₀ (Finset.mem_univ _))
  have hgm : g m ≠ 0 := norm_pos_iff.mp hpos
  let c : ι → ℤ_[l] := fun i => ⟨g i / g m, by
    rw [PadicInt.mem_subring_iff]
    rw [norm_div]
    exact (div_le_one hpos).mpr (hm i (Finset.mem_univ _))⟩
  have hsum : ∑ i, φ (c i) * x i = 0 := by
    apply Subtype.ext
    have h1 : ∀ i, ((φ (c i) * x i : O) : K) = (g m)⁻¹ • (g i • (x i : K)) := by
      intro i
      change algebraMap ℚ_[l] K (g i / g m) * (x i : K) = _
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul]
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [h1]
    rw [← Finset.smul_sum, hg, smul_zero]
    rfl
  have hred : ∑ i, PadicInt.toZMod (c i) • r (x i) = 0 := by
    have h2 := congrArg r hsum

    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφ, Algebra.smul_def]
  have h3 := h _ hred m
  have h4 : c m = 1 := Subtype.ext (div_self hgm)
  rw [h4, map_one] at h3
  exact one_ne_zero h3

private theorem mem_of_closed {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [TopologicalSpace K] [Algebra ℚ_[l] K] (O : Subring K) (hO : IsClosed (O : Set K))
    (hc : Continuous (algebraMap ℚ_[l] K)) (c : ℤ_[l]) :
    algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O := by
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun c : ℤ_[l] => algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) c ?_ ?_
  · exact hO.preimage (hc.comp continuous_subtype_val)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem O n

theorem linIndep : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : Algebra ℚ_[l] K] [inst_6 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Continuous ⇑(Algebra.algebraMap ℚ_[l] K) →
    LinearIndependent ℚ_[l] fun i => (blift K l i : K) := by
  intro K _ _ _ _ l _ _ _ hc
  letI := algRes K l
  refine key (ValuativeRel.valuation K).integer
    (IsLocalRing.residue (ValuativeRel.valuation K).integer)
    (mem_of_closed _ Valuation.isClosed_integer hc)
    (blift K l) ?_
  have h : (fun i => IsLocalRing.residue (ValuativeRel.valuation K).integer
      (blift K l i)) = bb K l :=
    funext fun i => (aux8 K l i).choose_spec
  rw [h]
  exact (bb K l).linearIndependent

end UpperTheory.Reformulated.B.Qi13
end

section

namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
end
