module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Polynomial

namespace UpperTheory.Reformulated.B.AdicCompleteRootExistence

private lemma exists_root_of_adicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I := by
  classical
  obtain ⟨f', hf'⟩ : ∃ f' : R[X], f' = derivative f := ⟨_, rfl⟩
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℕ → R, c 0 = a₀ ∧
      ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) :=
    ⟨fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b), rfl,
      fun _ => rfl⟩
  rw [← hf'] at h₂
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rw [hc0]
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [hc0, zero_add, pow_one] using h₁
    | succ n ih =>
      obtain ⟨q, hq⟩ := Polynomial.binomExpansion f (c n)
        (-(f.eval (c n) * Ring.inverse (f'.eval (c n))))
      rw [hc, sub_eq_add_neg, hq]
      have hcancel : f'.eval (c n) * Ring.inverse (f'.eval (c n)) = 1 :=
        Ring.mul_inverse_cancel _ (hf'c n)
      have hz : eval (c n) f + eval (c n) (derivative f) *
          (-(f.eval (c n) * Ring.inverse (f'.eval (c n)))) = 0 := by
        rw [← hf']
        linear_combination (-(f.eval (c n))) * hcancel
      rw [hz, zero_add]
      have hle : I ^ (2 * (n + 1)) ≤ I ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      refine Ideal.mul_mem_left _ _ (hle ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, hc0, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

private lemma root_of_local {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {ϖ : R}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (f : R[X]) (a : R) (k : ℕ) (ε : Rˣ)
    (h1 : f.derivative.eval a = ϖ ^ k * ε) (h2 : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b : R, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  obtain ⟨c, hc⟩ := h2
  obtain ⟨q, hq⟩ := Polynomial.binomExpansion (f.map C) (C a) (C (ϖ ^ (k + 1)) * X)
  have hcomp : eval (C a + C (ϖ ^ (k + 1)) * X) (f.map C) =
      f.comp (C a + C (ϖ ^ (k + 1)) * X) := by
    rw [eval_map]; rfl
  rw [hcomp, eval_map_apply, derivative_map, eval_map_apply, h1, hc] at hq
  let g : R[X] := C c + C (ε : R) * X + C ϖ * q * X ^ 2
  have hgy : ∀ y, g.eval y = c + ε * y + ϖ * (q.eval y * y ^ 2) := by
    intro y; simp only [g, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring
  have hg'y : ∀ y, g.derivative.eval y =
      ε + ϖ * (q.derivative.eval y * y ^ 2 + q.eval y * (2 * y)) := by
    intro y
    simp only [g, derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one, map_natCast, eval_natCast]
    norm_num
    ring
  set y₀ : R := -((ε⁻¹ : Rˣ) : R) * c with hy₀
  have hεy : (ε : R) * y₀ = -c := by
    rw [hy₀, ← mul_assoc, mul_neg, Units.mul_inv]; ring
  have hroot₀ : g.eval y₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [hgy, add_assoc, ← add_assoc c, hεy, add_neg_cancel, zero_add]
    exact Ideal.mul_mem_right _ _ hϖ
  have hunit : IsUnit (g.derivative.eval y₀) := by
    rw [hg'y]
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hε : (ε : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right
        (q.derivative.eval y₀ * y₀ ^ 2 + q.eval y₀ * (2 * y₀)) _ hϖ)
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 hε ε.isUnit
  obtain ⟨y, hy, -⟩ := exists_root_of_adicComplete (IsLocalRing.maximalIdeal R) g y₀ hroot₀
    (hunit.map _)
  refine ⟨a + ϖ ^ (k + 1) * y, ?_, ⟨y, by ring⟩⟩
  have hev := congrArg (eval y) hq
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hev
  rw [hev]
  have : ϖ ^ (2 * k + 1) * g.eval y = 0 := by rw [hy, mul_zero]
  rw [hgy] at this
  linear_combination this

end UpperTheory.Reformulated.B.AdicCompleteRootExistence

theorem UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
      {ϖ : ↥(ValuativeRel.valuation K).integer},
      Irreducible ϖ →
        ∀ (f : Polynomial ↥(ValuativeRel.valuation K).integer) (a : ↥(ValuativeRel.valuation K).integer) (k : ℕ)
          (ε : (↥(ValuativeRel.valuation K).integer)ˣ),
          Polynomial.eval a
                ((Polynomial.derivative :
                    Polynomial ↥(ValuativeRel.valuation K).integer → Polynomial ↥(ValuativeRel.valuation K).integer)
                  f) =
              ϖ ^ k * (↑ε : ↥(ValuativeRel.valuation K).integer) →
            ϖ ^ ((2 : ℕ) * k + (1 : ℕ)) ∣ Polynomial.eval a f →
              ∃ (b : ↥(ValuativeRel.valuation K).integer),
                Polynomial.eval b f = (0 : ↥(ValuativeRel.valuation K).integer) ∧ ϖ ^ (k + (1 : ℕ)) ∣ b - a := by
  intro K _ _ _ _ ϖ hϖ f a k ε h1 h2
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact UpperTheory.Reformulated.B.AdicCompleteRootExistence.root_of_local
    ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) f a k ε h1 h2
end

section

namespace UpperTheory.Reformulated.B.BlockHomomorphism

noncomputable def IsSmooth : {k G V : Type} →
  [inst : Field k] →
    [inst_1 : Group G] →
      [inst_2 : AddCommGroup V] → [inst_3 : Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
  fun {k G V} [Field k] [Group G] [AddCommGroup V] [Module k V] [TopologicalSpace G] ρ =>
    ∀ (v : V), IsOpen {g | (ρ g) v = v}

noncomputable def glCongr : (k : Type) →
  [inst : Field k] → {a b : ℕ} → a = b → GL (Fin a) k →* GL (Fin b) k :=
  fun k [Field k] {a b} h => Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMulEquiv.toMonoidHom

theorem aux3 : ∀ (k : Type) [inst : Field k] (n r : ℕ),
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0
    (1 : Matrix (Fin r) (Fin r) k) = 1 := by
  intro k _ n r
  exact Matrix.fromBlocks_one

theorem aux4 : ∀ (k : Type) [inst : Field k] (n r : ℕ)
  (A B : Matrix (Fin n) (Fin n) k),
  Matrix.fromBlocks (A * B) 0 0 (1 : Matrix (Fin r) (Fin r) k) =
    Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1 := by
  intro k _ n r A B
  simp [Matrix.fromBlocks_multiply]

noncomputable def blkHom : (k : Type) →
  [inst : Field k] → (n r : ℕ) → Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k :=
  fun k [Field k] n r =>
    { toFun := fun A => Matrix.fromBlocks A 0 0 1, map_one' := aux3 k n r,
      map_mul' := aux4 k n r }

noncomputable def blkGL : (k : Type) →
  [inst : Field k] → (n r : ℕ) → GL (Fin n) k →* GL (Fin (n + r)) k :=
  fun k [Field k] n r =>
    Units.map
      ((Matrix.reindexAlgEquiv k k finSumFinEquiv).toMulEquiv.toMonoidHom.comp
        (blkHom k n r))

noncomputable def blkAt : (k : Type) →
  [inst : Field k] → (n N : ℕ) → n ≤ N → GL (Fin n) k →* GL (Fin N) k :=
  fun k [Field k] n N h =>
    (glCongr k (Nat.add_sub_cancel' h)).comp
      (blkGL k n (N - n))

noncomputable def FixK : {k : Type} →
  [inst : Field k] →
    {m N : ℕ} →
      m + 1 ≤ N →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : Module ℂ V] → Representation ℂ (GL (Fin N) k) V → Subgroup (GL (Fin (m + 1)) k) → V → Prop :=
  fun {k} [Field k] {m N} h {V} [AddCommGroup V] [Module ℂ V] π K v =>
    ∀ g ∈ K, (π ((blkAt k (m + 1) N h) g)) v = v

theorem aux9 : ∀ {m N : ℕ} {h : m + 2 ≤ N}, ¬m + 1 ≤ N → False := by
  intro m N h a
  omega

private theorem continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    unfold blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (glCongr k e) := by
    intro a b e
    unfold glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_fixK : ∀ {k : Type} [inst : Field k]
  [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k] {m N : ℕ} {h : m + 2 ≤ N}
  {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V},
  IsSmooth π →
    ∀ (v w : V),
      ∃ K : Subgroup (GL (Fin (m + 1)) k),
        IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
          FixK
              (Decidable.byContradiction fun a => aux9 (h := h) a) π K v ∧
            FixK
              (Decidable.byContradiction fun a => aux9 (h := h) a) π K w := by
  intro k _ _ _ _ m N h V _ _ π hπ v w
  have hle : m + 1 ≤ N := by omega
  refine ⟨(fixer π v ⊓ fixer π w).comap
    (blkAt k (m + 1) N hle), ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (continuous_blkAt (m + 1) N hle)

end UpperTheory.Reformulated.B.BlockHomomorphism
end

section

open ValuativeRel

private lemma UpperTheory.isOpen_of_add_small {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] (s : Set k)
    (hs : ∀ x ∈ s, ∀ z, valuation k z < 1 → x + z ∈ s) : IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs x hx z (by simpa using hz)

private lemma UpperTheory.isOpen_valuation_le_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x ≤ 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_le hx hz.le

private lemma UpperTheory.isOpen_setOf_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x < 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_lt hx hz

private lemma UpperTheory.isClosed_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsClosed {x : k | valuation k x < 1} := by
  rw [← isOpen_compl_iff]
  refine UpperTheory.isOpen_of_add_small _ fun x hx z hz h => hx ?_
  have h' : valuation k (x + z - z) < 1 := (valuation k).map_sub_lt h hz
  simpa using h'

theorem UpperTheory.iwahori_subgroup_open :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
        (S : Set (Matrix.GeneralLinearGroup (Fin n) k)),
        (∀ g : Matrix.GeneralLinearGroup (Fin n) k, g ∈ S ↔
          (∀ i j, ValuativeRel.valuation k (g.val i j) ≤ 1) ∧ (∀ i j, ValuativeRel.valuation k ((g⁻¹).val i j) ≤ 1) ∧
            ∀ i j, j < i → ValuativeRel.valuation k (g.val i j) < 1) →
        IsOpen S ∧ IsCompact S := by
  intro k _ _ _ _ n S hS
  have c1 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  constructor
  · have e : S = (⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ((⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : j < i), (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) := by
      ext g
      rw [hS]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c1 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c2 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => (UpperTheory.isOpen_setOf_valuation_lt_one k).preimage (c1 i j)
  · let M : Set (Matrix (Fin n) (Fin n) k) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ 1}
    have hM : IsCompact M := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall k 1
    have hP : IsCompact (M ×ˢ (MulOpposite.op '' M)) :=
      hM.prod (hM.image MulOpposite.continuous_op)
    have hK := (Units.isClosedEmbedding_embedProduct
      (α := Matrix (Fin n) (Fin n) k)).isCompact_preimage hP
    have hC : IsClosed (⋂ i, ⋂ j, ⋂ (_ : j < i),
        (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) :=
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        (UpperTheory.isClosed_valuation_lt_one k).preimage (c1 i j)
    convert hK.inter_right hC using 1
    ext g
    rw [hS]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun i _ j _ => h1 i j, (g⁻¹).val, fun i _ j _ => h2 i j, rfl⟩, h3⟩
    · rintro ⟨⟨h1, m, hm, hme⟩, h3⟩
      have hm' : m = (g⁻¹).val := MulOpposite.op_injective hme
      subst hm'
      exact ⟨fun i j => h1 i trivial j trivial, fun i j => hm i trivial j trivial, h3⟩
end

section

theorem UpperTheory.Reformulated.B.DYda8.main :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] [IsGalois ℚ E],
      (∀ (a b : Gal(E/ℚ)), a * b = b * a) →
        ∀ (p : ℕ),
          Nat.Prime p →
            ∃ (φ : Gal(E/ℚ)),
              ∀ (O : Type) [inst_3 : CommRing O] (n : Ideal O),
                n.IsPrime →
                  (↑p : O) ∈ n →
                    ∀ (τ : NumberField.RingOfIntegers E →+* O) (x : NumberField.RingOfIntegers E),
                      (τ : NumberField.RingOfIntegers E → O)
                            ((NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv :
                                NumberField.RingOfIntegers E → NumberField.RingOfIntegers E)
                              x) -
                          (τ : NumberField.RingOfIntegers E → O) x ^ p ∈
                        n := by
  intro E _ _ _ hc p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa using hp.ne_zero
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) hp0
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := NumberField.RingOfIntegers E) (Ideal.span {(p : ℤ)})
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  haveI : Finite (NumberField.RingOfIntegers E ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) Q
  refine ⟨φ, ?_⟩
  intro O _ n hn hpn τ x
  have hP : (n.comap τ).IsPrime := Ideal.comap_isPrime τ n
  have hle : Ideal.span {(p : ℤ)} ≤ (n.comap τ).under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap]
    simpa using hpn
  have hund : (n.comap τ).under ℤ = Ideal.span {(p : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hund' : Q.under ℤ = Ideal.span {(p : ℤ)} := hQo.over.symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (NumberField.RingOfIntegers E)
    Gal(E/ℚ) Q (n.comap τ) (hund'.trans hund.symm)
  have hcj := hφ.conj g
  have hcomm : g * φ * g⁻¹ = φ := by
    rw [hc g φ, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm, ← hg] at hcj
  have hx := hcj x
  rw [hund] at hx
  rw [Int.card_ideal_quot, Ideal.mem_comap] at hx
  have he : (MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E) φ) x =
      NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv x := by
    ext
    rfl
  rw [he, map_sub, map_pow] at hx
  exact hx
end

section

theorem UpperTheory.Reformulated.B.DYha3.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] (x : E), ∃ (n : ℕ), (0 : ℕ) < n ∧ IsIntegral ℤ ((↑n : E) * x) := by
  intro E _ _ x
  obtain ⟨y, hy, h⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
    (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h
    simpa using h
  · rw [e] at h
    simpa using h.neg
end
