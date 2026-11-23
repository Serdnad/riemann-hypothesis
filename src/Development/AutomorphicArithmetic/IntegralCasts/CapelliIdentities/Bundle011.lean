module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

theorem UpperTheory.Reformulated.B.SummandLocalization.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.SummandLocalization.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SummandLocalization.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.SummandLocalization.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ

private theorem UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule {R K W : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (M : Submodule R W) (hM : Submodule.span K (M : Set W) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype where
  map_units s := by
    have hs : algebraMap R K s ≠ 0 := (IsLocalization.map_units K s).ne_zero
    rw [Module.End.isUnit_iff]
    have h : ((algebraMap R (Module.End R W)) s : W → W) = fun w => (algebraMap R K s) • w := by
      funext w
      simp
    rw [h]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set W) := hM ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set W) y hy
    rw [Submodule.span_eq] at ht
    exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

private theorem UpperTheory.Reformulated.B.SummandLocalization.exists_proj {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (X : Submodule K V) (L : Submodule R V) (hL : Submodule.IsFullLattice K L) :
    ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ L, π y ∈ L := by
  let q : V →ₗ[R] V ⧸ X := X.mkQ.restrictScalars R
  let M : Submodule R (V ⧸ X) := L.map q
  have hM : Submodule.span K (M : Set (V ⧸ X)) = ⊤ := by
    have h : (M : Set (V ⧸ X)) = X.mkQ '' (L : Set V) := rfl
    rw [h, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 (hL.fg.map q)
  haveI : Module.IsTorsionFree R (V ⧸ X) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ X)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective (q.submoduleMap L) := LinearMap.submoduleMap_surjective q L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.submoduleMap L) LinearMap.id hsurj
  haveI := UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule M hM
  have hb : IsBaseChange K M.subtype := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K M.subtype
  let σ : (V ⧸ X) →ₗ[K] V := hb.lift (L.subtype ∘ₗ s)
  have hσ : ∀ m : M, σ m = (s m : V) := fun m => hb.lift_eq (L.subtype ∘ₗ s) m
  have hq : X.mkQ ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext_on hM
    intro m hm
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨m, hm⟩)
    rw [LinearMap.comp_apply, hσ ⟨m, hm⟩]
    exact h1
  refine ⟨LinearMap.id - σ ∘ₗ X.mkQ, fun v => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 := LinearMap.congr_fun hq (X.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  · have h1 : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).2 hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  · have h1 := hσ ⟨q y, Submodule.mem_map_of_mem hy⟩
    have h2 : σ (X.mkQ y) ∈ L := by
      have h3 : σ (X.mkQ y) = _ := h1
      rw [h3]
      exact Subtype.property _
    exact L.sub_mem hy h2

theorem UpperTheory.Reformulated.B.SummandLocalization.summand_localization :
    UpperTheory.Reformulated.B.SummandLocalization.SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 _ Λ ⟨Λ₀, hΛ₀, rfl⟩
  obtain ⟨π, h1, h2, h3⟩ := UpperTheory.Reformulated.B.SummandLocalization.exists_proj X Λ₀ hΛ₀
  refine ⟨π, h1, h2, ?_⟩
  rintro y ⟨s, hs, hy⟩
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact h3 _ hy
end

section

namespace UpperTheory.Reformulated.B.Gr23

open Polynomial

private theorem eval_prod (m : Multiset ℂ) (u : ℂ) :
    ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod.eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ ↦ ?_
  simp

private theorem eq_of_prod_eq {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (fun x : ℂ ↦ u + x)).prod = (m'.map (fun x : ℂ ↦ u + x)).prod) :
    m = m' := by
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod := by
    refine Polynomial.funext fun u ↦ ?_
    rw [eval_prod, eval_prod, h u]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem abs {M : Type*} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} (hV : V ≠ ⊥)
    (T : ℂ → Module.End ℂ M) {a : ℕ} {m m' : Multiset ℂ}
    (h : m.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod • φ)
    (h' : m'.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod • φ) :
    m = m' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  refine eq_of_prod_eq fun u ↦ ?_
  exact smul_left_injective ℂ hφ0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))

end UpperTheory.Reformulated.B.Gr23
end

section

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep.{u_1} :
    {n : ℕ} →
      {M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → (Fin n → Fin n → Module.End ℂ M) → Prop :=
    fun {n : ℕ} {M : Type u_1} [AddCommGroup M] [_root_.Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b =
          (if b = c then E a d else (0 : Module.End ℂ M)) - if d = a then E c b else (0 : Module.End ℂ M)

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL

section helpers

variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

private abbrev P (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod

private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩

private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this

private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _

private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)

private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))

end helpers

end UpperTheory.Reformulated.B.ParabolicUnipotentGL

theorem UpperTheory.Reformulated.B.ParabolicUnipotentGL.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
end

section

noncomputable def UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

theorem UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ}
      {x y : Module.End ℂ V},
      x ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j → y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k → x * y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
  intro n V _ _ E j k x y hx hy
  have h : UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j * UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k ≤ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
    unfold UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ⟨l1, hl1, rfl⟩, b, ⟨l2, hl2, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [List.map_append, List.prod_append]
  exact h (Submodule.mul_mem_mul hx hy)
end

section

theorem UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∃ (e : Fin (Module.finrank ℂ V) → V),
          (∀ (i : Fin (Module.finrank ℂ V)), ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) (e i) = (1 : ℂ)) ∧
            (∀ (x y : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y =
                  ∑ i : Fin (Module.finrank ℂ V),
                    ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) (e i) * ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) y) ∧
              ∀ (x y : V),
                ‖((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
                  (((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ⋆[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ _ B hs hp
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by simp
      definite := fun x h => by
        by_contra hx
        have h1 := hp x hx
        have h2 : B x x = 0 := h
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hB : ∀ x y : V, B x y = inner ℂ y x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨b, fun i => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hB]
    exact b.inner_eq_one i
  · simp only [hB]
    rw [← b.sum_inner_mul_inner y x]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [hB]
    have h := inner_mul_inner_self_le (𝕜 := ℂ) y x
    rw [norm_inner_symm x y] at h
    rw [sq, mul_comm (inner ℂ x x).re]
    exact h
end

section

theorem UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∀ (L : V →ₗ⋆[ℂ] ℂ), ∃ (u : V), ∀ (b : V), (L : V → ℂ) b = ((B : V → V →ₗ⋆[ℂ] ℂ) u : V → ℂ) b := by
  intro V _ _ _ B _ hpos L
  let e := Module.finBasis ℂ V
  let Φ : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    { toFun := fun u i => B u (e i)
      map_add' := fun u v => by funext i; simp
      map_smul' := fun c u => by funext i; simp }
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : B u = 0 := e.ext fun i => congrFun hu i
    by_contra hne
    have h := hpos u hne
    rw [h0] at h
    simp at h
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨u, hu⟩ := hsurj fun i => L (e i)
  have hL : L = B u := e.ext fun i => (congrFun hu i).symm
  exact ⟨u, fun b => by rw [hL]⟩
end
