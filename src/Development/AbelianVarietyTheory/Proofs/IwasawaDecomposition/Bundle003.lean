module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
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
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.ProjModFinIso

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem finrank_prod_eq (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h1 := (TensorProduct.isBaseChange R (M × N) (FractionRing R)).finrank_eq
  have h2 := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  have h2' := (TensorProduct.isBaseChange R N (FractionRing R)).finrank_eq
  have h3 := (TensorProduct.prodRight R (FractionRing R) (FractionRing R) M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

theorem projective_of_isTorsionFree (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

theorem finrank_ideal (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by
  have h1 : Module.finrank R I ≤ 1 := by simpa using Submodule.finrank_le I
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr h
  have h2 := Module.finrank_pos (R := R) (M := I)
  omega

theorem nonempty_equiv_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have key : ∀ (z : R), z ≠ 0 → ∀ K : Ideal R, Nonempty (K ≃ₗ[R] ↥(Ideal.span {z} * K)) := by
    intro z hz K
    have hinj : Function.Injective (LinearMap.mulLeft R z) := fun a b hab => mul_left_cancel₀ hz hab
    refine ⟨(Submodule.equivMapOfInjective _ hinj K).trans (LinearEquiv.ofEq _ _ ?_)⟩
    ext w
    rw [Submodule.mem_map, Ideal.mem_span_singleton_mul]
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  exact ⟨(key x hx I).some.trans ((LinearEquiv.ofEq _ _ hxy).trans (key y hy J).some.symm)⟩

theorem exists_split (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R X)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    have := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a, s x a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsx (Finsupp.ext h)
  let f : X →ₗ[R] R := Finsupp.lapply a ∘ₗ s
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h
    have hm : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [h, Submodule.mem_bot] at hm
    exact ha hm
  let I : (Ideal R)⁰ := ⟨LinearMap.range f, mem_nonZeroDivisors_of_ne_zero hI⟩
  let g := f.rangeRestrict
  haveI := projective_of_isTorsionFree (R := R) (LinearMap.range f)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype ⟨l, hl⟩
  exact ⟨I, LinearMap.ker g, ⟨e⟩⟩

theorem exists_equiv_pi (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hne
      rw [not_subsingleton_iff_nontrivial] at hne
      have := Module.finrank_pos (R := R) (M := X)
      omega
    exact ⟨Empty, inferInstance, Empty.elim, by simp, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := R) (by omega)
    haveI := projective_of_isTorsionFree (R := R) X
    obtain ⟨I, K, ⟨e⟩⟩ := exists_split (R := R) X
    have hK : Module.finrank R K = r := by
      have h1 := e.finrank_eq
      rw [finrank_prod_eq, finrank_ideal _ (by simpa using nonZeroDivisors.ne_zero I.2)] at h1
      omega
    obtain ⟨ι, _, J, hcard, ⟨eK⟩⟩ := ih K hK
    refine ⟨Option ι, inferInstance, fun o => o.elim I J, by simp [hcard], ⟨?_⟩⟩
    exact e ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) eK ≪≫ₗ
      (LinearEquiv.piOptionEquivProd R (M := fun o => ((o.elim I J : (Ideal R)⁰) : Ideal R))).symm

theorem exists_finite_reps [Finite (ClassGroup R)] (q : ℕ) :
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} R), ∀ (X : Type) [AddCommGroup X] [Module R X]
      [Module.Finite R X] [Module.Projective R X], Module.finrank R X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[R] Y k) := by
  let rep : ClassGroup R → Ideal R := fun c => ((ClassGroup.mk0_surjective c).choose : Ideal R)
  have hrep : ∀ c : ClassGroup R, ClassGroup.mk0 (ClassGroup.mk0_surjective c).choose = c :=
    fun c => (ClassGroup.mk0_surjective c).choose_spec
  let S := Σ r : Fin (q + 1), (Fin r → ClassGroup R)
  let Y' : S → ModuleCat.{0} R := fun s => ModuleCat.of R ((b : Fin s.1) → rep (s.2 b))
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun k => Y' (eS.symm k), ?_⟩
  intro X _ _ _ _ hX
  obtain ⟨ι, _, I, hcard, ⟨e⟩⟩ := exists_equiv_pi (R := R) (Module.finrank R X) X rfl
  let eι := Fintype.equivFin ι
  let s : S := ⟨⟨Fintype.card ι, by omega⟩, fun b => ClassGroup.mk0 (I (eι.symm b))⟩
  refine ⟨eS s, ?_⟩
  show Nonempty (X ≃ₗ[R] Y' (eS.symm (eS s)))
  rw [Equiv.symm_apply_apply]
  have hI : ∀ i, Nonempty ((I i : Ideal R) ≃ₗ[R] rep (ClassGroup.mk0 (I i))) := fun i =>
    nonempty_equiv_of_mk0_eq (hrep _).symm
  exact ⟨e ≪≫ₗ LinearEquiv.piCongrRight (fun i => (hI i).some) ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun i => ↥(rep (ClassGroup.mk0 (I i)))) eι⟩

theorem finitely_many_iso_classes : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  intro E _ _ q
  exact exists_finite_reps q

end GlobalTheory.ProjModFinIso
end

section

open Polynomial

namespace GlobalTheory

theorem exists_galois_subfield_conj_stable (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ (∀ z ∈ S, z ∈ K) ∧
      Complex.I ∈ K ∧ ∀ z ∈ K, starRingEnd ℂ z ∈ K := by
  classical
  have hI : IsIntegral ℚ Complex.I := by
    refine ⟨X ^ 2 + C 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [Complex.I_sq]
  have hint : ∀ z ∈ insert Complex.I S, IsIntegral ℚ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hI
    · exact (hS z hz).isIntegral
  obtain ⟨p, hp⟩ : ∃ p : ℚ[X], p = ∏ z ∈ insert Complex.I S, minpoly ℚ z := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact Finset.prod_ne_zero_iff.2 fun z hz => minpoly.ne_zero (hint z hz)
  have hroot : ∀ z ∈ insert Complex.I S, z ∈ p.rootSet ℂ := by
    intro z hz
    rw [mem_rootSet]
    refine ⟨hp0, ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (minpoly ℚ) hz
    rw [hp, hq, map_mul, minpoly.aeval, zero_mul]
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have : p.IsSplittingField ℚ K :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
  have hfin : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K p
  have : Normal ℚ K := Normal.of_isSplittingField p
  refine ⟨K, hfin, IsGalois.mk,
    fun z hz => IntermediateField.subset_adjoin ℚ _ (hroot z (Finset.mem_insert_of_mem hz)),
    IntermediateField.subset_adjoin ℚ _ (hroot _ (Finset.mem_insert_self _ _)), ?_⟩
  let φ : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have hsub : φ '' (p.rootSet ℂ) ⊆ p.rootSet ℂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_rootSet] at hw ⊢
    exact ⟨hw.1, by rw [Polynomial.aeval_algHom_apply, hw.2, map_zero]⟩
  have hle : K.map φ ≤ K := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  intro z hz
  exact hle ⟨z, hz, rfl⟩

end GlobalTheory
end

section

namespace GlobalTheory.FiberCardPermutation

theorem card_fiber_eq_count {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by
  rw [← Fin.univ_val_map, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin n), v = w ∘ (⇑σ : Fin n → Fin n) := by
  classical
  have hm : (List.ofFn v : Multiset α) = (List.ofFn w : Multiset α) := Multiset.coe_eq_coe.mpr h
  have hc : ∀ c : α, Fintype.card {i : Fin n // v i = c} = Fintype.card {i : Fin n // w i = c} := by
    intro c
    have h1 := card_fiber_eq_count v c
    have h2 := card_fiber_eq_count w c
    rw [hm, ← h2] at h1
    convert h1
  refine ⟨Equiv.ofFiberEquiv (f := v) (g := w) (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map (f := v) (g := w) _ i).symm

end GlobalTheory.FiberCardPermutation
end

section

namespace GlobalTheory

theorem exists_generator_sq_eq_of_sq_mem_zpowers :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by
  intro p hp a ha
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgn : orderOf g = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : 0 < Nat.card (ZMod p)ˣ := Nat.card_pos
  have gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤ :=
    fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])
  have hdn : orderOf a ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard a
  have hd0 : 0 < orderOf a := orderOf_pos a
  have key : orderOf (g ^ 2) ∣ orderOf (a ^ 2) := orderOf_dvd_of_mem_zpowers (ha g)
  rw [orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn] at key
  generalize Nat.card (ZMod p)ˣ = n at *
  generalize hd : orderOf a = d at *
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd
  · rcases Nat.even_or_odd d with ⟨e, he⟩ | hd_odd
    · refine ⟨a, gen a ?_, rfl⟩
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      have h2 : d.gcd 2 = 2 := Nat.gcd_eq_right ⟨e, by omega⟩
      rw [h1, h2, show n / 2 = m by omega, show d / 2 = e by omega] at key
      have h3 : e ∣ m := by
        rw [he, hm, ← two_mul, ← two_mul] at hdn
        exact Nat.dvd_of_mul_dvd_mul_left two_pos hdn
      have := Nat.dvd_antisymm key h3
      omega
    · have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hd_odd
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      rw [h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega] at key
      have h3 : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])
      have hdm : d = m := Nat.dvd_antisymm h3 key
      have hgm : orderOf (g ^ m) = 2 := by
        have := orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)
        rwa [show orderOf g / 2 = m by omega] at this
      refine ⟨a * g ^ m, gen _ ?_, ?_⟩
      · rw [(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]
        omega
      · have hg1 : g ^ n = 1 := hgn ▸ pow_orderOf_eq_one g
        rw [mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]
  · have hd_odd : Odd d := hn_odd.of_dvd_nat hdn
    refine ⟨a, gen a ?_, rfl⟩
    rw [(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one,
      Nat.div_one, Nat.div_one] at key
    rw [hd]
    exact Nat.dvd_antisymm hdn key

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.LatticeLocBasis

theorem exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  have := Submodule.IsLattice.free E M
  have := Submodule.IsLattice.finite E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

theorem exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  intro K _ _ n _ _ L 𝔭 hfg hsp
  have hp := 𝔭.isPrime
  have hS : 𝔭.asIdeal.primeCompl ≤ (𝓞 K)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra K 𝔭.asIdeal.primeCompl hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) 𝔭.ne_bot A
  obtain ⟨⟨s, hs⟩, b, hli, hb, hw⟩ := exists_basis_up_to_fintype (A := A) 𝔭.asIdeal.primeCompl L hfg hsp
  let g : Matrix n n K := Matrix.of fun i j => b j i
  have hcol : g.col = b := by funext j i; rfl
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨g, hdet, s, hs, ?_, ?_⟩
  · intro x hx i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
    have hg : g *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = (s : K) • x := by
      have : (s : K) • x = s • x := algebraMap_smul K s x
      rw [this]
      change _ = ((⟨s, hs⟩ : 𝔭.asIdeal.primeCompl) : 𝓞 K) • x
      rw [← ha]
      funext i
      simp only [Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h2 : (s : K) • (g⁻¹ *ᵥ x) = fun i => algebraMap (𝓞 K) K (a i) := by
      rw [← Matrix.mulVec_smul, ← hg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    exact ⟨a i, (congrFun h2 i).symm⟩
  · intro j
    have : (s : K) • (fun i => g i j) = s • b j := algebraMap_smul K s (b j)
    rw [this]
    exact L.smul_mem _ (hb j)

end GlobalTheory.LatticeLocBasis
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DomainDens

def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))

theorem blockSym_apply {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := rfl

end GlobalTheory.DomainDens
end
end

section

namespace GlobalTheory.IntertwineAeval

theorem intertwine_pow {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (n : ℕ) (v : M) : r ((T ^ n) v) = (T' ^ n) (r v) := by
  induction n generalizing v with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem intertwine_aeval {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (p : Polynomial ℂ) (v : M) :
    r (Polynomial.aeval T p v) = Polynomial.aeval T' p (r v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, intertwine_pow r h]

end GlobalTheory.IntertwineAeval
end
