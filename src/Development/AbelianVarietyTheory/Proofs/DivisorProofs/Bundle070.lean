module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma trace_eq_zero_of_not_finite' {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = 0 := by
  have hb : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp [LinearMap.trace, hb]

open scoped TensorProduct in
private lemma finite_left_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ V := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra! h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  let p : V ⊗[ℂ] W →ₗ[ℂ] V :=
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ
  refine Module.Finite.of_surjective p fun v => ⟨v ⊗ₜ ((φ w)⁻¹ • w), ?_⟩
  simp [p, hφ]

open scoped TensorProduct in
private lemma finite_right_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ W := by
  have : Module.Finite ℂ (W ⊗[ℂ] V) :=
    Module.Finite.equiv (TensorProduct.comm ℂ V W)
  exact finite_left_of_finite_tensor_of_nontrivial (W := V)


open scoped TensorProduct in
theorem _root_.GlobalTheory.trace_tensorProduct_map_complex {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · rw [trace_eq_zero_of_not_finite' hU' T', mul_zero]
      by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
      · rcases subsingleton_or_nontrivial U with hs | hs
        · rw [Subsingleton.elim T 0, TensorProduct.map_zero_left, map_zero]
        · exact absurd (finite_right_of_finite_tensor_of_nontrivial (V := U)) hU'
      · exact trace_eq_zero_of_not_finite' hUU _
  · rw [trace_eq_zero_of_not_finite' hU T, zero_mul]
    by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
    · rcases subsingleton_or_nontrivial U' with hs | hs
      · rw [Subsingleton.elim T' 0, TensorProduct.map_zero_right, map_zero]
      · exact absurd (finite_left_of_finite_tensor_of_nontrivial (W := U')) hU
    · exact trace_eq_zero_of_not_finite' hUU _

end GlobalTheory
end

section

open Submodule

namespace GlobalTheory.AbsDec

theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (ht : iSupIndep t) :
    ∃ T : ι → V →ₗ[ℂ] V, (∀ i v, T i v ∈ t i) ∧
      (∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (⨆ i, t i)
  have hcompl : ∀ i, IsCompl (t i) ((⨆ (j) (_ : j ≠ i), t j) ⊔ C) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨q, hq, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
      have hcQ : c ∈ ⨆ i, t i := by
        have h1 : q + c ∈ ⨆ i, t i := Submodule.mem_iSup_of_mem i hx
        have h2 : q ∈ ⨆ i, t i :=
          (iSup₂_le fun j _ => le_iSup t j : (⨆ (j) (_ : j ≠ i), t j) ≤ ⨆ i, t i) hq
        simpa using Submodule.sub_mem _ h1 h2
      have hc0 : c = 0 := (Submodule.disjoint_def.1 hC.disjoint) c hcQ hc
      subst hc0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 ((iSupIndep_def.1 ht) i)) q hx hq
    · rw [codisjoint_iff, eq_top_iff, ← hC.sup_eq_top]
      refine sup_le (iSup_le fun j => ?_) (le_sup_of_le_right le_sup_right)
      by_cases h : j = i
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le j h le_rfl))
  refine ⟨fun i => (t i).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ (hcompl i),
    fun i v => ?_, fun i j v hv => ?_⟩
  · simp
  · split_ifs with h
    · subst h
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hcompl i) ⟨v, hv⟩)
    · have hv' : v ∈ (⨆ (k) (_ : k ≠ i), t k) ⊔ C :=
        Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm h) hv))
      have := Submodule.linearProjOfIsCompl_apply_right (hcompl i) ⟨v, hv'⟩
      exact congrArg Subtype.val this

theorem sum_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) {v : V} (hv : v ∈ ⨆ i, t i) :
    ∑ i, T i v = v := by
  refine Submodule.iSup_induction t (motive := fun v => ∑ i, T i v = v) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · simp [hT _ j x hx]
  · simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]

theorem proj_comm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0)
    (hst : ∀ j g, ∀ v ∈ t j, ρ g v ∈ t j) (i : ι) (g : G) {v : V} (hv : v ∈ ⨆ j, t j) :
    T i (ρ g v) = ρ g (T i v) := by
  refine Submodule.iSup_induction t (motive := fun v => T i (ρ g v) = ρ g (T i v)) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · rw [hT i j _ (hst j g x hx), hT i j x hx]
    split_ifs <;> simp
  · simp only [map_add (f := _), hx, hy]

end GlobalTheory.AbsDec

namespace GlobalTheory.AbsDec

theorem fixed_decomposition : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  intro G V _ _ _ ρ K F hF 𝒜 h𝒜 hfd
  classical
  let good : Finset (Submodule ℂ V) → Prop := fun s =>
    (∀ P ∈ s, P ∈ 𝒜 ∧ P ⊓ F ≠ ⊥) ∧ s.SupIndep id
  have bound : ∀ s, good s → s.card ≤ Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := by
    intro s hs
    have hv : ∀ P : s, ∃ v, v ∈ (P : Submodule ℂ V) ⊓ F ∧ v ≠ 0 := fun P =>
      Submodule.exists_mem_ne_zero_of_ne_bot (hs.1 P P.2).2
    choose v hv0 hvne using hv
    have hind : iSupIndep (fun P : s => (P : Submodule ℂ V) ⊓ F) :=
      ((iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2).mono fun P => inf_le_left
    have hli : LinearIndependent ℂ v := hind.linearIndependent _ hv0 hvne
    have hvM : ∀ P : s, v P ∈ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V) := fun P =>
      (le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (P : Submodule ℂ V) (hs.1 P P.2).1 le_rfl) (hv0 P)
    have hli' : LinearIndependent ℂ
        (fun P : s => (⟨v P, hvM P⟩ : (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    simpa using hli'.fintype_card_le_finrank
  have h0 : ∃ s, good s ∧ s.card = 0 := ⟨∅, ⟨by simp, Finset.supIndep_empty _⟩, rfl⟩
  obtain ⟨s, hs, hsN⟩ := Nat.findGreatest_spec (P := fun n => ∃ s, good s ∧ s.card = n)
    (Nat.zero_le (Module.finrank ℂ (⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V))) h0
  have hmax : ∀ s', good s' → s'.card ≤ s.card := by
    intro s' hs'
    rw [hsN]
    by_contra hlt
    push_neg at hlt
    exact Nat.findGreatest_is_greatest hlt (bound s' hs') ⟨s', hs', rfl⟩
  have hQ : ∀ g, ∀ v ∈ ⨆ P : s, (P : Submodule ℂ V), ρ g v ∈ ⨆ P : s, (P : Submodule ℂ V) := by
    intro g v hv
    have : (⨆ P : s, (P : Submodule ℂ V)) ≤ (⨆ P : s, (P : Submodule ℂ V)).comap (ρ g) :=
      iSup_le fun P w hw => Submodule.mem_iSup_of_mem P ((h𝒜 P (hs.1 P P.2).1).2.1 g w hw)
    exact this hv
  have hsup : s.sup id = ⨆ P : s, (P : Submodule ℂ V) := by
    rw [Finset.sup_eq_iSup, iSup_subtype']
    rfl
  have hcover : ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → P ≤ ⨆ Q : s, (Q : Submodule ℂ V) := by
    intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    rcases hirr (P ⊓ ⨆ Q : s, (Q : Submodule ℂ V)) inf_le_left
      (fun g v hv => ⟨hst g v hv.1, hQ g v hv.2⟩) with h | h
    · exfalso
      have hPs : P ∉ s := by
        intro hPs
        have hle : P ≤ P ⊓ ⨆ Q : s, (Q : Submodule ℂ V) :=
          le_inf le_rfl (le_iSup_of_le (⟨P, hPs⟩ : s) le_rfl)
        rw [h] at hle
        exact hne (eq_bot_iff.2 hle)
      have hgood : good (insert P s) := by
        refine ⟨fun R hR => ?_, hs.2.insert ?_⟩
        · rcases Finset.mem_insert.1 hR with rfl | hR
          · exact ⟨hP, hPF⟩
          · exact hs.1 R hR
        · rw [hsup, disjoint_iff]
          exact h
      have := hmax _ hgood
      rw [Finset.card_insert_of_notMem hPs] at this
      omega
    · rw [← h]
      exact inf_le_right
  have hind : iSupIndep (fun P : s => (P : Submodule ℂ V)) :=
    (iSupIndep_comp_coe_iff_supIndep (f := id)).2 hs.2
  obtain ⟨T, hTmem, hT⟩ := exists_proj (fun P : s => (P : Submodule ℂ V)) hind
  have hst' : ∀ (j : s) g, ∀ v ∈ (j : Submodule ℂ V), ρ g v ∈ (j : Submodule ℂ V) :=
    fun j => (h𝒜 j (hs.1 j j.2).1).2.1
  refine ⟨s, inferInstance, fun P => P, fun i => hs.1 i i.2, hind.mono fun i => inf_le_left,
    ?_, ?_⟩
  · apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (f := fun (Q : Submodule ℂ V) (_ : Q ∈ 𝒜) => Q ⊓ F)
        (i : Submodule ℂ V) (hs.1 i i.2).1 le_rfl
    · refine iSup₂_le fun P hP => ?_
      by_cases hPF : P ⊓ F = ⊥
      · rw [hPF]
        exact bot_le
      intro φ hφ
      have hφQ := hcover P hP hPF hφ.1
      rw [← sum_proj _ T hT hφQ]
      refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨hTmem i φ, ?_⟩
      refine (hF _).2 fun k hk => ?_
      rw [← proj_comm ρ _ T hT hst' i k hφQ, (hF φ).1 hφ.2 k hk]
  · intro P hP hPF
    obtain ⟨hne, hst, hirr⟩ := h𝒜 P hP
    have hPQ := hcover P hP hPF
    have hex : ∃ i, ∀ v ∈ P, T i v = 0 → v = 0 := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ i, ∀ v ∈ P, T i v = 0 := by
        intro i
        obtain ⟨w, hwP, hw0, hwne⟩ := hcon i
        rcases hirr (P ⊓ LinearMap.ker (T i)) inf_le_left (fun g v hv => ⟨hst g v hv.1,
            LinearMap.mem_ker.2 (by
              rw [proj_comm ρ _ T hT hst' i g (hPQ hv.1), LinearMap.mem_ker.1 hv.2, map_zero])⟩)
          with h | h
        · exact absurd ((Submodule.eq_bot_iff _).1 h w ⟨hwP, hw0⟩) hwne
        · intro v hv
          have hv' : v ∈ P ⊓ LinearMap.ker (T i) := by rw [h]; exact hv
          exact hv'.2
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hvne
      rw [← sum_proj _ T hT (hPQ hv)]
      exact Finset.sum_eq_zero fun i _ => hall i v hv
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, T i, fun v _ => hTmem i v, hi, fun g v hv => proj_comm ρ _ T hT hst' i g (hPQ hv)⟩

end GlobalTheory.AbsDec
end

section

open Module

namespace GlobalTheory.SemilinearReading

theorem exists_semilinear_extension_rep :
    ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  intro K LL Cs W G _ _ _ _ _ _ _ _ n m σ₀ σ hσ cu b hbs hbi hbt R hR hRs ρL
  classical
  let B : Basis (Fin m) LL (Fin n → LL) := Basis.mk hbi hbt.ge
  have hB : ∀ k, B k = cu (b k) := fun k => Basis.mk_apply _ _ _
  let f : (Fin n → LL) →ₛₗ[σ] W :=
    { toFun := fun w => ∑ k, σ (B.repr w k) • R (b k)
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.smul_sum, mul_smul] }
  have hfB : ∀ k, f (B k) = R (b k) := by
    intro k
    change ∑ j, σ (B.repr (B k) j) • R (b j) = _
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  have hcu : ∀ F, f (cu F) = R F := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [hbs]; trivial
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hF

    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ R, ← hB, ← algebraMap_smul LL (a k) (B k), map_smulₛₗ f, hσ, hfB]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun k => R (b k)) := by
    rw [← hRs, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    rw [← hcu]
    change ∑ j, σ (B.repr (cu F) j) • R (b j) ∈ _
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let C : Basis (Fin m) ℂ W := Basis.mk hR hsp
  have hC : ∀ k, C k = f (B k) := fun k => by rw [hfB]; exact Basis.mk_apply _ _ _
  let r : G → W →ₗ[ℂ] W := fun g => C.constr ℂ fun k => f (ρL g (B k))
  have hr : ∀ g w, r g (f w) = f (ρL g w) := by
    intro g w
    conv_lhs => rw [← B.sum_repr w]
    conv_rhs => rw [← B.sum_repr w]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ f, map_smul, map_smul, map_smulₛₗ f, ← hC]
    simp [r]
  let ρ : Representation ℂ G W :=
    { toFun := r
      map_one' := C.ext fun k => by rw [hC, hr]; simp
      map_mul' := fun g h => C.ext fun k => by
        rw [hC, Module.End.mul_apply, hr, hr, hr, map_mul]; rfl }
  refine ⟨f, ρ, hcu, hr, ?_, ?_⟩
  · have hmn : m = n := by
      simpa using (Module.finrank_eq_card_basis B).symm
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · refine hsp.trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change R (b k) ∈ _

      rw [← hfB, ← (Pi.basisFun LL (Fin n)).sum_repr (B k), map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smulₛₗ f, Pi.basisFun_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Module.finrank_eq_card_basis C, hmn]
  · rw [eq_top_iff]
    refine hsp.trans (Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨B k, hfB k⟩

end GlobalTheory.SemilinearReading
end

section

open Filter Topology

namespace GlobalTheory

open Polynomial

theorem adjoinRoot_map_complex_linearIndependent :
    ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic →
      ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))),
        (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧
        (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧
        ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e →
          LinearIndependent ℂ (fun j => τ (e j)) := by
  intro D P hP
  set f : MvPolynomial (Fin D) ℚ →+* MvPolynomial (Fin D) ℂ := MvPolynomial.map (algebraMap ℚ ℂ)
  set Q := P.map f
  have hQ : Q.Monic := hP.map f
  have h0 : P.eval₂ ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) = 0 := by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root]
  let τ := AdjoinRoot.lift ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) h0
  have hof : ∀ r, τ (AdjoinRoot.of P r) = AdjoinRoot.of Q (f r) := fun r => by
    simp [τ, AdjoinRoot.lift_of]
  have hroot : τ (AdjoinRoot.root P) = AdjoinRoot.root Q := AdjoinRoot.lift_root _
  have hsmul : ∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u := by
    intro q u
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin D) ℚ),
      AdjoinRoot.algebraMap_eq, hof, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin D) ℂ),
      AdjoinRoot.algebraMap_eq]
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨τ, fun i => by rw [hof]; simp [f], hsmul, ?_⟩
  intro J e he
  let τL : AdjoinRoot P →ₗ[ℚ] AdjoinRoot Q :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := fun q u => by
        rw [hsmul]
        exact algebraMap_smul ℂ q (τ u) }
  let bA := (MvPolynomial.basisMonomials (Fin D) ℚ).smulTower (AdjoinRoot.powerBasis' hP).basis
  let bB := (MvPolynomial.basisMonomials (Fin D) ℂ).smulTower (AdjoinRoot.powerBasis' hQ).basis
  have hdim : (AdjoinRoot.powerBasis' hP).dim = (AdjoinRoot.powerBasis' hQ).dim := by
    simp [AdjoinRoot.powerBasis', Q, hP.natDegree_map]
  let σ := Equiv.prodCongr (Equiv.refl (Fin D →₀ ℕ)) (finCongr hdim)
  let E := (Algebra.TensorProduct.basis ℂ bA).equiv bB σ
  have hbas : ∀ k, τ (bA k) = bB (σ k) := by
    rintro ⟨a, i⟩
    simp only [bA, bB, σ, Module.Basis.smulTower_apply, MvPolynomial.coe_basisMonomials,
      PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, Equiv.prodCongr_apply, Equiv.coe_refl,
      Prod.map, id, finCongr_apply, Fin.val_cast]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, hroot, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.algebraMap_eq, hof]
    simp [f, MvPolynomial.map_monomial]
  have hkey : ∀ v, E (1 ⊗ₜ[ℚ] v) = τ v := by
    intro v
    have := bA.ext (f₁ := (E.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ _ 1))
      (f₂ := τL) (fun k => by
        simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
        rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply]
        exact (hbas k).symm)
    exact congrArg (fun g => g v) this
  have hli : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) :=
    Module.Flat.linearIndependent_one_tmul he
  have := hli.map' E.toLinearMap E.ker
  have h2 : (fun j => τ (e j)) = E.toLinearMap ∘ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) := by
    funext j
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    exact (hkey (e j)).symm
  rw [h2]
  exact this

end GlobalTheory
end

section

namespace GlobalTheory.CMModel

theorem valuation_natCast_eq_one_of_coprime (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  have hint : ∀ z : ℤ, V.valuation (z : ℂ) ≤ 1 := fun z =>
    (V.valuation_le_one_iff _).2 (intCast_mem V z)
  have hnat : ∀ n : ℕ, V.valuation (n : ℂ) ≤ 1 := fun n =>
    (V.valuation_le_one_iff _).2 (natCast_mem V n)
  by_contra hcon
  rw [not_or] at hcon
  have ha : V.valuation (a : ℂ) < 1 := lt_of_le_of_ne (hnat a) hcon.1
  have hb : V.valuation (b : ℂ) < 1 := lt_of_le_of_ne (hnat b) hcon.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  have hC : (x : ℂ) * (a : ℂ) + (y : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hxy
  have h1 : V.valuation ((x : ℂ) * (a : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint x)) ha
  have h2 : V.valuation ((y : ℂ) * (b : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint y)) hb
  have h3 := V.valuation.map_add_lt h1 h2
  rw [hC, map_one] at h3
  exact lt_irrefl _ h3

end GlobalTheory.CMModel
end

section

namespace GlobalTheory.DiagVol

def ordL {n : Type*} (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) (fun i => 2 * (i.val + 1))

end GlobalTheory.DiagVol
end
