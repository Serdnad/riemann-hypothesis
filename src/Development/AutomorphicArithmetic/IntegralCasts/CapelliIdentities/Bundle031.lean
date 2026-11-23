module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

private theorem common_eigenvector_commuting_family {T D : Type}
    [AddCommGroup D] [_root_.Module ℂ D] [FiniteDimensional ℂ D] (φ : T → _root_.Module.End ℂ D)
    (hc : ∀ (s t : T), Commute (φ s) (φ t)) :
    ∀ (n : ℕ) (W : Submodule ℂ D), _root_.Module.finrank ℂ W = n → W ≠ ⊥ →
      (∀ (t : T), ∀ x ∈ W, φ t x ∈ W) →
      ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW hinv
    by_cases hs : ∀ t, ∃ c : ℂ, ∀ x ∈ W, φ t x = c • x
    · choose a ha using hs
      obtain ⟨l, hlW, hl⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨l, a, hl, fun t => ha t l hlW⟩
    · push Not at hs
      obtain ⟨t, ht⟩ := hs
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨c, hcv⟩ := _root_.Module.End.exists_eigenvalue ((φ t).restrict (hinv t))
      obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
      have hv0 : (v : D) ≠ 0 := fun h => hv.2 (Subtype.ext h)
      have hv1 : φ t (v : D) = c • (v : D) := by
        have := congrArg Subtype.val hv.apply_eq_smul
        simpa using this
      let E : Submodule ℂ D := W ⊓ _root_.Module.End.eigenspace (φ t) c
      have hE : ∀ y, y ∈ E ↔ y ∈ W ∧ φ t y = c • y := by
        intro y
        simp [E, Submodule.mem_inf, _root_.Module.End.mem_eigenspace_iff]
      have hEbot : E ≠ ⊥ := by
        intro h
        have : (v : D) ∈ E := (hE _).2 ⟨v.2, hv1⟩
        rw [h] at this
        exact hv0 (by simpa using this)
      have hlt : E < W := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hxW, hx⟩ := ht c
        exact hx ((hE x).1 (h ▸ hxW)).2
      have hfr : _root_.Module.finrank ℂ E < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ hfr E rfl hEbot ?_
      intro s y hy
      obtain ⟨hyW, hyc⟩ := (hE y).1 hy
      refine (hE _).2 ⟨hinv s y hyW, ?_⟩
      have h1 : φ t (φ s y) = φ s (φ t y) := by
        have := (hc t s).eq
        exact congrArg (fun f : _root_.Module.End ℂ D => f y) this
      rw [h1, hyc, map_smul]

theorem UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector :
    ∀ {T D : Type}
    [inst : AddCommGroup D] [inst_1 : _root_.Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D] (φ : T → Module.End ℂ D),
    (∀ (s t : T), Commute (φ s) (φ t)) → ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro T D _ _ _ _ φ hc
  exact common_eigenvector_commuting_family φ hc _ ⊤ rfl top_ne_bot (fun _ _ _ => Submodule.mem_top)
end

section

namespace CommutingFamilyCommonEigenvector

private lemma key {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
    (T : I → Module.End ℂ E) (hc : ∀ (a b : I), Commute (T a) (T b))
    (W : Submodule ℂ E) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W')
    (i : I) (w : E) (hw : w ∈ W) : ∃ μ : ℂ, T i w = μ • w := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let f : Module.End ℂ W := (T i).restrict (fun x hx => hinv i x hx)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  let W' : Submodule ℂ E := W ⊓ (T i).eigenspace μ
  have hW'le : W' ≤ W := inf_le_left
  have hvW' : (v : E) ∈ W' := by
    refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
    rw [Module.End.mem_eigenspace_iff]
    have := hv.apply_eq_smul
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  have hvne : (v : E) ≠ 0 := by
    intro h; apply hv.2; exact Subtype.ext h
  have hW'ne : W' ≠ ⊥ := by
    intro h; rw [h] at hvW'; exact hvne ((Submodule.mem_bot ℂ).mp hvW')
  have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
    intro j x hx
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hinv j x hx'.1, ?_⟩
    have hx2 : T i x = μ • x := Module.End.mem_eigenspace_iff.mp hx'.2
    rw [Module.End.mem_eigenspace_iff]
    have hcom : T i (T j x) = T j (T i x) := by
      have := hc i j
      exact congrArg (fun g : Module.End ℂ E => g x) this.eq
    rw [hcom, hx2, map_smul]
  have heq : W' = W :=
    Submodule.eq_of_le_of_finrank_le hW'le (hmin W' hW'ne hW'inv)
  have : w ∈ W' := heq ▸ hw
  exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp this).2

end CommutingFamilyCommonEigenvector

theorem UpperTheory.Reformulated.B.Ygb8.main :
    ∀ (d : ℕ) (E : Type) [inst : AddCommGroup E] [inst_1 : _root_.Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
      (T : I → Module.End ℂ E),
      (∀ (a b : I), Commute (T a) (T b)) →
        Module.finrank ℂ E = d → (0 : ℕ) < d → ∃ (w : E), w ≠ (0 : E) ∧ ∃ (c : I → ℂ), ∀ (i : I), (T i : E → E) w = c i • w := by
  intro d E _ _ _ I T hc hd hpos
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, T i x ∈ W) ∧
    Module.finrank ℂ W = n
  have hex : ∃ n, P n := by
    refine ⟨Module.finrank ℂ (⊤ : Submodule ℂ E), ⊤, ?_, fun i x _ => Submodule.mem_top, rfl⟩
    intro h
    have : Module.finrank ℂ (⊤ : Submodule ℂ E) = 0 := by rw [h]; simp
    rw [finrank_top] at this
    omega
  obtain ⟨W, hW, hinv, hWr⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWr]
    exact Nat.find_min' hex ⟨W', h1, h2, rfl⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨w, hw0, fun i => Classical.choose (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW), ?_⟩
  intro i
  exact Classical.choose_spec (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW)
end

section

theorem UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), Commute (f i) (f j)) →
      ∀ (n : ℕ) (W : Submodule ℂ M),
        Module.finrank ℂ ↥W = n →
          W ≠ ⊥ →
            (∀ (i : ι), ∀ x ∈ W, (f i : M → M) x ∈ W) →
              ∃ v ∈ W, v ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) v = c • v := by
  intro ι M _ _ _ f hc n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hW hinv
  by_cases h : ∀ i, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
    exact ⟨v, hv, hv0, fun i => (h i).imp fun c hc' => hc' v hv⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
    obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue
      ((f i).restrict (p := W) (q := W) (hinv i) : Module.End ℂ W)
    obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
    have hw1 : f i (w : M) = c • (w : M) := congrArg Subtype.val hw.apply_eq_smul
    have hw0 : (w : M) ≠ 0 := fun e => hw.2 (Subtype.ext e)
    have hlt : W ⊓ (f i).eigenspace c < W := by
      refine lt_of_le_of_ne inf_le_left fun e => hi ⟨c, fun x hx => ?_⟩
      rw [← e] at hx
      exact Module.End.mem_eigenspace_iff.1 hx.2
    have hne : W ⊓ (f i).eigenspace c ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, hw0⟩
    obtain ⟨v, hv, hv0, hall⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt)
      (W ⊓ (f i).eigenspace c) rfl hne (fun j x hx => by
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.2 ?_⟩
        have h1 : f i x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
        have h2 : f i (f j x) = f j (f i x) := LinearMap.congr_fun (hc i j).eq x
        rw [h2, h1, map_smul])
    exact ⟨v, hv.1, hv0, hall⟩
end

section

theorem UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), f i * f j = f j * f i) →
      ∀ (W : Submodule ℂ M),
        W ≠ ⊥ →
          (∀ (i : ι), ∀ y ∈ W, (f i : M → M) y ∈ W) →
            ∃ y ∈ W, y ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) y = c • y := by
  intro ι M _ _ _ f hc W hW hinv
  obtain ⟨V, ⟨hVW, hV0, hVinv⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ M)).has_min
      {V : Submodule ℂ M | V ≤ W ∧ V ≠ ⊥ ∧ ∀ i, ∀ y ∈ V, f i y ∈ V} ⟨W, le_rfl, hW, hinv⟩
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  refine ⟨y, hVW hyV, hy0, fun i => ?_⟩
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV0
  obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue ((f i).restrict (hVinv i) : Module.End ℂ V)
  obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
  have hv1 : f i (v : M) = c • (v : M) := by
    have h := congrArg Subtype.val hv.apply_eq_smul
    simpa using h
  have hv0 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  refine ⟨c, ?_⟩
  by_contra hne
  refine hmin (V ⊓ (f i).eigenspace c) ⟨inf_le_left.trans hVW, ?_, ?_⟩ ?_
  · intro h
    have hm : (v : M) ∈ V ⊓ (f i).eigenspace c :=
      ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv1⟩
    rw [h] at hm
    exact hv0 ((Submodule.mem_bot ℂ).mp hm)
  · intro j z hz
    refine ⟨hVinv j z hz.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    have hz2 : f i z = c • z := Module.End.mem_eigenspace_iff.mp hz.2
    have h : f i (f j z) = f j (f i z) := by
      rw [← Module.End.mul_apply, hc i j, Module.End.mul_apply]
    rw [h, hz2, map_smul]
  · refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hm : y ∈ V ⊓ (f i).eigenspace c := by rw [h]; exact hyV
    exact Module.End.mem_eigenspace_iff.mp hm.2
end

section

theorem UpperTheory.isOpen_stabilizer_linear_map :
    ∀ {G V M : Type} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup M] [Module ℂ M] (R : G → M →ₗ[ℂ] M) (f : V →ₗ[ℂ] M), (∀ v : V, IsOpen {g : G | R g (f v) = f v}) → IsOpen {g : G | R g ∘ₗ f = f} := by
  intro G V M _ _ _ _ _ _ R f h
  let b := Module.finBasis ℂ V
  have key : {g : G | R g ∘ₗ f = f} = ⋂ i, {g : G | R g (f (b i)) = f (b i)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hg i
      exact LinearMap.congr_fun hg (b i)
    · intro hg
      exact b.ext fun i => hg i
  rw [key]
  exact isOpen_iInter_of_finite fun i => h (b i)
end

section

theorem UpperTheory.Reformulated.B.IndependenceEigenvectors.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ j ∈ s, g j = 0 := by
      intro j hj
      have hne : lam j ≠ lam a := fun h => ha (hinj h ▸ hj)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam k i) • v k = 0 := by
        have h := congrArg (T i) hg

        simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam a i) • v k = 0 := by
        have h := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (lam a i)] using h
      have h3 : ∑ k ∈ s, (g k * (lam k i - lam a i)) • v k = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (add_left_cancel (h1.trans h2.symm))
      have h4 := ih (fun k => g k * (lam k i - lam a i)) h3 j hj
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hi)
    have hz : ∑ k ∈ s, g k • v k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hz, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
end

section

theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg

        simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
end

section

noncomputable def UpperTheory.Reformulated.B.Qh16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inG :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      X.conjTranspose * UpperTheory.Reformulated.B.Qh16.Jm ε + UpperTheory.Reformulated.B.Qh16.Jm ε * X = (0 : Matrix (Fin n) (Fin n) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inP :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      UpperTheory.Reformulated.B.Qh16.inG ε X ∧ X * UpperTheory.Reformulated.B.Qh16.Jm ε = -(UpperTheory.Reformulated.B.Qh16.Jm ε * X)

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end

section

theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card := by
  intro N J
  rfl

noncomputable def UpperTheory.Reformulated.B.MinorDeterminants.minorIJ :
    {R : Type} → [CommRing R] → {N : ℕ} → Matrix (Fin N) (Fin N) R → Finset (Fin N) → Finset (Fin N) → R :=
    fun {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) ↦
      if e : I.card = J.card then
        (h.submatrix (⇑(I.orderEmbOfFin e) : Fin J.card → Fin N)
            (⇑(J.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 J)) : Fin J.card → Fin N)).det
      else (0 : R)

theorem UpperTheory.Reformulated.B.MinorDeterminants.main :
    ∀ {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (f : Fin S.card → Fin N),
      Function.Injective f →
        UpperTheory.Reformulated.B.MinorDeterminants.minorIJ C (Finset.image f Finset.univ) S = (0 : ℂ) →
          (C.submatrix f (⇑(S.orderEmbOfFin rfl) : Fin S.card → Fin N)).det = (0 : ℂ) := by
  intro N C S f hf h0
  have e : (Finset.image f Finset.univ).card = S.card := by
    rw [Finset.card_image_of_injective _ hf]; simp
  unfold UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0
  rw [dite_eq_left e] at h0
  set I := Finset.image f Finset.univ with hI
  have mem : ∀ i, f i ∈ I := fun i => by simp [hI]
  let σf : Fin S.card → Fin S.card := fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩
  have hσ : Function.Injective σf := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab
    simpa [σf] using this
  let σ : Equiv.Perm (Fin S.card) := Equiv.ofBijective σf hσ.bijective_of_finite
  have hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ := by
    funext i
    simp only [Function.comp, σ, Equiv.ofBijective_apply, σf]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp
  have key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) =
      (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id := by
    rw [hfg, Matrix.submatrix_submatrix]
    rfl
  rw [key, Matrix.det_permute, h0, mul_zero]
end

section

theorem UpperTheory.multilinear_vanish_lattice :
    ∀ {ι : Type} [Finite ι] [DecidableEq ι] {M : ι → Type} {N : Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
        [AddCommGroup N] [Module ℂ N] (T : MultilinearMap (RingHom.id ℂ) M N) (L G : ∀ i, Set (M i)),
        (∀ v : ∀ i, M i, (∀ i, v i ∈ L i) → T v = 0) →
        (∀ i, ∀ w ∈ G i, ∃ w0 ∈ L i, ∀ v : ∀ i, M i, T (Function.update v i w0) = 0 → T (Function.update v i w) = 0) →
        ∀ v : ∀ i, M i, (∀ i, v i ∈ Submodule.span ℂ (G i)) → T v = 0 := by
  intro ι _ _ M N _ _ _ _ T L G hL hG
  have key : ∀ s : Finset ι, ∀ v : ∀ i, M i, (∀ i ∈ s, v i ∈ Submodule.span ℂ (G i)) →
      (∀ i, i ∉ s → v i ∈ L i) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h => hL v fun i => h i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro v hs hn
      have hker : Submodule.span ℂ (G a) ≤ LinearMap.ker (T.toLinearMap v a) := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨w0, hw0, h⟩ := hG a w hw
        have h0 : T (Function.update v a w0) = 0 := by
          apply ih
          · intro i hi
            have hia : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne hia]
            exact hs i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases hia : i = a
            · subst hia
              rw [Function.update_self]
              exact hw0
            · rw [Function.update_of_ne hia]
              exact hn i (by simp [hia, hi])
        exact h v h0
      have hv : T (Function.update v a (v a)) = 0 := hker (hs a (Finset.mem_insert_self a s))
      rwa [Function.update_eq_self] at hv
  intro v hv
  haveI := Fintype.ofFinite ι
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)
end
