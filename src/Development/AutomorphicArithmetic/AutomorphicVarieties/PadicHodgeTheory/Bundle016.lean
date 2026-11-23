module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def Reach {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) (U : Submodule A V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = U ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

private theorem reach_bot {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Reach ρ S ⊥ :=
  ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

private theorem reach_step {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {κ : G →* Aˣ} (hκ : κ ∈ S) {x : V} (hx : ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) :
    Reach ρ S (U ⊔ Submodule.span A {x}) := by
  obtain ⟨n, F, h0, hn, hs⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span A {x}, by simp [h0], by simp, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have h1 : i ≤ n := hi.le
    have h2 : i + 1 ≤ n := hi
    simp only [h1, h2, if_true]
    exact hs i hi
  · have h2 : ¬ (i + 1 ≤ i) := by omega
    simp only [h2, le_refl, if_true, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem reach_fin {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {T : Set V} (hT : T.Finite) :
    (∀ x ∈ T, ∃ κ ∈ S, ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) → Reach ρ S (U ⊔ Submodule.span A T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro _
    simpa using h
  | @insert a s ha hs ih =>
    intro hall
    have hr := ih (fun y hy => hall y (Set.mem_insert_of_mem a hy))
    obtain ⟨κ, hκ, hk⟩ := hall a (Set.mem_insert a s)
    have hr2 := reach_step hr hκ (x := a) (fun g => Submodule.mem_sup_left (hk g))
    have e : U ⊔ Submodule.span A (insert a s) = U ⊔ Submodule.span A s ⊔ Submodule.span A {a} := by
      rw [Submodule.span_insert]
      ac_rfl
    rw [e]
    exact hr2

theorem UpperTheory.filtBy_restrictScalars_of_residual_characters :
    ∀ {G E B V : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] [AddCommGroup V] [Module B V] [Module E V] [IsScalarTower E B V] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ (ρ : Representation B G V) (S : Set (G →* Eˣ)) {ι : Type} [Finite ι] (x : ι → V) (κ : ι → G →* Eˣ), Submodule.span B (Set.range x) = ⊤ → (∀ j, κ j ∈ S) → (∀ g j, ρ g (x j) - ((κ j g : Eˣ) : E) • x j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V)) → FiltBy (resCoef E ρ) S := by
  intro G E B V _ _ _ _ _ _ _ _ _ π hπ ρ S ι _ x κ hx hκ hstep
  have hnil : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.mpr (hπ a ha)
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule E V, ∀ k,
      M k = ((RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V)).restrictScalars E :=
    ⟨_, fun _ => rfl⟩
  have hMm : ∀ k v, v ∈ M k ↔ v ∈ (RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V) := by
    intro k v
    rw [hM, Submodule.restrictScalars_mem]
  have down : ∀ p, Reach (resCoef E ρ) S (M (p + 1)) → Reach (resCoef E ρ) S (M p) := by
    intro p h
    have hfg : (((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E).FG := IsNoetherian.noetherian _
    obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hfg
    have hsub : ∀ a ∈ s, a ∈ (RingHom.ker (π : B →+* E)) ^ p := fun a ha => by
      have : a ∈ ((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E := hs ▸ Submodule.subset_span ha
      exact this
    have hTf : (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)).Finite :=
      hsf.image2 _ Set.finite_univ
    have hr := reach_fin (ρ := resCoef E ρ) (S := S) h hTf (by
      rintro y ⟨a, ha, j, -, rfl⟩
      refine ⟨κ j, hκ j, fun g => ?_⟩
      rw [hMm]
      show ρ g (a • x j) - ((κ j g : Eˣ) : E) • (a • x j) ∈
        ((RingHom.ker (π : B →+* E)) ^ (p + 1) • (⊤ : Submodule B V))
      rw [map_smul, smul_comm ((κ j g : Eˣ) : E) a, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hsub a ha) (hstep g j))
    have claim : ∀ n ∈ Submodule.span B (Set.range x), ∀ a ∈ (RingHom.ker (π : B →+* E)) ^ p,
        a • n ∈ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro a ha
        have ha' : a ∈ Submodule.span E s := by
          rw [hs]
          exact ha
        clear ha
        induction ha' using Submodule.span_induction with
        | mem b hb => exact Submodule.subset_span ⟨b, hb, j, trivial, rfl⟩
        | zero => simp
        | add b c _ _ hb hc =>
          rw [add_smul]
          exact add_mem hb hc
        | smul c b _ hb =>
          rw [smul_assoc]
          exact Submodule.smul_mem _ c hb
      | zero => intro a _; simp
      | add y z _ _ hy hz =>
        intro a ha
        rw [smul_add]
        exact add_mem (hy a ha) (hz a ha)
      | smul b y _ hy =>
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (Ideal.mul_mem_right b _ ha)
    have e : M p = M (p + 1) ⊔ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      apply le_antisymm
      · intro v hv
        apply Submodule.mem_sup_right
        rw [hMm] at hv
        refine Submodule.smul_induction_on hv ?_ ?_
        · intro a ha n _
          exact claim n (by rw [hx]; trivial) a ha
        · intro y z hy hz
          exact add_mem hy hz
      · refine sup_le ?_ ?_
        · intro v hv
          rw [hMm] at hv ⊢
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ p)) hv
        · rw [Submodule.span_le]
          rintro y ⟨a, ha, j, -, rfl⟩
          show a • x j ∈ M p
          rw [hMm]
          exact Submodule.smul_mem_smul (hsub a ha) trivial
    rw [e]
    exact hr
  have base : M N = ⊥ := by
    rw [hM, hN, Submodule.zero_eq_bot, Submodule.bot_smul, Submodule.restrictScalars_bot]
  have all : ∀ k, Reach (resCoef E ρ) S (M (N - k)) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, base]
      exact reach_bot _ _
    | succ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · have e : N - k = (N - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact down _ ih
      · have e : N - (k + 1) = N - k := by omega
        rw [e]
        exact ih
  have top : M 0 = ⊤ := by
    rw [hM, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.restrictScalars_top]
  have fin := all N
  rw [Nat.sub_self, top] at fin
  exact fin
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
variable {Q : Type} [Field Q] {G V V' B : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
  [AddCommGroup B] [Module Q B]

private def fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (r g) (a g) - LinearMap.id)

private theorem mem_fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B)
    (x : V ⊗[Q] B) : x ∈ fixT r a ↔ ∀ g, AlgebraTensorModule.map (r g) (a g) x = x := by
  simp [fixT, Submodule.mem_iInf, sub_eq_zero]

private theorem prodLeft_act (r : V →ₗ[Q] V) (r' : V' →ₗ[Q] V') (a : B →ₗ[Q] B) (x : (V × V') ⊗[Q] B) :
    TensorProduct.prodLeft Q Q V V' B (AlgebraTensorModule.map (r.prodMap r') a x) =
      (AlgebraTensorModule.map r a (TensorProduct.prodLeft Q Q V V' B x).1,
        AlgebraTensorModule.map r' a (TensorProduct.prodLeft Q Q V V' B x).2) := by
  induction x with
  | tmul v b => obtain ⟨v, v'⟩ := v; simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

private theorem fixT_map (r : G → V →ₗ[Q] V) (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) :
    (fixT (fun g => (r g).prodMap (r' g)) a).map (TensorProduct.prodLeft Q Q V V' B).toLinearMap =
      (fixT r a).prod (fixT r' a) := by
  ext y
  obtain ⟨x, rfl⟩ := (TensorProduct.prodLeft Q Q V V' B).surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_prod, mem_fixT, mem_fixT, mem_fixT,
    ← forall_and]
  refine forall_congr' fun g => ?_
  rw [← (TensorProduct.prodLeft Q Q V V' B).injective.eq_iff, prodLeft_act, Prod.ext_iff]

private def prodEquiv' {M N : Type} [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module Q N]
    (p : Submodule Q M) (q : Submodule Q N) : ↥(p.prod q) ≃ₗ[Q] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixT_finite [FiniteDimensional Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) : Module.Finite Q ↥(fixT r a) := by
  rcases Nat.eq_zero_or_pos (finrank Q V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos (Nat.pos_of_ne_zero hn) h0)

private theorem fixT_prod [FiniteDimensional Q V] [FiniteDimensional Q V'] (r : G → V →ₗ[Q] V)
    (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) (h' : finrank Q ↥(fixT r' a) = n * finrank Q V') :
    finrank Q ↥(fixT (fun g => (r g).prodMap (r' g)) a) = n * finrank Q (V × V') := by
  haveI := fixT_finite r a hn h
  haveI := fixT_finite r' a hn h'
  rw [← LinearEquiv.finrank_map_eq (TensorProduct.prodLeft Q Q V V' B), fixT_map,
    (prodEquiv' _ _).finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end

theorem UpperTheory.V.Loc.isCrys_isDR_prod :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → (IsCr φ ρ → IsCr φ ρ' → IsCr φ (ρ.prod ρ')) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ (ρ.prod ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _
  have ho : IsOpen (φ.range : Set (GQ l)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ ho
  have h1 : φ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (φ.range ⊔ Iq l).index ≠ 0 := fun h =>
    h1 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_left))
  exact ⟨fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQ (φ g)).toLinearMap) h2 h h',
    fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQdR (φ g)).toLinearMap) h1 h h'⟩
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem kur_map {l : ℕ} [Fact l.Prime] (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    g x ∈ MaximalUnramifiedExtension l := by
  have h1 : g x ∈ (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    (Set.mem_image_of_mem _ hx :)
  rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map] at h1
  refine (IntermediateField.adjoin_le_iff.mpr ?_) h1
  rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩

private theorem iq_normal (l : ℕ) [Fact l.Prime] : (Iq l).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (kur_map g⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

section Gen

variable {Q Γ G A V B : Type} [Field Q] [Group Γ] [Group G] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V]
  [Module Q V] [IsScalarTower Q A V] [CommRing B] [Algebra Q B] (α : Γ →* (B ≃ₐ[Q] B))

private noncomputable def cj (c : Γ) : V ⊗[Q] B ≃ₗ[A] V ⊗[Q] B :=
  AlgebraTensorModule.congr (LinearEquiv.refl A V) (α c).toLinearEquiv

private theorem cj_act (c g : Γ) (f : V →ₗ[A] V) (x : V ⊗[Q] B) :
    AlgebraTensorModule.map f (α (c * g * c⁻¹)).toLinearMap (cj (A := A) α c x) =
      cj (A := A) α c (AlgebraTensorModule.map f (α g).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have h : α (c * g * c⁻¹) (α c b) = α c (α g b) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
    simp only [cj, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem cj_one (c : Γ) (v : V) : cj (A := A) α c (v ⊗ₜ[Q] (1 : B)) = v ⊗ₜ[Q] (1 : B) := by
  simp [cj]

private theorem finrank_inv (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) :
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) =
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (φ g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) := by
  symm
  refine ((cj (A := A) α c).ofSubmodules _ _ ?_).finrank_eq
  ext x
  obtain ⟨y, rfl⟩ := (cj (A := A) (V := V) α c).surjective x
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, (cj α c).injective.eq_iff]

private theorem cob_iff (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) (z : G → V) :
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap x - x) ↔
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g) (α (φ g)).toLinearMap x - x) := by
  rw [(cj (A := A) (V := V) α c).surjective.exists]
  refine exists_congr fun y => forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, ← map_sub, ← cj_one (A := A) α c, (cj α c).injective.eq_iff, cj_one]

private theorem index_conj (c : Γ) (φ : G →* Γ) (N : Subgroup Γ) [hN : N.Normal] :
    (((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N).index = (φ.range ⊔ N).index := by
  have h1 : N.map (MulAut.conj c).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy c
    · intro hx
      refine ⟨c⁻¹ * x * c⁻¹⁻¹, hN.conj_mem x hx c⁻¹, ?_⟩
      simp [mul_assoc]
  have h2 : ((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N = (φ.range ⊔ N).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_sup, h1, MonoidHom.range_comp]
  rw [h2]
  exact Subgroup.index_map_of_bijective (MulAut.conj c).bijective _

end Gen

theorem UpperTheory.V.Loc.admissible_conjugate :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (c : GQ l), (IsCr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsCr φ ρ) ∧ (IsDr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsDr φ ρ) ∧ UpperTheory.V.Loc.finiteCocycles ((MulAut.conj c).toMonoidHom.comp φ) ρ = UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro l _ G _ _ _ φ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ c
  refine ⟨?_, ?_, ?_⟩
  · haveI := iq_normal l
    have h1 : finrank ℚ_[l] ↥(Dcr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQ c φ (resCoef ℚ_[l] ρ)
    rw [IsCr, IsCr, h1, index_conj]
  · have h1 : finrank ℚ_[l] ↥(Ddr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQdR c φ (resCoef ℚ_[l] ρ)
    have h2 := index_conj c φ ⊥
    rw [sup_bot_eq, sup_bot_eq] at h2
    rw [IsDr, IsDr, h1, h2]
  · ext z
    exact and_congr_right fun _ => cob_iff (PP l).actQ c φ ρ z
end

section

noncomputable section

namespace UpperTheory.V.Loc

open ReciprocityTheory.Gal

def coSub {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : Submodule A V :=
  Submodule.span A {y | ∃ g x, y = ρ g x - ((χ g : Aˣ) : A) • x}

def lSub (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) : Submodule ℤ_[l] X :=
  LinearMap.range (((l : ℤ_[l]) ^ m) • (LinearMap.id : X →ₗ[ℤ_[l]] X))

theorem mem_lSub {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X] {m : ℕ} {x : X} :
    x ∈ lSub l X m ↔ ∃ y, (l : ℤ_[l]) ^ m • y = x := by
  simp only [lSub, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]

def redRep {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) : Representation ℤ_[l] G (X ⧸ lSub l X m) :=
  ρ.quotient (lSub l X m) fun g _ hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨ρ g y, (map_smul _ _ _).symm⟩

theorem redRep_mk {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) (g : G) (x : X) :
    redRep ρ m g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

theorem mem_lSub_pi {l : ℕ} [Fact l.Prime] {n m : ℕ} {x : Fin n → ℤ_[l]} :
    x ∈ lSub l (Fin n → ℤ_[l]) m ↔ ∀ i, PadicInt.toZModPow m (x i) = 0 := by
  rw [mem_lSub]
  have key : ∀ a : ℤ_[l], PadicInt.toZModPow m a = 0 ↔ (l : ℤ_[l]) ^ m ∣ a := by
    intro a
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  simp only [key]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simp [Pi.smul_apply, smul_eq_mul, hy i]⟩

theorem isOpen_lSub_pi (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    IsOpen ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) := by
  have hset : ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) =
      ⋂ i, (fun x : Fin n → ℤ_[l] => x i) ⁻¹' Metric.closedBall (0 : ℤ_[l]) ((l : ℝ) ^ (-(m : ℤ))) := by
    ext x
    simp only [SetLike.mem_coe, mem_lSub_pi, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    refine forall_congr' fun i => ?_
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))).preimage (continuous_apply i)

instance discrete_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    DiscreteTopology ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  QuotientAddGroup.discreteTopology (N := (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup) (isOpen_lSub_pi l n m)

theorem card_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let f : (Fin n → ℤ_[l]) →+ (Fin n → ZMod (l ^ m)) :=
    AddMonoidHom.compLeft (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toAddMonoidHom (Fin n)
  have hf : Function.Surjective f := by
    intro z
    choose k hk using fun i => ZMod.intCast_surjective (z i)
    exact ⟨fun i => (k i : ℤ_[l]), funext fun i => by simp [f, hk i]⟩
  have hk : f.ker = (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup := by
    ext x
    simp [f, mem_lSub_pi, funext_iff]
  have e : ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) ≃ (Fin n → ZMod (l ^ m)) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toEquiv
  rw [Nat.card_congr e]
  simp [Nat.card_fun, pow_mul]

instance finite_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  Nat.finite_of_card_ne_zero (by rw [card_quot_lSub]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

theorem contAction_redRep {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}
    {ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])} (h : ContAction ρ) (m : ℕ) : ContAction (redRep ρ m) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  rw [← (IsOpenQuotientMap.id.prodMap (lSub l (Fin n → ℤ_[l]) m).isOpenQuotientMap_mkQ).continuous_comp_iff]
  refine ((lSub l (Fin n → ℤ_[l]) m).continuous_mkQ.comp h).congr ?_
  intro p
  exact (redRep_mk ρ m p.1 p.2).symm

def FinLevel (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation ℤ_[l] G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (M ⧸ coSub χ ρ)

def FinLevelMod (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) :
    Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (H0dual
        ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ)

def Grows (l : ℕ) (a : ℕ → ℕ) (s : ℕ) : Prop := ∃ C : ℕ, ∀ m, 0 < m → l ^ (m * s) ≤ a m ∧ a m ≤ l ^ (m * s + C)

end UpperTheory.V.Loc
end
end
