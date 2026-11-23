module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)

private theorem ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private theorem omG_ne (i : Fin (d + 1)) : omG x i ≠ 0 := by
  unfold omG
  exact Finset.prod_ne_zero_iff.mpr (fun l _ => div_ne_zero (Units.ne_zero _) (Units.ne_zero _))

private theorem prod_eq (i i' : Fin (d + 1)) :
    (∏ j, (x i' : F) / x j) * omG x i = ((x i' : F) / x i) ^ (d + 1) := by
  unfold omG
  rw [← Finset.prod_mul_distrib]
  have h : ∀ j, (x i' : F) / x j * (x j / x i) = x i' / x i := fun j => by
    have h1 := (x j).ne_zero
    have h2 := (x i).ne_zero
    field_simp
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem mem_omA_iff' {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (y : F) :
    y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I := by
  have hG := omG_ne x i
  have key : ∀ i', (∏ j, (x i' : F) / x j) = ((x i' : F) / x i) ^ (d + 1) / omG x i := fun i' => by
    rw [eq_div_iff hG, prod_eq]
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule, xv]
  constructor
  · intro hy
    have h1 := hy i hi
    rw [key, div_self (Units.ne_zero (x i)), one_pow] at h1
    rwa [one_div, inv_mul_eq_div] at h1
  · intro hy i' hi'
    rw [key, div_mul_eq_mul_div, mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem x hi i') _) hy

private theorem loc_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) (y : F)
    (hy : y ∈ rA ℂ (xv x) (insert j I)) : ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ rA ℂ (xv x) I := by
  have hs : (x j : F) / x i ∈ rA ℂ (xv x) I := ratio_mem x hi j
  unfold rA at hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, rfl⟩ := hz
    rcases Finset.mem_insert.1 ha with h | h
    · rw [h]
      refine ⟨1, ?_⟩
      have e : ((x j : F) / x i) ^ 1 * (xv x b / xv x j) = x b / x i := by
        have h1 := (x j).ne_zero
        have h2 := (x i).ne_zero
        simp only [xv, pow_one]
        field_simp
      rw [e]
      exact ratio_mem x hi b
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact ratio_mem x h b
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y + z) = ((x j : F) / x i) ^ N2 * (((x j : F) / x i) ^ N1 * y) + ((x j : F) / x i) ^ N1 * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h1) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h2)
  | mul y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y * z) = (((x j : F) / x i) ^ N1 * y) * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.mul_mem _ h1 h2

end

theorem UpperTheory.Gal.productCup_of_system.latA_of :
    LatA := by
  intro F _ _ d x _ I i hi
  refine ⟨?_, mem_omA_iff' x hi, ?_⟩
  · unfold UpperTheory.Gal.productCup_of_system.Lat
    refine ⟨?_, 1, fun _ => omG x i, fun _ => LinearMap.mulLeft F (omG x i)⁻¹, ?_, ?_, ?_⟩
    · intro a ha m hm
      rw [smul_eq_mul, mem_omA_iff' x hi, mul_div_assoc]
      exact Subalgebra.mul_mem _ ha ((mem_omA_iff' x hi m).1 hm)
    · intro _
      rw [mem_omA_iff' x hi, div_self (omG_ne x i)]
      exact Subalgebra.one_mem _
    · intro _ m hm
      rw [LinearMap.mulLeft_apply, inv_mul_eq_div]
      exact (mem_omA_iff' x hi m).1 hm
    · intro m _
      rw [Fin.sum_univ_one, LinearMap.mulLeft_apply, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (omG_ne x i), one_mul]
  · intro j y hy
    obtain ⟨N, hN⟩ := loc_mem x hi j _ ((mem_omA_iff' x (Finset.mem_insert_of_mem hi) y).1 hy)
    exact ⟨N, (mem_omA_iff' x hi _).2 (by rwa [mul_div_assoc])⟩
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma actZ_tmul (a b : K) (w' w'' : DR ℂ K) :
    actZ K (a ⊗ₜ b) (w' ⊗ₜ w'') = (a • w') ⊗ₜ[ℂ] (b • w'') := by
  simp [actZ]
  rfl

private lemma key1 (τ : DR ℂ K →ₗ[K] K) (a b : K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (a ⊗ₜ b) m) w) = b • mulP F K (muP F K τ m (a • w)) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [actZ_tmul, muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, smul_mul_assoc, mul_smul_comm]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy, smul_add]

private lemma key2 (τ : DR ℂ K →ₗ[K] K) (f : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ m (algebraMap F K f • w)) = algebraMap F K f • mulP F K (muP F K τ m w) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, mul_smul_comm, map_smul, smul_eq_mul, ← Algebra.smul_def,
      map_smul, smul_eq_mul, map_mul, mul_smul]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hp, hq]

private lemma key3 (τ : DR ℂ K →ₗ[K] K) (f g : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (algebraMap F K f ⊗ₜ algebraMap F K g) m) w) =
      algebraMap F K (f * g) • mulP F K (muP F K τ m w) := by
  rw [key1, key2, ← mul_smul, ← map_mul, mul_comm g f]

private lemma sysP_act_tmul {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (f f' : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (f' ⊗ₜ w) = (f * f') ⊗ₜ[ℂ] (k • w) := by
  simp [sysP]
  rfl

private lemma r_eq {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i j : Fin (d + 1)) (l : Mi d) :
    (sysZ K x a).r n11 (sysZ K x a).mu i j l =
      algebraMap F K (x (ofLex l).1 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).2 / x j : Fˣ) -
      algebraMap F K (x (ofLex l).2 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).1 / x j : Fˣ) := by
  simp [Sys.r, Sys.mu, Sys.u, n11, sysZ, sub_mul, div_eq_mul_inv]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.actsLin_of :
    ActsLin := by
  intro F K _ _ _ _ _ _ d x _ τ _ a
  have hadd : ∀ (m m' : DR ℂ K ⊗[ℂ] DR ℂ K) (c c' : K),
      Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
        Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c') := by
    intro m m' c c' hm hm'
    unfold Acts at hm hm' ⊢
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), hm w hw, hm' w hw, add_smul]
    · rw [map_sub, LinearMap.sub_apply, map_sub, hm w hw, hm' w hw, sub_smul]
  have hr : ∀ (i j : Fin (d + 1)) (l : Mi d) (m : DR ℂ K ⊗[ℂ] DR ℂ K),
      Acts (F := F) K τ a (actZ K ((sysZ K x a).r n11 (sysZ K x a).mu i j l) m) 0 := by
    intro i j l m
    unfold Acts
    intro w _
    rw [r_eq, map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub, key3, key3,
      ← Units.val_mul, ← Units.val_mul, div_mul_div_comm, div_mul_div_comm,
      mul_comm (x (ofLex l).1) (x (ofLex l).2), sub_self, zero_smul]
  have hsm : ∀ (i j : Fin (d + 1)) (M : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)),
      ∀ m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)),
        Acts (F := F) K τ a m 0 := by
    intro i j M m hm
    let N : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
      { carrier := {m | Acts (F := F) K τ a m 0}
        add_mem' := fun {m m'} hm hm' => by simpa using (hadd m m' 0 0 hm hm').1
        zero_mem' := by
          simp only [Set.mem_setOf_eq, Acts]
          intro w _
          simp
        smul_mem' := fun c m hm => by
          simp only [Set.mem_setOf_eq, Acts] at hm ⊢
          intro w hw
          rw [map_smul, LinearMap.smul_apply, map_smul, hm w hw]
          simp }
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤ N := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨u, _, rfl⟩
      obtain ⟨l, rfl⟩ := hs
      exact hr i j l u
    exact hle hm
  refine ⟨hadd, ?_, hsm, ?_, ?_, ?_⟩
  · intro m c s hm
    induction s using TensorProduct.induction_on with
    | zero =>
      unfold Acts
      intro w _
      simp
    | tmul p q =>
      unfold Acts at hm ⊢
      intro w hw
      rw [key1, hm _ (Submodule.smul_mem _ p hw)]
      simp only [Algebra.TensorProduct.lmul'_apply_tmul, smul_smul]
      congr 1
      ring
    | add s s' hs hs' =>
      simpa only [map_add (f := _), LinearMap.add_apply, add_mul] using (hadd _ _ _ _ hs hs').1
  · intro u M m i j hm
    apply hsm i j (M.map (actZ K u))
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤
        (sm (actZ K) (M.map (actZ K u))
          (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j))).comap (actZ K u) := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem hs ⟨actZ K u v, ⟨v, hv, rfl⟩, ?_⟩)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    exact hle hm
  · intro s m
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul f' w =>
        rw [sysP_act_tmul, mulP_tmul, mulP_tmul]
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        rw [← algebraMap_smul K f' w, smul_smul]
        congr 1
        ring
      | add y z hy hz => simp only [map_add (f := _), smul_add, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, add_smul, hy, hz]
  · intro s m w
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul w' w'' =>
        rw [Algebra.TensorProduct.map_tmul, actZ_tmul, muP_tmul, muP_tmul, sysP_act_tmul]
        simp only [IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq, smul_mul_assoc, map_smul,
          smul_eq_mul]
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F V V' : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module F V] [Module ℂ V]
  [IsScalarTower ℂ F V] [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

private lemma actF_tmul (a b : F) (v : V) (v' : V') :
    actF F V V' (a ⊗ₜ b) (v ⊗ₜ v') = (a • v) ⊗ₜ (b • v') := by
  simp [actF, Module.endTensorEndAlgHom_apply]

private noncomputable def Ph (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] F ⊗[ℂ] F :=
  TensorProduct.map (ψ.restrictScalars ℂ) (ψ'.restrictScalars ℂ)

private lemma Ph_tmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (a : V) (b : V') :
    Ph ψ ψ' (a ⊗ₜ b) = ψ a ⊗ₜ ψ' b := rfl

private lemma Ph_act (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (s : F ⊗[ℂ] F) (t : V ⊗[ℂ] V') :
    Ph ψ ψ' (actF F V V' s t) = s * Ph ψ ψ' t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, add_mul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add c e hc he => simp only [map_add (f := _), mul_add, hc, he]
    | tmul c e => simp [actF_tmul, Ph_tmul]

private lemma Ph_lmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (t : V ⊗[ℂ] V') :
    Algebra.TensorProduct.lmul' ℂ (Ph ψ ψ' t) = ψ' (ctrF V' ψ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add c e hc he => simp only [map_add (f := _), hc, he]
  | tmul c e => simp [Ph_tmul, ctrF]

variable {A A' : Subalgebra ℂ F} {M : Submodule ℂ V} {M' : Submodule ℂ V'}

private lemma Ph_mem {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    Ph ψ ψ' t ∈ (Algebra.TensorProduct.map A.val A'.val).range := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ V V') M M' ≤
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range).comap (Ph ψ ψ') := by
    refine Submodule.map₂_le.2 fun m hm m' hm' => ?_
    exact ⟨(⟨ψ m, h m hm⟩ : A) ⊗ₜ (⟨ψ' m', h' m' hm'⟩ : A'), by simp [Ph_tmul]⟩
  exact key ht

private lemma act_mem (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {s : F ⊗[ℂ] F}
    (hs : s ∈ (Algebra.TensorProduct.map A.val A'.val).range) :
    actF F V V' s (v ⊗ₜ v') ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' := by
  obtain ⟨r, rfl⟩ := hs
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, actF_tmul]
    exact Submodule.apply_mem_map₂ _ (hA _ a.2 _ hv) (hA' _ a'.2 _ hv')
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact add_mem hx hy

private lemma decomp {n n' : ℕ} {v : Fin n → V} {φ : Fin n → V →ₗ[F] F} {v' : Fin n' → V'}
    {φ' : Fin n' → V' →ₗ[F] F} (h : ∀ m ∈ M, m = ∑ k, φ k m • v k) (h' : ∀ m ∈ M', m = ∑ k, φ' k m • v' k)
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    t = ∑ k, ∑ l, actF F V V' (Ph (φ k) (φ' l) t) (v k ⊗ₜ v' l) := by
  rw [Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    simp only [TensorProduct.mk_apply, Ph_tmul, actF_tmul]
    conv_lhs => rw [h a ha, h' b hb]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  | zero => simp
  | add a b _ _ ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]

private lemma Ph_sm {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {T : Set (F ⊗[ℂ] F)} {t : V ⊗[ℂ] V'}
    (ht : t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T) :
    Ph ψ ψ' t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T := by
  have hle : sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T ≤
      (sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
        (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T).comap (Ph ψ ψ') := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap, Ph_act]
    exact Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨_, Ph_mem h h' hu, by simp⟩)
  exact hle ht

private lemma act_sm (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {T : Set (F ⊗[ℂ] F)} {s : F ⊗[ℂ] F}
    (hs : s ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T) :
    actF F V V' s (v ⊗ₜ v') ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
  let L : (F ⊗[ℂ] F) →ₗ[ℂ] V ⊗[ℂ] V' :=
    (LinearMap.applyₗ (v ⊗ₜ v')) ∘ₗ (actF F V V').toLinearMap
  have hle : sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T ≤
      (sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T).comap L := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr
      ⟨actF F V V' u (v ⊗ₜ v'), act_mem hA hA' hv hv' hu, ?_⟩)
    simp [L, Module.End.mul_apply]
  exact hle hs

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.regLat_of :
    Reg0 → Ker0 → RegLat := by
  intro h0 hK F _ _ d x hx V V' _ _ _ _ _ _ _ _ I J M M' hL hL' j hjI hjJ
  obtain ⟨hA, n, v, φ, hv, hφ, hdec⟩ := hL
  obtain ⟨hA', n', v', φ', hv', hφ', hdec'⟩ := hL'
  have back : ∀ (T : Set (F ⊗[ℂ] F)) (t : V ⊗[ℂ] V'), t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' →
      (∀ k l, Ph (φ k) (φ' l) t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) T) →
      t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
    intro T t ht h
    rw [decomp hdec hdec' ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      act_sm hA hA' (hv k) (hv' l) (h k l)
  refine ⟨?_, ?_⟩
  · intro k m hm hk
    refine back _ m hm fun a b => ?_
    refine h0 F d x hx I J j hjI hjJ k _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    have := Ph_sm (ψ := φ a) (ψ' := φ' b) (fun m hm => hφ a m hm) (fun m hm => hφ' b m hm) hk
    rw [Ph_act] at this
    exact this
  · intro m hm hψ
    refine back _ m hm fun a b => ?_
    refine hK F d x hx I J j hjI hjJ _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    rw [Ph_lmul, hψ, map_zero]
end
