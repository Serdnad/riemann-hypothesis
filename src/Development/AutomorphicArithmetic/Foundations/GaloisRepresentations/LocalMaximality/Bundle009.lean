module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → Fˣ}

private lemma ratio_mem (i j : Fin (d + 1)) :
    algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := by
  have hm : ((x j : F) / x i) ∈ rA ℂ (xv x) {i} :=
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := rA ℂ (xv x) {i}) (x := ⟨_, hm⟩)

private lemma pow_mul_mem (h : IsFinCover ℂ K (xv x)) (i i' : Fin (d + 1)) (b : K)
    (hb : b ∈ rB ℂ K (xv x) {i}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} := by
  by_cases hne : i = i'
  · subst hne
    refine ⟨0, fun N _ => ?_⟩
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i i) N) hb
  have hb' : b ∈ rB ℂ K (xv x) {i, i'} :=
    (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i} i (by simp)).1 {i, i'} (by simp) hb
  obtain ⟨N0, hN0⟩ :=
    ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i, i'} i' (by simp)).2 b).mp hb'
  rw [Finset.prod_pair hne, div_self (Units.ne_zero (x i')), mul_one] at hN0
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have e : algebraMap F K ((x i : F) / x i') ^ (N0 + k) * b =
      algebraMap F K ((x i : F) / x i') ^ k * (b * algebraMap F K ((x i : F) / x i') ^ N0) := by
    ring
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i' i) k) hN0

private lemma gens (h : IsFinCover ℂ K (xv x)) (i : Fin (d + 1)) :
    ∃ G : Finset K, Algebra.adjoin ℂ (G : Set K) = rB ℂ K (xv x) {i} := by
  haveI := h.smooth i
  exact (Subalgebra.fg_iff_finiteType _).mpr inferInstance

private lemma tensor_id (a a' a'' b : K) (ha' : a' ≠ 0) (ha'' : a'' ≠ 0) (N : ℕ) :
    (((a ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a ^ N))) * (b ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] b) =
      ((((a / a') ^ N * b) ⊗ₜ[ℂ] ((a / a'') ^ N)) - (((a / a') ^ N) ⊗ₜ[ℂ] ((a / a'') ^ N * b))) *
        (((a' ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a'' ^ N))) := by
  have e1 : (a / a') ^ N * a' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha']
  have e2 : (a / a'') ^ N * a'' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha'']
  have e3 : (a / a') ^ N * b * a' ^ N = a ^ N * b := by rw [mul_right_comm, e1]
  have e4 : (a / a'') ^ N * b * a'' ^ N = a ^ N * b := by rw [mul_right_comm, e2]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, sub_mul, mul_sub, mul_one, one_mul, e1, e2, e3, e4]
  done

private lemma coe_XY (i j : Fin (d + 1)) (N : ℕ) :
    (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y j ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      (((algebraMap F K (x i)) ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] ((algebraMap F K (x j)) ^ N)) := by
  simp [sysZ, Units.val_pow_eq_pow_val, Algebra.TensorProduct.tmul_pow]

end

theorem UpperTheory.Gal.productCup_of_system.zFam_of :
    ZFam := by
  classical
  intro F K _ _ _ _ _ _ d x h
  choose G hG using fun i => gens (x := x) h i
  have hGm : ∀ i, ∀ b ∈ G i, b ∈ rB ℂ K (xv x) {i} := fun i b hb =>
    hG i ▸ Algebra.subset_adjoin hb
  have hP : ∀ i b, b ∈ G i → ∀ i', ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} :=
    fun i b hb i' => pow_mul_mem h i i' b (hGm i b hb)
  choose! Nb hNb using hP
  let Nq : Fin (d + 1) × K → ℕ := fun q => Finset.univ.sup (fun i' => Nb q.1 q.2 i')
  let P : Finset (Fin (d + 1) × K) :=
    Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))
  have hPm : ∀ q ∈ P, q.2 ∈ G q.1 := by
    intro q hq
    simp only [P, Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨i, _, b, hb, rfl⟩ := hq
    exact hb
  let e := P.equivFin.symm
  let zz : Fin (d + 1) × K → K ⊗[ℂ] K := fun q =>
    (((sysZ K x 0).X q.1 ^ Nq q * (sysZ K x 0).Y q.1 ^ Nq q : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) *
      (q.2 ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] q.2)
  refine ⟨P.card, fun l => (Nq (e l).1, Nq (e l).1), fun l => zz (e l).1, ⟨?_, ?_, ?_⟩⟩
  · intro i' j' l
    show zz (e l).1 * ↑((sysZ K x 0).X i' ^ Nq (e l).1 * (sysZ K x 0).Y j' ^ Nq (e l).1)⁻¹ ∈ _
    have hb := hPm _ (e l).2
    generalize (e l).1 = q at hb ⊢
    obtain ⟨i, b⟩ := q
    dsimp only [zz] at hb ⊢
    have hN1 : Nb i b i' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ i')
    have hN2 : Nb i b j' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ j')
    have hA := hNb i b hb i' _ hN1
    have hD := hNb i b hb j' _ hN2
    have hB := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) j' i) (Nq (i, b))
    have hC := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) i' i) (Nq (i, b))
    rw [coe_XY, tensor_id (algebraMap F K (x i)) (algebraMap F K (x i')) (algebraMap F K (x j')) b
      (by simp) (by simp) _, ← coe_XY i' j' _, Units.mul_inv_cancel_right]
    simp only [map_div₀] at hA hB hC hD
    exact Subalgebra.sub_mem _ ((AlgHom.mem_range _).mpr ⟨⟨_, hA⟩ ⊗ₜ ⟨_, hB⟩, by simp⟩)
      ((AlgHom.mem_range _).mpr ⟨⟨_, hC⟩ ⊗ₜ ⟨_, hD⟩, by simp⟩)
  · intro l
    simp [zz, Algebra.TensorProduct.lmul'_apply_tmul]
  · intro i
    apply le_antisymm
    · exact Algebra.adjoin_le (fun b hb => hb.1)
    · refine (hG i).symm.le.trans (Algebra.adjoin_mono ?_)
      intro b hb
      have hq : (i, b) ∈ P := by
        simp only [P, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨i, Finset.mem_univ _, b, hb, rfl⟩
      refine ⟨hGm i b hb, e.symm ⟨(i, b), hq⟩, Nq (i, b), ?_, ?_⟩ <;> simp [e, zz]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section Tensor
variable {S S' E E' : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
  [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

private theorem range_mono {A A' : Subalgebra ℂ S} {B B' : Subalgebra ℂ S'} (hA : A ≤ A') (hB : B ≤ B') :
    (Algebra.TensorProduct.map A.val B.val).range ≤ (Algebra.TensorProduct.map A'.val B'.val).range := by
  rintro _ ⟨z, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hA) (Subalgebra.inclusion hB) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add p q hp hq => simp only [map_add (f := _)] at *; rw [hp, hq]

private theorem tmul_mem_range {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {a : S} {b : S'} (ha : a ∈ A) (hb : b ∈ B) :
    a ⊗ₜ[ℂ] b ∈ (Algebra.TensorProduct.map A.val B.val).range :=
  ⟨(⟨a, ha⟩ : A) ⊗ₜ[ℂ] (⟨b, hb⟩ : B), by simp⟩

private theorem stab_tensor (f : S →ₐ[ℂ] Module.End ℂ E) (g : S' →ₐ[ℂ] Module.End ℂ E')
    {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {P : Submodule ℂ E} {Q : Submodule ℂ E'}
    (hP : ∀ a ∈ A, ∀ m ∈ P, f a m ∈ P) (hQ : ∀ b ∈ B, ∀ m ∈ Q, g b m ∈ Q) :
    Stab ((Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map f g))
      (Algebra.TensorProduct.map A.val B.val).range (Submodule.map₂ (TensorProduct.mk ℂ _ _) P Q) := by
  rintro _ ⟨z, rfl⟩ m hm
  induction z using TensorProduct.induction_on generalizing m with
  | zero => simp
  | tmul a b =>
    have hle : Submodule.map₂ (TensorProduct.mk ℂ E E') P Q ≤
        (Submodule.map₂ (TensorProduct.mk ℂ E E') P Q).comap (TensorProduct.map (f a) (g b)) := by
      rw [Submodule.map₂_le]
      intro p hp q hq
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ (hP _ a.2 _ hp) (hQ _ b.2 _ hq)
    have h2 := hle hm
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]
    exact h2
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact add_mem (hp m hm) (hq m hm)

private theorem units_ratio {F : Type} [Field F] (f : F →+* S) (u v : Fˣ) :
    ((Units.map (f : F →* S) u * (Units.map (f : F →* S) v)⁻¹ : Sˣ) : S) = f ((u : F) / v) := by
  simp [div_eq_mul_inv]

end Tensor

section Forms
variable {K : Type} [Field K] [Algebra ℂ K]

private theorem omB_mono' {B B' : Subalgebra ℂ K} (h : B ≤ B') (q : ℕ) : omB ℂ K B q ≤ omB ℂ K B' q := by
  unfold omB
  exact Submodule.span_mono (fun y ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩)

private theorem omB_smul (B : Subalgebra ℂ K) (q : ℕ) {c : K} (hc : c ∈ B) {m : DR ℂ K} (hm : m ∈ omB ℂ K B q) :
    Algebra.lsmul ℂ ℂ (DR ℂ K) c m ∈ omB ℂ K B q := by
  show c • m ∈ omB ℂ K B q
  unfold omB at hm ⊢
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [mul_smul]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

end Forms

section Chart
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem ratio_mem_rA {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private theorem ratio_mem_rB {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    algebraMap F K ((x a : F) / x i) ∈ rB ℂ K (xv x) I := by
  unfold rB
  exact (integralClosure (rA ℂ (xv x) I) K).algebraMap_mem (⟨_, ratio_mem_rA x hi a⟩ : rA ℂ (xv x) I)

private theorem sysZ_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).X b * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysZ_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).Y b * ((sysZ K x a).Y i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).X b * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).Y b * ((sysP K x a).Y i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

end Chart

theorem UpperTheory.Gal.productCup_of_system.goodZ_of :
    GoodZ := by
  intro F K _ _ _ _ _ _ d x hx a
  have hrB : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → I ⊆ J → rB ℂ K (xv x) I ≤ rB ℂ K (xv x) J := by
    intro I J hI hIJ
    obtain ⟨i, hi⟩ := hI
    exact (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) hx I i hi).1 J hIJ
  have hx0 : ∀ i, xv x i ≠ 0 := fun i => (x i).ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (hrB I I' hI hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    show MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J'
    unfold MZ
    exact Submodule.map₂_le_map₂ (omB_mono' (hrB I I' hI hII) _) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => omB_smul _ _ hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysZ_X]
    exact tmul_mem_range (ratio_mem_rB K x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysZ_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (rA_le_of_subset hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    exact Submodule.map₂_le_map₂ (omA_le_of_subset hx0 hI hII) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => mul_mem_omA_of_mem_rA hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysP_X]
    exact tmul_mem_range (ratio_mem_rA x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysP_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro s t hs hst
    exact omB_mono' (hrB s t hs hst) a
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma uni_empty_eq {α β : Type} [LinearOrder α] [LinearOrder β] (L : Finset α) :
    uni L (∅ : Finset β) = L.map (inlE : α ↪o α ⊕ₗ β).toEmbedding := by
  ext z
  simp only [uni, inlE, Finset.disjSum_empty, Finset.map_map, Finset.mem_map]
  simp

private lemma lft_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    lft (uni I J) = I := by
  ext t
  simp [lft, uni]

private lemma rgt_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    rgt (uni I J) = J := by
  ext t
  simp [rgt, uni]

private lemma img_trans_inlE {d : ℕ} {α β : Type} [LinearOrder α] [LinearOrder β] (e : Fin d ↪o α) :
    img (e.trans (inlE : α ↪o α ⊕ₗ β)) = uni (img e) (∅ : Finset β) := by
  rw [uni_empty_eq]
  ext t
  simp [img]

private lemma img_card {d : ℕ} {α : Type} [LinearOrder α] (e : Fin d ↪o α) : (img e).card = d := by
  simp [img]

theorem UpperTheory.Gal.productCup_of_system.zEx_of :
    ZCol → ColZ → CechKoszulSystemCocycleGluing → KoszulBoundaryOfComponentMemIdeal → KSub → RS → ActsLin → SysOk → GoodZ → ThMuLat → ZEx := by
  intro hZCol hColZ hSysL2 hK2 hKSub hRS hActsLin hSysOk hGoodZ hThMu
  intro F K _ _ _ _ _ _ d x hcov τ htop a ha κ _ _ n z hz
  have hGood : (sysZ K x a).Good := (hGoodZ F K d x hcov a).1
  have hAdm : (sysZ K x a).admitted (app n11 n) (app (sysZ K x a).mu z) := by
    intro i j l
    obtain ⟨l, rfl⟩ : ∃ l', toLex l' = l := ⟨ofLex l, rfl⟩
    cases l with
    | inl m => exact (hThMu d _ _ (sysZ K x a) hGood).1 i j m
    | inr k => exact hz.adm i j k
  have gen : ∀ (T : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K)) (i j : Fin (d + 1)),
      (fun l => T.r (app n11 n) (app T.mu z) i j (((dj j).trans (inlE (κ := κ))) l)) =
        fun l => T.r n11 T.mu i j (dj j l) := fun T i j => rfl
  have hOk := hSysOk d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm
  have key : ∀ (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I → j ∈ J →
      ∀ D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).Z d,
      Acts (F := F) K τ a (D (uni (img (dj j)) ∅)) 0 →
      D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).B d := by
    intro I J i j hi hj D hD hA
    have hI : I.Nonempty := ⟨i, hi⟩
    have hJ : J.Nonempty := ⟨j, hj⟩
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol] at hD ⊢
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) d D
    rw [hR.2.2.1]
    rw [hR.2.1] at hD
    have hCZ := hColZ F K d x hcov τ htop a ha I J i hi j hj
    refine hK2 _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) _ d ((dj j).trans inlE)
      (hGood.stab I J hI hJ) hr (by rw [gen]; exact hCZ.1) _ hD ?_
    rw [img_trans_inlE, gen]
    refine hCZ.2 _ ?_ ?_
    · have hC := (Submodule.mem_inf.1 hD).1
      simp only [kos, acx] at hC
      have h1 := (Submodule.mem_pi.1 hC) (uni (img (dj j)) ∅) (Set.mem_univ _)
      have hcard : (uni (img (dj j)) (∅ : Finset κ)).card = d := by
        rw [← img_trans_inlE, img_card]
      rw [hcard, if_pos rfl] at h1
      exact h1
    · have h2 := fun s => (hActsLin F K d x hcov τ htop a).2.1 _ 0 s hA
      simp only [mul_zero] at h2
      exact h2 _
  have hKE : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      KE ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J) d := by
    intro I J hI hJ
    obtain ⟨i, hi⟩ := hI
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol]
    have hks := (hKSub _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (hGood.stab I J ⟨i, hi⟩ ⟨j, hj⟩) hr).1 d
      ((dj j).trans inlE) (by rw [gen]; exact (hColZ F K d x hcov τ htop a ha I J i hi j hj).1)
    intro m hm c hc
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) m c
    rw [hR.2.2.1]
    exact hks m hm (hR.2.1.1 hc)
  have hc0 := fun i j => hZCol F K d x hcov τ htop a ha κ n z hz i j
  choose c0 hc0Z hc0A using hc0
  have hAct := (hActsLin F K d x hcov τ htop a).1
  obtain ⟨c, hcZ, hcol⟩ := hSysL2 d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm hKE c0 hc0Z
    (fun i i' j => by
      apply key {i, i'} {j} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i j))
          (hOk.2.2 {i'} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i' j))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i' j _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
    (fun i j j' => by
      apply key {i} {j, j'} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i} {j} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j))
          (hOk.2.2 {i} {i} {j'} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j'))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i j' _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
  refine ⟨c, hcZ, ?_⟩
  intro i j L hLc
  have e : resK inlE c (uni (uni {i} {j}) L) = c0 i j (uni L ∅) := by
    rw [← hcol i j]
    simp only [resK, col, lft_uni', rgt_uni', uni_empty_eq]
  rw [e]
  exact hc0A i j L hLc
end
