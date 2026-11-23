module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.LocAgree

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  apply GlobalTheory.InertParity.LengthSign.exists_int_mul <;> assumption

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((m : D.host.E) • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  show δ * embT D τ ((m : D.host.E) * z i j) = m • (δ * embT D τ (z i j))
  rw [map_mul, map_natCast, nsmul_eq_mul]
  ring

theorem matrix_move {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {N N' : ℕ} (g₁ g₂ : GL (Fin N) A)
    (g₁' g₂' : GL (Fin N') A) (s s' : ℕ) (z : Matrix (Fin N') (Fin N) R) :
    ((g₂'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * (((s * s' : ℕ) : R) • z).map f *
      (g₂ : Matrix (Fin N) (Fin N) A) =
      ((s' : A) • ((g₂'⁻¹ * g₁' : GL (Fin N') A) : Matrix (Fin N') (Fin N') A)) *
      (((g₁'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * z.map f * (g₁ : Matrix (Fin N) (Fin N) A)) *
      ((s : A) • ((g₁⁻¹ * g₂ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
  have e1 : (((s * s' : ℕ) : R) • z).map f = ((s : A) * (s' : A)) • z.map f := by
    ext i j
    simp
  rw [e1]
  simp only [Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g₁ : Matrix (Fin N) (Fin N) A), Units.mul_inv, Matrix.one_mul,
    ← Matrix.mul_assoc (g₁' : Matrix (Fin N') (Fin N') A), Units.mul_inv, Matrix.one_mul]

theorem smul_mem_La (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : cc ≠ ⊥) {N N' : ℕ}
    (g₁ g₂ : GA D N) (g₁' g₂' : GA D N')
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h₁ : Moves D (g₁ : GL (Fin N) (AE D)) L₁) (h₁' : Moves D (g₁' : GL (Fin N') (AE D)) L₁')
    (h₂ : Moves D (g₂ : GL (Fin N) (AE D)) L₂) (h₂' : Moves D (g₂' : GL (Fin N') (AE D)) L₂')
    (s s' : ℕ)
    (hs : ∀ i j, (s : AE D) * (((g₁ : GL (Fin N) (AE D))⁻¹ * (g₂ : GL (Fin N) (AE D)) : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (hs' : ∀ i j, (s' : AE D) * (((g₂' : GL (Fin N') (AE D))⁻¹ * (g₁' : GL (Fin N') (AE D)) : GL (Fin N') (AE D)) :
      Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D)
    (x : VC D N N') (hx : x ∈ La D (tor0 D cc δ) L₁ L₁') : (s * s') • x ∈ La D (tor0 D cc δ) L₂ L₂' := by
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hG cc δ hc N N' g₁ g₁' L₁ L₁' h₁ h₁' x hx
  rw [← pt_nsmul]
  refine GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hG cc δ hc N N' g₂ g₂' L₂ L₂' h₂ h₂' _ ?_
  have hI := (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hc).2.2
  intro i j
  rw [matrix_move (inc D) (g₁ : GL (Fin N) (AE D)) _ (g₁' : GL (Fin N') (AE D)), Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine hI _ (hs l j) _ ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun r _ => hI _ (hs' i r) _ (hz r l)

end GlobalTheory.NormSum.LocAgree


open GlobalTheory.NormSum.LocAgree in
theorem GlobalTheory.NormSum.La_agree_of_trivAt : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  intro D hG cc δ hc N N' q h k h' k' L₁ L₂ L₁' L₂' hk hk' h₁ h₁' h₂ h₂'
  obtain ⟨s, hsq, hs, hsi⟩ := exists_int_mul D q k hk
  obtain ⟨s', hsq', hs', hsi'⟩ := exists_int_mul D q k' hk'
  refine ⟨fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩,
    fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩⟩
  · refine smul_mem_La D hG cc δ hc h (h * k) h' (h' * k') h₁ h₁' h₂ h₂' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi'
  · refine smul_mem_La D hG cc δ hc (h * k) h (h' * k') h' h₂ h₂' h₁ h₁' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs'
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestCone

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ v ∈ wtSub act μ ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

lemma Eab_mul (a b c d : Ix p q) :
    (Eab a b : Mat p q) * Eab c d = (if b = c then (1 : ℂ) else 0) • Eab a d := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne, h]

lemma lie_Eab {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b c d : Ix p q) (y : V) :
    act (Eab a b) (act (Eab c d) y) = act (Eab c d) (act (Eab a b) y) +
      ((if b = c then (1 : ℂ) else 0) • act (Eab a d) y -
        (if d = a then (1 : ℂ) else 0) • act (Eab c b) y) := by
  have := congrArg (fun f => f y) (hL (Eab a b) (Eab c d))
  simp only [Eab_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at this
  rw [this]; abel

lemma wt_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b : Ix p q)
    {ν : Ix p q → ℚ} {y : V} (hy : y ∈ wtSub act ν) :
    act (Eab a b) y ∈ wtSub act
      (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wt] at hy ⊢
  intro c
  rw [lie_Eab hL, hy, map_smul]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]
  · subst h2; simp [h1, sub_eq_add_neg, add_smul]
  · simp [h1, h2, Ne.symm h2]

def InCone (ν μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧
    μ = fun c => ν c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

lemma inCone_self (μ : Ix p q → ℚ) : InCone μ μ :=
  ⟨fun _ _ => 0, by simp, by simp⟩

lemma inCone_step {ν μ : Ix p q → ℚ} (h : InCone ν μ) (i : Fin p) (j : Fin q) :
    InCone (fun c => ν c + ((if c = Sum.inr j then 1 else 0) - (if c = Sum.inl i then 1 else 0))) μ := by
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨fun a b => m a b + if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0, ?_, ?_⟩
  · intro a b hab
    by_cases h0 : m a b = 0
    · by_cases h1 : a = Sum.inl i
      · by_cases h2 : b = Sum.inr j
        · exact ⟨i, j, h1, h2⟩
        · simp [h0, h2] at hab
      · simp [h0, h1] at hab
    · exact hm a b h0
  · funext c
    have key : ∑ a : Ix p q, ∑ b : Ix p q,
        (((if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0 : ℕ)) : ℚ) *
          ((if c = a then 1 else 0) - (if c = b then 1 else 0)) =
        (if c = Sum.inl i then 1 else 0) - (if c = Sum.inr j then 1 else 0) := by
      rw [Finset.sum_eq_single (Sum.inl i), Finset.sum_eq_single (Sum.inr j)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, key]
    ring

lemma act_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, act (Eab a b) y ∈ N) (Z : Mat p q) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]

  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b)

lemma exists_down {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) : ∃ D : Submodule ℂ V, v ∈ D ∧
      (∀ i j, ∀ x ∈ D, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ D) ∧
      (∀ a b, posC a b → ∀ x ∈ D, act (Eab a b) x ∈ D) ∧
      D ≤ ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1 := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ i j, ∀ x ∈ N, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b y (Submodule.mem_sInf.1 hy M hM)
  refine ⟨sInf S, hG.1, hG.2, fun a b hab x hx => ?_, sInf_le ⟨?_, fun i j x hx => ?_⟩⟩
  · have hG' : (sInf S ⊓ (sInf S).comap (act (Eab a b))) ∈ S := by
      refine ⟨⟨hG.1, ?_⟩, fun i j y hy => ⟨hG.2 i j y hy.1, ?_⟩⟩
      · show act (Eab a b) v ∈ sInf S
        rw [hv.2 a b hab]; exact Submodule.zero_mem _
      · show act (Eab a b) (act _ y) ∈ sInf S
        rw [lie_Eab hL]
        refine Submodule.add_mem _ (hG.2 i j _ hy.2) ?_
        rcases a with a | a <;> rcases b with b | b
        · refine Submodule.sub_mem _ (by simp) (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1))
        · exact absurd hab (by simp [posC])
        · exact absurd hab (by simp [posC])
        · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1)) (by simp)
    exact (sInf_le hG' hx).2
  · exact Submodule.mem_iSup_of_mem (⟨μ, inCone_self μ⟩ : {ν // InCone ν μ}) hv.1
  · refine Submodule.iSup_induction _ (motive := fun x => act (Eab (Sum.inr j) (Sum.inl i)) x ∈
      ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1) hx ?_ (by simp) ?_
    · intro ν y hy
      exact Submodule.mem_iSup_of_mem (⟨_, inCone_step ν.2 i j⟩ : {ν // InCone ν μ})
        (wt_shift hL _ _ hy)
    · intro y z hy hz
      rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

lemma wt_orth {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H)
    (hadj : ∀ Z x y, inner ℂ (E (act Z x)) (E y) = inner ℂ (E x) (E (act (adjZ Z) y)))
    {ν Λ : Ix p q → ℚ} (hne : ν ≠ Λ) {x e : V} (hx : x ∈ wtSub act ν) (he : e ∈ wtSub act Λ) :
    inner ℂ (E x) (E e) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
  have h := hadj (Eab c c) x e
  rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, mem_wt.1 hx, mem_wt.1 he,
    map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast, ← sub_eq_zero,
    ← sub_mul] at h
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hc ?_
  exact_mod_cast sub_eq_zero.1 h0

theorem cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro p q M H _ _ E hE hadj Λ e he hlow hgen μ v hv
  by_contra hcone
  change ¬ InCone Λ μ at hcone
  obtain ⟨D, hvD, hDm, hDp, hDle⟩ := exists_down M.lie hv.2
  rw [mem_hw] at he
  let C : Submodule ℂ M.V := ((D.map E)ᗮ).comap E
  have hC : ∀ x, x ∈ C ↔ ∀ d ∈ D, inner ℂ (E d) (E x) = 0 := by
    intro x
    simp only [C, Submodule.mem_comap, Submodule.mem_orthogonal]
    constructor
    · intro h d hd; exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩; exact h d hd
  have hstab : ∀ a b, (∀ d ∈ D, M.act (Eab a b) d ∈ D) → ∀ x ∈ C, M.act (Eab b a) x ∈ C := by
    intro a b h x hx
    rw [hC] at hx ⊢
    intro d hd
    have := hadj (adjZ (Eab b a)) d x
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at this
    rw [← this, GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact hx _ (D.smul_mem _ (h d hd))
  have heC : e ∈ C := by
    rw [hC]
    intro d hd
    refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (E x) (E e) = 0) (hDle hd) ?_
      (by simp) ?_
    · intro ν y hy
      exact wt_orth E hadj (fun h : ν.1 = Λ => hcone (h ▸ ν.2)) hy he.1
    · intro y z hy hz
      rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let r : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.1)
  have hr : Function.Injective r := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · congr 1; ext; omega
    · have := b.2; omega
    · have := a.2; omega
    · congr 1; ext; omega
  have hcase : ∀ a b, r a < r b → posC a b ∨ ∃ i j, a = Sum.inr j ∧ b = Sum.inl i := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · left; show a < b; rw [Fin.lt_def]; omega
    · have := b.2; omega
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · left; exact h
  obtain ⟨U, heU, hU, hUmin, -⟩ := GlobalTheory.ExtremalGen.exists_generated p q M.V M.act M.lie (fun _ _ => True)
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ r hr Λ e he.1 (by
      intro a b _ h
      rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
      · exact he.2 a b h
      · exact hlow i j)
  have hUC : U ≤ C := hUmin C heC (by
    intro a b _ h
    refine hstab a b ?_
    rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
    · exact hDp a b h
    · exact hDm i j)
  have hgU : genSub M.act {e} ≤ U :=
    sInf_le ⟨by simpa using heU, fun Z y hy => act_mem U y (fun a b => hU a b trivial y hy) Z⟩
  have hvC : v ∈ C := hUC (hgU (hgen ▸ Submodule.mem_top))
  have h0 := (hC v).1 hvC v hvD
  rw [inner_self_eq_zero] at h0
  exact hv.1 (hE (by rw [h0, map_zero]))

end GlobalTheory.LowestCone
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FockGrade

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_Eab_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (a b c d : Ix p q) (x : V) :
    act (Eab a b) (act (Eab c d) x) = act (Eab c d) (act (Eab a b) x) +
      (if b = c then act (Eab a d) x else 0) - (if d = a then act (Eab c b) x else 0) := by
  have h1 := congrArg (fun f : Module.End ℂ V => f x) (h (Eab a b) (Eab c d))
  simp only [map_sub, LinearMap.sub_apply, Module.End.mul_apply] at h1
  have e1 : act (Eab a b * Eab c d) x = if b = c then act (Eab a d) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  have e2 : act (Eab c d * Eab a b) x = if d = a then act (Eab c b) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  rw [← e1, ← e2, add_sub_assoc, h1]; abel

def layer (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  Nat.rec W (fun _ N => ⨆ ab : Fin p × Fin q, N.map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2)))) m

theorem layer_succ (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) :
    layer act W (m + 1) =
      ⨆ ab : Fin p × Fin q, (layer act W m).map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2))) := rfl

theorem raise_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} (a : Fin p) (b : Fin q)
    {y : V} (hy : y ∈ layer act W m) : act (Eab (Sum.inl a) (Sum.inr b)) y ∈ layer act W (m + 1) :=
  Submodule.mem_iSup_of_mem (a, b) (Submodule.mem_map_of_mem hy)

theorem layer_succ_le {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} {S : Submodule ℂ V}
    (h : ∀ a b, ∀ y ∈ layer act W m, act (Eab (Sum.inl a) (Sum.inr b)) y ∈ S) : layer act W (m + 1) ≤ S := by
  refine iSup_le fun ab => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h _ _ y hy

theorem layer_finite {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} (hW : FiniteDimensional ℂ W)
    (m : ℕ) : FiniteDimensional ℂ (layer act W m) := by
  induction m with
  | zero => exact hW
  | succ m ih => rw [layer_succ]; infer_instance

theorem layer_compact {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (m : ℕ) : ∀ a b, sameBlock a b → ∀ y ∈ layer act W m,
      act (Eab a b) y ∈ layer act W m := by
  induction m with
  | zero => intro a b hab y hy; exact hK _ (GlobalTheory.FockTensor.isKC_Eab hab) y hy
  | succ m ih =>
    intro a b hab
    have : layer act W (m + 1) ≤ (layer act W (m + 1)).comap (act (Eab a b)) := by
      refine layer_succ_le fun i j y hy => ?_
      rw [Submodule.mem_comap, act_Eab_comm h]
      refine sub_mem (add_mem (raise_mem _ _ (ih a b hab y hy)) ?_) ?_
      · split_ifs with hb
        · subst hb
          rcases a with a | a
          · exact raise_mem _ _ hy
          · exact absurd hab (by simp [sameBlock])
        · exact zero_mem _
      · split_ifs with hb
        · subst hb
          rcases b with b | b
          · exact absurd hab (by simp [sameBlock])
          · exact raise_mem _ _ hy
        · exact zero_mem _
    exact fun y hy => this hy

theorem sup_stable_of {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {f : Module.End ℂ V}
    (hf : ∀ m, ∀ y ∈ layer act W m, f y ∈ ⨆ m, layer act W m) :
    ∀ y ∈ ⨆ m, layer act W m, f y ∈ ⨆ m, layer act W m := by
  have : (⨆ m, layer act W m) ≤ (⨆ m, layer act W m).comap f := iSup_le fun m y hy => hf m y hy
  exact fun y hy => this hy

theorem sup_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (hL : ∀ e ∈ W, KilledByLower act e) (a b : Ix p q) :
    ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m := by
  have hk : ∀ a b, sameBlock a b → ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m :=
    fun a b hab => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem m (layer_compact h hK m a b hab y hy)
  have hr : ∀ a b, ∀ y ∈ ⨆ m, layer act W m,
      act (Eab (Sum.inl a) (Sum.inr b)) y ∈ ⨆ m, layer act W m :=
    fun a b => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem (m + 1) (raise_mem a b hy)
  rcases a with a | a <;> rcases b with b | b
  · exact hk _ _ trivial
  · exact hr _ _
  · refine sup_stable_of fun m => ?_
    induction m with
    | zero => intro y hy; rw [hL y hy b a]; exact zero_mem _
    | succ m ih =>
      have : layer act W (m + 1) ≤ (⨆ m, layer act W m).comap (act (Eab (Sum.inr a) (Sum.inl b))) := by
        refine layer_succ_le fun i j y hy => ?_
        have hy' : y ∈ ⨆ m, layer act W m := Submodule.mem_iSup_of_mem m hy
        rw [Submodule.mem_comap, act_Eab_comm h]
        refine sub_mem (add_mem (hr _ _ _ (ih y hy)) ?_) ?_
        · split_ifs
          · exact hk (Sum.inr a) (Sum.inr j) trivial _ hy'
          · exact zero_mem _
        · split_ifs
          · exact hk (Sum.inl i) (Sum.inl b) trivial _ hy'
          · exact zero_mem _
      exact fun y hy => this hy
  · exact hk _ _ trivial

theorem layer_eigen {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V} {c : ℂ}
    (hc : ∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) (m : ℕ) :
    ∀ x ∈ layer act W m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  induction m with
  | zero => intro x hx; simpa using hc x hx
  | succ m ih =>
    have : layer act W (m + 1) ≤ LinearMap.ker ((∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i))) -
        (c + ((m + 1 : ℕ) : ℂ)) • (LinearMap.id : V →ₗ[ℂ] V)) := by
      refine layer_succ_le fun a b y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      have e : ∀ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) (act (Eab (Sum.inl a) (Sum.inr b)) y) =
          act (Eab (Sum.inl a) (Sum.inr b)) (act (Eab (Sum.inl i) (Sum.inl i)) y) +
            (if i = a then act (Eab (Sum.inl a) (Sum.inr b)) y else 0) := by
        intro i
        rw [act_Eab_comm h]
        by_cases hi : i = a
        · subst hi; simp
        · simp [hi]

      simp only [e, Finset.sum_add_distrib, ← map_sum, ih y hy]
      simp [add_smul, add_assoc]
    intro x hx
    have h2 := this hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero] at h2
    simpa using h2

theorem exists_grading : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (W : Submodule ℂ V) (c : ℂ), FiniteDimensional ℂ W → KStable act W → (∀ e ∈ W, KilledByLower act e) → (∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) → ∃ N : ℕ → Submodule ℂ V, N 0 = W ∧ (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = genSub act (W : Set V) ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  intro p q V _ _ act h W c hW hK hL hc
  refine ⟨layer act W, rfl, layer_finite hW, le_antisymm ?_ ?_, layer_eigen h hc⟩
  · refine iSup_le fun m => le_sInf fun S hS => ?_
    induction m with
    | zero => exact hS.1
    | succ m ih => exact layer_succ_le fun a b y hy => hS.2 _ _ (ih hy)
  · refine sInf_le ⟨fun x hx => Submodule.mem_iSup_of_mem 0 hx, fun Z y hy => ?_⟩
    have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    rw [hZ]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (sup_stable h hK hL a b y hy)

end GlobalTheory.FockGrade
end
end
