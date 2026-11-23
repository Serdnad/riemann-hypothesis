module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle029
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

private theorem sepMod {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

private theorem sepRep {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (hρ : ρ'.IsIrreducible)
    (h : ∀ y, y ∈ ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] V', (∀ g v, p (ρ g v) = ρ' g (p v)) ∧ p x ≠ 0 := by
  classical
  let F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
  let Φ := Finsupp.lsum ℕ F
  have hs : Function.Surjective Φ := fun y => by
    refine Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) (h y) ?_ ⟨0, map_zero Φ⟩ ?_
    · rintro f _ ⟨v, rfl⟩
      exact ⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩
    · rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z + z', map_add Φ z z'⟩
  obtain ⟨p, hp⟩ := sepMod Φ hs x hx
  let q := (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p
  exact ⟨q.toLinearMap, fun g v => q.isIntertwining _ _ g v, hp⟩

private def piRep {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (ι : Type) :
    Representation ℂ G (ι → M) where
  toFun g := (ρ g).compLeft ι
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

private theorem piIso {G M S : Type} [Group G] [AddCommGroup M] [Module ℂ M] [AddCommGroup S] [Module ℂ S]
    (ρ : Representation ℂ G M) (σ : Representation ℂ G S) (ι : Type) [Finite ι]
    (h : ∀ y, y ∈ ⨆ f : {f : S →ₗ[ℂ] M // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) (y : ι → M) :
    y ∈ ⨆ f : {f : S →ₗ[ℂ] (ι → M) // ∀ g v, f (σ g v) = piRep ρ ι g (f v)}, LinearMap.range f.1 := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.iSup_induction _ (motive := fun z : M => (Pi.single i z : ι → M) ∈ _) (h (y i)) ?_ ?_ ?_
  · rintro f _ ⟨v, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : ι => M) i ∘ₗ f.1, fun g v => ?_⟩ ⟨v, rfl⟩
    funext j
    change (Pi.single i (f.1 (σ g v)) : ι → M) j = ρ g ((Pi.single i (f.1 v) : ι → M) j)
    by_cases hj : j = i
    · subst hj; simp [f.2]
    · simp [Pi.single_eq_of_ne hj]
  · simp
  · intro a b ha hb
    rw [Pi.single_add]; exact add_mem ha hb

theorem UpperTheory.isotypic_separates_and_embeds_into_invariant_subspace :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (σ : SmIrr H), IsoSum ρ ⊤ σ → (∀ x : M, x ≠ 0 → ∃ p : M →ₗ[ℂ] σ.V, (∀ g v, p (ρ g v) = σ.ρ g (p v)) ∧ p x ≠ 0) ∧ ∀ (ι : Type) [Finite ι] (Y : Submodule ℂ (ι → M)), Y ≠ ⊥ → (∀ g, ∀ F ∈ Y, (fun i => ρ g (F i)) ∈ Y) → ∃ s : σ.V →ₗ[ℂ] (ι → M), Function.Injective s ∧ (∀ v, s v ∈ Y) ∧ ∀ g v i, s (σ.ρ g v) i = ρ g (s v i) := by
  intro H M _ _ _ _ _ ρ σ hI
  have h : ∀ y, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)}, LinearMap.range f.1 := fun y => by
    refine (le_trans hI (iSup_le fun f => ?_)) (Submodule.mem_top (x := y))
    exact le_iSup_of_le (f := fun f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)} => LinearMap.range f.1)
      ⟨f.1, f.2.1⟩ le_rfl
  refine ⟨sepRep ρ σ.ρ σ.irred h, fun ι _ Y hY hst => ?_⟩
  let π : Representation ℂ H Y := (piRep ρ ι).subrepresentation Y fun g F hF => hst g F hF
  have h2 := UpperTheory.V.PiLin.iso_sub σ.ρ π (piRep ρ ι) σ.irred Y.subtype Y.injective_subtype (fun _ _ => rfl)
    fun y => piIso ρ σ.ρ ι h _
  obtain ⟨f, hf⟩ : ∃ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, f.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY
    have := h2 ⟨y, hy⟩
    simp only [hc, LinearMap.range_zero, iSup_bot, Submodule.mem_bot] at this
    exact hy0 (congrArg Subtype.val this)
  haveI := σ.irred
  have hi : Function.Injective f.1 := by
    let F : σ.ρ.IntertwiningMap π := ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (congrArg Representation.IntertwiningMap.toLinearMap hz) hf
  refine ⟨Y.subtype ∘ₗ f.1, Y.injective_subtype.comp hi, fun v => (f.1 v).2, fun g v i => ?_⟩
  exact congrFun (congrArg Subtype.val (f.2 g v)) i
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

namespace UpperTheory.V

variable {l : ℕ} [Fact l.Prime]

private def slS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem sl_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ slS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

end UpperTheory.V

open UpperTheory.V in
theorem UpperTheory.filtration_entries_of_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a : ℤ, (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil a) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1 := by
  intro l hl K f hf hσ d M M' A F hMM hA hφ hF a hFil β hβ
  obtain ⟨u, hu, hφu⟩ := UpperTheory.exists_crystalline_unit_frobenius_eigen l (-a)
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  have hit : ∀ k : ℕ, ((PP l).φB)^[k] (u : Bcr l) =
      algebraMap ℚ_[l] (Bcr l) (((l : ℚ_[l]) ^ (-a)) ^ k) * (u : Bcr l) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes, hφu, pow_succ, map_mul, mul_assoc]
  have huM : ∀ i j, (u : Bcr l) * M i j ∈ slS l := fun i j => by
    have := ((PP l).PD (botExt l)).Fil_mul _ _ _ _ hu (hFil i j)
    rw [neg_add_cancel, ← map_mul] at this
    exact this
  have key : ∀ (k : ℕ) (E : Matrix (Fin d) (Fin d) ↥(K0 K)),
      M.map (((PP l).φB)^[k]) = M * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ((u : Bcr l) • M).map (((PP l).φB)^[k]) = ((u : Bcr l) • M) *
        (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ k) • E).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k E hE
    ext i j
    have h1 := congrFun (congrFun hE i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at h1
    have h2 : ((PP l).φB)^[k] ((u : Bcr l) * M i j) =
        ((PP l).φB)^[k] (u : Bcr l) * ((PP l).φB)^[k] (M i j) := by
      rw [hc, map_mul]
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2, hit, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  have h := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ ((u : Bcr l) • M) (((u⁻¹ : (Bcr l)ˣ) : Bcr l) • M') _
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, hMM'])
    (fun k i j => by
      obtain ⟨E, -, hE⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ k
      have h1 := congrFun (congrFun (key k E hE) i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at h1
      rw [h1]
      exact Subring.sum_mem (slS l) fun r _ => Subring.mul_mem _ (huM _ _) (sl_alg K _))
    (key f F hF)
  apply h
  have hl0 : ((l : Om l) ^ f) ^ (-a) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
  have e : (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ f) • F).map (algebraMap ↥(K0 K) (Om l)) =
      Units.mk0 _ hl0 • F.map (algebraMap ↥(K0 K) (Om l)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_zpow₀, map_natCast,
      Units.smul_mk0]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (f : ℤ)]
  rw [e]
  exact (spectrum.smul_mem_smul_iff (r := Units.mk0 _ hl0)).2 hβ
end
