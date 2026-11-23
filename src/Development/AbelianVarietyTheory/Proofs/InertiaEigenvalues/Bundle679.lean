module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle647
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveGeneratorBoundedMultipleSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.TorsFree

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_le_one_of_mul {x g : K⟦X⟧} (hx : ∃ B : ℝ, ∀ n, ‖coeff n x‖ ≤ B)
    (hg : ∀ n, ‖coeff n g‖ ≤ 1) (hg1 : ∃ n, ‖coeff n g‖ = 1) (hgx : ∀ n, ‖coeff n (g * x)‖ ≤ 1) :
    ∀ n, ‖coeff n x‖ ≤ 1 := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hbdd : BddAbove (Set.range fun n => ‖coeff n x‖) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  set S := ⨆ n, ‖coeff n x‖ with hSdef
  have hxS : ∀ n, ‖coeff n x‖ ≤ S := fun n => le_ciSup hbdd n
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hxS 0)
  set d := Nat.find hg1 with hd
  have hgd : ‖coeff d g‖ = 1 := Nat.find_spec hg1
  have hlt : ∀ i < d, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne (hg i) (Nat.find_min hg1 hi)
  set θ : NNReal := (Finset.range d).sup fun i => ‖coeff i g‖₊ with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, Finset.sup_lt_iff (by simp)]
    intro i hi
    have := hlt i (Finset.mem_range.1 hi)
    rw [← NNReal.coe_lt_coe]; simpa using this
  have hθi : ∀ i < d, ‖coeff i g‖ ≤ (θ : ℝ) := fun i hi => by
    have : ‖coeff i g‖₊ ≤ θ := Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 hi)
    exact_mod_cast this
  have hθ0 : (0 : ℝ) ≤ θ := θ.2
  set Mx := max 1 ((θ : ℝ) * S) with hMx
  have hM0 : 0 ≤ Mx := le_trans zero_le_one (le_max_left _ _)
  have key : ∀ n, ‖coeff n x‖ ≤ Mx := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hmem : (d, n) ∈ Finset.HasAntidiagonal.antidiagonal (n + d) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact add_comm d n
    have hc := coeff_mul (n + d) g x
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x‖ ≤ Mx := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun p hp => ?_
      obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [norm_mul]
      rcases lt_trichotomy p.1 d with h | h | h
      · calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ θ * S :=
            mul_le_mul (hθi _ h) (hxS _) (norm_nonneg _) hθ0
          _ ≤ Mx := le_max_right _ _
      · exact absurd (Prod.ext h (by omega)) hne
      · have hj : p.2 < n := by omega
        calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ 1 * Mx :=
            mul_le_mul (hg _) (ih _ hj) (norm_nonneg _) zero_le_one
          _ = Mx := one_mul _
    have heq : coeff d g * coeff n x = coeff (n + d) (g * x) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x := by
      rw [hc]; ring
    have : ‖coeff n x‖ = ‖coeff d g * coeff n x‖ := by rw [norm_mul, hgd, one_mul]
    rw [this, heq, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hrest))
    exact (hgx _).trans (le_max_left _ _)
  have hSM : S ≤ Mx := ciSup_le key
  have hS1 : S ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : S ≤ θ * S := by
      rcases le_total 1 ((θ : ℝ) * S) with h3 | h3
      · rwa [hMx, max_eq_right h3] at hSM
      · rw [hMx, max_eq_left h3] at hSM; linarith
    have : (1 - (θ : ℝ)) * S ≤ 0 := by linarith
    have h4 : (0 : ℝ) < 1 - θ := by have := (NNReal.coe_lt_coe.2 hθ1); simp at this; linarith
    nlinarith
  exact fun n => (hxS n).trans hS1

end GlobalTheory.BK.TorsFree

namespace GlobalTheory.BK.Hom

open GlobalTheory.BK.TorsFree

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mem_imM_of_smul_mem (F : Hom P Q)
    (hg : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧
      Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧))
    (hl : ∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) {v : Vec K a κ} (hv : v ∈ Q.M) {f : K⟦X⟧}
    (hf0 : f ≠ 0) (hfv : f • v ∈ F.imM) : v ∈ F.imM := by
  unfold imM at hfv ⊢
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hfv
  rw [LinearMap.restrictScalars_apply] at hwv
  choose Y hYb hY using fun τ => (hl τ).2
  choose Y0 g hY0A hg1 hY0 using hg
  have hv' : ∀ τ i, v τ i ∈ A O K := fun τ => mem_tot.1 hv τ
  let x : Vec K a ι := fun τ => Y τ *ᵥ v τ
  have hfx : ∀ τ, f • x τ = w τ := by
    intro τ
    have h1 : f • v τ = F.mat τ *ᵥ w τ := by rw [← app_apply, hwv]; rfl
    change f • (Y τ *ᵥ v τ) = w τ
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, hY τ, one_smul, Matrix.one_mulVec]
  have hFx : F.app x = v := by
    funext τ i
    have h2 : f • F.app x τ = f • v τ := by
      rw [app_apply, ← Matrix.mulVec_smul, hfx τ, ← app_apply, hwv]; rfl
    exact mul_left_cancel₀ hf0 (congrFun h2 i)
  have hbx : ∀ τ i, ∃ B : ℝ, ∀ n, ‖coeff n (x τ i)‖ ≤ B := by
    intro τ i
    obtain ⟨c, hc⟩ := hYb τ
    refine ⟨max c 0, fun n => ?_⟩
    change ‖coeff n (∑ j, Y τ i j * v τ j)‖ ≤ max c 0

    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun j _ => ?_
    have := norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (le_max_right c 0) zero_le_one (f := Y τ i j) (g := v τ j)
      (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _))
      (fun m => by rw [mul_one]; exact hv' τ j m) n
    rwa [mul_one, mul_one] at this
  have hgA : ∀ τ (i : ι), ∀ n, ‖coeff n (g τ)‖ ≤ 1 := by
    intro τ i
    have h5 : g τ = (Y0 τ * F.mat τ) i i := by rw [hY0 τ]; simp
    rw [h5]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (F.mem τ j i)
  have hgx : ∀ τ i, ∀ n, ‖coeff n (g τ * x τ i)‖ ≤ 1 := by
    intro τ i
    have h3 : g τ • x τ = Y0 τ *ᵥ v τ := by
      conv_rhs => rw [← hFx]
      rw [app_apply, Matrix.mulVec_mulVec, hY0 τ]
      first
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h4 : g τ * x τ i = (Y0 τ *ᵥ v τ) i := by rw [← h3]; rfl
    rw [h4]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (hv' τ j)
  have hxA : x ∈ P.M := mem_tot.2 fun τ i =>
    norm_coeff_le_one_of_mul (hbx τ i) (hgA τ i) (hg1 τ) (hgx τ i)
  exact Submodule.mem_map.2 ⟨x, hxA, by rw [LinearMap.restrictScalars_apply]; exact hFx⟩

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.coker_torsionFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hg hl v hv f _ hf0 hfv
  exact F.mem_imM_of_smul_mem hg hl hv hf0 hfv
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem cosetSum_transfer_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H)
    (hψ : Function.Surjective ψ) (hTU : ∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0)
    (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ)
    (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x)
    (hfin : (Function.support fun d : H ⧸ K => a d.out).Finite)
    (hβ : ∀ x, ∀ u ∈ U0, β (x * u) = β x)
    (hφ : ∀ t : T, φ' (ψ t) = lam (β t)) :
    ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0,
      if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  classical
  set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF
  let t : H ⧸ K → T := fun d => (hψ d.out).choose
  have ht : ∀ d, ψ (t d) = d.out := fun d => (hψ d.out).choose_spec
  let f : H ⧸ K → G ⧸ U0 := fun d => ((t d : G) : G ⧸ U0)

  have key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) →
      ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    refine ⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩
    simp [map_mul, map_inv]

  have hinj : Function.Injective f := by
    intro d d' h
    obtain ⟨-, k, hk, hkk⟩ := key _ _ h
    rw [ht, ht] at hkk
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]
    simpa using hk

  have hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧
      a (((ψ x : H) : H ⧸ K).out) = a (ψ x) := by
    intro x
    set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd
    have h1 : d.out⁻¹ * ψ x ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)
      rw [QuotientGroup.eq]
      have : ψ ((t d)⁻¹ * x) ∈ K := by simpa [map_mul, map_inv, ht] using h1
      simpa using (hTU _).1 this
    · have := ha d.out _ h1
      simpa using this.symm

  have hval : ∀ d, F (f d) = a d.out • β (t d) := by
    intro d
    have hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T := ⟨t d, rfl, (t d).2⟩
    simp only [hF, dif_pos hc]
    obtain ⟨hU, k, hk, hkk⟩ := key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm
    rw [hkk, ha _ k hk, ht]
    congr 1
    have := hβ (t d : G) _ hU
    simpa using this

  set S : Finset (H ⧸ K) := hfin.toFinset with hS
  have hsupp : Function.support F ⊆ ↑(S.image f) := by
    intro c hc
    rw [Function.mem_support] at hc
    have hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T := by
      by_contra hn
      exact hc (by simp only [hF, dif_neg hn])
    obtain ⟨x, rfl, hx⟩ := hc'
    obtain ⟨h1, h2⟩ := hcover ⟨x, hx⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support, h2]
    intro h0
    apply hc
    have hF' := hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)
    rw [h1, h2, h0, zero_smul] at hF'
    exact hF'
  have hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S := by
    intro d hd
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hd (by simp only [h0, zero_mul])

  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp,
  Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hval, map_smul, smul_eq_mul, ← hφ, ht]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.linearIndependent_of_mutual_span_of_indep : ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W), (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) → (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) → (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) → ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  first | exact @GlobalTheory.linIndep_of_mutual_span_of_indep | exact GlobalTheory.linIndep_of_mutual_span_of_indep | (intros; apply GlobalTheory.linIndep_of_mutual_span_of_indep <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1 := by
  first | exact @GlobalTheory.powerSeries_inv_coeff_norm_le_one | exact GlobalTheory.powerSeries_inv_coeff_norm_le_one | (intros; apply GlobalTheory.powerSeries_inv_coeff_norm_le_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.exists_primitive_generator_boundedMultiple_set : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) → (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) → (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧ ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q := by
  first | exact @GlobalTheory.exists_primitive_generator | exact GlobalTheory.exists_primitive_generator | (intros; apply GlobalTheory.exists_primitive_generator <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory

theorem coeff_coeff_pow_eq_of_box :
    ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧),
      (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  intro R _ m i n G H h
  induction m generalizing i n with
  | zero => simp
  | succ k ih =>

    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨s, t⟩ hst
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hst
    dsimp only at hpq hst ⊢
    rw [ih p s (fun i' hi' n' hn' => h i' (by omega) n' (by omega)), h q (by omega) t (by omega)]

end GlobalTheory
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.cosetSum_transfer_along_surjection_preimage : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H), Function.Surjective ψ → (∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0) → ∀ (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ), (∀ x, ∀ k ∈ K, a (x * k) = a x) → (Function.support fun d : H ⧸ K => a d.out).Finite → (∀ x, ∀ u ∈ U0, β (x * u) = β x) → (∀ t : T, φ' (ψ t) = lam (β t)) → ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0, if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  first | exact @GlobalTheory.cosetSum_transfer_surj | exact GlobalTheory.cosetSum_transfer_surj | (intros; apply GlobalTheory.cosetSum_transfer_surj <;> assumption)

end
end
