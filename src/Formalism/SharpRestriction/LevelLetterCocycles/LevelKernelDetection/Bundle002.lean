module

public import Formalism.DistinguishedUnitIdeals.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan
public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.DistinguishedUnitIdeals.Statement
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

theorem detect_pt {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) {r : ℕ} (hr : r = Module.finrank LL D)
    (g : Fin r → ℤ → D) (hsupp : ∀ j, ∃ m : ℤ, ∀ k < m, g j k = 0) (hg : ∀ j k, g j k ∈ F (-k))
    (hspan : Submodule.span LL (Set.range fun j =>
      (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) = ⊤)
    (a : Fin r → PowerSeries LL) (e : ℕ)
    (h : ∀ k : ℤ, (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k - i)) ∈ F ((e : ℤ) - k)) :
    ∀ j, PowerSeries.X ^ e ∣ a j := by
  classical
  have hanti : Antitone F := hF.1
  have hli : LinearIndependent LL
      (fun j => (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) := by
    obtain ⟨_, hrk⟩ := finrank_grQ F hF
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [Fintype.card_fin, hrk, hr])
  have key : ∀ m, m < e → ∀ j, PowerSeries.coeff m (a j) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hcl : ∀ k' : ℤ, (∑ j, PowerSeries.coeff m (a j) • g j k') ∈ F (1 - k') := by
        intro k'
        have hS := h (k' + m)
        have hle : F ((e : ℤ) - (k' + m)) ≤ F (1 - k') := hanti (by omega)
        have hS' := hle hS
        have hR : ∀ j, (∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k' + m - i)) -
            PowerSeries.coeff m (a j) • g j k' ∈ F (1 - k') := by
          intro j
          obtain ⟨mj, hmj⟩ := hsupp j
          obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, m < N ∧ ∀ i : ℕ, N ≤ i → k' + m - i < mj :=
            ⟨(k' + m - mj).toNat + m + 1, by omega, fun i hi => by
              have := Int.self_le_toNat (k' + m - mj); omega⟩
          have hsub : (Function.support fun i : ℕ => PowerSeries.coeff i (a j) • g j (k' + m - i)) ⊆
              ↑(Finset.range N) := by
            intro i hi
            rw [Function.mem_support] at hi
            simp only [Finset.coe_range, Set.mem_Iio]
            by_contra hne
            apply hi
            rw [hmj _ (hN2 i (not_lt.mp hne)), smul_zero]
          rw [finsum_eq_sum_of_support_subset _ hsub,
            ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN1)]
          simp only [add_sub_cancel_right, add_sub_cancel_left]
          refine sum_mem fun i hi => ?_
          obtain ⟨hne, -⟩ := Finset.mem_erase.mp hi
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [ih i hlt (by omega) j, zero_smul]
            exact zero_mem _
          · exact Submodule.smul_mem _ _ (hanti (by omega) (hg j (k' + m - i)))
        have hsum := sub_mem hS' (sum_mem (t := Finset.univ) fun j _ => hR j)
        rw [Finset.sum_sub_distrib, sub_sub_cancel] at hsum
        exact hsum
      have hz : ∑ j, PowerSeries.coeff m (a j) •
          (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = 0 := by
        have hmk : ∑ j, PowerSeries.coeff m (a j) •
            (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) =
            (Submodule.mkQ _) (∑ j, PowerSeries.coeff m (a j) •
              (⟨g j, fun k _ => hg j k⟩ : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
        rw [hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.mem_pi]
        intro k _
        simpa using hcl k
      exact fun j => Fintype.linearIndependent_iff.mp hli _ hz j
  intro j
  exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => key m hm j

end Formalism.MainNotions.N.Ln03.K8
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem lvBasis_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V) (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.actVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := V) x) =
      φVB PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.mulVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.Dcris, sub_eq_zero]

theorem lvBasis_mem_DcrisL (ρ : Representation LL G V) (τ₀ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ₀ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ₀ c • x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.DcrisL, sub_eq_zero]

theorem lvBasis_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [lvBasis_mem_Dcris] at hx ⊢
  intro g
  rw [lvBasis_φ_act, hx g]

theorem lvBasis_φ_letter (ρ : Representation LL G V) {τ₀ τ₁ : K₀ →ₐ[Qp] LL}
    (h : τ₁.comp PD.σ = τ₀) {x : V ⊗[Qp] B} (hx : x ∈ DcrisL PD ρ τ₀) :
    φVB PD (LL := LL) (V := V) x ∈ DcrisL PD ρ τ₁ := by
  rw [lvBasis_mem_DcrisL] at hx ⊢
  refine ⟨lvBasis_φ_Dcris PD ρ hx.1, fun c => ?_⟩
  obtain ⟨c', rfl⟩ := PD.σ_bij.2 c
  rw [lvBasis_φ_mul, hx.2 c', map_smul, ← h, AlgHom.comp_apply]

theorem lvBasis_φ_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have hfun : ⇑(Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V)) = ⇑(LinearMap.lTensor V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.φVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [hfun]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj

theorem lvBasis_φpow_inj (k : ℕ) : Function.Injective ((φVB PD (LL := LL) (V := V)) ^ k) := by
  first
  | (rw [Module.End.coe_pow]; exact (lvBasis_φ_inj PD).iterate k)
  | simpa using (lvBasis_φ_inj PD).iterate k

private theorem eigen_finset_eq_zero_of_injective_embeddings {ι : Type} [DecidableEq ι] (τ : ι → (K₀ →ₐ[Qp] LL))
    (hτ : Function.Injective τ) (s : Finset ι) : ∀ (x : ι → V ⊗[Qp] B),
    (∀ i ∈ s, ∀ c, Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i) →
    ∑ i ∈ s, x i = 0 → ∀ i ∈ s, x i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro x _ _ i hi; simp at hi
  | @insert j s hj ih =>
    intro x hx hs
    rw [Finset.sum_insert hj] at hs
    have h2 : ∑ i ∈ s, x i = -x j := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    have key : ∀ c, ∀ i ∈ s, (τ i c - τ j c) • x i = 0 := by
      intro c
      apply ih (fun i => (τ i c - τ j c) • x i)
      · intro i hi c'
        rw [map_smul, hx i (Finset.mem_insert_of_mem hi) c', smul_comm]
      · have h1 := congrArg (Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c) hs

        rw [map_add (f := _), map_sum, map_zero, hx j (Finset.mem_insert_self j s) c,
        Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_insert_of_mem hi) c)] at h1
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, ← Finset.smul_sum, h2, smul_neg, sub_neg_eq_add, add_comm]
        exact h1
    have hs0 : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have hij : τ i ≠ τ j := fun h => hj (by rw [← hτ h]; exact hi)
      obtain ⟨c, hc⟩ : ∃ c, τ i c ≠ τ j c := by
        by_contra hne
        push_neg at hne
        exact hij (AlgHom.ext hne)
      exact (smul_eq_zero.mp (key c i hi)).resolve_left (sub_ne_zero.mpr hc)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hs0, add_zero] at hs
      exact hs
    · exact hs0 i hi

theorem lvBasis_indep {ι : Type} [Fintype ι] (τ : ι → (K₀ →ₐ[Qp] LL)) (hτ : Function.Injective τ)
    (x : ι → V ⊗[Qp] B)
    (hx : ∀ i c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i)
    (hs : ∑ i, x i = 0) (i : ι) : x i = 0 := by
  classical
  exact eigen_finset_eq_zero_of_injective_embeddings τ hτ Finset.univ x (fun i _ c => hx i c) hs i (Finset.mem_univ i)

end Formalism.MainNotions.N.Ln03.Pf
end
end
