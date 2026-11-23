module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle019
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle022
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirIsotypicNoHigherWeight
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrAevalStable
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle021
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle016
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem lattice_theorem_single_rep_linf (h : InvariantDenominatorLinftyBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation) (hInv : InvariantProjectionExists)
    (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (hE : IsGLRep E)
    (M : Submodule O V) (hM : UZLattice E M) (hMQ : MQ (K := KK O) M = ⊤)
    (lam : Fin n → ℤ) (hdom : Dominant lam) (e : Module.End (KK O) V) (he : IsIsoProj E lam e) (x : V)
    (hx : x ∈ M) :
    ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) • e x ∈ M := by
  have : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime
  by_cases hv : ∃ v0, IsHWV E lam v0
  · obtain ⟨v0, hv0⟩ := hv
    have hL := cyclicSubmodule_isSubrepresentation E v0
    obtain ⟨d, b, hbM, hbc⟩ := hB O V M hM.2 hMQ (cyclicSubmodule E v0)
    have hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E) :=
      hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE
    obtain ⟨P, hP⟩ := hInv n (KK O) _ _ hEH
    obtain ⟨hl1, hl2⟩ := hLat O n V E hE M hM hMQ _ hL
    have key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) •
        P ((b.coord i).smulRight x) (b i) ∈ M := by
      intro i
      have hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0) := by
        intro y hy
        obtain ⟨o, ho⟩ := hbc y hy i
        rw [LinearMap.smulRight_apply, ho, algebraMap_smul]
        exact M.smul_mem _ hx
      have h1 := h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf
      have h2 := h1 (b i) (hbM i)
      rw [LinearMap.smul_apply] at h2
      refine pow_smul_mem_of_le' M _ ?_ h2
      refine Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)
      rw [hl2, hMQ]
      exact linf_homRep_le_ell_add E hE lam hdom v0 hv0 hL
    rw [← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm,
      Finset.smul_sum]
    exact M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)
  · have h0 : e x = 0 := by
      have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e := by
        refine iSup_le fun mu => ?_
        by_cases hmu : mu = lam
        · subst hmu
          refine Submodule.span_le.2 ?_
          rintro y ⟨u, _, v, hv', _⟩
          exact absurd ⟨v, hv'⟩ hv
        · intro y hy
          exact he.2 mu hmu y hy
      have : x ∈ (⨆ mu, isoSub E mu) := by rw [hTop n (KK O) V E hE]; trivial
      exact hle this
    rw [h0, smul_zero]; exact M.zero_mem

theorem isotypicProjectorTheoremField_of_linfty_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : IsotypicProjectorTheoremField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw hSw e he x hx
  rw [Finset.smul_sum]
  refine M.sum_mem fun lam hlam => ?_
  have h1 := lattice_theorem_single_rep_linf h (isotypic_submodules_span_top D h2) restriction_is_representation hom_space_is_representation (invariant_projection_exists D h2) (isotypic_projector_trace_formula D h2)
    lattice_adapted_basis_exists hom_lattice_dividedPower_stable p n' O S hG n V E hE M hM hMQ lam (hSw lam hlam) (e lam) (he lam hlam) x hx
  refine pow_smul_mem_of_le' M _ ?_ h1
  exact Finset.le_sup (f := fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam)) hlam

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cr_lift [CharZero K] (E : GLOps n K V) (hT : (⨆ ν, weightSp E ν) = ⊤) (W Z : Submodule K V)
    (hW : IsStableUnderOperators E W) (hZ : IsStableUnderOperators E Z) (mu : Fin n → ℤ) (x0 : V) (hx0 : x0 ∈ W)
    (hq : Z.mkQ x0 ∈ weightSp (cr_quot E Z hZ) mu) :
    ∃ x ∈ W, x ∈ weightSp E mu ∧ Z.mkQ x = Z.mkQ x0 := by
  classical
  have hg := v2rep_graded E W (fun a x hx => hW a a x hx) x0 hx0 (by rw [hT]; trivial)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hg
  have hm : ∑ ν ∈ f.support, Z.mkQ (f ν) = Z.mkQ x0 := by

    rw [← hsum, Finsupp.sum, map_sum]
  have hc := v2rep_comp_mem (cr_quot E Z hZ) (weightSp (cr_quot E Z hZ) mu)
    (fun a x hx => cr_wt_diag_stable _ mu a x hx) f.support (fun ν => Z.mkQ (f ν))
    (fun ν _ => cr_quot_wt E Z hZ ν _ (hf ν).1) (by rw [hm]; exact hq)
  refine ⟨f mu, (hf mu).2, (hf mu).1, ?_⟩
  rw [← hm]
  symm
  refine Finset.sum_eq_single mu (fun ν hν hne => ?_) (fun hn => ?_)
  · exact cr_wt_disj _ hne (cr_quot_wt E Z hZ ν _ (hf ν).1) (hc ν hν)
  · rw [Finsupp.notMem_support_iff.1 hn, map_zero]

theorem cr_CR [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    W ≤ ⨆ mu, isotypicPartIn E W mu := by
  classical
  set W2 : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW2
  have hW2st : IsStableUnderOperators E W2 := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  by_contra hnot
  have hZne : W.map W2.mkQ ≠ ⊥ := by
    intro h
    apply hnot
    have := (LinearMap.le_ker_iff_map (f := W2.mkQ) (p := W)).2 h
    rwa [Submodule.ker_mkQ] at this
  have hZst : IsStableUnderOperators (cr_quot E W2 hW2st) (W.map W2.mkQ) := by
    rintro a b y ⟨x, hx, rfl⟩
    exact ⟨E a b x, hW a b x hx, rfl⟩
  have hRq := cr_quot_rel E hR W2 hW2st
  obtain ⟨mu, xb, hxbZ, hxb⟩ := v2rep_exists_hwv (cr_quot E W2 hW2st) hRq (W.map W2.mkQ) hZst
    (le_top.trans (cr_quot_top E W2 hW2st hT)) hZne
  obtain ⟨x0, hx0W, rfl⟩ := hxbZ
  obtain ⟨x, hxW, hxwt, hxq⟩ := cr_lift E hT W W2 hW hW2st mu x0 hx0W hxb.2.1
  rw [← hxq] at hxb
  have hdom : Dominant mu := cr_hwv_dom _ hRq hxb
  have hxn : x ∉ W2 := fun h => hxb.1 ((Submodule.Quotient.mk_eq_zero W2).2 h)
  have hup : ∀ a b : Fin n, a < b → E a b x ∈ W2 := by
    intro a b hab
    have := hxb.2.2 a b hab
    rw [cr_quot_mk] at this
    exact (Submodule.Quotient.mk_eq_zero W2).1 this
  set T := cr_C E with hTdef
  have hTW2 : ∀ z ∈ W2, T z ∈ W2 := cr_C_stable E W2 hW2st
  have hy : T x - ((cr_c mu : ℤ) : K) • x ∈ W2 := by
    rw [hTdef, cr_C_wt E hR mu x hxwt, add_sub_cancel_left]
    refine W2.smul_mem _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_)
    split_ifs with h
    · exact hW2st b a _ (hup a b h)
    · exact zero_mem _
  obtain ⟨q, hq1, hq2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) _ hy (cr_c mu)
  set x' := aeval T q x with hx'
  have h1 : x' - x ∈ W2 := by
    have := cr_aeval_mod T W2 hTW2 _ x hy q
    rwa [hq1, one_smul] at this
  have h2 : x' ∈ W := cr_aeval_stable T W (cr_C_stable E W hW) x hxW q
  have h3 : x' ∈ weightSp E mu := cr_aeval_stable T _ (cr_C_weightSp E hR mu) x hxwt q
  have h4 : x' ∉ W2 := by
    intro h
    apply hxn
    have : x = x' - (x' - x) := by abel
    rw [this]; exact W2.sub_mem h h1

  have hy0 : T x' - ((cr_c mu : ℤ) : K) • x' = aeval T q (T x - ((cr_c mu : ℤ) : K) • x) := by
    rw [map_sub, map_smul, cr_aeval_comm T T rfl q x]
  have hy0e : T (T x' - ((cr_c mu : ℤ) : K) • x') = ((cr_c mu : ℤ) : K) • (T x' - ((cr_c mu : ℤ) : K) • x') := by
    rw [hy0]
    exact casimir_acts_scalar_on_level E hR (fun _ => W) (cr_c mu) _ hq2
  have hzero : ∀ a b : Fin n, a < b → E a b x' = 0 := by
    intro a b hab
    set z := E a b x' with hz
    have hzW2 : z ∈ W2 := by
      have : z = E a b x + E a b (x' - x) := by rw [hz, ← map_add (f := _)]; congr 1; abel
      rw [this]; exact W2.add_mem (hup a b hab) (hW2st a b _ h1)
    have hzwt : z ∈ weightSp E (mu + rootW a b) := v2rep_shift E hR a b mu x' h3
    set w1 := T z - ((cr_c mu : ℤ) : K) • z with hw1
    have hw1' : w1 = E a b (T x' - ((cr_c mu : ℤ) : K) • x') := by
      rw [hw1, hz, map_sub, map_smul, hTdef, cr_C_comm_apply E hR]
    have hw1e : T w1 = ((cr_c mu : ℤ) : K) • w1 := by
      rw [hw1', hTdef, cr_C_comm_apply E hR, ← hTdef, hy0e, map_smul]
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) z hzW2 (cr_c mu)
    have hz0 : aeval T r z = 0 := by
      refine casimir_isotypic_no_higher_weight E hR (fun _ => W) mu hdom (mu + rootW a b) ?_ ?_ _ hr2
        (cr_aeval_stable T _ (cr_C_weightSp E hR _) z hzwt r)
      · rw [add_sub_cancel_left]; exact cr_root_mem a b hab
      · rw [add_sub_cancel_left]; exact cr_ht_root a b hab
    have hspan : aeval T r z - r.eval (((cr_c mu : ℤ) : K)) • z ∈ Submodule.span K {w1} := by
      refine cr_aeval_mod T (Submodule.span K {w1}) ?_ _ z (Submodule.mem_span_singleton_self w1) r
      intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hw1e, smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w1))
    rw [hz0, hr1, one_smul, zero_sub] at hspan
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hspan
    have hzt : z = (-t) • w1 := by rw [neg_smul, ht, neg_neg]
    have hw0 : w1 = 0 := by
      have : T z = ((cr_c mu : ℤ) : K) • z := by rw [hzt, map_smul, hw1e, smul_comm]
      rw [hw1, this, sub_self]
    rw [hzt, hw0, smul_zero]
  apply h4
  have hne : x' ≠ 0 := fun h => h4 (by rw [h]; exact zero_mem _)
  exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, one_mem _, x', h2, ⟨hne, h3, hzero⟩, rfl⟩)

end Formalism.MainNotions.G.GLWeightTheory
end
end
