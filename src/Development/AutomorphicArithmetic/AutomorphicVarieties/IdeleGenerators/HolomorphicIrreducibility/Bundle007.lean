module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle043
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open Matrix Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.U3

theorem UpperTheory.V.Sd.irrAb :
    UpperTheory.V.Sd.IrrAb := by
  intro l _ Γ _ _ _ n r hr hio H H' hH hle hab
  have h0 := hio H hH
  have hne : (⊤ : Submodule (Formalism.ConjugateSelfDual.Qbar l) (Fin n → Formalism.ConjugateSelfDual.Qbar l)) ≠ ⊥ := h0.1
  haveI : Nontrivial (Fin n → Formalism.ConjugateSelfDual.Qbar l) := Submodule.nontrivial_iff (Formalism.ConjugateSelfDual.Qbar l) |>.mp ⟨_, _, hne⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hne (Subsingleton.elim _ _)
  refine ⟨hne, fun _ _ _ => trivial, fun W _ hW => ?_⟩
  by_contra hcon
  have hab' : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ H'.subgroupOf H := fun a b =>
    Subgroup.mem_subgroupOf.mpr (hab a a.2 b b.2)
  haveI : (H'.subgroupOf H).Normal := ⟨fun x hx g => by
    have := (H'.subgroupOf H).mul_mem (hab' g x) hx
    simpa using this⟩
  obtain ⟨φ, hφ1, -, hφn, M, hM⟩ := exists_selfTwist (r.comp H.subtype) (H'.subgroupOf H) hab'
    (fun U hU => h0.2.2 U le_top fun g v hv => hU g trivial v hv)
    (fun h => hcon (h W fun g hg v hv => hW ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ v hv))
  have hM' : ∀ g : H, ((φ g : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) • ((M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    have := hM g trivial
    rw [Matrix.mul_smul] at this
    exact this
  have hiff : ∀ g : H, φ g = 1 ↔ (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    constructor
    · intro h
      have := hM' g
      rwa [h, Units.val_one, one_smul] at this
    · intro h
      have h1 := hM' g
      rw [← h] at h1
      haveI : NeZero n := ⟨hn⟩
      have h2 : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) ≠ 0 :=
        (M * r g).ne_zero
      exact Units.ext (smul_left_injective _ h2 (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set H) := by
    have hc : Continuous fun g : H => (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) :=
      Units.continuous_val.comp (hr.comp continuous_subtype_val)
    have : (φ.ker : Set H) = {g : H | (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M} := Set.ext fun g => hiff g
    rw [this]
    exact isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)
  haveI : NeZero n := ⟨hn⟩
  have hrg : φ.range ≤ rootsOfUnity n (Formalism.ConjugateSelfDual.Qbar l) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hφn g
  haveI : Finite φ.range := Finite.of_injective _ (Subgroup.inclusion_injective hrg)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker : Set H) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hop' : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hop
  have h1 := hio _ hop'
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)))
  have htop := (h1.2.2 (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a) le_top (by
    rintro ⟨_, g, hg, rfl⟩ v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    change (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v) =
      a • ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, (hiff g).mp hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])).resolve_left ha
  have hMa : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = a • 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a := by
      rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at this
    rw [this]; simp
  apply hφ1
  ext1 g
  exact (hiff g).mpr (by rw [hMa]; simp)
end

section

open Polynomial Formalism.ConjugateSelfDual Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix

private lemma trace_zero {k : Type} [Field k] (S T : Matrix (Fin 2) (Fin 2) k) (hT : T.det ≠ 0)
    (hS : S.charpoly.Separable) (v : Fin 2 → k) (hv : v ≠ 0) (hw : T *ᵥ v ∉ Submodule.span k {v})
    (a b c : k) (ha : S *ᵥ v = a • v) (hb : S *ᵥ (T *ᵥ v) = b • (T *ᵥ v))
    (hc : S *ᵥ (T *ᵥ (T *ᵥ v)) = c • (T *ᵥ (T *ᵥ v))) : T.trace = 0 :=
  _root_.UpperTheory.Reformulated.B.Qf25.trace_zero S T hT hS v hv hw a b c ha hb hc

private lemma line_of_not_irr {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : ¬ IsIrr ρ) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ ∀ g, ∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by
    simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank k W = 1 := by omega
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, fun h => hv (Subtype.ext h), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨_, hW g v v.2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

private lemma moves_line {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : IsIrr ρ) (v : Fin 2 → k)
    (hv : v ≠ 0) : ∃ t, (ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∉ Submodule.span k {v} := by
  by_contra hcon
  push Not at hcon
  have hinv : IsInv ρ (Submodule.span k {v}) := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hcon g)
  rcases h.2.2 _ le_top hinv with h1 | h1
  · exact hv (Submodule.span_singleton_eq_bot.mp h1)
  · have := finrank_span_singleton (K := k) hv
    rw [h1] at this
    simp at this

private lemma core {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (hirr : IsIrr ρ) (H : Subgroup Γ)
    (hN : H.Normal) (hs : ∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).charpoly.Separable)
    (hred : ¬ IsIrr (ρ.comp H.subtype)) :
    ∃ D : Γ → Prop, (∀ s ∈ H, D s) ∧ (∃ t, ¬ D t) ∧ (∀ s t, D s → ¬ D t → ¬ D (t * s)) ∧
      ∀ t, ¬ D t → (ρ t : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  obtain ⟨v, hv, hev⟩ := line_of_not_irr _ hred
  obtain ⟨s₀, hs₀, hsep⟩ := hs
  have hev' : ∀ s ∈ H, ∃ c : k, (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := fun s hs => hev ⟨s, hs⟩
  have hmul : ∀ (s t : Γ) (u : Fin 2 → k), (ρ (s * t) : Matrix (Fin 2) (Fin 2) k) *ᵥ u =
      (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ u) := by
    intro s t u
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hconj : ∀ g, ∃ c : k, (ρ s₀ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      c • ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g
    obtain ⟨c, hc⟩ := hev' _ (hN.conj_mem' s₀ hs₀ g)
    refine ⟨c, ?_⟩
    rw [← Matrix.mulVec_smul, ← hc, ← hmul, ← hmul]
    congr 3
    group
  refine ⟨fun s => (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ Submodule.span k {v}, fun s hs => ?_,
    moves_line ρ hirr v hv, fun s t hs ht hts => ht ?_, fun t ht => ?_⟩
  · obtain ⟨c, hc⟩ := hev' s hs
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv
      have := hmul s⁻¹ s v
      rw [← hc, zero_smul, Matrix.mulVec_zero] at this
      simpa using this
    simp only [hmul, ← hc, Matrix.mulVec_smul] at hts
    exact (Submodule.smul_mem_iff _ hc0).mp hts
  · obtain ⟨a, ha⟩ := hev' s₀ hs₀
    obtain ⟨b, hb⟩ := hconj t
    obtain ⟨c, hc⟩ := hconj (t * t)
    rw [hmul t t] at hc
    exact trace_zero _ _ (Matrix.GeneralLinearGroup.det_ne_zero (ρ t)) hsep v hv ht a b c ha hb hc

theorem UpperTheory.V.Sd.sIabs :
    UpperTheory.V.Sd.SIabs := by
  intro l _ _ Γ _ ρ Φ hΦ hirr hres H hN hs hred
  obtain ⟨D, hH, ⟨t₀, ht₀⟩, hmul, htr⟩ := core ρ hirr H hN hs hred
  have hneg : ∀ t, ¬ D t → ‖(Φ t : Qbar l) + 1‖ < 1 := by
    intro t ht
    have h := hres t 1
    rw [Matrix.charpoly_fin_two, htr t ht, Fin.prod_univ_two] at h
    have e : (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 0 t : Qbar l)) * (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 1 t : Qbar l)) =
        X ^ 2 - C ((Φ t : Qbar l) + 1) * X + C (Φ t : Qbar l) := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_add (f := _), map_one]
      ring
    rw [e] at h
    simpa [coeff_X_pow, coeff_C, coeff_one] using h
  have hpos : ∀ s, D s → ‖(Φ s : Qbar l) - 1‖ < 1 := by
    intro s hs
    have h1 := hneg _ ht₀
    have h2 := hneg _ (hmul s t₀ hs ht₀)
    rw [map_mul, Units.val_mul] at h2
    have e : (Φ t₀ : Qbar l) * ((Φ s : Qbar l) - 1) = ((Φ t₀ : Qbar l) * Φ s + 1) + (-((Φ t₀ : Qbar l) + 1)) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max ((Φ t₀ : Qbar l) * Φ s + 1) (-((Φ t₀ : Qbar l) + 1))
    rw [← e, norm_mul, hΦ, one_mul, norm_neg] at h3
    exact h3.trans_lt (max_lt h2 h1)
  refine ⟨fun s hs => by simpa [Cong] using hpos s (hH s hs), fun s => ?_⟩
  have e : ((Φ s ^ 2 : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((Φ s : Qbar l) + 1) * ((Φ s : Qbar l) - 1) := by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; ring
  have p1 : ‖(Φ s : Qbar l) + 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) 1
    simpa [hΦ] using this
  have p2 : ‖(Φ s : Qbar l) - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) (-1)
    simpa [hΦ, sub_eq_add_neg] using this
  rw [Cong, e, norm_mul]
  by_cases hs : D s
  · exact mul_lt_one_of_nonneg_of_lt_one_right p1 (norm_nonneg _) (hpos s hs)
  · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hneg s hs) p2
end

section

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k c} {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : Sd.IsHol k c ω φ) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ.cent, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem qdet2 {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

theorem UpperTheory.V.Sd.holCap :
    UpperTheory.V.Sd.HolCap := by
  intro F _ _ _ k c ω hω φ hφ
  refine ⟨by simpa using lie_scalar hω hφ 1, fun v u => ?_⟩
  have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
    classical
    rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have := casimir _ (TR.glRel_Eop v) k φ h0 (hφ.wt v) (hφ.low v) u
  rw [← this, TR.cap]
  norm_num
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd

private theorem charpoly_smul' {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by field_simp⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, mul_sub]

private theorem scaleRoots_prod' {K ι : Type} [Field K] (m : Finset ι) (a : ι → K) (s : K) :
    (∏ j ∈ m, (X - C (a j))).scaleRoots s = ∏ j ∈ m, (X - C (a j * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp [one_scaleRoots]
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

private theorem sub_le' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

private theorem prod_cong {K ι : Type} [NormedField K] [IsUltrametricDist K] (m : Finset ι) (a b : ι → K)
    (ha : ∀ j, ‖a j‖ ≤ 1) (hab : ∀ j, ‖b j - a j‖ < 1) :
    ∀ i, ‖(∏ j ∈ m, (X - C (a j))).coeff i‖ ≤ 1 ∧
      ‖(∏ j ∈ m, (X - C (a j))).coeff i - (∏ j ∈ m, (X - C (b j))).coeff i‖ < 1 := by
  classical
  induction m using Finset.induction_on with
  | empty =>
    intro i
    simp only [Finset.prod_empty, sub_self, norm_zero, zero_lt_one, and_true, coeff_one]
    split_ifs <;> simp
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set p := ∏ j ∈ m, (X - C (a j))
    set q := ∏ j ∈ m, (X - C (b j))
    have hb : ‖b j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (b j - a j) (a j)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hab j).le (ha j))
    have h1 : ∀ i, ‖a j * p.coeff i‖ ≤ 1 := fun i => by
      rw [norm_mul]; exact mul_le_one₀ (ha j) (norm_nonneg _) (ih i).1
    have h2 : ∀ i, ‖a j * p.coeff i - b j * q.coeff i‖ < 1 := fun i => by
      have e : a j * p.coeff i - b j * q.coeff i = b j * (p.coeff i - q.coeff i) - (b j - a j) * p.coeff i := by ring
      rw [e]
      refine (sub_le' _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) (ih i).2
      · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hab j) (ih i).1
    intro i
    cases i with
    | zero =>
      simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub, norm_neg]
      refine ⟨h1 0, ?_⟩
      rw [neg_sub_neg, norm_sub_rev]
      exact h2 0
    | succ i =>
      simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      refine ⟨(sub_le' _ _).trans (max_le (ih i).1 (h1 _)), ?_⟩
      rw [sub_sub_sub_comm]
      exact (sub_le' _ _).trans_lt (max_lt (ih i).2 (h2 _))

theorem UpperTheory.V.Sd.shapeFacts :
    UpperTheory.V.Sd.ShapeFacts := by
  intro l _ Γ _ n r δ
  have conj : ∀ (g : GL (Fin n) (Qbar l)) (s : Γ), ((g * tw r δ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      (δ s : Qbar l) • ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := fun g s => by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro H χ ⟨g, hg⟩
    refine ⟨g, fun s hs => ?_⟩
    rw [conj, hg s hs, ← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [mul_comm]
  · rintro H χ χ' e ⟨g, hg⟩ h
    let P : GL (Fin n) (Qbar l) := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
    refine ⟨P * g, fun s hs => ?_⟩
    have e1 : P * g * r s * (P * g)⁻¹ = P * (g * r s * g⁻¹) * P⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul P, hg s hs]
    change e.toPEquiv.toMatrix * _ * e.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [Matrix.diagonal_apply, h i s hs]
  · rintro H κ ⟨g, hg⟩
    refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [conj, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
    · rw [conj, Matrix.smul_apply, (hg s).2 i]
      simp [mul_comm]
  · intro χ hδ h s i
    have e1 : ∏ j, (X - C (((χ j * δ) s : (Qbar l)ˣ) : Qbar l)) = (∏ j, (X - C (χ j s : Qbar l))).scaleRoots (δ s) := by
      rw [scaleRoots_prod']; simp
    have e2 : (∏ j, (X - C (χ j s : Qbar l))).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
    rw [e1, tw_val, charpoly_smul' _ (Units.ne_zero _), coeff_scaleRoots, coeff_scaleRoots, e2,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← sub_mul, norm_mul, norm_pow, hδ, one_pow, mul_one]
    exact h s i
  · intro χ χ' e hχ h hc s i
    have h1 := h s i
    rw [← Equiv.prod_comp e fun j => (X - C (χ j s : Qbar l))] at h1
    have h2 := (prod_cong Finset.univ (fun j => (χ (e j) s : Qbar l)) (fun j => (χ' j s : Qbar l))
      (fun j => (hχ _ _).le) (fun j => hc j s) i).2
    rw [← sub_add_sub_cancel _ ((∏ j, (X - C (χ (e j) s : Qbar l))).coeff i)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  · intro hr
    have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : Qbar l)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
end

section

theorem UpperTheory.V.Sd.finCoef :
    UpperTheory.V.Sd.FinCoef := by
  intro l _ Γ _ _ _ _ _ n r hr
  exact GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ n r
    fun i j => (Units.continuous_val.comp hr).matrix_elem i j
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem cong_iff (a : c.Oˣ) :
    Cong (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom a) 1 ↔ residue c.O a = 1 := by
  rw [← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c _).2]
  rfl

end SlopeTestRemainingChoices
end
