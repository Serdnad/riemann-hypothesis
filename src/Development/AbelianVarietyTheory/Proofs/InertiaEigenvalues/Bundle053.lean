module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle018
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Analysis.Normed.Group.Ultra
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

namespace GlobalTheory.CloseToUnitNorm

theorem norm_eq_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (1 - u)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  apply GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption

end GlobalTheory.CloseToUnitNorm
end

section

namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩

  · rw [map_smul, map_sum, smul_comm]
    apply congrArg ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • ·)
    rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
    exact congrArg (θ h • ·) (Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j))
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]

    simp only [map_smul, map_sum, Finset.sum_apply]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
end

section

namespace GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem exists_orth_proj (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hdef : ∀ v, B v v = 0 → v = 0)
    (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | (apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj ..)

theorem rho_inv_rho (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g⁻¹ (ρ g u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_rho_inv (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g (ρ g⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem orth_stable (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (Z : Subrepresentation ρ) (s : W)
    (hs : ∀ z ∈ Z.toSubmodule, B z s = 0) (g : H) : ∀ z ∈ Z.toSubmodule, B z (ρ g s) = 0 := by
  intro z hz
  calc B z (ρ g s) = B (ρ g (ρ g⁻¹ z)) (ρ g s) := by rw [rho_rho_inv]
    _ = B (ρ g⁻¹ z) s := hinv _ _ _
    _ = 0 := hs _ (Z.apply_mem_toSubmodule _ hz)

theorem exists_compl_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) (v : W) :
    ∃ t ∈ Z.toSubmodule, ∀ z ∈ Z.toSubmodule, B z (v - t) = 0 := by
  classical
  obtain ⟨K, hvK, hfd, hfin⟩ := hadm v
  have ofF : ∀ u ∈ GlobalTheory.PRep.fixed ρ K, ∀ k ∈ K, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K, ρ k u = u) → u ∈ GlobalTheory.PRep.fixed ρ K := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  haveI : FiniteDimensional ℂ (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K : Submodule ℂ W) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨m, hmM, hm⟩ := exists_orth_proj B hdef (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K) v
  refine ⟨m, hmM.1, fun z hz => ?_⟩
  have hwK : ∀ k ∈ K, ρ k (v - m) = v - m := by
    intro k hk
    rw [map_sub, hvK k hk, ofF m hmM.2 k hk]
  set s := (hfin z).toFinset with hs
  have hmem : ∀ o ∈ s, ∃ k' : K, ρ k' z = o := by
    intro o ho
    simpa [s] using ho
  have hperm : ∀ k ∈ K, ∑ o ∈ s, ρ k o = ∑ o ∈ s, o := by
    intro k hk
    apply Finset.sum_nbij' (fun o => ρ k o) (fun o => ρ k⁻¹ o)
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩⁻¹ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o _; exact rho_inv_rho ρ k o
    · intro o _; exact rho_rho_inv ρ k o
    · intro o _; rfl
  have heZ : ∑ o ∈ s, o ∈ Z.toSubmodule := by
    refine Submodule.sum_mem _ (fun o ho => ?_)
    obtain ⟨k', rfl⟩ := hmem o ho
    exact Z.apply_mem_toSubmodule _ hz
  have heF : ∑ o ∈ s, o ∈ GlobalTheory.PRep.fixed ρ K := by
    refine memF _ (fun k hk => ?_)

    rw [map_sum, hperm k hk]
  have h0 := hm _ ⟨heZ, heF⟩
  have hterm : ∀ o ∈ s, B o (v - m) = B z (v - m) := by
    intro o ho
    obtain ⟨k', rfl⟩ := hmem o ho
    rw [← hinv k' z (v - m), hwK k' k'.2]

  rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hz1 : z ∈ s := by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, by simp⟩
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.2 ⟨z, hz1⟩
  rw [nsmul_eq_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (by exact_mod_cast h) hcard
  · exact h

def orbSpan (ρ : Representation ℂ H W) (y : W) : Subrepresentation ρ :=
  ⟨Submodule.span ℂ (Set.range fun g => ρ g y), by
    intro g v hv
    have hle : (Submodule.span ℂ (Set.range fun g => ρ g y)).map (ρ g) ≤
        Submodule.span ℂ (Set.range fun g => ρ g y) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hv)⟩

theorem mem_orbSpan (ρ : Representation ℂ H W) (y : W) : y ∈ (orbSpan ρ y).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbSpan_le (ρ : Representation ℂ H W) (y : W) (Z : Subrepresentation ρ)
    (hy : y ∈ Z.toSubmodule) : (orbSpan ρ y).toSubmodule ≤ Z.toSubmodule :=
  Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact Z.apply_mem_toSubmodule g hy)

end GlobalTheory.UnitarySemisimple

namespace GlobalTheory.UnitarySemisimple

end GlobalTheory.UnitarySemisimple
end

section

open GlobalTheory.JR Matrix

namespace GlobalTheory

theorem mul_star_anisotropic_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  intro F E _ _ _ _ hU r V hV B hB
  letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup
  letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _
  have hsE : Continuous (star : E → E) :=
    AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])
  haveI : ContinuousStar E := ⟨hsE⟩
  have hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z :=
    continuous_id.mul continuous_star
  have hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z) := by
    intro d z
    rw [star_smul, smul_mul_smul_comm]
  have hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2 := by
    intro d; rw [norm_mul, hU.norm_star, sq]
  have hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E)) := Submodule.closed_of_finiteDimensional V
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm E
  set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    · exact (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset
        (fun w hw => by simpa using hw.2.2)
  have hkpos : 0 < ‖k‖⁻¹ := inv_pos.mpr (lt_trans one_pos hk)
  have hA0 : ∀ w ∈ A, 0 < ‖w * star w‖ := by
    intro w hw
    apply norm_pos_iff.mpr
    intro h0
    have := hV w hw.1 h0
    have h1 := hw.2.1
    rw [this, norm_zero] at h1
    linarith
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by
    rcases A.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hAc.exists_isMinOn hne (hQc.norm.continuousOn)
      exact ⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := (hB.isBounded).subset_closedBall 0
  apply Metric.isCompact_of_isClosed_isBounded
  · exact hVc.inter (hB.isClosed.preimage hQc)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hQR : ‖z * star z‖ ≤ |R| := by
      have := hR hz.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact Real.sqrt_nonneg _
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hz0
    have hdA : d • z ∈ A := ⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩
    have h1 := hc _ hdA
    rw [hQs, norm_smul, hnd] at h1
    rw [norm_smul] at hd1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0

    have hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1 := by
      have : 0 ≤ ‖d‖ * ‖z‖ := by positivity
      nlinarith
    have hQ0 : 0 ≤ ‖z * star z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.InverseCompactOpen

theorem inv_exists_compact_open (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F)
    (hU : IsOpen U) (ha : a₀ ∈ U) :
    ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  have hUn : Unram F E := inferInstance
  haveI : LocallyCompactSpace F := hUn.lcF
  haveI : IsUltrametricDist F := hUn.ultraF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU a₀ ha
  have hε2 : 0 < ε / 2 := half_pos hε
  refine ⟨Metric.closedBall a₀ (ε / 2), isCompact_closedBall _ _, ?_,
    Metric.mem_closedBall_self hε2.le, ?_⟩
  · have hpi : ∀ x : Fin r → F, IsOpen (Metric.closedBall x (ε / 2)) := by
      intro x
      rw [closedBall_pi x hε2.le]
      exact isOpen_set_pi Set.finite_univ
        (fun i _ => IsUltrametricDist.isOpen_closedBall (x i) hε2.ne')
    obtain ⟨p, q, l⟩ := a₀
    rw [← closedBall_prod_same, ← closedBall_prod_same]
    exact (hpi p).prod ((hpi q).prod (IsUltrametricDist.isOpen_closedBall l hε2.ne'))
  · exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball

end GlobalTheory.InverseCompactOpen
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem isTest_nhds_inv : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ),
    IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  intro X _ _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hK : IsCompact (tsupport f) := hcs
  have key : ∀ᶠ u in 𝓝 (0 : X), ∀ y ∈ tsupport f, f (y + u) = f y := by
    refine hK.eventually_forall_of_forall_eventually (P := fun u y => f (y + u) = f y) ?_
    intro y _
    have hy : ∀ᶠ z in 𝓝 y, f z = f y := (IsLocallyConstant.iff_eventually_eq f).1 hlc y
    have hc : Filter.Tendsto (fun p : X × X => p.2 + p.1) (𝓝 ((0 : X), y)) (𝓝 y) := by
      have hcont : Continuous fun p : X × X => p.2 + p.1 := continuous_snd.add continuous_fst
      have := hcont.tendsto ((0 : X), y)
      simpa only [add_zero] using this
    have h2 : Filter.Tendsto (fun p : X × X => p.2) (𝓝 ((0 : X), y)) (𝓝 y) :=
      (continuous_snd.tendsto ((0 : X), y))
    filter_upwards [hc.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have hneg : Filter.Tendsto (fun u : X => -u) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : X))
  refine ⟨{u | ∀ y ∈ tsupport f, f (y + u) = f y} ∩ (fun u : X => -u) ⁻¹' {u | ∀ y ∈ tsupport f, f (y + u) = f y},
    Filter.inter_mem key (hneg key), ?_⟩
  rintro x u ⟨h1, h2⟩
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  by_cases hxu : x + u ∈ tsupport f
  · have := h2 (x + u) hxu
    simp only [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory
end
