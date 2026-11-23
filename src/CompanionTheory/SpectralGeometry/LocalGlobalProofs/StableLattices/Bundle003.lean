module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle002
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add (f := _), ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by

      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩

    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add (f := _), map_add (f := _), hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
end
end

section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_isDelta (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    [CharZero L] (s : L →+* L) (hs : IsInv s) : ∃ δ, IsDelta s δ := by
  obtain ⟨hss, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have h2pos : 0 < ‖(2 : L)‖ := norm_pos_iff.2 h2
  have h2le : ‖(2 : L)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : L) 1
    rw [one_add_one_eq_two] at this
    simpa using this
  have htr : ∀ y : L, ‖y‖ ≤ 1 → ‖y + s y‖ ≤ 1 := fun y hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy (by rw [hn]; exact hy))

  let I : Set L := {a | ∀ x : L, ‖x‖ ≤ 1 → ‖a * x + s (a * x)‖ ≤ 1}
  have h1I : (1 : L) ∈ I := fun x hx => by simpa using htr x hx
  have hclosed : IsClosed I := by
    have : I = ⋂ (x : L) (_ : ‖x‖ ≤ 1), {a : L | ‖a * x + s (a * x)‖ ≤ 1} := by
      ext a; simp [I]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    have hm : Continuous fun a : L => a * x := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨p, hp⟩ := NormedField.exists_one_lt_norm L
  obtain ⟨N, hNdef⟩ : ∃ N : L, N = p * s p := ⟨_, rfl⟩
  have hNfix : s N = N := by rw [hNdef, map_mul, hss, mul_comm]
  have hN1 : 1 < ‖N‖ := by
    rw [hNdef, norm_mul, hn]
    nlinarith
  have hbound : ∀ a ∈ I, ‖a‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have hNle : ‖N‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      nlinarith [norm_nonneg N]
    have ha1 : 1 ≤ ‖a‖ := by linarith
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ha1 hN1
    have a0 : a ≠ 0 := by
      rintro rfl
      simp at ha1
      linarith
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 a0
    have hx : ‖N ^ k / a‖ ≤ 1 := by
      rw [norm_div, norm_pow]
      exact (div_le_one hapos).2 hk1
    have h3 := ha _ hx
    have h4 : a * (N ^ k / a) = N ^ k := by field_simp
    rw [h4, map_pow, hNfix, ← two_mul, norm_mul, norm_pow] at h3
    have h5 : ‖N‖ ^ k ≤ 1 / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      linarith
    have h6 : ‖N‖ ^ (k + 1) ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [pow_succ, div_eq_mul_one_div ‖N‖, mul_comm]
      exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    linarith
  have hIc : IsCompact I :=
    (isCompact_closedBall (0 : L) (‖N‖ / ‖(2 : L)‖)).of_isClosed_subset hclosed
      (fun a ha => by simpa using hbound a ha)
  obtain ⟨δ, hδ, hmax⟩ := hIc.exists_isMaxOn ⟨1, h1I⟩ continuous_norm.continuousOn
  have hmax' : ∀ a ∈ I, ‖a‖ ≤ ‖δ‖ := fun a ha => hmax ha
  have hδ1 : 1 ≤ ‖δ‖ := by simpa using hmax' 1 h1I
  have δ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ1
    linarith
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.2 δ0

  have hf : Continuous fun x : L => ‖x * δ + s (x * δ)‖ := by
    have hm : Continuous fun a : L => a * δ := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨x₀, hx₀, hx₀max⟩ := (isCompact_closedBall (0 : L) 1).exists_isMaxOn
    ⟨0, by simp⟩ hf.continuousOn
  have hx₀' : ‖x₀‖ ≤ 1 := by simpa using hx₀
  have hfmax : ∀ x : L, ‖x‖ ≤ 1 → ‖x * δ + s (x * δ)‖ ≤ ‖x₀ * δ + s (x₀ * δ)‖ := fun x hx =>
    hx₀max (by simpa using hx)
  obtain ⟨m, hm⟩ : ∃ m : L, m = x₀ * δ + s (x₀ * δ) := ⟨_, rfl⟩
  rw [← hm] at hfmax
  have hmfix : s m = m := by rw [hm, map_add (f := _), hss, add_comm]
  have hm1 : ‖m‖ ≤ 1 := by
    rw [hm, mul_comm]
    exact hδ x₀ hx₀'
  have hm0 : m ≠ 0 := by
    have hx : ‖δ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hδ1
    have h3 := hfmax _ hx
    have h4 : δ⁻¹ * δ = 1 := inv_mul_cancel₀ δ0
    rw [h4, map_one, one_add_one_eq_two] at h3
    intro h
    rw [h, norm_zero] at h3
    linarith
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  have hmeq : ‖m‖ = 1 := by
    by_contra hne
    have hlt : ‖m‖ < 1 := lt_of_le_of_ne hm1 hne
    have hI' : δ / m ∈ I := by
      intro x hx
      have h3 : δ / m * x + s (δ / m * x) = (x * δ + s (x * δ)) / m := by
        rw [map_mul, map_div₀, hmfix, map_mul]
        field_simp
      rw [h3, norm_div]
      exact (div_le_one hmpos).2 (hfmax x hx)
    have h4 := hmax' _ hI'
    rw [norm_div, div_le_iff₀ hmpos] at h4
    nlinarith
  refine ⟨δ, δ0, fun a => ⟨fun ha => hmax' a ha, fun ha x hx => ?_⟩, x₀ / m, ?_, ?_⟩
  · have h3 : a * x = δ * (a / δ * x) := by field_simp
    rw [h3]
    refine hδ _ ?_
    rw [norm_mul, norm_div]
    exact mul_le_one₀ ((div_le_one hδpos).2 ha) (norm_nonneg _) hx
  · rw [norm_div, hmeq, div_one]
    exact hx₀'
  · have h3 : x₀ / m * δ + s (x₀ / m * δ) = (x₀ * δ + s (x₀ * δ)) / m := by
      rw [map_mul, map_div₀, hmfix, map_mul]
      field_simp
    rw [h3, ← hm, div_self hm0]

theorem stDelta : StDelta := fun L _ _ _ _ s hs => exists_isDelta L s hs

end GlobalTheory.CompanionTheory.RgFl
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Lattice

open CompanionTheory.Rg.FlB
open scoped NormedField Valued

theorem exists_common_denom {L ι : Type} [Field L] (O : Subring L)
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) (s : Finset ι) (g : ι → L) :
    ∃ d : O, (d : L) ≠ 0 ∧ ∀ i ∈ s, (d : L) * g i ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i s _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, ha, hi⟩ := hfrac (g i)
    refine ⟨a * d, by simp [ha, hd], fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem d.2 hi
    · have : ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem a.2 (h j hj)

theorem exists_basis_of_pid {L V : Type} [Field L] [AddCommGroup V] [Module L V] (O : Subring L)
    [IsPrincipalIdealRing O]
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) {m : ℕ}
    (b : Module.Basis (Fin m) L V) (Λ : AddSubgroup V) (c : L) (hc : c ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ i, b.repr (c • x) i ∈ O) (hspan : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ)
    (hO : ∀ a ∈ O, ∀ x ∈ Λ, a • x ∈ Λ) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) L V), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ O := by
  classical

  let ψ : (Fin m → O) →ₗ[O] V :=
    { toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j
      map_add' := fun y z => by
        simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          Subring.coe_mul, mul_smul]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  have hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j := fun _ => rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    rw [hψ] at hy
    have h0 : ∑ j, (y j : L) • b j = 0 := (smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0
    exact funext fun j => Subtype.ext (this j)
  let N : Submodule O (Fin m → O) :=
    { carrier := {y | ψ y ∈ Λ}
      add_mem' := fun {y z} hy hz => by
        simpa [map_add (f := _)] using Λ.add_mem hy hz
      zero_mem' := by simp [Λ.zero_mem]
      smul_mem' := fun a y hy => by
        simpa [map_smul, Subring.smul_def] using hO a a.2 _ hy }
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin m)) N
  let v : Fin n → V := fun i => ψ (bN i : Fin m → O)
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (bN i).2

  have hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i := by
    intro z hz
    let y : Fin m → O := fun j => ⟨b.repr (c • z) j, h1 z hz j⟩
    have hy : ψ y = z := by
      rw [hψ]
      have : ∑ j, (y j : L) • b j = c • z := b.sum_repr (c • z)
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hyN : y ∈ N := by
      change ψ y ∈ Λ
      rwa [hy]
    refine ⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩
    have h2 := congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)

    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]

  have hliO : LinearIndependent O v := by
    have h3 : LinearIndependent O (fun i => (bN i : Fin m → O)) :=
      bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    exact h3.map' ψ hinj
  have hli : LinearIndependent L v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain ⟨d, hd, hdg⟩ := exists_common_denom O hfrac Finset.univ g
    have h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0 := by
      have : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j
          = (d : L) • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]
      rw [this, hg, smul_zero]
    have h5 := Fintype.linearIndependent_iff.1 hliO _ h4 i
    have h6 : (d : L) * g i = 0 := congrArg Subtype.val h5
    exact (mul_eq_zero.1 h6).resolve_left hd
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, ha, hax⟩ := hspan x
    obtain ⟨o, ho⟩ := hrep _ hax
    have hx : x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx, ho]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  refine ⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · obtain ⟨o, ho⟩ := hrep x hx
    have h7 : x = ∑ j, (o j : L) • B j := by simpa only [hB] using ho
    have h8 : B.repr x i = (o i : L) := by
      rw [h7, B.repr_sum_self]
    rw [h8]
    exact (o i).2
  · rw [← B.sum_repr x]
    exact Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)

theorem stSandwich : StSandwich := by
  intro L _ _ hp V _ _ Λ₀ Λ c ⟨m, b, hb⟩ hc hcΛ hspan hO
  have hmem : ∀ x : L, x ∈ 𝒪[L] ↔ ‖x‖ ≤ 1 := fun x => Valued.integer.mem_iff
  haveI : CompactSpace 𝒪[L] := by
    have hset : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [hmem]
    have hk : IsCompact ((𝒪[L] : Subring L) : Set L) := by
      rw [hset]
      exact isCompact_closedBall 0 1
    exact isCompact_iff_compactSpace.1 hk
  haveI : (Valued.v : Valuation L NNReal).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
    refine (Valued.v : Valuation L NNReal).isNontrivial_iff_exists_lt_one.2 ⟨x, ?_, ?_⟩
    · simpa using hx0
    · simpa [← NNReal.coe_lt_coe] using hx1
  haveI : IsDiscreteValuationRing 𝒪[L] := Valued.integer.isDiscreteValuationRing_of_compactSpace
  have hfrac : ∀ x : L, ∃ a : 𝒪[L], (a : L) ≠ 0 ∧ (a : L) * x ∈ 𝒪[L] := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · exact ⟨1, by simp, by simpa using (hmem x).2 hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hlt : 1 < ‖x‖ := not_le.1 hx
      refine ⟨⟨x⁻¹, (hmem _).2 ?_⟩, by simpa using hx0, ?_⟩
      · rw [norm_inv]
        exact inv_le_one_of_one_le₀ hlt.le
      · simp [hx0, one_mem]
  obtain ⟨n, B, hB⟩ := exists_basis_of_pid 𝒪[L] hfrac b Λ c hc
    (fun x hx i => (hmem _).2 ((hb _).1 (hcΛ x hx) i)) hspan
    (fun a ha x hx => hO a ((hmem a).1 ha) x hx)
  exact ⟨n, B, fun x => (hB x).trans (forall_congr' fun i => hmem _)⟩

end GlobalTheory.CompanionTheory.Lattice
end
end

section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.LocalHensel

theorem stHensel_holds : StHensel := by
  intro L _ _ _ s hs c d hsc hsd hc hd
  obtain ⟨-, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have hXc : IsClosed {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    (isClosed_eq hcont continuous_id).inter (isClosed_le continuous_norm continuous_const)
  haveI : CompleteSpace {u : L | s u = u ∧ ‖u‖ ≤ 1} := hXc.completeSpace_coe
  haveI : Nonempty {u : L | s u = u ∧ ‖u‖ ≤ 1} := ⟨⟨0, map_zero s, by simp⟩⟩
  have hmaps : ∀ u : L, s u = u ∧ ‖u‖ ≤ 1 → s (-d - c * u ^ 2) = -d - c * u ^ 2 ∧
      ‖-d - c * u ^ 2‖ ≤ 1 := by
    rintro u ⟨hu, hu1⟩
    refine ⟨by simp only [map_sub, map_neg, map_mul, map_pow, hu, hsc, hsd], ?_⟩
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simpa using hd) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h2 : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    exact mul_le_one₀ hc.le (by positivity) h2
  let F : {u : L | s u = u ∧ ‖u‖ ≤ 1} → {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    fun u => ⟨-d - c * (u : L) ^ 2, hmaps u u.2⟩
  have hF : ContractingWith ‖c‖₊ F := by
    refine ⟨by exact_mod_cast hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxy : ‖(x : L) + y‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le x.2.2 y.2.2)
    have key : (-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)
        = -(c * (((x : L) + y) * ((x : L) - y))) := by ring
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖(-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)‖ ≤ _
    rw [key, norm_neg, norm_mul, norm_mul, coe_nnnorm]
    have h0 : 0 ≤ ‖(x : L) - y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left h0 hxy) (norm_nonneg _)
  have hfix := hF.fixedPoint_isFixedPt
  set u := ContractingWith.fixedPoint F hF with hu
  have hval : -d - c * (u : L) ^ 2 = u := congrArg Subtype.val hfix
  refine ⟨u, u.2.1, u.2.2, ?_⟩
  linear_combination -hval

end GlobalTheory.CompanionTheory.LocalHensel
end

section


theorem _root_.GlobalTheory.T.compact_subgroup_finite_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  first | exact @GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | exact GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | (intros; apply GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover <;> assumption)
end
