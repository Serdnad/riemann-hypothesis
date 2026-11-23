module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
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
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown

@[expose] public section

section

open GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.CuspFin.One

private noncomputable def lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    gl n →ₗ[ℂ] A where
  toFun X := ∑ a : Fin n × Fin n, X a.1 a.2 • F a.1 a.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

private theorem lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (a : Fin n × Fin n) :
    lin F (E a) = F a.1 a.2 := by
  obtain ⟨i, j⟩ := a
  show ∑ b : Fin n × Fin n, (E (i, j)) b.1 b.2 • F b.1 b.2 = F i j
  rw [Finset.sum_eq_single (i, j)]
  · simp [E]
  · rintro ⟨k, l⟩ _ hb
    have : ¬ (i = k ∧ j = l) := fun h => hb (by rw [h.1, h.2])
    simp [E, Matrix.single_apply, this]
  · simp

private theorem lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : gl n) : lin F ⁅X, Y⁆ = ⁅lin F X, lin F Y⁆ := by
  have hE : ∀ a b : Fin n × Fin n, lin F ⁅E a, E b⁆ = ⁅lin F (E a), lin F (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul, lin_E, lin_E,
      hF, map_sub]
    congr 1 <;> split_ifs <;> simp_all [lin_E]
  rw [eq_sum_E X, eq_sum_E Y]

  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private noncomputable def lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : gl n →ₗ⁅ℂ⁆ A :=
  { lin F with map_lie' := fun {X Y} => lin_lie F hF X Y }

end UpperTheory.V.Af.CuspFin.One

open UpperTheory.V.Af.CuspFin UpperTheory.V.Af.CuspFin.One in
theorem UpperTheory.glRelations_hasUniversalProperty :
    ∀ n : ℕ, UpperTheory.V.Af.CuspFin.HasUniv Unit n := by
  intro n
  refine ⟨U n, inferInstance, inferInstance, fun _ i j => e (i, j), ⟨fun _ => ?_, fun v v' h => (h rfl).elim⟩,
    ?_, fun A _ _ E' hE => ?_, ?_⟩
  · intro i j k l
    rw [e_mul_sub_mul]
  · refine eq_top_iff.2 fun u hu => ?_
    clear hu
    induction u using U.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X =>
      rw [ι_eq_sum_e]
      refine Subalgebra.sum_mem _ fun a _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      exact ⟨(), a.1, a.2, rfl⟩
    | hmul a b ha hb => exact Subalgebra.mul_mem _ ha hb
    | hadd a b ha hb => exact Subalgebra.add_mem _ ha hb
  · refine ⟨UniversalEnvelopingAlgebra.lift ℂ (lie (E' ()) (hE.1 ())), fun v i j => ?_⟩
    rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact lin_E (E' ()) (i, j)
  · refine (UpperTheory.center_envelopingGL_le_adjoin_quantumDet n).trans (Algebra.adjoin_mono ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨(), u, rfl⟩
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem comap_relIndex_ne_zero {G H : Type} [Group G] [Group H] (p : G →* H) (A B : Subgroup H)
    (T : Subgroup G) (hAB : A.relIndex B ≠ 0) (hT : ∀ g ∈ T, p g ∈ B) : (A.comap p).relIndex T ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h
  exact hAB (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.mpr hT) h)

private theorem finset_relIndex_ne_zero {G I : Type} [Group G] (H : I → Subgroup G) (T : Subgroup G) (S : Finset I)
    (h : ∀ v ∈ S, (H v).relIndex T ≠ 0) : ∃ W : Subgroup G, W.relIndex T ≠ 0 ∧ ∀ v ∈ S, W ≤ H v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨W, hW, hWS⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    refine ⟨H a ⊓ W, Subgroup.relIndex_inf_ne_zero (h a (Finset.mem_insert_self a S)) hW, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact inf_le_left
    · exact inf_le_right.trans (hWS v hv)

theorem UpperTheory.orbitalFiber_level_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.LevFin := by
  unfold Fib.LevFin
  intro F _ _ Δ D hD
  have hDet : Fib.DetOne := UpperTheory.orbitalFiber_det_eq_one
  unfold Fib.DetOne at hDet
  set P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) with hP
  have hle : ∀ v, D.J2v v ≤ KD ((cv v) Δ) (Ov v) := by
    intro v
    rw [Dat.J2v.eq_1]
    split_ifs with hv
    · exact SigOk.levelTwoLeIntegral (hD.sig v hv)
    · exact le_rfl
  have hT : ∀ v, ∀ g ∈ D.UZ ⊓ SA Δ, P.p v g ∈ KD ((cv v) Δ) (Ov v) := by
    intro v g hg
    have h1 : g ∈ D.UZ := hg.1
    have h2 : g ∈ SA Δ := hg.2
    rw [Dat.UZ.eq_1, RPG.box.eq_1, Subgroup.mem_iInf] at h1
    rw [SA.eq_1, Subgroup.mem_iInf] at h2
    have a := h1 v
    have b := h2 v
    rw [Subgroup.mem_comap] at a b
    exact hDet _ _ _ _ (sup_le_sup_left (hle v) _ a) b
  have hfin : ∀ v ∈ D.Sg, ((D.J2v v).comap (P.p v)).relIndex (D.UZ ⊓ SA Δ) ≠ 0 := by
    intro v hv
    apply comap_relIndex_ne_zero (P.p v) (D.J2v v) (KD ((cv v) Δ) (Ov v))
    · rw [Dat.J2v.eq_1, if_pos hv]
      exact SigOk.levelTwoFiniteIndex (hD.sig v hv)
    · exact hT v
  obtain ⟨W, hW, hWS⟩ := finset_relIndex_ne_zero (fun v => (D.J2v v).comap (P.p v)) _ D.Sg hfin
  have hsub : W ⊓ (D.UZ ⊓ SA Δ) ≤ D.U2 := by
    intro g hg
    rw [Dat.U2.eq_1, RPG.box.eq_1, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    by_cases hv : v ∈ D.Sg
    · exact hWS v hv hg.1
    · have e := hT v g hg.2
      rw [Dat.J2v.eq_1, if_neg hv]
      exact e
  refine ⟨?_, ?_⟩
  · rw [Dat.U2.eq_1, Dat.UZ.eq_1, RPG.box.eq_1, RPG.box.eq_1]
    exact iInf_mono fun v => Subgroup.comap_mono le_sup_right
  · intro h
    apply hW
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_eq_zero_of_le_left hsub h
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

private theorem card_step {O : Type} [CommRing O] [IsDomain O] (π : O) (h0 : π ≠ 0) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {π ^ (n + 1)}) =
      Nat.card (O ⧸ Ideal.span {π ^ n}) * Nat.card (O ⧸ Ideal.span {π}) := by
  have hrange : (AddMonoidHom.mulLeft (π ^ n)).range = (Ideal.span {π ^ n}).toAddSubgroup := by
    ext r
    simp [Ideal.mem_span_singleton', mul_comm]
  have hcomap : (Ideal.span {π ^ (n + 1)}).toAddSubgroup.comap (AddMonoidHom.mulLeft (π ^ n)) =
      (Ideal.span {π}).toAddSubgroup := by
    ext r
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    show π ^ (n + 1) ∣ π ^ n * r ↔ π ∣ r
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n h0)]
  have hle : (Ideal.span {π ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {π ^ n}).toAddSubgroup := by
    intro r hr
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hr ⊢
    exact (pow_dvd_pow π (Nat.le_succ n)).trans hr
  show (Ideal.span {π ^ (n + 1)}).toAddSubgroup.index =
    (Ideal.span {π ^ n}).toAddSubgroup.index * (Ideal.span {π}).toAddSubgroup.index
  rw [← AddSubgroup.relIndex_mul_index hle, ← hcomap, AddSubgroup.index_comap, hrange, mul_comm]

theorem UpperTheory.card_quotient_span_uniformizer_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → ∀ π : O, Irreducible π → ∀ n : ℕ, Nat.card (O ⧸ Ideal.span {π ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro O K _ _ _ _ _ Δ τ hL π hπ n
  have hres : Nat.card (IsLocalRing.ResidueField O) = Nat.card (O ⧸ Ideal.span {π}) := by
    rw [← hπ.maximalIdeal_eq]
    rfl
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    show (⊤ : Ideal O).toAddSubgroup.index = 1
    simp
  | succ k ih =>
    rw [card_step π hπ.ne_zero k, ih, hres, pow_succ]
end
