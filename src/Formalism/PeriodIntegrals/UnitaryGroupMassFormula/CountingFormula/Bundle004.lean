module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle001
public import Formalism.HermitianLattices.StatementLat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle071
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomMove
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle003
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

open NumberField Module

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}

def PairUnit (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ w y : V, h y w = 1 → h w w ∈ S → h y y ∈ S →
    ∃ c ∈ S, ∃ d ∈ S, IsUnitIn S (h (c • w + d • y) (c • w + d • y))

theorem linIndep_orth {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) : LinearIndependent K x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (h (x j)) hc

  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (hx0 j)
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

theorem orth_sub_proj {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) (v : V) (j : ι) :
    h (x j) (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
  classical

  rw [map_sub, map_sum, Finset.sum_eq_single j]
  · rw [map_smul, smul_eq_mul, mul_right_comm, inv_mul_cancel₀ (hx0 j), one_mul, sub_self]
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

theorem exists_ortho_unit [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) :=
  _root_.UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit hS hs hnd hPU hL

theorem exists_isom_frameU (hS : IsHermSemilocal S) (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {n : ℕ} (x : Fin n → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (x i) ∈ M := by
  classical
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (x i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ a b, h (g a) (g b) = h a b := hg
      have hne : ∀ i : Fin n, i.val < k → i ≠ ⟨k, hk⟩ := by
        intro i hi e
        rw [e] at hi
        exact lt_irrefl _ hi
      let y : {i : Fin n // i.val < k} → V := fun i => g (x i.1)
      have hyo : ∀ i j : {i : Fin n // i.val < k}, i ≠ j → h (y i) (y j) = 0 := by
        intro i j hij
        simp only [y]
        rw [hg']
        exact hxo _ _ (fun e => hij (Subtype.ext e))
      have hyu : ∀ i : {i : Fin n // i.val < k}, IsUnitIn S (h (y i) (y i)) := by
        intro i
        simp only [y]
        rw [hg']
        exact hxu _
      have hyM : ∀ i : {i : Fin n // i.val < k}, y i ∈ M := fun i => hgM i.1 i.2
      have hu := hxu ⟨k, hk⟩
      have hus : star (h (x ⟨k, hk⟩) (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := star_h hs _ _
      have hrr : h (g (x ⟨k, hk⟩)) (g (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := hg' _ _
      have hrx : ∀ i : {i : Fin n // i.val < k}, h (y i) (g (x ⟨k, hk⟩)) = 0 := by
        intro i
        simp only [y]
        rw [hg']
        exact hxo _ _ (hne i.1 i.2)
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_of_ref hS hs hM y hyo hyu hyM hu hus hrr hrx
      obtain ⟨τ, hτ, hτr, hτfix⟩ := exists_isom_move hS hs hu.1 hus hrr hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (x i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hg']
          exact hxo _ _ (fun e => hne i h1 e.symm)
        · rw [← star_h hs]
          have := hzo ⟨i, h1⟩
          simp only [y] at this
          rw [this, star_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτr]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

theorem exists_isom_selfDual [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L M : AddSubgroup V} (hL : IsSelfDualMod S h L)
    (hM : IsSelfDualMod S h M) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, v ∈ L ↔ g v ∈ M := by
  classical
  obtain ⟨x, hxL, hxo, hxu⟩ := exists_ortho_unit hS hs hnd hPU hL
  obtain ⟨g, hg, hgM⟩ := exists_isom_frameU hS hs hM x hxo hxu
  have hg' : ∀ a b, h (g a) (g b) = h a b := hg
  have hli := linIndep_orth x hxo (fun i => (hxu i).1)
  have hspan : Submodule.span K (Set.range x) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hexp : ∀ v, v = ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i := by
    intro v
    have hxv' := orth_sub_proj x hxo (fun i => (hxu i).1) v
    have hall : ∀ y, h y (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
      intro y
      have hy : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨j, rfl⟩ := ha
        exact hxv' j
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    exact sub_eq_zero.1 (hnd.2 _ hall)
  have hfwd : ∀ v, v ∈ L → g v ∈ M := by
    intro v hv

    rw [hexp v, map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul]
    exact hM.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hv)) _ (hgM i)
  refine ⟨g, hg, fun v => ⟨hfwd v, fun hv => hL.dual v fun m hm => ?_⟩⟩
  rw [← hg']
  exact hM.int _ (hfwd m hm) _ hv

end Abs

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_ic_free {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) :
    Module.Free 𝒪[F] (integralClosure 𝒪[F] E) ∧ Module.Finite 𝒪[F] (integralClosure 𝒪[F] E) ∧
      Module.finrank 𝒪[F] (integralClosure 𝒪[F] E) = 2 := by
  haveI := hl
  haveI := hc
  have hnt : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := L.rank
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  letI : Field E := (show IsField E from
    ⟨exists_pair_ne E, mul_comm, fun {x} hx => (hE x hx).exists_right_inv⟩).toField
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ L.rank
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : Module.IsTorsionFree 𝒪[F] E := FaithfulSMul.to_isTorsionFree _ E
    refine ⟨IsIntegralClosure.module_free 𝒪[F] F E (integralClosure 𝒪[F] E),
      IsIntegralClosure.finite 𝒪[F] F E (integralClosure 𝒪[F] E), ?_⟩
    rw [IsIntegralClosure.rank 𝒪[F] F E (integralClosure 𝒪[F] E), L.rank]

theorem fr_card {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 := by
  classical
  haveI := hl
  obtain ⟨hfree, hfin, hrank⟩ := fr_ic_free L hl hc hE
  set A := integralClosure 𝒪[F] E with hA

  have hOA : L.O = A.toSubring := by
    ext x
    rw [L.O_def]
    rfl
  let e : L.O ≃+* A.toSubring := RingEquiv.subringCongr hOA

  let b : Module.Basis (Fin 2) 𝒪[F] A := (Module.finBasisOfFinrankEq 𝒪[F] A hrank)

  let πA : A := algebraMap 𝒪[F] A ϖ
  have hmemI : ∀ x : A, x ∈ (Ideal.span {πA} : Ideal A) ↔ ∃ y : A, x = ϖ • y := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
  let I' : Submodule 𝒪[F] A := (Ideal.span {πA} : Ideal A).restrictScalars 𝒪[F]
  let P : Submodule 𝒪[F] (Fin 2 → 𝒪[F]) := Submodule.pi Set.univ fun _ => Ideal.span {ϖ}
  have hmap : I'.map (b.equivFun : A →ₗ[𝒪[F]] (Fin 2 → 𝒪[F])) = P := by
    ext v
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, P, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      obtain ⟨y, rfl⟩ := (hmemI x).mp hx
      exact ⟨b.equivFun y i, by rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]⟩
    · intro h
      choose w hw using h
      refine ⟨ϖ • b.equivFun.symm w, (hmemI _).mpr ⟨_, rfl⟩, ?_⟩
      funext i
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, ← hw i,
        mul_comm]
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  calc Nat.card (L.O ⧸ Ideal.span {piO L ϖ})
      = Nat.card (A.toSubring ⧸ Ideal.span {e (piO L ϖ)}) := by
        apply Nat.card_congr
        refine (Ideal.quotientEquiv _ _ e ?_).toEquiv
        rw [Ideal.map_span, Set.image_singleton]
        rfl
    _ = Nat.card (A ⧸ (Ideal.span {πA} : Ideal A)) := by
        rfl
    _ = Nat.card (A ⧸ I') := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv.symm
    _ = Nat.card ((Fin 2 → 𝒪[F]) ⧸ P) := by
        apply Nat.card_congr
        rw [← hmap]
        exact (Submodule.Quotient.equiv I' _ b.equivFun rfl).toEquiv
    _ = Nat.card (Fin 2 → 𝒪[F] ⧸ Ideal.span {ϖ}) := Nat.card_congr (Submodule.quotientPi _).toEquiv
    _ = Nat.card (𝒪[F] ⧸ Ideal.span {ϖ}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_fin]
    _ = Nat.card 𝓀[F] ^ 2 := by
        congr 1
        apply Nat.card_congr
        exact (Ideal.quotEquivOfEq hmax).toEquiv.symm

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_main {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hnt : Nontrivial E)
    (hden : ∀ x : E, ∃ s ∈ M.L.O, s ≠ 0 ∧ s * x ∈ M.L.O)
    (hpid : IsPrincipalIdealRing M.L.O)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) :
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1 := by
  classical
  haveI : NoZeroDivisors E := ⟨fun {a b} hab => by
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hE a hne.1
    apply hne.2
    have h2 := congrArg (fun t => (↑u⁻¹ : E) * t) hab
    simp only [mul_zero, ← mul_assoc] at h2
    rwa [← hu, Units.inv_mul, one_mul] at h2⟩
  haveI : IsDomain E := NoZeroDivisors.to_isDomain E
  obtain ⟨hfg, hspan, hdual⟩ := hΛ
  haveI : Module.Finite M.L.O Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors M.L.O Λ := ⟨fun {r x} h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
    obtain ⟨u, hu⟩ := hE _ hr'
    have h1 : (r : E) • (x : V) = 0 := by
      have := congrArg Subtype.val h
      simpa [Submodule.coe_smul, Subring.smul_def] using this
    apply Subtype.ext
    have h2 := congrArg (fun v => (↑u⁻¹ : E) • v) h1
    simp only [smul_zero, smul_smul] at h2
    rw [← hu, Units.inv_mul, one_smul] at h2
    simpa using h2⟩
  haveI : Module.Free M.L.O Λ := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis M.L.O Λ
  let bb : Module.Free.ChooseBasisIndex M.L.O Λ → V := fun i => (B i : V)
  have hexp : ∀ (x : V) (hx : x ∈ Λ), x = ∑ i, ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i := by
    intro x hx
    have h2 := congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    exact h2.symm
  have hli : LinearIndependent E bb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose s hsO hs using fun j => hden (g j)
    set t := ∏ j, s j with ht
    have htO : t ∈ M.L.O := Subring.prod_mem _ fun j _ => hsO j
    have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hs j).1
    have htg : ∀ j, t * g j ∈ M.L.O := by
      intro j
      have e : t * g j = (∏ j' ∈ Finset.univ.erase j, s j') * (s j * g j) := by
        rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        ring
      rw [e]
      exact M.L.O.mul_mem (Subring.prod_mem _ fun j' _ => hsO j') (hs j).2
    let g' : Module.Free.ChooseBasisIndex M.L.O Λ → M.L.O := fun j => ⟨t * g j, htg j⟩
    have hsum : ∑ j, g' j • B j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero]
      have : ∑ j, (t * g j) • bb j = t • ∑ j, g j • bb j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      simpa [g', bb, hg] using this
    have h0 := Fintype.linearIndependent_iff.mp B.linearIndependent g' hsum i
    have h0' : t * g i = 0 := congrArg Subtype.val h0
    exact (mul_eq_zero.mp h0').resolve_left ht0
  have hsp : ⊤ ≤ Submodule.span E (Set.range bb) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let BE := Basis.mk hli hsp
  have hcard : Module.finrank E V = Fintype.card (Module.Free.ChooseBasisIndex M.L.O Λ) :=
    Module.finrank_eq_card_basis BE
  let eι := Fintype.equivFinOfCardEq hcard.symm
  let b : Fin (Module.finrank E V) → V := fun k => bb (eι.symm k)
  have hbΛ : ∀ k, b k ∈ Λ := fun k => (B (eι.symm k)).2
  have hlib : LinearIndependent E b := hli.comp _ eι.symm.injective
  have hexpb : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧
      x = ∑ k, c k • b k := by
    intro x hx
    refine ⟨fun k => ((B.repr ⟨x, hx⟩ (eι.symm k) : M.L.O) : E), fun k => Subtype.property _, ?_⟩
    exact (hexp x hx).trans
      (Equiv.sum_comp eι.symm (fun i => ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i)).symm
  refine ⟨b, hbΛ, hlib, hexpb, ?_⟩
  set G : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E :=
    Matrix.of (fun k l => H.h (b k) (b l)) with hG
  have hdet0 : G.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    set x := ∑ k, v k • b k with hx
    have hxb : ∀ l, H.h x (b l) = 0 := by
      intro l
      rw [hx, flb_h_sum_left]
      have := congrFun hv l
      simpa [Matrix.vecMul, dotProduct, hG] using this
    have hx0 : x = 0 := by
      apply H.nondeg
      intro y
      have hy := BE.sum_repr y
      rw [← hy, flb_h_sum_right]
      apply Finset.sum_eq_zero
      intro i _
      have : BE i = b (eι i) := by simp [BE, b]
      rw [this, hxb, mul_zero]
    apply hv0
    funext k
    exact Fintype.linearIndependent_iff.mp hlib v hx0.symm.symm k
  have hdet : IsUnit G.det := hE _ hdet0
  refine ⟨G⁻¹, ?_, Matrix.nonsing_inv_mul G hdet⟩
  have hQG := Matrix.nonsing_inv_mul G hdet
  intro k m
  set d := ∑ m', G⁻¹ k m' • b m' with hd
  have hdb : ∀ l, H.h d (b l) = if k = l then 1 else 0 := by
    intro l
    rw [hd, flb_h_sum_left]
    have := congrFun (congrFun hQG k) l
    simpa [Matrix.mul_apply, hG, Matrix.one_apply] using this
  have hdΛ : d ∈ Λ := by
    rw [hdual]
    intro y hy
    obtain ⟨c, hcO, rfl⟩ := hexpb y hy
    rw [flb_h_sum_right]
    simp only [hdb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact flb_cj_mem M.L (hcO k)
  obtain ⟨c', hc'O, hc'⟩ := hexpb d hdΛ
  have hz : ∑ m', (G⁻¹ k m' - c' m') • b m' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hd, ← hc', sub_self]
  have := Fintype.linearIndependent_iff.mp hlib _ hz m
  rw [sub_eq_zero.mp this]
  exact hc'O m

theorem flatBasis_of (h1 : FLocO) : FLatBasis := by
  intro F E _ _ _ _ _ _ _ M hF hc hE V _ _ H Λ hΛ
  haveI := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hden0, hfac⟩ := h1 F E M.L hF hc hE ϖ hϖ
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  refine flb_main M hE hnt ?_ (flb_pid M.L.O _ (flb_int_mem M.L ϖ) hfac) V H Λ hΛ
  intro x
  obtain ⟨c, hc0, hcx⟩ := hden0 x
  refine ⟨_, flb_int_mem M.L c, ?_, hcx⟩
  have hcF : (c : F) ≠ 0 := by exact_mod_cast hc0
  exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hcF

end PI.UnitaryGroupMassFormula.CntFormula
end
end
