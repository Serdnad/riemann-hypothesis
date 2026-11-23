module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle004
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle040
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle001
public import Mathlib.GroupTheory.Index
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle002
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section SlopeTestRemainingChoices

variable {k H V : Type} [Field k] [Group H] [AddCommGroup V] [Module k V]

private def ecStab (T : Representation k H V) (v : V) : Subgroup H where
  carrier := {g | T g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

private theorem ec_out (T : Representation k H V) (v : V) (S : Subgroup H) (hS : S ≤ ecStab T v) (g : H) :
    T ((g : H ⧸ S).out) v = T g v := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S g
  have h : T s v = v := hS s.2
  rw [hs, map_mul, Module.End.mul_apply, h]

private theorem ec_right (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    ∑ q : H ⧸ S, T q.out (T n v) = ∑ q : H ⧸ S, T q.out v := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulRight (n : H ⧸ S) q = ((q.out * n : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

private theorem ec_left (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    T n (∑ q : H ⧸ S, T q.out v) = ∑ q : H ⧸ S, T q.out v := by

  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulLeft (n : H ⧸ S) q = ((n * q.out : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

variable {G : Type} [Group G]

private def ecTw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) : Representation k K V where
  toFun x := (((χ x)⁻¹ : kˣ) : k) • ρ x
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

private theorem ecTw_apply (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ecTw ρ K χ x v = (((χ x)⁻¹ : kˣ) : k) • ρ x v := rfl

private theorem ecTw_smul (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ρ x v = (χ x : k) • ecTw ρ K χ x v := by
  rw [ecTw_apply, smul_smul]
  simp

private theorem ec_mem_eig (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (v : V) :
    v ∈ eig ρ K χ ↔ ∀ x, ecTw ρ K χ x v = v := by
  refine forall_congr' fun x => ?_
  rw [ecTw_smul ρ K χ]
  exact smul_right_inj (χ x).ne_zero

private theorem ec_mem_tw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    v - ecTw ρ K χ x v ∈ twKer ρ K χ := by
  have h : ρ x v - (χ x : k) • v ∈ twKer ρ K χ := Submodule.subset_span ⟨x, v, rfl⟩
  have h2 := (twKer ρ K χ).smul_mem (-(((χ x)⁻¹ : kˣ) : k)) h
  convert h2 using 1
  rw [ecTw_apply, smul_sub, smul_smul]
  simp
  abel

private theorem ec_fin [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G)
    (χ : K →* kˣ) (hρ : IsSmooth ρ) (hK : IsCompact (K : Set G)) (hχ : IsOpen {x : K | χ x = 1}) (v : V) :
    (ecStab (ecTw ρ K χ) v).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen (ecStab (ecTw ρ K χ) v : Set K) := by
    have h1 : IsOpen ((fun x : K => (x : G)) ⁻¹' {g : G | ρ g v = v}) := (hρ v).preimage continuous_subtype_val
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((h1.inter hχ).mem_nhds (by simp)) ?_)
    rintro x ⟨hx1, hx2⟩
    have a : ρ x v = v := hx1
    have b : χ x = 1 := hx2
    show ecTw ρ K χ x v = v
    rw [ecTw_apply, a, b]
    simp
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

end SlopeTestRemainingChoices

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigCompl :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ), IsSmooth ρ → IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → IsCompl (eig ρ K χ) (twKer ρ K χ) ∧ ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W, ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
  intro k G V _ _ _ _ _ _ _ ρ K χ hρ hK hχ
  have hfin := ec_fin ρ K χ hρ hK hχ
  have part2 : ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W,
      ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
    intro W hW v hv
    haveI := hfin v
    set S := (ecStab (ecTw ρ K χ) v).normalCore with hSdef
    have hS : S ≤ ecStab (ecTw ρ K χ) v := Subgroup.normalCore_le _
    letI : Fintype (K ⧸ S) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ S) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨(Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v, ?_, ?_, ?_⟩
    · exact W.smul_mem _ (W.sum_mem fun q _ => W.smul_mem _ (hW _ q.out.2 v hv))
    · exact Submodule.smul_mem _ _ ((ec_mem_eig ρ K χ _).2 fun x => ec_left _ v S hS x)
    · have : v - (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v =
          (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, (v - ecTw ρ K χ q.out v) := by
        rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
          inv_smul_smul₀ hc]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ec_mem_tw ρ K χ _ v)
  have key : ∀ w ∈ twKer ρ K χ, ∃ S₀ : Subgroup K, S₀.FiniteIndex ∧
      ∀ (S : Subgroup K) [S.Normal] [Fintype (K ⧸ S)], S ≤ S₀ → ∑ q : K ⧸ S, ecTw ρ K χ q.out w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨n, u, rfl⟩ := hw
      refine ⟨_, hfin u, fun S _ _ hS => ?_⟩
      rw [ecTw_smul ρ K χ]
      simp only [map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [ec_right _ u S hS, sub_self]
    | zero => exact ⟨⊤, inferInstance, fun S _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, ha⟩ := ha
      obtain ⟨B, hB, hb⟩ := hb
      refine ⟨A ⊓ B, inferInstance, fun S _ _ hS => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [ha S (hS.trans inf_le_left), hb S (hS.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA, ha⟩ := ha
      refine ⟨A, hA, fun S _ _ hS => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [ha S hS, smul_zero]
  refine ⟨⟨?_, ?_⟩, part2⟩
  · rw [Submodule.disjoint_def]
    intro w he hw
    obtain ⟨A, hA, h⟩ := key w hw
    letI : Fintype (K ⧸ A.normalCore) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ A.normalCore) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h2 := h A.normalCore A.normalCore_le
    simp only [(ec_mem_eig ρ K χ w).1 he, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k] at h2
    exact (smul_eq_zero.1 h2).resolve_left hc
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, -, h1, h2⟩ := part2 ⊤ (fun _ _ _ _ => trivial) v trivial
    have := Submodule.add_mem_sup h1 h2
    simpa using this
end

section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (T : Module.End O M), LinearMap.range T ≤ IsLocalRing.maximalIdeal O • ⊤ → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → T.baseChange K y = μ • y → μ ≠ 0 → ¬ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint
  obtain ⟨p, hmon, -, hcoef, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)
  have hK : Polynomial.aeval (T.baseChange K) p = 0 := by
    have e : T.baseChange K = Module.End.baseChangeHom O K M T := rfl
    rw [e, Polynomial.aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvector (T.baseChange K) μ y :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩
  have hq : Polynomial.aeval μ p = 0 := by
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy
  set n := p.natDegree with hn
  set ν := μ⁻¹ with hνdef
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hq
    have h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0 := by
      rw [hq, mul_zero]
    rw [mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hp' : ν ^ n = ν ^ (n - i) * ν ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
    have e : ν ^ i * μ ^ i = 1 := by rw [← mul_pow, hνμ, one_pow]
    rw [Algebra.smul_def, hp']
    calc algebraMap O K (p.coeff i) * ν ^ (n - i)
        = algebraMap O K (p.coeff i) * ν ^ (n - i) * (ν ^ i * μ ^ i) := by rw [e, mul_one]
      _ = ν ^ (n - i) * ν ^ i * (algebraMap O K (p.coeff i) * μ ^ i) := by ring
  let C := integralClosure O K
  let ν' : C := ⟨ν, hint⟩
  have hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0 := by
    apply Subtype.ext
    simpa [C, ν'] using key
  have hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈
      (IsLocalRing.maximalIdeal O).map (algebraMap O C) := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have hin : i < n := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hcoef i)
  have htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]
    exact (Ideal.neg_mem_iff _).mpr hmem
  have hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hint' : (algebraMap O C).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (ι : Type) (t : ι → T) (a : ι → Λ), Algebra.adjoin Λ (Set.range t) = ⊤ → ∃ e : T, IsIdempotentElem e ∧ (∀ i, ∃ n : ℕ, (t i - algebraMap Λ T (a i)) ^ n * e ∈ (maximalIdeal Λ).map (algebraMap Λ T)) ∧ 1 - e ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i)) ∧ (∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))) ∧ (e ≠ 0 → ((maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))).IsMaximal) :=
  _root_.UpperTheory.Reformulated.B.Qe2.locAbs
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.extendPt :
    ∀ (O Λ T K : Type) [CommRing O] [CommRing Λ] [CommRing T] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O T] [Algebra Λ T] [IsScalarTower O Λ T] [Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K), P.comap (algebraMap Λ T) ≤ RingHom.ker y → ∃ x : T →ₐ[O] K, P ≤ RingHom.ker x ∧ ∀ a, x (algebraMap Λ T a) = y a :=
  _root_.UpperTheory.Reformulated.B.Qi4.extendPt
end

section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent
    {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (U : Submodule K Y) :
    U ≠ ⊥ → (∀ i, ∀ y ∈ U, T i y ∈ U) → (∀ i, ∀ y ∈ U, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → V ≠ ⊥ →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → (∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv hnil
  by_cases hall : ∀ i, ∀ y ∈ V, T i y = 0
  · obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    exact ⟨y, hy0, fun i => hall i y hyV⟩
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  have hpowmem : ∀ k : ℕ, (T i ^ k) z ∈ V := by
    intro k
    induction k with
    | zero => simpa using hzV
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hinv i _ ihk
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i)
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWne : W ≠ ⊥ := by
    classical
    have hex : ∃ n : ℕ, (T i ^ n) z = 0 := hnil i z hzV
    have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hz0 this
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hspec := Nat.find_spec hex
    rw [hm] at hspec
    have hmin : (T i ^ m) z ≠ 0 := Nat.find_min hex (by omega)
    rw [Submodule.ne_bot_iff]
    refine ⟨(T i ^ m) z, Submodule.mem_inf.mpr ⟨hpowmem m, ?_⟩, hmin⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
    exact hspec
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, hyk, map_zero]
  have hWnil : ∀ j, ∀ y ∈ W, ∃ n : ℕ, (T j ^ n) y = 0 :=
    fun j y hy => hnil j y (hWle hy)
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWne hWinv hWnil

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot
    {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (φ : Y →ₗ[K] Z)
    (hφ : ∀ i y, φ (T i y) = 0) (U : Submodule K Y) :
    (∃ u ∈ U, φ u ≠ 0) → (∀ i, ∀ y ∈ U, T i y ∈ U) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  intro hu hinv
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → (∃ u ∈ V, φ u ≠ 0) →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl hu hinv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv
  obtain ⟨u, huV, hu⟩ := hV
  have hVne : V ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨u, huV, fun h0 => hu (by rw [h0, map_zero])⟩
  by_cases hall : ∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0
  · exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent T hc V hVne hinv hall
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  let f : Module.End K V := (T i).restrict (hinv i)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_codisjoint_ker_pow_range_pow f)
  have hcod := hn (n + 1) (by omega)
  have hfpow : ∀ (k : ℕ) (w : V), ((f ^ k) w : Y) = (T i ^ k) (w : Y) := by
    intro k w
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
      rfl
  have hmem : (⟨u, huV⟩ : V) ∈ LinearMap.ker (f ^ (n + 1)) ⊔ LinearMap.range (f ^ (n + 1)) := by
    rw [codisjoint_iff.mp hcod]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hb
  have hφb : φ (((f ^ (n + 1)) c : V) : Y) = 0 := by
    rw [hfpow, pow_succ', Module.End.mul_apply, hφ]
  have hab' : (a : Y) + (((f ^ (n + 1)) c : V) : Y) = u := by
    have := congrArg Subtype.val hab
    simpa using this
  have hφa : φ (a : Y) ≠ 0 := by
    have h2 := congrArg φ hab'
    rw [map_add (f := _), hφb, add_zero] at h2
    rw [h2]
    exact hu
  have haker : (T i ^ (n + 1)) (a : Y) = 0 := by
    rw [← hfpow]
    rw [LinearMap.mem_ker.mp ha]
    rfl
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i ^ (n + 1))
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (n + 1) (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, ((hc i j).pow_left (n + 1)).eq, Module.End.mul_apply, hyk,
      map_zero]
  have hWu : ∃ w ∈ W, φ w ≠ 0 :=
    ⟨(a : Y), Submodule.mem_inf.mpr ⟨a.2, LinearMap.mem_ker.mpr haker⟩, hφa⟩
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWu hWinv

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot :
    ∀ {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] [AddCommGroup Z] [Module K Z] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (φ : Y →ₗ[K] Z), φ ≠ 0 → (∀ i y, φ (A i y) = x i • φ y) → ∃ y : Y, y ≠ 0 ∧ ∀ i, A i y = x i • y := by
  intro K Y Z ι _ _ _ _ _ _ A hA x φ hφ0 hφ
  let T : ι → Module.End K Y := fun i => A i - x i • (1 : Module.End K Y)
  have hT : ∀ i y, T i y = A i y - x i • y := by
    intro i y
    simp [T]
  have hc : ∀ i j, Commute (T i) (T j) := by
    intro i j
    exact ((hA i j).sub_right ((Commute.one_right (A i)).smul_right (x j))).sub_left
      (((Commute.one_left (A j)).smul_left (x i)).sub_right
        (((Commute.one_left 1).smul_left (x i)).smul_right (x j)))
  have hφT : ∀ i y, φ (T i y) = 0 := by
    intro i y
    rw [hT, map_sub, map_smul, hφ, sub_self]
  have hu : ∃ u ∈ (⊤ : Submodule K Y), φ u ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hφ0 (LinearMap.ext fun y => by simpa using hno y Submodule.mem_top)
  obtain ⟨y, hy0, hy⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot T hc φ hφT ⊤ hu
    (fun _ _ _ => Submodule.mem_top)
  refine ⟨y, hy0, fun i => ?_⟩
  have := hy i
  rw [hT, sub_eq_zero] at this
  exact this
end
