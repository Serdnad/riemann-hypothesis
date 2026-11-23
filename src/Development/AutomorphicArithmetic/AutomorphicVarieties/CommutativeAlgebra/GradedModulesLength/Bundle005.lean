module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle001
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem et_point (E K C : Type) [Field E] [Field K] [Algebra E K] [IsAlgClosed K] [CommRing C] [Algebra E C]
    [Algebra.FiniteType E C] (m : Ideal C) [m.IsMaximal] :
    ∃ ι : (C ⧸ m) →ₐ[E] K, Function.Injective ι := by
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite E (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing E (C ⧸ m)
  let ι : (C ⧸ m) →ₐ[E] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨ι, ι.toRingHom.injective⟩

private theorem et_unram (O K C : Type) [CommRing O] [Field K] [Algebra O K] [CommRing C] [Algebra O C]
    [Algebra.FiniteType O C]
    (hp : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι)
    (hD : ∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) : Algebra.FormallyUnramified O C := by
  have key : ∀ m : Ideal C, m.IsMaximal → (⊤ : Submodule C Ω[C⁄O]) ≤ m • ⊤ := by
    intro m hm x _
    by_contra hx
    letI : Field (C ⧸ m) := Ideal.Quotient.field m
    obtain ⟨ι, hι⟩ := hp m hm
    have hq : Submodule.Quotient.mk (p := m • (⊤ : Submodule C Ω[C⁄O])) x ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (C ⧸ m) (Ω[C⁄O] ⧸ m • (⊤ : Submodule C Ω[C⁄O])),
        φ (Submodule.Quotient.mk x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff (C ⧸ m) _).mp hall)
    let f : Ω[C⁄O] →ₗ[C] C ⧸ m := (φ.restrictScalars C).comp (m • (⊤ : Submodule C Ω[C⁄O])).mkQ
    let D : Derivation O C (C ⧸ m) := f.compDer (KaehlerDifferential.D O C)
    let ξ : C →ₐ[O] K := ι.comp (Ideal.Quotient.mkₐ O m)
    let L : C →ₗ[O] K := ι.toLinearMap.comp (D : C →ₗ[O] C ⧸ m)
    have hL : L ∈ PtDer ξ K := by
      intro a b
      show ι (D (a * b)) = ι (Ideal.Quotient.mk m a) • ι (D b) + ι (Ideal.Quotient.mk m b) • ι (D a)
      rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_mul, map_mul,
        smul_eq_mul, smul_eq_mul]
      rfl
    rw [hD ξ, Submodule.mem_bot] at hL
    have hDz : ∀ c, D c = 0 := by
      intro c
      apply hι
      rw [map_zero]
      exact LinearMap.congr_fun hL c
    have hf : f = 0 := by
      apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation O C)
      intro c
      simpa [D] using hDz c
    apply hφ
    have h2 := LinearMap.congr_fun hf x
    simpa [f] using h2
  have hfg : (⊤ : Submodule C Ω[C⁄O]).FG := Module.finite_def.mp inferInstance
  have hann : Module.annihilator C Ω[C⁄O] = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (key m hm)
    have hrJ : r ∈ Module.annihilator C Ω[C⁄O] := Module.mem_annihilator.mpr (fun n => hr n trivial)
    have h3 := m.sub_mem (hle hrJ) hr1
    rw [sub_sub_cancel] at h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h3)
  have h1 : (1 : C) ∈ Module.annihilator C Ω[C⁄O] := by
    rw [hann]
    exact Submodule.mem_top
  have h0 : ∀ n : Ω[C⁄O], n = 0 := by
    intro n
    rw [← one_smul C n]
    exact Module.mem_annihilator.mp h1 n
  exact ⟨⟨fun a b => (h0 a).trans (h0 b).symm⟩⟩

theorem UpperTheory.V.Alg.M.et_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (C : Type) [CommRing C] [Algebra O C] [Algebra.FiniteType O C], (∀ c : O, c ≠ 0 → IsUnit (algebraMap O C c)) →
      (∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) → Finite (C →ₐ[O] K) ∧ ∀ h : C, (∀ ξ : C →ₐ[O] K, ξ h = 0) → h = 0 := by
  intro O _ _ _ _ _ K _ _ _ _ C _ _ _ hunit hD
  have huC : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O C y) :=
    fun y => hunit y (nonZeroDivisors.ne_zero y.2)
  have hinjK : Function.Injective (algebraMap O K) := FaithfulSMul.algebraMap_injective O K
  have huK : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O K y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun h0 => nonZeroDivisors.ne_zero y.2 (hinjK ?_))
    rw [h0, map_zero]
  letI : Algebra (FractionRing O) C :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huC).toAlgebra
  letI : Algebra (FractionRing O) K :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huK).toAlgebra
  haveI : IsScalarTower O (FractionRing O) C := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huC r).symm)
  haveI : IsScalarTower O (FractionRing O) K := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huK r).symm)
  haveI : Algebra.FiniteType (FractionRing O) C :=
    Algebra.FiniteType.of_restrictScalars_finiteType O (FractionRing O) C
  have hpt : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι := by
    intro m hm
    haveI := hm
    obtain ⟨ι, hι⟩ := et_point (FractionRing O) K C m
    exact ⟨ι.restrictScalars O, hι⟩
  haveI : Algebra.FormallyUnramified O C := et_unram O K C hpt hD
  haveI : Algebra.FormallyUnramified (FractionRing O) C :=
    Algebra.FormallyUnramified.of_restrictScalars O (FractionRing O) C
  haveI : Module.Finite (FractionRing O) C := Algebra.FormallyUnramified.finite_of_free (FractionRing O) C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field (FractionRing O) C
  refine ⟨?_, ?_⟩
  · have hcompat : ∀ ξ : C →ₐ[O] K, ∀ r : FractionRing O,
        ξ (algebraMap (FractionRing O) C r) = algebraMap (FractionRing O) K r := by
      intro ξ r
      have hc : ξ.toRingHom.comp (algebraMap (FractionRing O) C) = algebraMap (FractionRing O) K := by
        apply IsLocalization.ringHom_ext (nonZeroDivisors O)
        apply RingHom.ext
        intro a
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact ξ.commutes a
      exact RingHom.congr_fun hc r
    let up : (C →ₐ[O] K) → (C →ₐ[FractionRing O] K) := fun ξ => { ξ.toRingHom with commutes' := hcompat ξ }
    have hup : Function.Injective up := by
      intro ξ₁ ξ₂ h
      ext c
      exact AlgHom.congr_fun h c
    haveI : Finite (C →ₐ[FractionRing O] K) := (linearIndependent_toLinearMap (FractionRing O) C K).finite
    exact Finite.of_injective up hup
  · intro h hh
    haveI : IsJacobsonRing C := isJacobsonRing_of_finiteType (A := FractionRing O)
    have hrad : (⊥ : Ideal C).IsRadical := by
      intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [Ideal.mem_bot] at hn ⊢
      exact IsNilpotent.eq_zero ⟨n, hn⟩
    have hj := IsJacobsonRing.out' (⊥ : Ideal C) hrad
    rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    haveI := hJ
    obtain ⟨ι, hι⟩ := hpt J hJ
    have h5 := hh (ι.comp (Ideal.Quotient.mkₐ O J))
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_zero ι] at h5
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hι h5)
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem sm_smith {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] [Module.Finite O P] [Module.IsTorsionFree O P] {r : ℕ} (hr : Module.finrank O P = r)
    (N : Submodule O P) (hN : Module.finrank O N = Module.finrank O P) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (y : Fin r → P) (c : Fin r → ℕ), Submodule.span O (Set.range fun i => ϖ ^ c i • y i) = N ∧
      Module.length O (P ⧸ N) = ((∑ i, c i : ℕ) : ℕ∞) := by
  classical
  let b := Module.finBasisOfFinrankEq O P hr
  have ha := fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Submodule.smithNormalFormCoeffs_ne_zero b hN i) hϖ
  choose c u hu using ha
  refine ⟨fun i => (u i : O) • Submodule.smithNormalFormTopBasis b hN i, c, ?_, ?_⟩
  · have h1 : (fun i => ϖ ^ c i • (u i : O) • Submodule.smithNormalFormTopBasis b hN i) =
        N.subtype ∘ Submodule.smithNormalFormBotBasis b hN := by
      funext i
      simp only [Function.comp, Submodule.subtype_apply]
      rw [Submodule.smithNormalFormBotBasis_def, hu i, smul_smul, mul_comm]
    rw [h1, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rw [(N.quotientEquivPiSpan b hN).length_eq, Module.length_pi_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Ideal.span {Submodule.smithNormalFormCoeffs b hN i} = maximalIdeal O ^ c i := by
      rw [hu i, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit (u i).isUnit]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private theorem sm_lift {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] {r : ℕ} (φ : (Fin (r + 1) → O) →ₗ[O] P) (hr : Module.finrank O (LinearMap.range φ) = r)
    (n : Fin r → P) (hn : Submodule.span O (Set.range n) = LinearMap.range φ) :
    ∃ v : Fin (r + 1) → (Fin (r + 1) → O), Submodule.span O (Set.range v) = ⊤ ∧
      (∀ i : Fin r, φ (v i.castSucc) = n i) ∧ φ (v (Fin.last r)) = 0 := by
  have hw : ∀ i, ∃ w, φ w = n i := fun i => by
    have : n i ∈ LinearMap.range φ := hn ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  choose w hw using hw
  have hk : Module.finrank O (LinearMap.ker φ) = 1 := by
    have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    rw [φ.quotKerEquivRange.finrank_eq, hr, Module.finrank_fin_fun] at h1
    omega
  let b := Module.finBasisOfFinrankEq O (LinearMap.ker φ) hk
  refine ⟨Fin.snoc (α := fun _ => Fin (r + 1) → O) w (b 0 : Fin (r + 1) → O), ?_, fun i => by simp [hw], by simp⟩
  rw [eq_top_iff]
  intro u _
  have h1 : φ u ∈ Submodule.span O (Set.range n) := hn ▸ LinearMap.mem_range_self φ u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
  have h2 : u - ∑ i, a i • w i ∈ LinearMap.ker φ := by

    simp [LinearMap.mem_ker, map_sum, hw, ha]
  have h3 := congrArg Subtype.val (b.sum_repr ⟨_, h2⟩)
  simp only [Fin.sum_univ_one, Submodule.coe_smul] at h3
  rw [← sub_add_cancel u (∑ i, a i • w i), ← h3]
  refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, by simp⟩)) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)

theorem UpperTheory.V.Alg.M.sm_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra O A]
      (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O), (∀ f ∈ 𝒜 (-1), x f = 0) → ∀ (r : ℕ) (F : Fin (r + 1) → A), (∀ i, F i ∈ 𝒜 (-1)) →
      Module.Finite O (cotLat x 𝒜 (-1)) → Module.finrank O (cotLat x 𝒜 (-1)) = r → SpansCot x 𝒜 (-1) F →
      ∀ ϖ : O, Irreducible ϖ → ∃ (F' : Fin (r + 1) → A) (y : Fin r → A) (c : Fin r → ℕ),
        Submodule.span O (Set.range F') = Submodule.span O (Set.range F) ∧
        (∀ i, y i ∈ 𝒜 (-1) ∧ F' i.castSucc - ϖ ^ c i • y i ∈ satSq x) ∧ F' (Fin.last r) ∈ satSq x ∧
        cotLen x 𝒜 (-1) F = ((∑ i, c i : ℕ) : ℕ∞) := by
  intro O _ _ _ A _ _ 𝒜 x hx r F hF hfin hr hs ϖ hϖ
  classical
  haveI : Module.IsTorsionFree O (A ⧸ satSq x) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c p h => ?_
    obtain ⟨f, rfl⟩ := (satSq x).mkQ_surjective p
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨d, hd, h⟩ := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have hle : cotSpan x F ≤ cotLat x 𝒜 (-1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F i, ⟨hF i, hx _ (hF i)⟩, rfl⟩
  set N := (cotSpan x F).comap (cotLat x 𝒜 (-1)).subtype with hNdef
  have hN : Module.finrank O N = Module.finrank O (cotLat x 𝒜 (-1)) := by
    have h1 := N.finrank_quotient_add_finrank
    have h2 : Module.finrank O (cotLat x 𝒜 (-1) ⧸ N) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨p, rfl⟩ := N.mkQ_surjective q
      obtain ⟨c, hc, hp⟩ := hs p.1 p.2
      refine ⟨c, hc, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp
    omega
  obtain ⟨y, c, hy, hlen⟩ := sm_smith hr N hN ϖ hϖ
  let ψ : (Fin (r + 1) → O) →ₗ[O] A := Fintype.linearCombination O F
  have hψ : LinearMap.range ψ = Submodule.span O (Set.range F) := Fintype.range_linearCombination O F
  have hφ : LinearMap.range ((satSq x).mkQ ∘ₗ ψ) = cotSpan x F := by
    rw [LinearMap.range_comp, hψ, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmap : N.map (cotLat x 𝒜 (-1)).subtype = cotSpan x F := by
    rw [hNdef, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  obtain ⟨v, hv, hv1, hv2⟩ := sm_lift ((satSq x).mkQ ∘ₗ ψ)
    (by rw [hφ]; exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm.trans (hN.trans hr))
    (fun i => ϖ ^ c i • (y i : A ⧸ satSq x))
    (by rw [hφ, ← hmap, ← hy, Submodule.map_span, ← Set.range_comp]; rfl)
  have hz : ∀ i, ∃ z ∈ 𝒜 (-1), (satSq x).mkQ z = y i := fun i => by
    obtain ⟨z, hz, h⟩ := (y i).2
    exact ⟨z, hz.1, h⟩
  choose z hz hz' using hz
  refine ⟨ψ ∘ v, z, c, ?_, fun i => ⟨hz i, ?_⟩, ?_, hlen⟩
  · rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, hψ]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hz', sub_eq_zero]
    exact hv1 i
  · rw [← Submodule.Quotient.mk_eq_zero]
    exact hv2
end
