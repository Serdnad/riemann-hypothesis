module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle070
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle073
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import GroundTheory.ProfiniteCohomology.Bundle005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle037
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle006
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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

@[expose] public section

section

theorem UpperTheory.Reformulated.B.LocalSmoothExtension.exists_smooth_eq : ∀ {K : Type} [Field K] [NumberField K] {n : ℕ}
    {U : Set (GlobalTheory.CuspRep.Lie K n)}, IsOpen U →
    ∀ {F : GlobalTheory.CuspRep.Lie K n → ℂ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U →
    ∀ {x : GlobalTheory.CuspRep.Lie K n}, x ∈ U →
      ∃ G : GlobalTheory.CuspRep.Lie K n → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro K _ _ n U hU F hF x hx
  exact UpperTheory.Reformulated.B.ContDiffOnLocalExtension.abs hU hF hx
end

section

theorem UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {U : Subgroup Γ} {a a' : Γ → Matrix (Fin n) (Fin n) k},
      UpperTheory.V.U3.MatIrr U a →
        ∀ (h : GL (Fin n) k),
          (∀ g ∈ U, a' g = (↑h : Matrix (Fin n) (Fin n) k) * a g * (↑h⁻¹ : Matrix (Fin n) (Fin n) k)) →
            UpperTheory.V.U3.MatIrr U a' := by
  intro Γ k _ _ n U a a' hirr h hconj
  refine UpperTheory.Reformulated.B.G5.matIrr_conj h (fun g hg => ?_) hirr
  rw [hconj g hg, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
end

section

open Formalism.WeaklyAdmissibleFiltrations in
/-- Apply compact-quotient finite generation to the lattice cocycles, using reduction modulo `ϖ`. -/
theorem UpperTheory.Reformulated.B.Gub2.fg_Z1T
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {LL O V : Type} [inst_2 : Field LL] [inst_3 : CommRing O] [inst_4 : Algebra O LL]
    [inst_5 : AddCommGroup V] [inst_6 : Module LL V] [inst_7 : Module O V]
    [inst_8 : IsScalarTower O LL V] {ρ : Representation LL G V}
    [inst_9 : TopologicalSpace V] [inst_10 : ContinuousAdd V] [inst_11 : ContinuousConstSMul LL V]
    [inst_12 : TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V]
    (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0)
    (hb : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hc : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T))
    (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG := by
  have hmem : ∀ x : L.T, x ∈ (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) ↔
      ∃ y ∈ L.T, ϖ • y = (x : V) := by
    intro x
    rw [pow_one, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  have hred : ∀ c : latticeCocycles L, redT L _ c ∈ quotientCocycles L _ hI := by
    intro c
    have hcont : Continuous (c : G → V) := c.2.1.1
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, fun g h => ?_⟩
    · have h0 : Filter.Tendsto (fun y => (c : G → V) y - (c : G → V) g) (nhds g) (nhds 0) := by
        have := (hcont.sub (continuous_const (y := (c : G → V) g))).tendsto g
        rw [Pi.sub_apply, sub_self] at this
        exact this
      filter_upwards [h0 (hb.mem_of_mem (i := 1) trivial)] with y hy
      obtain ⟨v, hv, hvy⟩ := hy
      refine (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨v, hv, ?_⟩)
      rw [← pow_one ϖ]
      exact hvy
    · have : evT L (g * h) c = evT L g c + actT L g (evT L h c) :=
        Subtype.ext (c.2.1.2 g h)
      change Submodule.mkQ _ (evT L (g * h) c) = _
      rw [this, map_add (f := _)]
      rfl
  refine UpperTheory.compact_quotient_submodule (LL := LL) (latticeCocycles L) ϖ
    ((redT L _).codRestrict (quotientCocycles L _ hI) hred) hc ?_ ?_
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIf, t, ht, hsub⟩ := hU
    obtain ⟨n, -, hn⟩ := hb.mem_iff.1 ((Filter.biInter_mem hIf).2 fun i _ => ht i)
    refine ⟨n, fun z hz => hsub fun i hi => ?_⟩
    exact Set.mem_iInter₂.1 (hn ⟨z i, hz.2 i trivial, rfl⟩) i hi
  · intro z hz
    have hz' : ∀ g, ∃ y ∈ L.T, ϖ • y = (z : G → V) g := fun g =>
      (hmem (evT L g z)).1
        ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Subtype.val hz) g))
    refine ⟨(algebraMap O LL ϖ)⁻¹ • (z : G → V),
      ⟨(continuousCocycles ρ).smul_mem _ z.2.1, fun g _ => ?_⟩, ?_⟩
    · obtain ⟨y, hy, h⟩ := hz' g
      have : ((algebraMap O LL ϖ)⁻¹ • (z : G → V)) g = y := by
        rw [Pi.smul_apply, ← h, ← algebraMap_smul LL ϖ y, inv_smul_smul₀ hϖ]
      rw [this]
      exact hy
    · rw [← algebraMap_smul LL ϖ, smul_inv_smul₀ hϖ]
end

section

private theorem isDiscreteRep_of_forall_eq {k G : Type} [CommRing k] [Group G]
    [TopologicalSpace G] (A : Rep.{0, 0, 0} k G) (h : ∀ (g : G) (a : A.V), A.ρ g a = a) :
    GroundTheory.ProfCoh.IsDiscreteRep A := by
  have : A.ρ.IsTrivial := ⟨fun g => LinearMap.ext fun a => h g a⟩
  infer_instance

open GroundTheory.ProfCoh in
theorem UpperTheory.Reformulated.B.Gua5.finite_cohomology_of_trivial_of_cyclic
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (n r : ℕ)
    (hC : ∀ (C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep C] [Finite C.V] [IsAddCyclic C.V],
      (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) →
      Finite (cohomology C r))
    (A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep A] [Finite A.V]
    (htriv : ∀ (g : H) (a : A.V), A.ρ g a = a) (hn : ∀ a : A.V, n • a = 0) :
    Finite (cohomology A r) := by
  have hι : ∀ (B : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep B],
      (∀ m : ℕ, Function.Injective ((cochainsComplexι B).f m).hom) ∧
      ∀ (m : ℕ) (x : (Fin m → H) → B.V),
        (∃ y, ((cochainsComplexι B).f m).hom y = x) ↔ IsLocallyConstant x := by
    intro B _
    refine ⟨fun m => Subtype.val_injective, fun m x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
    rintro ⟨y, rfl⟩
    exact y.2
  refine UpperTheory.cyclic_trivial_induction n
    (fun B => ∀ [IsDiscreteRep B], Finite (cohomology B r))
    ?_ ?_ A ‹Finite A.V› htriv hn
  · intro C _ _ h1 h2 _
    exact hC C h1 h2
  · intro A B C f g hA hC' hf hfg hg PA PC _
    have := isDiscreteRep_of_forall_eq A hA
    have := isDiscreteRep_of_forall_eq C hC'
    obtain ⟨φ, ψ, w, hS⟩ := UpperTheory.cochain_injective_exact A B C f g _ _ _ (cochainsComplexι A)
      (cochainsComplexι B) (cochainsComplexι C) hf hfg hg
      (hι A).1 (hι B).1 (hι C).1 (hι A).2 (hι B).2 (hι C).2
    exact (UpperTheory.homology_finite_short_exact hS r).1 PA PC
end

section

open ReciprocityTheory.ChartRestriction.G.FD in
private theorem UpperTheory.Reformulated.B.Ue6.herm_smul_right {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (w0 : NumberField.RingOfIntegers E),
      ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E) = (1 : E) - (↑w0 : E) →
        ∀ u ∈ X.Λ,
          ∀ v ∈ X.Λ,
            ∃ (k : ℤ),
              (Algebra.trace ℚ E : E → ℚ)
                    (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u (((↑w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (↑w0 : E)) • v)) -
                  (Algebra.trace ℚ E : E → ℚ) (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) =
                (2 : ℚ) * (↑k : ℚ) := by
  intro E _ _ _ r X w0 hw u hu v hv
  have hwv : (w0 : E) • v ∈ X.Λ := X.Λ.smul_mem w0 hv
  obtain ⟨a, ha⟩ := X.EF_int u hu _ hwv
  obtain ⟨b, hb⟩ := X.EF_int u hu v hv
  have hc : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) = 1 - 2 * (w0 : E) := by
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.cc ((w0 : E) - (1 - (w0 : E))) =
        ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) - (1 - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_sub, map_one]
    rw [hw, h1, hw]
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.EFf at ha hb
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hw] at ha
  refine ⟨b - a, ?_⟩
  rw [UpperTheory.Reformulated.B.Ue6.herm_smul_right, hc, Int.cast_sub, ← ha, ← hb, ← map_sub, ← map_sub,
    two_mul ((Algebra.trace ℚ E) _), ← map_add]
  congr 1
  ring
end
