module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturality
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogStep

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem constantCoeff_up_eq_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up E μ i) = 0 := by
  rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
    map_zero]

theorem ql_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} {f g : MvPowerSeries (Fin d) E} (hf : QL μ N f) (hg : QL μ N g) :
    QL μ N (f + g) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨by rw [map_add (f := _), f0, g0, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := f1 i
    obtain ⟨b, hb, hb'⟩ := g1 i
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    simp only [lin, map_add (f := _)] at ha' hb' ⊢
    rw [ha', hb']
  · obtain ⟨a, ha, ha'⟩ := f2 α
    obtain ⟨b, hb, hb'⟩ := g2 α
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    rw [formalCoboundary_add (constantCoeff_up_eq_zero hμ), map_add (f := _), ha', hb', map_add (f := _)]

theorem ql_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} (a : O) {f : MvPowerSeries (Fin d) E} (hf : QL μ N f) :
    QL μ N (algebraMap O E a • f) := by
  obtain ⟨f0, f1, f2⟩ := hf
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, f0,
      mul_zero]
  · obtain ⟨b, hb, hb'⟩ := f1 i
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    simp only [lin, coeff_smul] at hb' ⊢
    rw [hb', map_mul]
  · obtain ⟨b, hb, hb'⟩ := f2 α
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    rw [formalCoboundary_smul (constantCoeff_up_eq_zero hμ), coeff_smul, hb', map_mul]

theorem ql_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (N : Ideal O) : QL μ N (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
  have := formalCoboundary_smul (constantCoeff_up_eq_zero (E := E) hμ) 0 0
  rw [zero_smul, zero_smul] at this
  rw [this, map_zero, map_zero]

theorem comb_add {ι : Type} [Fintype ι] (b b' : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb (b + b') e = comb b e + comb b' e := by
  simp only [comb, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem ql_comb {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E)
    (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact ql_zero hμ _
  | cons i s hi ih => rw [Finset.sum_cons]; exact ql_add hμ (ql_smul hμ _ (he i)) ih

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQe hcob hlin hLie f hf
  have hμ := c.isLaw.const
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hc0 := constantCoeff_up_eq_zero (E := E) hμ

  let t : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) fun j => lb j
  have ht : ∀ i, c.IsLie (e i) (t i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF _ (hQe (Sum.inl i))
      have := ((GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ l l 0 hl hl).2.2 (hcob i))
      subst this
      exact hl
    · exact hLie j

  have hcombS : ∀ (b : Fin d ⊕ Fin k → O) (S : Finset (Fin d ⊕ Fin k)),
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e i) (∑ i ∈ S, b i • t i) ∧
        QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e i) := by
    intro b S
    induction S using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ⟨c.isLie_zero hinj, ql_zero hμ _⟩
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_comm, add_comm (b i • t i)]
      exact ⟨(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ _ _ (b i) ih.1 (ht i)).1 ih.2 (hQe i),
        ql_add hμ ih.2 (ql_smul hμ _ (hQe i))⟩
  have hcombLie : ∀ b : Fin d ⊕ Fin k → O, c.IsLie (comb b e) (∑ i, b i • t i) :=
    fun b => (hcombS b Finset.univ).1

  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF f hf
  let b0 : Fin d ⊕ Fin k → O := Sum.elim (0 : Fin d → O) fun j => lb.repr l j
  have hb0 : ∑ i, b0 i • t i = l := by
    rw [Fintype.sum_sum_type]
    simp only [b0, t, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]
    exact lb.sum_repr l
  set f' := f + algebraMap O E (-1) • comb b0 e with hf'
  have hQf' : QL c.μ ⊤ f' := ql_add hμ hf (ql_smul hμ _ (ql_comb hμ b0 e hQe))
  have hLf' : c.IsLie f' ((p : O) • 0) := by
    have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f (comb b0 e) l _ (-1) hl (hcombLie b0)).1 hf
      (ql_comb hμ b0 e hQe)
    rwa [hb0, neg_one_smul, add_neg_cancel, ← smul_zero (p : O)] at this
  obtain ⟨s, g, hg, hh⟩ := GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p p C v O hv G d c E hF f' 0 hQf' hLf'
  set h := f' - map (algebraMap O E) s - g with hhdef

  have hw : ∀ i, ∃ w : O, lin g i = algebraMap O E w := by
    intro i
    obtain ⟨b1, -, hb1⟩ := hQf'.2.1 i
    obtain ⟨b3, -, hb3⟩ := hh.2.1 i
    refine ⟨b1 - coeff (Finsupp.single i 1) s - b3, ?_⟩
    have : g = f' - map (algebraMap O E) s - h := by rw [hhdef]; ring
    simp only [lin] at hb1 hb3 ⊢
    rw [this, map_sub, map_sub, hb1, hb3, coeff_map, map_sub, map_sub]
  choose w hw using hw
  let bw : Fin d ⊕ Fin k → O := Sum.elim w 0
  have hcw : comb bw e = ∑ i, algebraMap O E (w i) • e (Sum.inl i) := by
    simp [comb, bw, Fintype.sum_sum_type]

  have hgw : g = comb bw e := by
    have key := GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E hF d c.μ c.isLaw (g - comb bw e) ?_ ?_
    · exact sub_eq_zero.1 key
    · funext i

      simp only [lin, hcw, map_sub, map_sum, coeff_smul, Pi.zero_apply] at hw ⊢
      have hl' : ∀ j, coeff (Finsupp.single i 1) (e (Sum.inl j)) =
          (Pi.single j (1 : E) : Fin d → E) i := fun j => congrFun (hlin j) i
      simp only [hl', hw]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp
    · let L : MvPowerSeries (Fin d) E →+ MvPowerSeries (Fin d ⊕ Fin d) E :=
        AddMonoidHom.mk' (cob1 (up E c.μ)) (formalCoboundary_add hc0)
      have hL : ∀ x, L x = cob1 (up E c.μ) x := fun _ => rfl

      rw [← hL, map_sub, hcw, map_sum]
      simp only [hL, formalCoboundary_smul hc0, hcob, smul_zero, Finset.sum_const_zero, sub_zero]
      exact hg

  obtain ⟨u, hu⟩ := hF.unit_p
  refine ⟨bw + b0, s, (↑u⁻¹ : E) • h, ?_, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · obtain ⟨b, hb, hb'⟩ := h1 i
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      simp only [lin, coeff_smul] at hb' ⊢
      rw [hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · obtain ⟨b, hb, hb'⟩ := h2 α
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      rw [formalCoboundary_smul hc0, coeff_smul, hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul,
        one_mul]
  · rw [smul_smul, ← hu, Units.mul_inv, one_smul, comb_add, ← hgw]
    rw [map_neg, map_one, neg_one_smul] at hf'
    rw [hhdef, hf']
    ring

end GlobalTheory.QLogStep
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.exists_cocycles_omega : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
    ∃ (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ ∀ n, w.1 n = d.om n := by
  intro R _ A _ hA p G t c d
  have hs : IsSymCoc d.g := isSymCoc_of_isAdd R A hA _ _ d.add
  refine ⟨⟨fun n => d.coc n, fun n => ⟨coc_mem_symCocycles R A p G t c d hs n,
    Dat.pullTwo_res_coc R A p G t c d n⟩⟩, ⟨fun n => d.om n, fun n => OmRes.cotMap_res_om R A p G t c d n⟩,
    fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cup_pullback_cocycles_pointValue : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  exact GlobalTheory.PtExt.cupZ_pull_apply_fv
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
          ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
            (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
            Sm (D := E) W (spOver ψ ≫ x) →
              σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) :=
  @GlobalTheory.PtExt.CocSec.exists_section
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
      (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
      IsSymCoc d.g → ∀ n, d.coc n ∈ symCocycles R (G.A n) :=
  @GlobalTheory.PtExt.coc_mem_symCocycles
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  first | exact @GlobalTheory.PtExt.contr_chern_eq_tanCoc | exact GlobalTheory.PtExt.contr_chern_eq_tanCoc | (intros; apply GlobalTheory.PtExt.contr_chern_eq_tanCoc <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
      (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A),
    t.LieCorr x v → x (ψ ⟨_, hF⟩) = tanVal v β :=
  @PtExt.lie_psi_cl_eq_tanVal
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality : ∀ (p : ℕ) (R R' : Type) [CommRing R] [CommRing R'] (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A') (σ : R →+* R') (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A) (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), IsCan t c x → IsCan t' (m.pull c) ((t'.semiHom t m).rig x) := by
  first | exact @GlobalTheory.PtExtNat.isCan_pull | exact GlobalTheory.PtExtNat.isCan_pull | (intros; apply GlobalTheory.PtExtNat.isCan_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.DomSurj

open CategoryTheory.Limits

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem surjective_cxPts_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  intro k _ X _ p D hX Y _ q E hY π hπ hgen σ x
  have := isProper_of_projOver hX.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ isProper_of_projOver hY.isProjOver
  have : IsProper π := IsProper.of_comp π p

  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hall : Set.range π = Set.univ := by
      rw [← Set.univ_subset_iff, ← genericPoint_closure X, hcl.closure_subset_iff]
      exact Set.singleton_subset_iff.2 ⟨_, hgen⟩
    exact Set.range_eq_univ.1 hall
  obtain ⟨y, hy⟩ := hsurj (x.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x.1) y
    (IsLocalRing.closedPoint ℂ) hy
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x.1)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback π x.1)))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨⟨pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hπ, ← Category.assoc, Category.assoc _ _ π, pullback.condition,
      ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp, x.2]
  · show (pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1) ≫ π = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.DomSurj
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

theorem _root_.GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  first | exact @GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | exact GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | (intros; apply GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le <;> assumption)
end
