module

public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle079
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open Formalism.REAL
open scoped InnerProductSpace

namespace GlobalTheory.KTypeSteps

theorem sqrt_nsq_eq {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_root {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  have h : ∀ c, root a b c * root a b c =
      (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      simp [root, hab]
    · by_cases h2 : c = b
      · subst h2
        simp [root, h1]
      · simp [root, h1, h2]
  simp only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem kSpan_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hne : μ ≠ ν) :
    kSpan ε E y ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  intro z hz
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply]
  exact kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x
    (mem_compact_span_self_general x) z hz

theorem pfil_one_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hfd : FiniteDimensional ℂ (kSpan ε E y))
    (hne : μ ≠ ν) (hne' : ∀ a b, ε a ≠ ε b → μ ≠ ν + root a b) :
    pfil ε E y 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  refine le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)
  · obtain ⟨hA, hθ⟩ := (arrModule V n ε E 1).1 hg
    have hKU := (arrModule V n ε E 1).2 hu
    have := noncompact_arr_finite_dimensional (j := 1) hfd
    obtain ⟨m, F, lam, hF, -, hsup⟩ := kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1)
      inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable
    change (arrV0 ε E y 1).map (thetaA E 1) ≤ _
    rw [← hsup, Submodule.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    obtain ⟨hmem, h0, hhi⟩ := hF i
    obtain ⟨a, b, hab, hlam⟩ := hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0
    have hθhi : KHighest ε E (lam i) (thetaA E 1 (F i)) := by
      refine ⟨fun c => ?_, fun c d hcd he => ?_⟩
      · rw [← hθ, hhi.1 c, map_smul]
      · rw [← hθ, hhi.2 c d hcd he, map_zero]
    have hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1) := by
      refine compact_span_le_of_stable ?_ (mem_compact_span_self_general _)
      intro c d hcd G hG
      rw [Submodule.mem_comap] at hG ⊢
      rw [hθ]
      exact compact_span_stable_general _ c d hcd _ hG
    exact hle.trans (Submodule.comap_mono
      (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))
  · rw [(pfilFacts V n ε E y hg).1]
    exact kSpan_le_ker hg hu hx hy hne

theorem ew_mem_pfil {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    {w : List (Fin n × Fin n)} (hw : w.length ≤ j) (hp : ∀ p ∈ w, ε p.1 ≠ ε p.2) {y : V}
    (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j :=
  Submodule.subset_span ⟨w, hw, hp, y, hy, rfl⟩

theorem ktypes_within_steps :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E →
      KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
      ∀ (j : ℕ) (μ : Fin n → ℝ), ∀ x ∈ pfil ε E u j, x ≠ 0 → KHighest ε E μ x →
        Real.sqrt (nsq (μ - Λ)) ≤ Real.sqrt 2 * j := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd j
  obtain ⟨h0, -, hst, -, -, -, hfin⟩ := pfilFacts V n ε E u hg
  induction j with
  | zero =>
    intro μ x hx hx0 hhi
    rw [h0] at hx
    have := compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0
    subst this
    simp [nsq, dot]
  | succ j ih =>
    intro μ x hx hx0 hhi
    by_contra hlt
    rw [not_le] at hlt
    push_cast at hlt
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have := hfin hfd j
    obtain ⟨m, y, lam, hy, -, hsup⟩ := kDecomp V n ε E (pfil ε E u j) inferInstance
      (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)
    have hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      intro i
      obtain ⟨hmem, hy0, hyh⟩ := hy i
      have hb := ih (lam i) (y i) hmem hy0 hyh
      refine pfil_one_le_ker hg hu hhi hyh
        (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_
      · intro h
        rw [h] at hlt
        nlinarith
      · intro a b hab h
        have hab' : a ≠ b := fun h => hab (h ▸ rfl)
        have ht := sqrt_nsq_add_le (lam i - Λ) (root a b)
        rw [nsq_root hab'] at ht
        have he : μ - Λ = lam i - Λ + root a b := by rw [h]; abel
        rw [he] at hlt
        nlinarith
    have hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      rw [← hsup]
      refine iSup_le fun i => le_trans ?_ (hone i)
      obtain ⟨g0, g1, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0]
      exact g1 0
    have hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b) := by
      intro a b
      rw [← hsup]
      refine iSup_le fun i z hz => hone i ?_
      obtain ⟨g0, -, -, g3, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0] at hz
      exact g3 0 a b z hz
    have hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hp, z, hz, rfl⟩
      cases w with
      | nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)
      | cons p w =>
        have hw' : w.length ≤ j := by simpa using hw
        exact hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)
    have := hC hx
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at this
    exact hx0 (inner_self_eq_zero.mp this)

end GlobalTheory.KTypeSteps
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocAtTopology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem secondCountable_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

theorem t2Space_of_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_integer_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsOpen (𝒪[k] : Set k) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  exact Valued.isOpen_integer k

theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

theorem mem_closure_int (T : LocAt F E sig p) (c : T.Fp) (hc : c ∈ 𝒪[T.Fp]) :
    c ∈ closure (Set.range fun a : 𝓞 F => T.ιF (algebraMap (𝓞 F) F a)) := by
  haveI := T.lf
  have hc' : valuation T.Fp c ≤ 1 := hc
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.1 hU
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero T.Fp)
  have hn : ∀ (y : T.Fp) (δ : (ValueGroupWithZero T.Fp)ˣ),
      {z : T.Fp | valuation T.Fp (z - y) < δ} ∈ nhds y := fun y δ =>
    IsValuativeTopology.mem_nhds_iff'.2 ⟨δ, fun z hz => hz⟩
  obtain ⟨b, hb⟩ := T.dense.mem_nhds (hn t γ)
  have hb' : valuation T.Fp (T.ιF b - t) < valuation T.Fp t := by rw [ht]; exact hb
  have hbv : valuation T.Fp (T.ιF b) = γ := by
    rw [← ht]; exact Valuation.map_eq_of_sub_lt _ hb'
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hbv
    exact γ.ne_zero hbv.symm
  obtain ⟨x, hx1, hx2⟩ := T.dense.mem_nhds (Filter.inter_mem (hn c γ) (hn c 1))
  have hx1' : valuation T.Fp (T.ιF x - c) < γ := hx1
  have hx2' : valuation T.Fp (T.ιF x - c) < 1 := by simpa using hx2
  have hx : valuation T.Fp (T.ιF x) ≤ 1 := by
    have : T.ιF x = (T.ιF x - c) + c := by ring
    rw [this]
    exact (valuation T.Fp).map_add_le hx2'.le hc'
  have hxF : p.valuation F x ≤ 1 := by
    have h := val_le_iff T x 1
    simp only [map_one] at h
    exact h.1 hx
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hxF
    (Units.mk0 (p.valuation F b) (by simpa using hb0))
  refine ⟨T.ιF (algebraMap (𝓞 F) F a), hγ ?_, a, rfl⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - x)) < γ := by
    rw [← hbv, ← not_le, val_le_iff, not_le]
    exact ha
  have : T.ιF (algebraMap (𝓞 F) F a) - c = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - c) := by
    rw [map_sub]; ring
  change valuation T.Fp (_ - c) < γ
  rw [this]
  exact (valuation T.Fp).map_add_lt ha' hx1'

theorem locAt_topology : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), IsTopologicalRing A.Ep ∧ T2Space A.Ep ∧ LocallyCompactSpace A.Ep ∧ SecondCountableTopology A.Ep ∧ IsOpen (A.O : Set A.Ep) ∧ IsCompact (A.O : Set A.Ep) ∧ DenseRange A.ιE ∧ Function.Injective A.ιE ∧ (∀ x : E, x ≠ 0 → IsUnit (A.ιE x)) ∧ closure (Set.range fun x : 𝓞 E => A.ιE (x : E)) = (A.O : Set A.Ep) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A
  have hO := GlobalTheory.T.mem_integers_localisation_iff_sum_cmData hc sig hsig p A
  haveI := A.lf
  haveI := A.char0
  haveI := A.free
  haveI := A.top
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  haveI := secondCountable_localField A.Fp
  haveI := t2Space_of_nonarchimedeanLocalField A.Fp
  haveI hR : IsTopologicalRing A.Ep := IsModuleTopology.isTopologicalRing A.Fp A.Ep
  haveI : ContinuousSMul A.Fp A.Ep := IsModuleTopology.toContinuousSMul A.Fp A.Ep
  have hcont : Continuous (algebraMap A.Fp A.Ep) := continuous_algebraMap _ _
  let b := Module.finBasis A.Fp A.Ep
  let h : A.Ep ≃ₜ (Fin (Module.finrank A.Fp A.Ep) → A.Fp) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI hT2 : T2Space A.Ep := h.symm.t2Space
  have hLC : LocallyCompactSpace A.Ep := h.isClosedEmbedding.locallyCompactSpace
  have hSC : SecondCountableTopology A.Ep := h.secondCountableTopology
  let w := RingOfIntegers.basis E
  let L : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A.Fp) →ₗ[A.Fp] A.Ep :=
    Fintype.linearCombination A.Fp (fun i => A.ιE (w i : E))
  have hL : ∀ c, L c = ∑ i, c i • A.ιE (w i : E) := fun c => Fintype.linearCombination_apply _ _ _
  have hint : ∀ x : 𝓞 E, A.ιE (x : E) = L (fun i => (w.repr x i : A.Fp)) := by
    intro x
    rw [hL]
    conv_lhs => rw [← w.sum_repr x]
    simp [Int.cast_smul_eq_zsmul]
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← A.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, y, hn, hy⟩ : ∃ (n : ℤ) (y : 𝓞 E), n ≠ 0 ∧ (y : E) = n • x := by
      obtain ⟨n, hn, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
      exact ⟨n, ⟨_, hi⟩, hn, rfl⟩
    have h1 : A.ιE x = ((n : A.Fp)⁻¹) • A.ιE (y : E) := by
      rw [hy, map_zsmul, ← Int.cast_smul_eq_zsmul A.Fp, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [h1, hint]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hOeq : (A.O : Set A.Ep) = L '' (Set.univ.pi fun _ => (𝒪[A.Fp] : Set A.Fp)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      refine ⟨∑ j, (c j : A.Fp) • (fun i => (w.repr (x j) i : A.Fp)), ?_, ?_⟩
      · intro i _
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (c j).2 (intCast_mem _ _)

      · rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ← hint, Algebra.smul_def]
    · rintro ⟨c, hc, rfl⟩
      rw [hL]
      refine Subring.sum_mem _ fun i _ => (hO _).2 ⟨1, fun _ => ⟨c i, hc i trivial⟩, fun _ => w i, ?_⟩
      simp [Algebra.smul_def]
  have hopen : IsOpen (A.O : Set A.Ep) := by
    rw [hOeq]
    exact IsModuleTopology.isOpenMap_of_surjective hsurj _
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integer_localField A.Fp)
  have hcomp : IsCompact (A.O : Set A.Ep) := by
    rw [hOeq]
    exact (isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[A.Fp]))).image
      (IsModuleTopology.continuous_of_linearMap L)
  refine ⟨hR, hT2, hLC, hSC, hopen, hcomp, ?_, A.ιE.injective,
    fun x hx => (IsUnit.mk0 x hx).map A.ιE, ?_⟩
  · let S : Subring A.Ep := A.ιE.range.topologicalClosure
    have hS : ∀ a : A.Fp, algebraMap A.Fp A.Ep a ∈ S := by
      intro a
      refine map_mem_closure (t := Set.range A.ιE) hcont (A.dense a) ?_
      rintro _ ⟨r, rfl⟩
      exact ⟨_, A.compat r⟩
    intro y
    have hy : y ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
    change y ∈ S
    induction hy using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact S.mul_mem (hS a) hx
  · apply le_antisymm
    · refine closure_minimal ?_ hcomp.isClosed
      rintro _ ⟨x, rfl⟩
      exact (hO _).2 ⟨1, fun _ => 1, fun _ => x, by simp⟩
    · let S : Subring A.Ep := (A.ιE.comp (algebraMap (𝓞 E) E)).range.topologicalClosure
      intro y hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      change _ ∈ S
      refine S.sum_mem fun j _ => S.mul_mem ?_ (subset_closure ⟨x j, rfl⟩)
      refine map_mem_closure (t := Set.range (A.ιE.comp (algebraMap (𝓞 E) E))) hcont
        (mem_closure_int A _ (c j).2) ?_
      rintro _ ⟨r, rfl⟩
      refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
      rw [← A.compat]
      rfl

end GlobalTheory.LocAtTopology
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory

theorem inv_upperUnitriangular (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (hlow : ∀ x y : Fin n, y < x → A x y = 0) (hdiag : ∀ x, A x x = 1) :
    (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧
      ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  have hA : A.BlockTriangular id := fun i j h => hlow i j h
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    simp [hdiag]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (by rw [hdet]; exact isUnit_one)
  have hB : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hlowB : ∀ x y : Fin n, y < x → A⁻¹ x y = 0 := fun x y h => hB h
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one)
  have hdiagB : ∀ x, A⁻¹ x x = 1 := by
    intro x
    have h := congrFun (congrFun hmul x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single x] at h
    · simpa [hdiag] using h
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hlow x j hj, zero_mul]
      · rw [hlowB j x hj, mul_zero]
    · simp
  refine ⟨hlowB, hdiagB, ?_⟩
  intro x y hxy
  have hxy' : x < y := by
    rw [Fin.lt_def]; omega
  have h := congrFun (congrFun hmul x) y
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hxy'),
    Finset.sum_eq_add (x) (y) (ne_of_lt hxy')] at h
  · rw [hdiag x, hdiagB y, one_mul, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro j _ hj
    rcases lt_trichotomy j x with h1 | h1 | h1
    · rw [hlow x j h1, zero_mul]
    · exact absurd h1 hj.1
    · have : y < j := by
        rcases lt_trichotomy j y with h2 | h2 | h2
        · exfalso; rw [Fin.lt_def] at h1 h2; omega
        · exact absurd h2 hj.2
        · exact h2
      rw [hlowB j y this, mul_zero]
  · simp
  · simp

end GlobalTheory
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inv_upperUnitriangular_superdiag_neg : ∀ (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, y < x → A x y = 0) → (∀ x, A x x = 1) → (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧ ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  first | exact @GlobalTheory.inv_upperUnitriangular | exact GlobalTheory.inv_upperUnitriangular | (intros; apply GlobalTheory.inv_upperUnitriangular <;> assumption)

end
end
