module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

theorem coneMap_rename {F : Type} [Field F] {κ : Type} {Ω : Type} [Field Ω] [Algebra F Ω] (x' : κ → Ω) {N : ℕ}
    (e : κ ≃ Fin (N + 1)) (p : NumbersDVR.MRing (fun _ : Unit => κ) F) :
    uniqueAlgEquiv Ω Unit (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p) =
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename (fun v : Σ _ : Unit, κ => e v.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

theorem ReindexDim.proof : ReindexDim.Statement := by
  intro F _ κ _ Ω _ _ x' N e
  let σ : (Σ _ : Unit, κ) ≃ Fin (N + 1) :=
    { toFun := fun v => e v.2, invFun := fun i => ⟨(), e.symm i⟩, left_inv := fun _ => by simp,
      right_inv := fun _ => by simp }
  let f : NumbersDVR.MRing (fun _ : Unit => κ) F ≃+* Kleiman.Poly F N := (renameEquiv F σ).toRingEquiv
  have hc : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      (Kleiman.primeOf (S := F) (x' ∘ e.symm)).comap f.toRingHom := by
    ext p
    change mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p = 0 ↔
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename σ p) = 0
    rw [← (uniqueAlgEquiv Ω Unit).injective.eq_iff, map_zero]
    exact Iff.of_eq (congrArg (· = 0) (coneMap_rename x' e p))
  have h : Kleiman.primeOf (S := F) (x' ∘ e.symm) = (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Local

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem spanSecs_mem_locIn_self {A : Subalgebra F Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem spanSecs_mul_step {B : Subalgebra F Ω} {q : Ideal B} [hq : q.IsPrime] {T : Set Ω} {u g : Ω}
    (hg : g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (hu : ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * (g * u) ∈ Submodule.span B T := by
  obtain ⟨b, hb, hbu⟩ := hu
  obtain ⟨a, b', hb', rfl⟩ := mem_locIn.mp hg
  refine ⟨b' * b, fun h => (hq.mem_or_mem h).elim hb' hb, ?_⟩
  have h0 := coe_ne_zero_of_not_mem hb'
  have e : ((b' * b : B) : Ω) * ((a : Ω) / b' * u) = a • ((b : Ω) * u) := by
    rw [Subalgebra.smul_def, smul_eq_mul, Subalgebra.coe_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ hbu

theorem spanSecs_exists_mul_mem (B C : Subalgebra F Ω) (q : Ideal B) [hq : q.IsPrime]
    (hC : ∀ a ∈ C, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (T : Set Ω) {u : Ω} (hu : u ∈ Submodule.span C T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T := by
  induction hu using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_not_mem_of_prime hq, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_not_mem_of_prime hq, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨b₁, hb₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, fun h => (hq.mem_or_mem h).elim hb₁ hb₂, ?_⟩
    have e : ((b₁ * b₂ : B) : Ω) * (z + w) = b₂ • ((b₁ : Ω) * z) + b₁ • ((b₂ : Ω) * w) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul a z _ hz =>
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact spanSecs_mul_step (hC _ a.2) hz

theorem spanSecs_mem_of_local (B : Subalgebra F Ω) (T : Set Ω) (u : Ω)
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    u ∈ Submodule.span B T := by
  let J : Ideal B := (Submodule.span B T).comap (LinearMap.toSpanSingleton B Ω u)
  have hJ : ∀ b : B, b ∈ J ↔ (b : Ω) * u ∈ Submodule.span B T := fun b => Iff.rfl
  by_cases hJt : J = ⊤
  · have h1 : (1 : B) ∈ J := hJt ▸ Submodule.mem_top
    simpa using (hJ 1).mp h1
  · obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJt
    obtain ⟨b, hb, hbu⟩ := h q hq
    exact absurd (hJq ((hJ b).mpr hbu)) hb

end Local

theorem SpanSecs.proof : SpanSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod T d s
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  let B : ι k₀ → Subalgebra F Ω := fun i' =>
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => i')
  have hB : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), Kleiman.chartRing F x (Kleiman.singleChart hi) = B (e.symm i) := by
    intro i hi
    rw [← chartRingOver_oneBlock_eq_chartRing (S := F) x (fun _ => i) hi]
    unfold B chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e.symm l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩

  have hBc : ∀ c : ∀ k, ι k, B (c k₀) ≤ chartRingOver F y c := by
    intro c
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨_, l⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, l⟩, rfl⟩
  constructor
  · intro hs c hc
    have hi : x (e (c k₀)) ≠ 0 := by rw [hxv, Equiv.symm_apply_apply]; exact hc k₀
    set A := Kleiman.chartRing F x (Kleiman.singleChart hi) with hA
    have hAc : A ≤ chartRingOver F y c := by
      rw [hA, hB, Equiv.symm_apply_apply]; exact hBc c
    have hs' := Submodule.mem_iInf _ |>.mp hs (Kleiman.singleChart hi)
    rw [Submodule.restrictScalars_mem,
      Kleiman.twistMod_eq_span d _ (Finset.mem_singleton_self (e (c k₀)))] at hs'
    have hv : y ⟨k₀, c k₀⟩ = x (e (c k₀)) := by rw [hxv, Equiv.symm_apply_apply]
    rw [hv]
    refine Submodule.mul_induction_on hs' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have e1 : m * (a • x (e (c k₀)) ^ d) * x (e (c k₀)) ^ (-d) = (⟨a, hAc a.2⟩ : chartRingOver F y c) • m := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, zpow_neg]
        field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (span_subset_span hAc T hm)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    rw [Submodule.restrictScalars_mem]
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hiI)
    rw [Kleiman.twistMod_eq_span d I hiI]
    have hle : Kleiman.chartRing F x (Kleiman.singleChart hi) ≤ Kleiman.chartRing F x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiI)

    suffices key : s * x i ^ (-d) ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.singleChart hi)) T by
      have e1 : s = s * x i ^ (-d) * x i ^ d := by
        rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero d hi), mul_one]
      rw [e1]
      exact Submodule.mul_mem_mul (span_subset_span hle T key) (Submodule.subset_span rfl)
    rw [hB i hi]
    have hxi' : y ⟨k₀, e.symm i⟩ ≠ 0 := by rw [← hxv]; exact hi
    refine spanSecs_mem_of_local _ T _ fun q hq => ?_
    have := hq.isPrime

    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q ∈
        IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
      ⟨fun _ => e.symm i, fun _ => hxi', q, hq.isPrime, rfl⟩
    rw [← hmod.2] at hz
    obtain ⟨c, hc, p, hp, hzp⟩ := hz
    have := hp
    have hCz : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      intro a ha
      rw [hzp]
      exact spanSecs_mem_locIn_self ha

    set w := y ⟨k₀, c k₀⟩ with hw
    set v := y ⟨k₀, e.symm i⟩ with hvdef
    have hw0 : w ≠ 0 := hc k₀
    have h1 : w / v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      spanSecs_mem_locIn_self (Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩)
    have h2 : v / w ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      hCz _ (Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩)
    have hg : (w / v) ^ d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
      · rw [zpow_natCast]; exact pow_mem h1 n
      · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem h2 n
    have e2 : s * x i ^ (-d) = (w / v) ^ d * (s * w ^ (-d)) := by
      rw [hxv, ← hvdef, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e2]
    exact spanSecs_mul_step hg (spanSecs_exists_mul_mem _ _ q hCz T (h c hc))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem sum_block_eq_blockWeight (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, e ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]


omit [DecidableEq K] in
theorem mConeMapOver_eq_of_block (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) S} {d : K → ℕ}
    (hf : ∀ e ∈ f.support, ∀ k, ∑ i, e ⟨k, i⟩ = d k) :
    mConeMapOver S y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ e p =
      ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ e ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf e he k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMapOver (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MvPolynomial (Σ k, ι k) S) :
    AddMonoidAlgebra.coeff (mConeMapOver S y f) (Finsupp.equivFunOnFinite.symm b) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) e c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) e = _)
    have hb : ∀ e' ∈ (monomial e c : MvPolynomial (Σ k, ι k) S).support, ∀ k,
        ∑ i, e' ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
      intro e' he' k
      rw [sum_block_eq_blockWeight, hm (mem_support_iff.mp he')]
    rw [mConeMapOver_eq_of_block y hb,
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) e k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) e)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) e
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]

theorem isMultiHomogIdeal_mIdealOver (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := S) (mIdealOver S y) := by
  intro f hf b
  have hf' : mConeMapOver S y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  have hb : ∀ e' ∈ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f).support, ∀ k,
      ∑ i, e' ⟨k, i⟩ = b k := by
    intro e' he' k
    rw [sum_block_eq_blockWeight,
      weightedHomogeneousComponent_isWeightedHomogeneous b f (mem_support_iff.mp he')]
  rw [mConeMapOver_eq_of_block y hb, ← coeff_mConeMapOver, hf']
  simp

theorem isMultiProjPrime_mIdealOver (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S y) := by
  refine ⟨RingHom.ker_isPrime (mConeMapOver S y), isMultiHomogIdeal_mIdealOver y, ?_⟩
  intro k
  obtain ⟨i, hi⟩ := hy k
  refine ⟨i, fun h => ?_⟩
  have h' : mConeMapOver S y (X ⟨k, i⟩) = 0 := RingHom.mem_ker.mp h
  simp only [mConeMapOver, aeval_X] at h'
  exact mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (X_ne_zero _) h'

end Homog

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ}

theorem mConeMapOver_graph_comp_base (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mConeMapOver S (graphVec x s)).comp
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      ((Polynomial.aeval (X baseBlock : MvPolynomial (Unit ⊕ Unit) Ω)).restrictScalars S).comp
        (Kleiman.cone (S := S) x) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem cone_eq_graph_comp (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    Kleiman.cone (S := S) x =
      ((aeval fun _ : Unit ⊕ Unit => (Polynomial.X : Polynomial Ω)).restrictScalars S).comp
        ((mConeMapOver S (graphVec x s)).comp
          (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem comap_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mIdealOver S (graphVec x s)).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      Kleiman.primeOf (S := S) x := by
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver S (graphVec x s) (rename _ f) = 0 ↔ _
  constructor
  · intro h
    rw [cone_eq_graph_comp x s, AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero]
  · intro h
    rw [← AlgHom.comp_apply, mConeMapOver_graph_comp_base, AlgHom.comp_apply, h, map_zero]

theorem isMultiProjPrime_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (hx : ∃ i, x i ≠ 0)
    (hs : ∃ j, s j ≠ 0) : NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S (graphVec x s)) :=
  isMultiProjPrime_mIdealOver _ (by rintro (⟨⟩ | ⟨⟩); exacts [hx, hs])

end Graph

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def GraphModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (graphVec x s) baseBlock

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def RatioDim.Statement : Prop :=
  ∀ (k : Type) [Field k] (N m : ℕ) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)), W.IsPrime →
    NumbersDVR.IsMultiHomogIdeal W → ∀ j : Fin m,
      (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
      (∀ b : Fin m, ∃ f g : Kleiman.Poly k N,
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W) →
      ringKrullDim (NumbersDVR.MRing (graphIdx N m) k ⧸ W) =
        ringKrullDim (Kleiman.Poly k N ⧸ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) + 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

def BundleRealises {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {x : Fin (N + 1) → Ω}
    (Q : Kleiman.LineBundle S x) (β : K → ℤ) : Prop :=
  ∀ c : ℤ, (Q.toSubSystem.twist (Kleiman.twistSys S x c)).secs =
    secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem realises_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    BundleRealises (graphVec x s) baseBlock Q (graphDeg n) :=
  fun c => twist_secs_eq_secOver Q n s hgen c

end Graph

section Point

variable (k : Type) [Field k]

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NefEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s → (Kleiman.Nef Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef k (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
