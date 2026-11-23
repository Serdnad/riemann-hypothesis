module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectors
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv

@[expose] public section

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.DerivedSeriesAdjoint : DsAd := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsAd.dsAd | exact GlobalTheory.CompanionTheory.BmuDsAd.dsAd | (intros; apply GlobalTheory.CompanionTheory.BmuDsAd.dsAd <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.DerivedSeriesLinear : DsLin := by
  first | exact @GlobalTheory.CompanionTheory.BesselMapSm.dsLin | exact GlobalTheory.CompanionTheory.BesselMapSm.dsLin | (intros; apply GlobalTheory.CompanionTheory.BesselMapSm.dsLin <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.truncated_derivation_limit : Factor → CutDer → CutLim := by
  first | exact @GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | exact GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | (intros; apply GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.TruncatedDerivation : CutDer := by
  first | exact @GlobalTheory.CompanionTheory.CutDeriv.cutDer | exact GlobalTheory.CompanionTheory.CutDeriv.cutDer | (intros; apply GlobalTheory.CompanionTheory.CutDeriv.cutDer <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.factorization' : Factor := by
  first | exact @GlobalTheory.CompanionTheory.BmuFactor.factor | exact GlobalTheory.CompanionTheory.BmuFactor.factor | (intros; apply GlobalTheory.CompanionTheory.BmuFactor.factor <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.quotient_bound_of_factor_reduce_chart : Factor → Reduce → ChartExists → QBound := by
  first | exact @GlobalTheory.CompanionTheory.BmuQBound.qBound | exact GlobalTheory.CompanionTheory.BmuQBound.qBound | (intros; apply GlobalTheory.CompanionTheory.BmuQBound.qBound <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.reduction_of_derived_series : DsLin → DsAd → DsDer → Reduce := by
  first | exact @GlobalTheory.CompanionTheory.BmuReduce.reduce | exact GlobalTheory.CompanionTheory.BmuReduce.reduce | (intros; apply GlobalTheory.CompanionTheory.BmuReduce.reduce <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.ChartExistence : ChartExists := by
  first | exact @GlobalTheory.CompanionTheory.ProdExChart.chartExists | exact GlobalTheory.CompanionTheory.ProdExChart.chartExists | (intros; apply GlobalTheory.CompanionTheory.ProdExChart.chartExists <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.DerivedSeriesDerivation : DsDer := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsDer.dsDer | exact GlobalTheory.CompanionTheory.BmuDsDer.dsDer | (intros; apply GlobalTheory.CompanionTheory.BmuDsDer.dsDer <;> assumption)
end

section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.RootVectors : RootVec := by
  first | exact @GlobalTheory.CompanionTheory.BmuRootVec.rootVec | exact GlobalTheory.CompanionTheory.BmuRootVec.rootVec | (intros; apply GlobalTheory.CompanionTheory.BmuRootVec.rootVec <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Chains

theorem cre_single {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Pos n) (S : Finset (Pos n)) (w : V)
    (h : f ∉ S) :
    (cre f : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) =
      CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V) := by
  funext A
  show (if f ∈ A then CompanionTheory.D.LK.sg f A • (Pi.single S w : Cn n V) (A.erase f) else 0) = _
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (Finset.mem_insert_self f S), Finset.erase_insert h]
    simp [Pi.single_apply]
  · have hr : (CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V)) A = 0 := by
      simp [Pi.single_apply, hA]
    rw [hr]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun he => hA (by rw [← he, Finset.insert_erase hf])
      simp [Pi.single_apply, hne]
    · rfl

theorem sg_ne_zero {n : ℕ} (f : Pos n) (A : Finset (Pos n)) : CompanionTheory.D.LK.sg f A ≠ 0 := by
  delta CompanionTheory.D.LK.sg
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

theorem prod_cre_single : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  intro n V _ _ l S w
  induction l with
  | nil =>
    intro _ _
    refine ⟨1, one_ne_zero, ?_⟩
    simp
  | cons a l ih =>
    intro hnd hS
    obtain ⟨c, hc, hcl⟩ := ih hnd.of_cons (fun i hi => hS i (by simp [hi]))
    have ha : a ∉ S ∪ l.toFinset := by
      rw [Finset.mem_union, not_or, List.mem_toFinset]
      exact ⟨hS a (by simp), (List.nodup_cons.1 hnd).1⟩
    refine ⟨c * CompanionTheory.D.LK.sg a (insert a (S ∪ l.toFinset)), mul_ne_zero hc (sg_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons]
    show cre a (((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V)) = _
    rw [hcl, map_smul, cre_single a _ w ha, smul_smul, List.toFinset_cons, Finset.union_insert]

end GlobalTheory.CompanionTheory.Chains
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FarReg

theorem highest_preimage_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (T : Submodule ℂ E) (a b : ι → Module.End ℂ E) (D : Module.End ℂ E) (y : E)
    (hT : FiniteDimensional ℂ T)
    (hadj : ∀ i x z, ⟪a i x, z⟫_ℂ = ⟪x, b i z⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) :
    ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ {z | ∃ i, ∃ t ∈ T, z = b i t}
  have hST : S ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, t, ht, rfl⟩
    exact hbT i t ht
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hST
  obtain ⟨u, huS, w, hw, hyuw⟩ := S.exists_add_mem_mem_orthogonal y
  have hbS : ∀ i, ∀ t ∈ T, b i t ∈ S := fun i t ht => Submodule.subset_span ⟨i, t, ht, rfl⟩
  have huT : u ∈ T := hST huS
  have hwT : w ∈ T := by
    have : w = y - u := by rw [hyuw]; abel
    rw [this]
    exact T.sub_mem hy huT
  have haw : ∀ i, a i w = 0 := by
    intro i
    have h0 : ⟪a i w, a i w⟫_ℂ = 0 := by
      rw [hadj]
      exact (Submodule.mem_orthogonal' S w).1 hw _ (hbS i _ (haT i w hwT))
    exact inner_self_eq_zero.1 h0
  have har : ∀ i, a i (D u) = 0 := by
    intro i
    have h1 : a i (D y) = a i (D u) + D (a i w) := by
      rw [← haD i w hwT, ← map_add (f := _), ← map_add (f := _), hyuw]
    rw [hDy i, haw i, map_zero, add_zero] at h1
    exact h1.symm
  have hperp : ∀ z ∈ S, ⟪D u, D z⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, t, ht, rfl⟩ := hz
      rw [← hbD i t ht, ← hadj, har i, inner_zero_left]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add (f := _), inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [map_smul, inner_smul_right, hx, mul_zero]
  have hDu : D u = 0 := inner_self_eq_zero.1 (hperp u huS)
  exact ⟨w, hwT, haw, by rw [hyuw, map_add (f := _), hDu, zero_add]⟩

theorem highest_preimage_of_stable : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  intro n V _ _ ι T a b D y hT hadj haT hbT haD hbD hy hDy
  let e : Cn n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Pos n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Pos n) → V)).symm
  let c : Module.End ℂ (Cn n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Pos n) => V)) := fun f =>
    (e : Cn n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cn n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

end GlobalTheory.CompanionTheory.FarReg
end
