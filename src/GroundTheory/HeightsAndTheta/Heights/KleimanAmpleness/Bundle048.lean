module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver secOver secMOver)

noncomputable section

section OneBlock

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

variable {κ : Type} [Fintype κ]


omit [Fintype κ] in
theorem chartRingOver_oneBlock_eq (x : κ → Ω) (c : Unit → κ) :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin F (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩


omit [Fintype κ] in
theorem mem_secOver_oneBlock (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin F (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())


omit [Fintype κ] in
theorem secOver_oneBlock_comp {κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'


omit [Fintype κ] in
theorem relDim_oneBlock_eq_iff (P : Ideal (MvPolynomial (Σ _ : Unit, κ) F)) (e : ℕ) :
    FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MvPolynomial (Σ _ : Unit, κ) F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit]

end OneBlock

section FirstTyping

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}

theorem twistSys_secs_eq_secOver (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys F x n).secs = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_oneBlock]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  change t ∈ Kleiman.twistMod F x n (Kleiman.singleChart hj) ↔ _
  rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
  have hA : Kleiman.chartRing F x (Kleiman.singleChart hj) =
      Algebra.adjoin F (Set.range fun i => x i / x j) :=
    (chartRingOver_oneBlock x (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
  rw [← hA]
  have hxn : x j ^ n ≠ 0 := zpow_ne_zero n hj
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ hxn, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ hxn t

theorem mIdealOver_oneBlock (x : Fin (N + 1) → Ω) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = Kleiman.primeOfOne (S := F) x := by
  have hc : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars F).comp
      (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = (Kleiman.cone (S := F) x).comp (Kleiman.oneBlock (S := F) (N := N)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, Kleiman.oneBlock, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  ext f
  rw [mIdealOver, RingHom.mem_ker, Kleiman.primeOfOne, Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  have h := congrArg (fun φ => φ f) hc
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective).symm

theorem isSubvar_primeOf_iff (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) x) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hX : ∀ i, (X i : Kleiman.Poly F N) ∈ Kleiman.primeOf (S := F) x ↔ x i = 0 := fun i => by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X F i), aeval_X]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.relevant
    exact ⟨⟨i, fun hx => hi ((hX i).mpr hx)⟩, h.dim⟩
  · rintro ⟨⟨i, hi⟩, hdim⟩
    exact ⟨inferInstance, fun p hp d => Kleiman.homogeneousComponent_mem_primeOf x hp d, le_rfl,
      ⟨i, fun h => hi ((hX i).mp h)⟩, hdim⟩

theorem isSubvar_iff_relDim (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ FieldNumbers.relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  rw [isSubvar_primeOf_iff, relDim_oneBlock_eq_iff, mIdealOver_oneBlock, HilbertPositive.ringKrullDim_primeOfOne]

end FirstTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GraphRestrict.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω)
    (K' : Type) [Field K'] [Algebra k K'] (x' : Fin (N + 1) → K') (s' : Fin m → K')
    (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0),
    IsGraphGen Q n s → mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') →
    (∃ i, x' i ≠ 0) → (∃ j, s' j ≠ 0) →
    ∃ (Q' : Kleiman.LineBundle k x') (r : Ω → K'),
      Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ IsGraphGen Q' n s'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def DegEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)),
      Kleiman.IsSubvar x pp 1 → NumbersDVR.IsMultiProjPrime W → mIdealOver k (graphVec x s) ≤ W →
      W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp →
      NumbersDVR.intNum k W ![graphDeg n] = Kleiman.interNum pp ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveComap.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ e : ℕ,
        (relDim W = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
          Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveLift.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (e : ℕ), Kleiman.IsSubvar x pp e →
      ∃ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W ∧
        mIdealOver k (graphVec x s) ≤ W ∧ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibreIdeal.Statement : Prop :=
  ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (F : Type) [Field F] (φ : O →+* F)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω),
    segreRels ι F ⊆ ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) : Set _) ∧
    (mIdealOver O y).map (MvPolynomial.map φ) ≤
      ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ)).comap (segreIncl ι F) ∧
    ∀ W : Ideal (MRing ι F), (mIdealOver O y).map (MvPolynomial.map φ) ≤ W →
      (mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) ≤ segreLift ι F W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dite_eq_left hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

def ModelCechRefine.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (T : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω),
      (∀ J, (T.sub J : Set Ω) = chartSecOver F y k₀ e γ J) →
      ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellH F y γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelRowExact.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      CellAugExact F y (fun I => cellSec F y γ (baseCell k₀ e J.1 I))
        (Submodule.span F (chartSecOver F y k₀ e γ J))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)),
    (∀ k, (I k).Nonempty) → CellMeets y I →
      chartSecOver S y k₀ e γ J ⊆ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSecGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (a : Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → a ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) →
      a ∈ chartSecOver S y k₀ e γ J

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def BlockGenOfModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → BlockGen S y k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
