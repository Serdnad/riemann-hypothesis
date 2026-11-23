module

import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalNeZeroOfMemCellMon
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem cellSec_mono [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  classical
  unfold cellSec
  rw [if_pos hI']
  split_ifs with hI
  · refine Submodule.span_mono ?_
    rintro z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩
    refine ⟨g, t, a, ?_, hta, hγ, hg, rfl⟩
    refine Submonoid.closure_mono ?_ ht
    rintro f ⟨k, i, hi, rfl⟩
    exact ⟨k, i, h k hi, rfl⟩
  · exact bot_le

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem subset_baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) : I k ⊆ baseCell k₀ e J I k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self]; exact Finset.subset_union_left
  · rw [Function.update_of_ne hk]

theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {J J' : Finset (Fin (N + 1))}
    {I I' : ∀ k, Finset (ι k)} (hJ : J ⊆ J') (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J' I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

theorem cellMeets_baseCell (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) :
    CellMeets y (baseCell k₀ e J.1 I) := by
  apply _root_.GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.cellMeets_baseCell <;> assumption

theorem ModelCechRefine.proof (hC : CechContract.Statement) (hR : ModelRowExact.Statement)
    (hD : DoubleCech.Statement) : ModelCechRefine.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n
  have hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I →
      cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun J I hI => by
    unfold cellSec
    rw [if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]
  have hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 →
      cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I) := fun J J' I h => by
    by_cases hI : CellMeets y I
    · exact cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (cellMeets_baseCell y k₀ e J' hI)
    · rw [hM0 J I hI]; exact bot_le
  refine (hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_
    (fun I hI => by unfold cellSec; rw [if_neg hI]) hM0 hMJ
    (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (cellMeets_baseCell y k₀ e J hI'))
    ?_ ?_ n)
  · obtain ⟨i, hi⟩ := hM.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  · intro I hne hI
    obtain ⟨i, hi⟩ := hne k₀
    have hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hI k₀ i hi
    let J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) :=
      ⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩
    have hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I := by
      intro J
      unfold baseCell
      congr 1
      rw [Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]
      congr 1
      exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))
    have h₀ : baseCell k₀ e J₀.1 I = I := by
      have := hadd ∅
      rw [Finset.union_empty] at this
      rw [show J₀.1 = {e i} from rfl, this]
      unfold baseCell
      simp
    have := hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _)
      (fun J J' h => hMJ J J' I h) (fun J J' h => by
        show cellSec F y γ (baseCell k₀ e J'.1 I) = _
        rw [h]; exact congrArg _ (hadd J.1))
    simpa only [h₀] using this
  · intro J
    have h := hR F K ι Ω y k₀ N e hM γ J
    rwa [← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq] at h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  change MvPolynomial.X i ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.coneMap F x)
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
    let e : ι k₀ ≃ Fin (Fintype.card (ι k₀) - 1 + 1) :=
      (Fintype.equivFin _).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    have hs := (hDim F K ι Ω y k₀ _ e hmod d).mpr hdim
    have hn := (hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q hs hn t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    have hx := exists_ne_zero_of_isSubvar hs
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
      (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hgen : IsGraphGen M n g := hg
    have hmod := GraphModel.full k N Ω x M n (r + 1) g hx hgen
    have hsec := twist_secs_eq_secOver M n g hgen
    have hdim := (hDim k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod d).mp hs
    have hnef' := (hNef k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec).mp hnef
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock hmod hdim
      (graphDeg n) hnef' t ht
    exact ⟨a, m, ha, hm, (hVA k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec a m ha).mpr hva⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem SectionCount.bound_from_one {X : ℝ} {d : ℕ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  refine ⟨max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)), fun n hn => ?_⟩
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rcases le_or_gt n₀ n with h | h
  · have h1 := hn₀ n h
    have h2 : C * (n : ℝ) ^ d ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (n : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hX : X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
        |X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc X * (n : ℝ) ^ (d + 1) ≤ |X| * (n : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self X) (by positivity)
        _ ≤ |X| * (n₀ : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) _)
              (abs_nonneg X)
    have hM := le_max_right C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))
    have hM0 : 0 ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) :=
      le_trans (by positivity) hM
    have h3 := le_mul_of_one_le_right hM0 hnd
    linarith [hf n]

theorem SectionCount.exists_ne_zero_of_isSubvar {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {e : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := k) x) e) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  rw [Kleiman.primeOf, ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal, RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem SectionCount.transfer (hBase : BaseRealises.Statement)
    (hP : PowRealises.Statement) (hN : NumModel.Statement)
    (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω) (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (Q : Kleiman.LineBundle F x) (ν : K → ℤ)
    (hQ : BundleRealises y k₀ Q ν) (d q : ℕ) (hsub : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) (d + 1)) :
    ((Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) -
        ((d + 1 : ℕ) : ℤ) * Kleiman.interNum (Kleiman.primeOf (S := F) x)
          (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
            (fun _ : Fin d => Q.toSubSystem)) : ℤ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
        ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F y)
          (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℝ) ∧
    ∀ n : ℕ, (Kleiman.twistMul Q.toSubSystem n (-((n : ℤ) * q))).secs =
      secOver F y (n • (ν - q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
  have h1 : Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) =
      NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) :=
    hN F K ι Ω y k₀ N e x hx hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  have hqs : ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    funext j; simp
  have hL : (fun i => (Fin.cons (α := fun _ => Kleiman.LineBundle F x) (Kleiman.twistBundle F x (q : ℤ))
      (fun _ : Fin d => Q) i).toSubSystem) =
      Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have h2 : Kleiman.interNum (Kleiman.primeOf (S := F) x)
      (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem)) =
      NumbersDVR.intNum F (mIdealOver F y)
        (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
    rw [NumbersDVR.VerticalDivisorsCommuting.intNum_snoc, ← hL, ← hqs]
    exact hN F K ι Ω y k₀ N e x hx hmod (d + 1) _ (Fin.cons ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) fun _ => ν)
      (fun i => Fin.cases (hBase F K ι Ω y k₀ N e x hx hmod (q : ℤ)) (fun _ => hQ) i) hsub
  refine ⟨by rw [h1, h2]; push_cast; ring, fun n => ?_⟩
  rw [hP F K ι Ω y k₀ N e x hx hmod Q ν hQ n (-((n : ℤ) * q))]
  congr 1
  funext j
  simp only [smul_eq_mul, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply]
  ring

theorem SectionCount.equiv (hG : GraphModel.Statement) (hB : BundleOfDeg.Statement) (hD : ModelDim.Statement)
    (hBase : BaseRealises.Statement) (hP : PowRealises.Statement) (hV : VeryAmpleModel.Statement)
    (hN : NumModel.Statement) :
    Kleiman.SectionCount.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := by
  constructor
  · intro hA F _ K _ _ ι _ Ω _ _ y k₀ d ν q hmod hdim hva hq
    have hpos : 0 < Fintype.card (ι k₀) := by
      obtain ⟨i, -⟩ := hmod.1 k₀
      exact Fintype.card_pos_iff.2 ⟨i⟩
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
    obtain ⟨Q, hQ⟩ := hB F K ι Ω y k₀ N e hmod ν
    have hsub := (hD F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
    have hvaQ := (hV F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN F K ι Ω y k₀ N e _ rfl hmod Q ν hQ d q hsub
    obtain ⟨C, hC⟩ := hA F Ω N _ d Q q hsub hvaQ hq
    refine SectionCount.bound_from_one (fun n => Nat.cast_nonneg _) ⟨C, hC.mono fun n hn => ?_⟩
    rw [← hZ, ← hS n]
    exact hn
  · intro hB' k _ Ω _ _ N x d Nb b hsub hva hb
    obtain ⟨r, h, hby⟩ := hva
    have hgen : IsGraphGen Nb 0 h := fun I => by
      rw [Kleiman.SubSystem.twist_twistSys_zero]
      exact hby.generates I
    have hmod := hG k N Ω x Nb 0 (r + 1) h (SectionCount.exists_ne_zero_of_isSubvar hsub) hgen
    have hQ := realises_graph Nb 0 h hgen
    have hdim := (hD k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod (d + 1)).1 hsub
    have hvaB := (hV k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod Nb (graphDeg 0) hQ).1 ⟨r, h, hby⟩
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω
      (graphVec x h) baseBlock N (Equiv.refl _) x rfl hmod Nb (graphDeg 0) hQ d b hsub
    obtain ⟨C, hC⟩ := hB' k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock d (graphDeg 0) b
      hmod hdim hvaB hb
    refine ⟨C, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    rw [hZ, hS n]
    exact hC n hn

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelMulSecs.of_powRealises (h : PowRealises.Statement) : ModelMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p j => h F K ι Ω y k₀ N e _ rfl hmod Q β hQ p j

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelCechTwist.proof (hMul : ChartSecMul.Statement) (hBase : BaseRealises.Statement)
    (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) : ModelCechTwist.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM β Q hQ p b m c i

  have hbun : ∀ (L : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : K → ℤ),
      BundleRealises y k₀ L δ → ∀ J, (L.sub J : Set Ω) = chartSecOver F y k₀ e δ J := by
    intro L δ hL J
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hL]
  have hO : ∀ (a : ℤ) J,
      ((Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) a).sub J : Set Ω) =
        chartSecOver F y k₀ e (a • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) J := fun a =>
    hbun (Kleiman.twistBundle F _ a) _ (hBase F K ι Ω y k₀ N e _ rfl hM a)

  have hmul : ∀ (R R' : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ δ' : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      (∀ J, (R'.sub J : Set Ω) = chartSecOver F y k₀ e δ' J) →
      ∀ J, ((R.twist R').sub J : Set Ω) = chartSecOver F y k₀ e (δ' + δ) J := by
    intro R R' δ δ' hR hR' J
    rw [twist_sub_eq_mul, Submodule.mul_eq_span_mul_set, hR' J, hR J]
    exact hMul F K ι Ω y k₀ N e hM δ' δ J
  have hpow : ∀ (R : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      ∀ (n : ℕ) J, ((R.pow n).sub J : Set Ω) = chartSecOver F y k₀ e (n • δ) J := by
    intro R δ hR n
    induction n with
    | zero =>
      intro J
      have h0 := hO 0 J
      rw [zero_smul] at h0
      rw [zero_smul]
      exact h0
    | succ n ih =>
      intro J
      rw [succ_nsmul']
      exact hmul _ _ _ _ ih hR J
  have hT := hmul _ _ _ _ (hpow _ _ (hmul _ _ _ _ (hpow _ _ (hbun Q β hQ) p) (hO m)) b) (hO c)
  have hγ : c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + b • (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + p • β) =
      b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp only [IndefiniteRowSideFullHecke.Kleiman2.stepL]
    module
  rw [hγ] at hT
  obtain ⟨e₁⟩ := hRef F K ι Ω y k₀ N e hM _ _ hT i
  obtain ⟨e₂⟩ := hLoc F K ι Ω y _ i
  exact ⟨e₁.trans e₂⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelNumEq.proof (hN : NumModel.Statement) : ModelNumEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d βs Qs hsecs hsub
  exact hN F K ι Ω y k₀ N e _ rfl hmod d Qs βs (fun j c => hsecs j c) hsub

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem ModelCurveNum.proof (hN : CurveNumModel.Statement) : ModelCurveNum.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hb
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hm β
  have hQ' : BundleRealises y' k₀' Q β' := fun c => (hQ c).trans (hs c)
  have h1 := hN F K ι Ω y k₀ N e _ rfl hm Q β hQ W hW hle hrel
  have h2 := hN F K' ι' Ω y' k₀' N e' _ hx hm' Q β' hQ' W' hW' hle' hrel'
  have hc : W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      W'.comap (rename fun a : Fin (N + 1) => (⟨k₀', e'.symm a⟩ : Σ k, ι' k)) := by
    ext p
    have := SetLike.ext_iff.mp hb (rename (fun a : Fin (N + 1) => (⟨(), a⟩ : Σ _ : Unit, Fin (N + 1))) p)
    simp only [baseComap, Ideal.mem_comap, rename_rename] at this
    exact this
  rw [h1, h2, hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
