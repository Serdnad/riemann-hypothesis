module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private noncomputable def listProd {ι : Type} {a b : ℕ} (d : ι → Ex (Fin (a + 1) × Fin (b + 1))) :
    List ι → Ex (Fin (a + 1) × Fin (b + 1))
  | [] => .one
  | i :: l => .mul (d i) (listProd d l)

private theorem list_prod_unitary_test {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (h : ∀ i, U1 (d i)) : ∀ l : List ι, U1 (listProd d l)
  | [] => .one
  | i :: l => .mul (h i) (list_prod_unitary_test h l)

private theorem listProd_ev_zero {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (x : Fin (a + 1) × Fin (b + 1) → ℂ) {i : ι} (h0 : (d i).ev x = 0) :
    ∀ l : List ι, i ∈ l → (listProd d l).ev x = 0
  | [], h => by simp at h
  | j :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [listProd, Ex.ev, h0]
    · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

open scoped Classical in
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.enlarge :
    StUnit → EvaluationAtUnitaryOne → SeparatesUnitaryOne → Places → Enlarge := by
  intro hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC
  obtain ⟨-, hcp, -, hsec⟩ := hPl E
  have hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0 := fun i =>
    hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2
  choose d hdU hd0 using hd
  haveI : Fintype I := Fintype.ofFinite I
  have hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S := by
    intro w hw
    have hc : cPl w = w := by
      by_contra h
      exact hw ((hcp w).2.2 h)
    rcases (hsec S hS w).1 with h | h
    · exact h
    · rwa [hc] at h
  have hTns : ∀ w ∈ T, IsSplitAt w := fun w hw => (hT w hw).2
  have hZns : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hZ w hw).2
  let L : Pl E → List I := fun w => (Finset.univ.filter fun i => u i = w).toList
  let T' : Finset (Pl E) := T ∪ Finset.univ.image u
  let f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₁ w else listProd d (L w)
  let f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₂ w else .one
  have hfU : ∀ w, w ∉ T → U1 (f₁ w) := by
    intro w hw
    simp only [f₁, if_neg hw]
    exact list_prod_unitary_test hdU _
  have hf₂ : ∀ w, w ∉ T → f₂ w = .one := fun w hw => by simp only [f₂, if_neg hw]
  have hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w := by
    intro w hw hwT
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd h hwT
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (hC i).1
  have huT : ∀ i, u i ∉ T := fun i h => (hC i).1 (hTns _ h)
  refine ⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwT : w ∈ T
    · exact (hT w hwT).1
    · exact hnsS w (hT'ns w hw hwT)
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    by_cases hwT : w ∈ T
    · exact Finset.disjoint_left.1 hTZ hwT hwZ
    · exact hT'ns w hw hwT (hZns w hwZ)
  · intro w hw hns
    have hwT : w ∉ T := fun h => hns (hTns w h)
    exact hf₂ w hwT
  · intro i
    refine Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
    have : ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0 := by
      simp only [f₁, if_neg (huT i)]
      refine listProd_ev_zero _ (hd0 i) _ ?_
      simp [L]
    rw [this, zero_mul]
  · intro B₁ B₂ hB
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
    symm
    have hsub : T ⊆ T' := Finset.subset_union_left
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun w hw => ?_
      simp only [f₁, f₂, if_pos hw]
    · intro w hw hwT
      rcases Finset.mem_union.1 hw with h | h
      · exact absurd h hwT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      rw [hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]
      simp [ev2, Ex.ev]
  · intro l₁ l₂ φ k
    have hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
        stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w) := by
      intro w Q₁ Q₂ h₁ h₂
      unfold fam
      by_cases hwZ : w ∈ Z
      · simp only [if_pos hwZ]
      simp only [if_neg hwZ]
      by_cases hwT : w ∈ T
      · have hw' : w ∈ T' := Finset.mem_union_left _ hwT
        simp only [if_pos hwT, if_pos hw', f₁, f₂]
      by_cases hw' : w ∈ T'
      · simp only [if_neg hwT, if_pos hw']
        rw [hf₂ w hwT]
        exact hSt E hunr w (hT'ns w hw' hwT) a b _
          (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂
      · simp only [if_neg hwT, if_neg hw']
    unfold PositivityTheory.Rg.BcB.G8.geomSt2
    refine finsum_mem_congr rfl fun p hp => ?_
    congr 1
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    exact hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.endoS :
    Enlarge → Places → EndoBlockG → EndoBlockS := by
  intro hEn hP hG E _ _ _ hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  obtain ⟨J, _, D₁, D₂, B₁, B₂, hSat, hInf, hGr⟩ := hG E hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := fun w hw => by
    have hc : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hz : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hz, by rw [hc]; exact hz⟩
  let St : J → Prop := fun j =>
    ∀ w : Pl E, ¬ IsSplitAt w → inv (B₁ j w) = B₁ j w ∧ inv (B₂ j w) = B₂ j w
  have hu : ∀ i : {j // ¬ St j}, ∃ w : Pl E, ¬ IsSplitAt w ∧
      ¬ (inv (B₁ i.1 w) = B₁ i.1 w ∧ inv (B₂ i.1 w) = B₂ i.1 w) := fun i => by
    by_contra h
    exact i.2 fun w hw => by_contra fun h' => h ⟨w, hw, h'⟩
  choose u hu₁ hu₂ using hu
  classical
  refine ⟨{j // St j}, inferInstance, fun j => D₁ j.1, fun j => D₂ j.1, fun j => B₁ j.1, fun j => B₂ j.1,
    fun j w h => hSat j.1 w h, fun j => hInf j.1, fun j w h => j.2 w h, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hone, hzero, hval, hgeom⟩ :=
    hEn E hunr a b S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ St j} u (fun i => B₁ i.1) (fun i => B₂ i.1) fun i =>
      ⟨hu₁ i, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).1, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).2, hu₂ i⟩
  have hsm := hGr T' hT'S hT'Z e₁' e₂' ρ hone hρ fun j => by
    by_cases hj : St j
    · rw [hval (B₁ j) (B₂ j) fun i =>
        ⟨sat_card (hSat j (u i) (hoff _ (hu₁ i))).1, sat_card (hSat j (u i) (hoff _ (hu₁ i))).2,
          (hj (u i) (hu₁ i)).1, (hj (u i) (hu₁ i)).2⟩]
      exact hlt ⟨j, hj⟩
    · have h0 := hzero ⟨j, hj⟩
      simp only at h0
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom] using hsm
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.stableS :
    Enlarge → Places → StableBlockG → StableBlockS := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn π hreg hd
  obtain ⟨l₁, hl⟩ := hG E hunr n hn π hreg hd
  refine ⟨l₁, fun l₂ S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl l₂ S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end
