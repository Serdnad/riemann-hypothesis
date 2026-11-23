module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V' V : Scheme.{0}} (s : V' ⟶ V) (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k), (∀ m, uV B α k (s ≫ y) h' m = s.appTop.hom (uV B α k y h m)) ∧ secOf B α k (s ≫ y) h' = s ≫ secOf B α k y h := by
  intro K _ W Z Y q i π D d B α k V' V s y h h'
  constructor
  · intro m
    have hs : (⊤ : V'.Opens) ≤ s ⁻¹ᵁ (⊤ : V.Opens) := le_rfl
    have key : (s ≫ y).appLE ((B.c α).C k) ⊤ h' = y.appLE ((B.c α).C k) ⊤ h ≫ s.appTop := by
      have h1 := Scheme.Hom.appLE_comp_appLE s y ((B.c α).C k) ⊤ ⊤ h hs
      rw [← h1]
      congr 1
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change _ ≫ V'.presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    unfold uV
    rw [key]
    rfl
  · unfold secOf
    rw [← Category.assoc]
    congr 1
    symm
    apply IsOpenImmersion.lift_uniq
    rw [Category.assoc, IsOpenImmersion.lift_fac]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.coverComm :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i), rhoP B j r hw ≫ cP B = eP B j ≫ r ∧ tauP B j ≫ D.f = eP B j ≫ j := by
  intro K _ W Z Y q i π D d B T j r hw
  constructor
  · refine Sigma.hom_ext _ _ fun p => ?_
    have h1 : wI B p.1 ≫ cP B = (oW B p.1).ι := by
      simp only [wI, cP, Sigma.ι_desc]
    have h2 : rhoC B j r hw p ≫ (oW B p.1).ι = (oT B j p).ι ≫ r := by
      simp only [rhoC, IsOpenImmersion.lift_fac]
    simp only [rhoP, eP, Sigma.ι_desc_assoc, Category.assoc, h1, h2]
  · refine Sigma.hom_ext _ _ fun p => ?_
    simp only [tauP, eP, Sigma.ι_desc_assoc, secOf_f]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α) → LocMat B α α p 1 := by
  intro K _ W Z Y q i π D d B α V p h x
  have hU : ⊤ ≤ (((⊤ : V.Opens).ι ≫ p ≫ i) ⁻¹ᵁ B.V α) := by
    intro y _
    exact h y.1
  refine ⟨⊤, B.V α, trivial, (B.c α).affine, le_rfl, le_rfl, hU, 1, ?_, ?_⟩
  · intro m
    simp [Matrix.one_apply]
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.tCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → Smooth (eP B j) ∧ Surjective (eP B j) := by
  intro K _ W Z Y q i π D d B T j r hsq
  refine ⟨?_, ?_⟩
  · have hloc : IsZariskiLocalAtSource @Smooth.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    unfold eP
    exact IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance
  · refine ⟨fun x => ?_⟩
    have hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (Set.mem_univ (r x))
    have hx' : i (r x) ∈ (⨆ α, B.V α) := hx
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have h3 : π (j x) = i (r x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]
    have h4 : j x ∈ π ⁻¹ᵁ B.V α := by
      change π (j x) ∈ B.V α
      rw [h3]; exact hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)
    let p : B.ι × Fin d := (α, k)
    have hp : x ∈ oT B j p := hk
    let y : (oT B j p : Scheme.{0}) := ⟨x, hp⟩
    have hc : tI B j p ≫ eP B j = (oT B j p).ι := by
      unfold tI eP
      exact Sigma.ι_desc _ _
    refine ⟨tI B j p y, ?_⟩
    have hy : (tI B j p ≫ eP B j) y = x := by
      rw [hc]
      rfl
    rw [← Scheme.Hom.comp_apply]
    exact hy
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.wCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), Smooth (cP B) ∧ Surjective (cP B) := by
  intro K _ W Z Y q i π D d B
  refine ⟨?_, ⟨fun x => ?_⟩⟩
  · have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
    unfold cP
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun α => inferInstance)
  · have hx : i x ∈ ⨆ α, B.V α := B.cover (Set.mem_univ x)
    obtain ⟨α, hα⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (oW B α).ι := by
      rw [Scheme.Opens.range_ι]
      exact hα
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    refine ⟨wI B α y, ?_⟩
    rw [← Scheme.Hom.comp_apply, h, hy]
end
