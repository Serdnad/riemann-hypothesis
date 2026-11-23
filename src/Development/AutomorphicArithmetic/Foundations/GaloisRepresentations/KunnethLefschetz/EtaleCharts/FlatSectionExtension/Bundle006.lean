module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsV :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y), ∃ v : Fin d → Γ(TP B j, ⊤), IsV B j v ∧ Ideal.span (Set.range v) = ⊤ := by
  intro K _ W Z Y q i π D d B T j
  classical
  let X : B.ι × Fin d → Scheme.{0} := fun p => (oT B j p : Scheme.{0})
  choose v hv _ using fun m : Fin d =>
    sigmaSection X (fun p => uV B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) m)
  refine ⟨v, fun p m => hv m p, ?_⟩
  choose b hb _ using fun m : Fin d =>
    sigmaSection X (fun p => if p.2 = m then (1 : Γ(X p, ⊤)) else 0)
  obtain ⟨s, -, hs⟩ := sigmaSection X (fun _ => 1)
  have h1 : (∑ m, b m * v m) = 1 := by
    have e2 := hs 1 (fun p => map_one _)
    have e1 : (∑ m, b m * v m) = s := by
      refine hs _ fun p => ?_

      rw [map_sum]
      simp only [map_mul, hb, hv]
      simp [uSelf]
    rw [e1, e2]
  rw [Ideal.eq_top_iff_one, ← h1]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma flat_of_etale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (h : f.Etale) : f.Flat := by
  letI := f.toAlgebra
  haveI : Algebra.Etale A B := h
  exact (inferInstance : Module.Flat A B)

private lemma flat_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have e : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U := h
  have h1 := HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat) (𝟙 X)
    (inferInstance : AlgebraicGeometry.Flat (𝟙 X)) ⟨U, hU⟩ ⟨V, hV⟩ e
  have h2 : (𝟙 X : X ⟶ X).appLE U V e = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
    exact Category.id_comp _
  simpa only [h2] using h1

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β h₁ h₂ G → IsTr B α β h₁ h₂ G' → ∀ m l, (i.app N).hom (G m l) = (i.app N).hom (G' m l) := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂ G G' hG hG' m l
  let φ₀ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α) :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t
  let φ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, N) :=
    (Z.presheaf.map (homOfLE h₁).op).hom.comp φ₀
  have hflat : φ.Flat :=
    RingHom.Flat.comp (flat_of_etale φ₀ (etaleSplit B α)) (flat_res (B.c α).affine hN h₁)
  have hX : ∀ l, φ (MvPolynomial.X l) = tN B α h₁ l := by
    intro l
    simp [φ, φ₀, tN]
  have hfun : (fun l => φ (MvPolynomial.X l)) = tN B α h₁ := funext hX
  have hzero : ∑ l, (G m l - G' m l) * φ (MvPolynomial.X l) = 0 := by
    simp only [hX, sub_mul, Finset.sum_sub_distrib]
    rw [← hG m, ← hG' m, sub_self]
  have key := UpperTheory.Gal.KunnethLefschetz.G.regSeq _ _ d φ hflat (fun l => G m l - G' m l)
    (by rw [hzero]; exact zero_mem _) l
  rw [hfun, ← kerRes B α hN h₁, RingHom.mem_ker, map_sub] at key
  exact sub_eq_zero.mp key
end
