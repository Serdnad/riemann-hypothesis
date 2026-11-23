module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

private theorem pre_lemma {Z Y X : Scheme.{0}} (x : Z ⟶ Y) (y : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ⊤ ≤ (x ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (show x.base p ∈ (⊤ : Y.Opens) from trivial)
  exact this

private theorem norm_natCast_le_one_kummer_theta_logarithms {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := pre_lemma _ _ _ h
  unfold valR
  rw [dite_eq_left h, dite_eq_left h']
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h (by intro _ _; trivial)]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e5 := fun w => congrArg (fun g => CommRingCat.Hom.hom g w) e2
  simp only [Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e5
  simp only [spMap, CommRingCat.hom_comp, RingHom.comp_apply, ← e5]
  congr 1

private theorem univ_le_preimage_inf_of_univ_le {Z X : Scheme.{0}} (y : Z ⟶ X) (U V : X.Opens) (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro p hp
  exact ⟨h1 hp, h2 hp⟩

private theorem alg_lemma_5 {S : Type} [CommRing S] {n : ℕ} (a b : Fin n → S) (Ps g1 g2 g T : S)
    (h : Ps * (g1 * g2) = T) : (∑ i, a i * (Ps * b i)) * (g1 * (g2 * g)) = T * ∑ i, a i * (b i * g) := by
  rw [← h, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private theorem mul_prod_four_rearrange {S : Type} [CommRing S] (a0 a1 a2 a3 b0 b1 b2 b3 : S) :
    a0 * a1 * a2 * a3 * (b0 * b1 * b2 * b3) = (a0 * b2) * (a1 * b0) * (a2 * b1) * (a3 * b3) := by
  ring

theorem jc_eq_unit_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  intro R _ _ D C _ _ N ν gm₀ gm htan hpull k J hJ
  have hb : gm.b.left = spMap (dualMap (toF R C)) ≫ gm₀.b.left := hpull.1
  have hν : ∀ (P : Sp (DualNumber C) ⟶ D.P.A.left), ⊤ ≤ P ⁻¹ᵁ D.P.L.U (ν.J (redE C ≫ P)) :=
    fun P => GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction C P _ (ν.good _)
  have hQ : redE C ≫ gm.b.left = (TF (R := R) C).hom ≫ eSec D.P.A := by
    rw [hb, ← Category.assoc, gl_redE, Category.assoc, gl_tan D gm₀ htan, ← gl_TF R C]
  have hJb : ∀ (p : Sp (DualNumber R) ⟶ D.P.A.left), ⊤ ≤ (spMap (dualMap (toF R C)) ≫ p) ⁻¹ᵁ D.P.L.U (J p) :=
    fun p => pre_lemma _ _ _ (hJ p)
  have hc0 : ⊤ ≤ gm.b.left ⁻¹ᵁ (D.P.L.U (ν.J (redE C ≫ gm.b.left)) ⊓ D.P.L.U (J gm₀.b.left)) :=
    univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb]; exact hJb _)
  have hcR : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left) :=
    top_le_wchart _ _ _ _ (fun _ => by rw [Category.id_comp, ← gl_tan D gm₀ htan]; exact pre_lemma _ _ _ (hJ _))
  refine ⟨(isUnit_trV D.P.L gm.b.left _ _ hc0 (k : ℤ)).unit, ?_, ?_, ?_⟩
  · unfold TanExp.rigValD valR
    rw [dite_eq_left hcR]
    exact (((D.rig.s _).isUnit.map _).map _).ne_zero
  · rw [IsUnit.unit_spec]
    have e1 : (trV D.P.L gm.b.left (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ)).fst =
        trV D.P.L (redE C ≫ gm.b.left) (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ) := by
      unfold trV
      exact (norm_natCast_le_one_kummer_theta_logarithms (TrivSqZeroExt.fstHom C C C).toRingHom _ _ _ hc0).symm
    have e2 : toF R C (TanExp.rigValD D (J gm₀.b.left)) = valR (TF (R := R) C).hom
        (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left)) (D.rig.s fun _ => J gm₀.b.left).val := by
      unfold TanExp.rigValD
      rw [gl_TF R C]
      have h5 := norm_natCast_le_one_kummer_theta_logarithms (toF R C) (𝟙 _) _ (D.rig.s fun _ => J gm₀.b.left).val hcR
      rw [Category.comp_id] at h5
      exact h5.symm
    have hQ1 : ⊤ ≤ ((TF (R := R) C).hom ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U (J gm₀.b.left) := by
      rw [← hQ, hb, ← Category.assoc]; exact pre_lemma _ _ _ (hJ _)
    have e3 := GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) C).hom
      (fun _ => ν.J ((TF (R := R) C).hom ≫ eSec D.P.A)) (fun _ => J gm₀.b.left)
      (top_le_wchart _ _ _ _ (fun _ => ν.good _)) (top_le_wchart _ _ _ _ (fun _ => hQ1))
    rw [e1, e2, hQ]
    simp only [NumOf.rg, vF]
    unfold valF
    unfold valR at e3 ⊢
    rw [e3]
    simp only [Finset.univ_unique, Finset.prod_singleton, mul_pow]
    rw [trV_pow D.P.L _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (ν.good _) hQ1), _root_.one_mul]
  · intro s n c f hlin α
    have hyP : ∀ {Z : Scheme.{0}} (g : D.P.A.left ⟶ Z),
        (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left ≫
          (D.prB C).left ≫ g = gm.b.left ≫ g :=
      fun g => by rw [← Category.assoc, gl_prB']
    have hsec := GlobalTheory.T.sectionValue_linear_relation_linComb D.P.L (D.famφ C (ν.eX α)) (DegPre.famε k) (s.s (ν.eX α)) (D.famφB (ν.eX α))
      (DegPre.famε k) (fun i => f i (ν.eX α)) (D.prB C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))
      (hlin _)
      (fun i => ν.J (redE C ≫ (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C)
        gm.b).left ≫ D.famφ C (ν.eX α) i))
      (fun i => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
      (by
        intro k₁ k₂ e
        rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢
        · rw [e]
        · rw [← hyP, ← e]
        · rw [← hyP, e]
        · rw [← hyP, ← hyP, e])
      (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left
      (top_le_wchart _ _ _ _ (fun i => hν _))
      (top_le_wchart _ _ _ _ (fun i => by rw [gl_prB']; exact hν _))
    have hS : ∀ i, valR gm.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
        ((f i (ν.eX α)).f fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j)) =
        (∏ j, trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) j) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
          (J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) (DegPre.famε k j)) *
        dualMap (toF R C) (valR gm₀.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
          ((f i (ν.eX α)).f fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))) := by
      intro i
      have hA : ⊤ ≤ gm₀.b.left ⁻¹ᵁ LB.wchart D.P.L (D.famφB (ν.eX α)) (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) :=
        top_le_wchart _ _ _ _ (fun j => hJ _)
      rw [GlobalTheory.T.sectionValue_linComb_change_of_charts D.P.L (D.famφB (ν.eX α)) (DegPre.famε k) (f i (ν.eX α)) gm.b.left _
        (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
        (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [hb, Category.assoc]; exact hJb _))]
      congr 1
      rw [hb]
      exact norm_natCast_le_one_kummer_theta_logarithms _ _ _ _ hA
    have hφ : ∀ j, D.gtφT (TE R C) gm.b (ν.eX α) j = spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j :=
      fun j => gl_gtφT_pull D (epsR R) (TE R C) (spMap (dualMap (toF R C))) (gl_hom R C) gm₀.b gm.b hb (ν.eX α) j
    have hpj : ∀ j, ⊤ ≤ D.gtφT (TE R C) gm.b (ν.eX α) j ⁻¹ᵁ D.P.L.U (pickJ (D.gtφT (TE R C) gm.b (ν.eX α))
        (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j) := by
      intro j
      obtain ⟨i', he, hj⟩ := pickJ_spec (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j
      rw [hj, ← he, hφ i']
      exact hJb _
    unfold jc sE vE
    rw [hsec]
    simp only [gl_scal, gl_prB', hS]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε (gm.s (ν.eX α)) (gm.3 _) (𝟙 _) _
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))]
    rw [gl_corr D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε
      (fun j => spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j) DegPre.gtε _ _ (hpull.2 _)
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (fun k₁ k₂ e => pickJ_congr _ _ e)
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ, hφ]; exact e))
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ k₂]; exact e))
      (𝟙 _)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [gl_pullGen D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (spMap (dualMap (toF R C)))
      _ (𝟙 _) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [Category.id_comp]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (gm₀.3 _)
      (spMap (dualMap (toF R C))) _ (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j))
      (top_le_wchart _ _ _ _ (fun j => by rw [← hφ]; exact hpj j)) (top_le_wchart _ _ _ _ (fun j => hJb _))]
    have hn := norm_natCast_le_one_kummer_theta_logarithms (dualMap (toF R C)) (𝟙 _) (LB.wchart D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) (((gm₀.s (ν.eX α)).s fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)).val)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hJ _))
    rw [Category.comp_id] at hn
    rw [hn, IsUnit.unit_spec]
    unfold TanExp.termV
    simp only [map_mul]
    refine alg_lemma_5 _ _ _ _ _ _ _ ?_
    rw [← Finset.prod_mul_distrib]
    simp only [Category.id_comp, ← hφ]
    rw [Finset.prod_congr rfl (fun j _ => GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle D.P.L D.P.isLB _ _ _ _ _ (hν _) (hpj j) (by rw [hφ]; exact hJb _))]
    simp only [gl_gtφT_famφB]
    have tadd : ∀ (i : Fin 4) (a b : ℤ), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) a * trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i)
        (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i)) (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) b =
        trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) (a + b) :=
      fun i a b => trV_add _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _)) a b
    have tzero : ∀ (i : Fin 4), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) 0 = 1 :=
      fun i => trV_zero _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _))
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_prod_four_rearrange, tadd, tadd, tadd, tadd]
    have h0 : D.famφB (ν.eX α) 0 = 𝟙 _ := by
      unfold DegPre.famφB
      rfl
    simp only [sub_add_cancel, add_neg_cancel, neg_add_cancel, tzero, _root_.mul_one, h0, Category.comp_id]

end GlobalTheory.MBLow.TanGauge

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_integral_labels : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q → ∃ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, (∀ a, d.Rep σ k (M a) (Nn a) (q a)) ∧ (∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ) := by
  intro N g' r g bX d σ k hk ζ q hq
  obtain ⟨-, hadd, hinj, hsurj, hwp⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.degenerationTorsion_eq_periodLattice_mod_level N g' r g bX d σ k hk
  have h5 := GlobalTheory.T.weilPairing_degenerationTorsion_classical N g' r g bX d σ k hk
  choose M0 N0 hMN using h1
  refine ⟨fun a => M0 (q a), fun a => N0 (q a), fun a => hMN _, fun a a' => ?_, fun a a' M' N' hM hN => ?_,
    fun M₁ N₁ => ?_, fun i j => ?_⟩
  · exact (h4 _ _ _ _ _ _ (h3 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))) (hMN (q (a + a')))).1 (hadd a a')
  · exact hinj a a' ((h4 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))).2 ⟨M', N', hM, hN⟩)
  · obtain ⟨p, hp, -⟩ := h2 M₁ N₁
    obtain ⟨a, ha⟩ := hsurj p
    exact ⟨a, (h4 _ _ _ _ _ _ (hMN (q a)) hp).1 ha⟩
  · rw [← hwp i j]
    exact (h5 _ _ _ _ _ _ (hMN _) (hMN _)).symm

end GlobalTheory.MBLow.Cl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem termsum_fderiv_mul_affine {g : ℕ} (f F : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hF : Differentiable ℂ F)
    (c : ℂ) (p W : Fin g → ℂ) :
    fderiv ℂ (fun Z => f Z * F (c • Z + p)) 0 W = fderiv ℂ f 0 W * F p + f 0 * fderiv ℂ F p (c • W) := by
  have h1 : HasFDerivAt (fun Z : Fin g → ℂ => c • Z + p) (c • ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    ((hasFDerivAt_id (0 : Fin g → ℂ)).const_smul c).add_const p
  have h2 : HasFDerivAt F (fderiv ℂ F p) (c • (0 : Fin g → ℂ) + p) := by
    rw [smul_zero, zero_add]; exact (hF p).hasFDerivAt
  have h3 : HasFDerivAt (fun Z => F (c • Z + p)) _ 0 := h2.comp (0 : Fin g → ℂ) h1
  have h4 : HasFDerivAt (fun Z => f Z * F (c • Z + p)) _ 0 := (hf 0).hasFDerivAt.mul h3
  rw [h4.fderiv]
  simp
  ring

theorem termsum_trFac_differentiable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ)
    (M N : Fin g → ℤ) : Differentiable ℂ (trFac τ a b m M N) := by
  unfold trFac
  simp only [dotProduct]
  fun_prop

theorem termsum_full_isSymm {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (hS : S.IsSymm) : (d.full σ S).IsSymm := by
  unfold CD.full
  apply Matrix.IsSymm.submatrix
  exact Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)

theorem termsum_half_aF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.aF σ) := by
  intro j
  unfold CD.aF
  rcases σ j with i | l
  · exact d.ha i
  · exact Or.inl rfl

theorem termsum_half_bF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.bF σ) := by
  intro j
  unfold CD.bF
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

theorem term_sum_and_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ (m : ℕ) (M Nn : Fin g → ℤ) (W : Fin g → ℂ), (Summable fun χ => ‖d.term σ S m M Nn χ 0‖) ∧ (Summable fun χ => ‖fderiv ℂ (d.term σ S m M Nn χ) 0 W‖) ∧ ∑' χ, d.term σ S m M Nn χ 0 = trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn 0 ∧ ∑' χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W = fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W := by
  intro N g' r g bX d σ S hS hpos m M Nn W
  have hθ := (GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g _ _ _ (termsum_full_isSymm d σ S hS) hpos (termsum_half_aF d σ) (termsum_half_bF d σ)).1
  set p := (m : ℂ)⁻¹ • perV (d.full σ S) M Nn with hp
  obtain ⟨hs, he⟩ := GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion N g' r g bX d σ S hS hpos p
  obtain ⟨hd, hD⟩ := GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise N g' r g bX d σ S hS hpos
  obtain ⟨hs', he'⟩ := hD p ((m : ℂ) • W)
  have hf := termsum_trFac_differentiable (d.full σ S) (d.aF σ) (d.bF σ) m M Nn
  set f := trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn with hfdef
  have e0 : ∀ χ, d.term σ S m M Nn χ 0 = f 0 * d.fj σ S χ p := fun χ => by
    simp only [CD.term, smul_zero, zero_add, hfdef, hp]
  have e1 : ∀ χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W =
      fderiv ℂ f 0 W * d.fj σ S χ p + f 0 * fderiv ℂ (d.fj σ S χ) p ((m : ℂ) • W) := fun χ =>
    termsum_fderiv_mul_affine f (d.fj σ S χ) hf (hd χ) m p W
  have e2 : fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W = _ :=
    termsum_fderiv_mul_affine f _ hf hθ m p W
  have s1 := hs.of_norm
  have s2 := hs'.of_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [e0]
    exact (s1.mul_left _).norm
  · simp only [e1]
    exact ((s1.mul_left _).add (s2.mul_left _)).norm
  · simp only [e0]
    rw [tsum_mul_left, he]
    simp only [trF, smul_zero, zero_add, hfdef, hp]
  · simp only [e1]
    rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left, he, he', e2]

end GlobalTheory.MBLow.Cl
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ClosedExt

theorem locExt {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ)
    (hu : ∀ y, CInfAt u y) (x : CxPts p σ) :
    ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧
      ∀ y : CxPts q σ, ptMap π hπ σ y ∈ O → v (ptMap π hπ σ y) = u y := by
  have := GlobalTheory.LocExt.isSeparated_of_isProjOver hp
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩
  have hemb : IsClosedEmbedding (ptMap π hπ σ) := by
    have : CompactSpace (CxPts q σ) := GlobalTheory.CxPts.compactSpace σ hq
    have hc : Continuous (ptMap π hπ σ) := continuous_of_comp (f := π) fun _ => rfl
    refine hc.isClosedEmbedding fun y y' h => Subtype.ext ?_
    exact (cancel_mono π).1 (congrArg Subtype.val h)
  by_cases hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x
  · obtain ⟨y₀, rfl⟩ := hx
    obtain ⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩ := hu y₀
    obtain ⟨t, ht, htW⟩ := (π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2
    let W₁ : X.Opens := ⟨t, ht⟩
    have hW₁ : π ⁻¹ᵁ W₁ = W := Opens.ext htW
    have hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁ := by
      have := mem_ptsIn.1 h₁
      rw [← hW₁] at this
      exact this
    obtain ⟨W', hW'a, hzW', hW'le⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀
    have hle : π ⁻¹ᵁ W' ≤ W := by
      rw [← hW₁]
      exact fun a ha => hW'le ha
    choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))
    have hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) :
        ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y := by
      rw [← ev_res hle hy, ← hg' a]
      exact valR_comp y.1 π W' (g' a)
    obtain ⟨s, hs, hsu⟩ := h₅.exists_mem
    obtain ⟨N, hNs, hN, hy₀N⟩ := mem_nhds_iff.1 hs
    obtain ⟨N', hN', hNN'⟩ := (hemb.isInducing.isOpen_iff).1 hN
    have hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀) :=
      (continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂
    have hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 hzW'
    refine ⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀),
      fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩
    · have : y₀ ∈ ptMap π hπ σ ⁻¹' N' := hNN'.symm ▸ hy₀N
      exact this
    · exact mem_ptsIn.2 hzW'
    · simp only [Set.mem_preimage, hval y₀ hy₀W']
      exact h₃
    · exact ⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩
    · have hyN : y ∈ N := by
        have : y ∈ ptMap π hπ σ ⁻¹' N' := hy.1
        rwa [hNN'] at this
      have hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)
      simp only [hval y hyW']
      exact (hsu (hNs hyN)).symm
  · exact ⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx,
      fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩

theorem exists_extension : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ), (∀ y, CInfAt u y) → ∃ v : CxPts p σ → ℝ, (∀ y, CInfAt v y) ∧ ∀ y, v (ptMap π hπ σ y) = u y := by
  intro k _ X Y p q σ hp π _ hπ u hu
  exact GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)

end GlobalTheory.ClosedExt
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem loc_one_add (P : Pair p) (a b a' b' : ℤ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') 1 i j = P.loc a b 1 i j * P.loc a' b' 1 i j := by
  have h₁ : ((P.r i : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h₂ : ((P.r' j : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [loc, one_mul, zpow_add₀ h₁, zpow_add₀ h₂]
  ring

theorem rep_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' →
      P.Rep (a + a') (b + b') (M.tens M') := by
  intro k _ X _ p P a b a' b' M M' ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  have e (c : (M.tens M').B.ι) (i : P.L.B.ι) (j : P.A.B.ι) :
      (((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField) / P.loc (a + a') (b + b') 1 i j) =
        ((ρ c.1 : X.functionField) / P.loc a b 1 i j) * ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) := by
    rw [loc_one_add, Units.val_mul]
    ring
  refine ⟨fun c => ρ c.1 * ρ' c.2, GlobalTheory.PtHtComb.isRatSec_tens hρ hρ', ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [e]
    exact (hu x c.1 i j hc.1 hi hj).mul (hu' x c.2 i j hc.2 hi hj)
  · intro σ y c i j hc hi hj
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have u₁ := hu _ c.1 i j (mem_ptsIn.1 hc₁) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have u₂ := hu' _ c.2 i j (mem_ptsIn.1 hc₂) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have n₁ := hn σ y c.1 i j hc₁ hi hj
    have n₂ := hn' σ y c.2 i j hc₂ hi hj
    have z₁ : ‖ratVal ((ρ c.1 : X.functionField) / P.loc a b 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₁)
    have z₂ : ‖ratVal ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₂)
    change Real.log ‖ratVal ((((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField)) /
        P.loc (a + a') (b + b') 1 i j) y‖ - ((M.φ σ).φ c.1 y + (M'.φ σ).φ c.2 y) / 2 = _
    rw [e, ratVal_mul u₁.regAt u₂.regAt, norm_mul, Real.log_mul z₁ z₂]
    push_cast
    linear_combination n₁ + n₂

end GlobalTheory.VolBr.Pair
end
end
