module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open ReciprocityTheory.PTheta Matrix

private theorem levelTheta_one_zero {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : GlobalTheory.levelTheta a b 1 τ 0 z = theta a b z τ := by
  unfold GlobalTheory.levelTheta
  have e1 : ((fun i => ((0 : Fin g → ℤ) i : ℝ) / ((1 : ℕ) : ℝ)) + a) = a := by
    funext i; simp
  rw [e1]
  simp

theorem differentiableOn_thetaChar_comp {g : ℕ} {a b : Fin g → ℂ} (h : charHalf g a b)
    {w : (Fin g → Fin g → ℂ) → Fin g → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun p => thetaChar (per p) a b (w p)) (Key.phDom g) := by
  obtain ⟨ha, hb⟩ := h
  have hF := GlobalTheory.KeyKa.LevelBasis.holFam_levelTheta (fun i => (a i).re) (fun i => (b i).re) Nat.one_pos 0
  unfold GlobalTheory.KeyKa.HolFam at hF
  simp only [levelTheta_one_zero] at hF
  have hm : Differentiable ℂ (fun p : Fin g → Fin g → ℂ => (p, w p)) := by fun_prop
  refine (hF.comp hm.differentiableOn (fun p hp => ⟨hp, Set.mem_univ _⟩)).congr (fun p _ => ?_)
  rw [GlobalTheory.TorusAlg.thetaChar_eq_theta _ ha hb]
  rfl

theorem differentiable_per_apply {g : ℕ} (i j : Fin g) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => per p i j) := by
  simp only [GlobalTheory.KeyKa.per, ReciprocityTheory.ChartRestriction.G.Key.phSym, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

theorem differentiable_lat {g : ℕ} (k n : Fin g → ℤ) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) k n) := by
  rw [differentiable_pi]
  intro i
  have hp := differentiable_per_apply (g := g)
  simp only [lat, Pi.add_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem differentiable_tors {g : ℕ} (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => tors (per p) al m k n r) := by
  have hl : ∀ c, Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) (k c) (n c)) :=
    fun c => differentiable_lat (k c) (n c)
  unfold tors
  exact (Differentiable.fun_sum fun c _ => (hl c).const_smul (al r c)).const_smul ((m : ℂ)⁻¹)

theorem level_one_and_holomorphic : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  intro g a b h
  refine ⟨fun p hp => ?_, fun al m k n y => ?_, fun k n z => ?_⟩
  · have hτ : per p ∈ SiegelH (Fin g) := hp
    obtain ⟨ha, hb⟩ := h
    have e := GlobalTheory.KeyKa.LevelBasis.isLevel_iff (per p) (fun i => (a i).re) (fun i => (b i).re) 1
      (thetaChar (per p) a b)
    rw [GlobalTheory.TorusAlg.ofRealVec_re ha, GlobalTheory.TorusAlg.ofRealVec_re hb] at e
    rw [e, (GlobalTheory.TorusAlg.thetaChar_level hτ.1 hτ.2 ha hb).2.1]
    exact Submodule.mem_span_singleton_self _
  · unfold simTheta
    have hθ : ∀ r, DifferentiableOn ℂ
        (fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r)) (Key.phDom g) :=
      fun r => differentiableOn_thetaChar_comp h
        ((differentiable_const _).add (differentiable_tors al m k n r))
    have hprod : DifferentiableOn ℂ
        (∏ r, fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r))
        (Key.phDom g) :=
      Finset.prod_induction _ (fun F => DifferentiableOn ℂ F (Key.phDom g))
        (fun _ _ h1 h2 => h1.mul h2) (differentiableOn_const 1) (fun r _ => hθ r)
    rw [Finset.prod_fn] at hprod
    exact hprod.mul (differentiableOn_const _)
  · have hp := differentiable_per_apply (g := g)
    simp only [aut, Matrix.mulVec, dotProduct]
    fun_prop

end GlobalTheory.SimilTheta
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem dualNumber_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {F G : DualNumber R →+* S}
    (h : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) (he : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine RingHom.ext fun z => ?_
  have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, he]

section Sec

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem appLE_eq_iff_stalk (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

end Sec

theorem keyPB_cancel : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R')
    (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x (f'.comp f) → KeyPB x'' x' f' := by
  intro R R' R'' _ _ _ x x' x'' f f' ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩
    ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyCancel
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta


theorem _root_.GlobalTheory.T.thetaChar_level_one_and_holomorphic_parameter : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  first | exact @GlobalTheory.SimilTheta.level_one_and_holomorphic | exact GlobalTheory.SimilTheta.level_one_and_holomorphic | (intros; apply GlobalTheory.SimilTheta.level_one_and_holomorphic <;> assumption)

end
end
