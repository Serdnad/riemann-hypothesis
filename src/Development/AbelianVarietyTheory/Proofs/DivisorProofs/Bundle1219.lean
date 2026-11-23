module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanAdd

section General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem corr_mul {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (ρ : (Over.map (thick R I e)).obj T' ⟶ T) (x x' : T' ⟶ thickObj R I e G) (p p' p'' : GtPt D T)
    (h : GtPt.IsAdd p p' p'') (hb : TorusCoord.im g x = ρ ≫ p.b) (hb' : TorusCoord.im g x' = ρ ≫ p'.b) (χ : D.X)
    (hs : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (p.s χ) ρ.left))
    (hs' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x'.left) (LB.pullGen D.P.L _ _ (p'.s χ) ρ.left)) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left) (LB.pullGen D.P.L _ _ (p''.s χ) ρ.left) := by
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have k := TorusCoord.val_t_mul_points g GlobalTheory.globalFns_holds χ x x' z J hJ
  have a := val_corr hJ (h.2 χ) ρ.left
  have a₁ := (val_mul hJ _ _ _).symm.trans (a.trans (val_mul hJ _ _ _))
  have c : val (DegPre.cubAtT D T (DegPre.cT D T χ) p.b p'.b) ρ.left z J = TorusCoord.cubeVal g χ z J x x' := by
    refine (val_cub D.cub ρ hJ _ _ _).trans ?_
    unfold TorusCoord.cubeVal
    rw [hb, hb']
    congr 1
    simp
  have s := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs (𝟙 _))).trans (val_pull hJ _ _ _)
  have s' := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs' (𝟙 _))).trans (val_pull hJ _ _ _)
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  simp only [Category.id_comp] at s s' ⊢
  refine mul_right_cancel (k.trans ?_)
  exact ((congrArg₂ (· * ·) s s').trans a₁.symm).trans (congrArg (_ * ·) c)

theorem fst_mul {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T' ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).map (x * x') ≫ fstG I e G =
      ((Over.map (thick R I e)).map x ≫ fstG I e G) * ((Over.map (thick R I e)).map x' ≫ fstG I e G) :=
  map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T') x x'

end General

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_over {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ (epsR A).hom = (epsR B).hom ≫ spMap f := by
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_scale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    spMap (epsScaleR (f c)) ≫ spMap (dualMap f) = spMap (dualMap f) ≫ spMap (epsScaleR c) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, epsScaleR, mul_comm]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_mul (y y' : epsR R ⟶ G) (gm gm' gm'' : GtPt D.toPre (epsR R)) (h : TanRel U y gm) (h' : TanRel U y' gm')
    (ha : GtPt.IsAdd gm gm' gm'') : TanRel U (y * y') gm'' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  obtain ⟨ye', h₁', h₂', h₃'⟩ := h' e
  have hci : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hw := dual_over (Ideal.Quotient.mk (I ^ (e + 1)))
  let ρ : (Over.map (thick R I e)).obj (epsR (R ⧸ I ^ (e + 1))) ⟶ epsR R :=
    Over.homMk (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))) hw
  have key : ∀ (w : epsR R ⟶ G) (we : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      we ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ w.left →
      we ≫ (thickObj R I e G).hom = (epsR (R ⧸ I ^ (e + 1))).hom := by
    intro w we hh
    have h0 := congrArg (· ≫ G.hom) hh
    simp only [Category.assoc, Over.w] at h0
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact h0.trans hw
  let x : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye (key y ye h₁)
  let x' : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye' (key y' ye' h₁')
  have f : (Over.map (thick R I e)).map x ≫ fstG I e G = ρ ≫ y := Over.OverMorphism.ext h₁
  have f' : (Over.map (thick R I e)).map x' ≫ fstG I e G = ρ ≫ y' := Over.OverMorphism.ext h₁'
  have b : TorusCoord.im (U.gt e) x = ρ ≫ gm.b := Over.OverMorphism.ext h₂
  have b' : TorusCoord.im (U.gt e) x' = ρ ≫ gm'.b := Over.OverMorphism.ext h₂'
  refine ⟨(x * x').left, ?_, ?_, fun χ => corr_mul (U.gt e) ρ x x' gm gm' gm'' ha b b' χ (h₃ χ) (h₃' χ)⟩
  · have := fst_mul x x'
    rw [f, f', ← MonObj.comp_mul] at this
    exact congrArg (·.left) this
  · have := TorusCoord.im_mul (U.gt e) x x'
    rw [b, b', ← MonObj.comp_mul] at this
    rw [ha.1]
    exact congrArg (·.left) this

theorem tanRel_scale (c : R) (y : epsR R ⟶ G) (gm gm' : GtPt D.toPre (epsR R)) (h : TanRel U y gm)
    (hp : GtPt.IsPull (epsScale R c).left gm gm') : TanRel U (epsScale R c ≫ y) gm' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  have hc : spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsScale R c).left := dual_scale _ c
  refine ⟨spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ ye, ?_, ?_, fun χ => ?_⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.left) hc).trans (Category.assoc _ _ _))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gm.b.left) hc).trans ((Category.assoc _ _ _).trans ?_))
    exact congrArg (_ ≫ ·) hp.1.symm
  · refine corr_of_val D.toPre.P.isLB fun z J hJ => ?_
    have s := ((val_pull hJ _ _ _).symm.trans
      (val_corr hJ (h₃ χ) (spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c))))).trans (val_pull hJ _ _ _)
    have t := (val_corr hJ (hp.2 χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))))).trans (val_pull hJ _ _ _)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    simp only [Category.id_comp]
    exact s.trans ((congrArg (fun q => val (gm.s χ) q z J) hc).trans t.symm)

end GlobalTheory.MBLow.TanAdd

end
end

section

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr


open Filter Topology in
theorem _root_.GlobalTheory.VolBr.encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hR)
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hB1 : (B 1).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.1 ⟨0, hB.zero_mem 1 zero_le_one⟩
  by_cases hbig : (B (R * Q ^ e)).Finite
  swap
  · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
    exact le_top
  set s : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range j, (Q : ℝ) ^ i with hs
  have hs_succ : ∀ j, s (j + 1) = Q * s j + 1 := by
    intro j
    simp only [hs, Finset.sum_range_succ', pow_succ, pow_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ Finset.sum_nonneg fun i _ ↦ by positivity
  have hs_le : ∀ j, s j + 1 ≤ (Q : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp [hs]
    | succ j ih =>
      rw [hs_succ, pow_succ]
      nlinarith [hs_nonneg j]
  have hclaim : ∀ j ≤ e, (B R).encard ^ j ≤ (B 1).encard ^ j * (B (R * s j)).encard := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hs, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 0 le_rfl⟩
    | succ j ih =>
      intro hj
      have hRs : R * s j ≤ R * Q ^ e := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc s j ≤ (Q : ℝ) ^ j := by linarith [hs_le j]
          _ ≤ (Q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have hfs : (B (R * s j)).Finite := hbig.subset (isBallFam_mono hB hRs)
      have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
      have step := encard_mul_encard_le_isBallFam hB (a := R * s j) (b := R) hQpos (by linarith)
        hfs hfin h1
      have hrad : (Q : ℝ) * (R * s j) + R = R * s (j + 1) := by rw [hs_succ]; ring
      rw [hrad] at step
      calc (B R).encard ^ (j + 1) = (B R).encard ^ j * (B R).encard := pow_succ _ _
        _ ≤ (B 1).encard ^ j * (B (R * s j)).encard * (B R).encard := by
            gcongr; exact ih (by omega)
        _ = (B 1).encard ^ j * ((B (R * s j)).encard * (B R).encard) := mul_assoc _ _ _
        _ ≤ (B 1).encard ^ j * ((B 1).encard * (B (R * s (j + 1))).encard) := by gcongr
        _ = (B 1).encard ^ (j + 1) * (B (R * s (j + 1))).encard := by rw [pow_succ, mul_assoc]
  calc (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * s e)).encard := hclaim e le_rfl
    _ ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
        gcongr
        exact isBallFam_mono hB (mul_le_mul_of_nonneg_left (by linarith [hs_le e]) (by linarith))

end GlobalTheory.VolBr
end

section

open Complex ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.LogPos

theorem prod_inv_one_sub_eq_exp (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    (S.map fun w => (1 - w)⁻¹).prod = exp (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, exp_add,
      ih fun w hw => h w (Multiset.mem_cons_of_mem hw)]
    congr 1
    have ha : 1 - a ≠ 0 := by
      intro h0
      have e : a = 1 := by linear_combination -h0
      have := h a (Multiset.mem_cons_self a S)
      simp [e] at this
    rw [exp_neg, exp_log ha]

theorem hasSum_log (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    HasSum (fun n : ℕ => (S.map fun w => w ^ n).sum / n) (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasSum_zero
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
    exact (hasSum_taylorSeries_neg_log (h a (Multiset.mem_cons_self a S))).add
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

theorem sum_pow_product (x : ℂ) (n : ℕ) (s t : Multiset ℂˣ) :
    ((s ×ˢ t).map fun p : ℂˣ × ℂˣ => ((p.1 : ℂ) * p.2 * x) ^ n).sum =
      x ^ n * (s.map fun b : ℂˣ => (b : ℂ) ^ n).sum * (t.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add (f := _), Multiset.sum_add, ih, Multiset.map_map]
    simp only [Function.comp_def, mul_pow]
    rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Multiset.map_cons, Multiset.sum_cons]
    ring

theorem sum_pow_star (n : ℕ) (B : Multiset ℂˣ) :
    ((B.map star).map fun b : ℂˣ => (b : ℂ) ^ n).sum = conj (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp [Units.coe_star, star_pow]

theorem cpow_neg_eq (q : ℕ) (σ : ℝ) : (q : ℂ) ^ (-(σ : ℂ)) = (((q : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]

theorem norm_pair_le {B : Multiset ℂˣ} {M : ℝ} (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) {p : ℂˣ × ℂˣ}
    (hp : p ∈ B ×ˢ B.map star) : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ M := by
  rw [Multiset.mem_product] at hp
  obtain ⟨b', hb', hpb⟩ := Multiset.mem_map.1 hp.2
  have h1 := hM _ hp.1
  have h2 := hM _ hb'
  have e2 : ‖(p.2 : ℂ)‖ = ‖(b' : ℂ)‖ := by rw [← hpb, Units.coe_star, norm_star]
  rw [e2]
  nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(b' : ℂ)‖)]

theorem locL_conj_eq_exp (q : ℕ) (B : Multiset ℂˣ) (M : ℝ) (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) (σ : ℝ)
    (hσ : M * (q : ℝ) ^ (-σ) < 1) :
    ∃ L : ℝ, HasSum (fun n : ℕ => ((q : ℝ) ^ (-σ)) ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n) L ∧
      locL q B (B.map star) σ = Real.exp L := by
  set x : ℝ := (q : ℝ) ^ (-σ) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set S := (B ×ˢ B.map star).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * x with hSdef
  have hS : ∀ w ∈ S, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hw
    have := norm_pair_le hM hp
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hx0]
    nlinarith [mul_le_mul_of_nonneg_right this hx0]
  have hloc : locL q B (B.map star) σ = (S.map fun w => (1 - w)⁻¹).prod := by
    simp only [locL, cpow_neg_eq, ← hxdef, hSdef, Multiset.map_map, Function.comp_def]
  have hterm : ∀ n : ℕ, (S.map fun w => w ^ n).sum / n =
      ((x ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n : ℝ) : ℂ) := by
    intro n
    simp only [hSdef, Multiset.map_map, Function.comp_def]
    rw [sum_pow_product, sum_pow_star, mul_assoc, mul_conj]
    push_cast
    ring
  have hL := hasSum_log S hS
  simp only [hterm] at hL
  have hre := Complex.hasSum_re hL
  have him := Complex.hasSum_im hL
  simp only [ofReal_re, ofReal_im] at hre him
  have hLim := him.unique hasSum_zero
  refine ⟨_, hre, ?_⟩
  rw [hloc, prod_inv_one_sub_eq_exp S hS, ofReal_exp]
  congr 1
  exact Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, hLim])

end GlobalTheory.JSW.LogPos
end
end

section

open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_of_quot_embed : ∀ (G : Type) [AddCommGroup G] (Λ Λ' Λ₀ Λ₀' : AddSubgroup G) (B E : ℝ → Set G)
    (T : G →+ G), IsBallFam Λ B → IsBallFam Λ' E → (∀ u ∈ B 1, T u ∈ E 1) → (∀ u ∈ Λ, T u ∈ Λ₀' → u ∈ Λ₀) →
    (B 1).Finite → (B 1).encard * (E 1 ∩ Λ₀').encard ≤ (B 2 ∩ Λ₀).encard * (E 2).encard := by
  intro G _ Λ Λ' Λ₀ Λ₀' B E T hB hE hT hpull _
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  let q : G → G ⧸ Λ₀ := QuotientAddGroup.mk
  let R : Set (G ⧸ Λ₀) := q '' B 1
  let s : G ⧸ Λ₀ → G := Function.invFunOn q (B 1)
  have hs_mem : ∀ c ∈ R, s c ∈ B 1 := fun c hc => Function.invFunOn_mem hc
  have hs_eq : ∀ c ∈ R, q (s c) = c := fun c hc => Function.invFunOn_eq hc

  have h1 : (B 1).encard ≤ R.encard * (B 2 ∩ Λ₀ : Set G).encard := by
    rw [← Set.encard_prod]
    refine le_trans (Set.encard_le_encard (s := B 1)
      (t := (fun p : (G ⧸ Λ₀) × G => s p.1 + p.2) '' (R ×ˢ (B 2 ∩ (Λ₀ : Set G)))) ?_) (Set.encard_image_le _ _)
    intro x hx
    have hqx : q x ∈ R := ⟨x, hx, rfl⟩
    refine ⟨(q x, x - s (q x)), ⟨hqx, ?_, ?_⟩, by simp⟩
    · have := hB.sub_mem 1 1 x (s (q x)) hx (hs_mem _ hqx)
      rwa [h2] at this
    · have he : q (s (q x)) = q x := hs_eq _ hqx
      have := (QuotientAddGroup.eq).mp he
      show x - s (q x) ∈ Λ₀
      rwa [sub_eq_neg_add]

  have h3 : R.encard * (E 1 ∩ Λ₀' : Set G).encard ≤ (E 2).encard := by
    rw [← Set.encard_prod]
    refine Set.encard_le_encard_of_injOn (f := fun p : (G ⧸ Λ₀) × G => T (s p.1) - p.2) ?_ ?_
    · rintro ⟨c, v⟩ ⟨hc, hv, -⟩
      have := hE.sub_mem 1 1 _ _ (hT _ (hs_mem c hc)) hv
      rwa [h2] at this
    · rintro ⟨c, v⟩ ⟨hc, hv, hv'⟩ ⟨c', w⟩ ⟨hc', hw, hw'⟩ heq
      simp only at heq
      have hd : T (s c - s c') ∈ Λ₀' := by
        have : T (s c - s c') = v - w := by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp heq
        rw [this]; exact Λ₀'.sub_mem hv' hw'
      have hΛ : s c - s c' ∈ Λ := Λ.sub_mem (hB.subset 1 (hs_mem c hc)) (hB.subset 1 (hs_mem c' hc'))
      have h0 : s c - s c' ∈ Λ₀ := hpull _ hΛ hd
      have hqq : q (s c) = q (s c') := by
        apply (QuotientAddGroup.eq).mpr
        have := Λ₀.neg_mem h0
        rwa [neg_sub, sub_eq_neg_add] at this
      have hcc : c = c' := by rw [← hs_eq c hc, ← hs_eq c' hc', hqq]
      subst hcc
      have : v = w := by simpa using heq
      rw [this]
  calc (B 1).encard * (E 1 ∩ Λ₀' : Set G).encard
      ≤ (R.encard * (B 2 ∩ Λ₀ : Set G).encard) * (E 1 ∩ Λ₀' : Set G).encard := by gcongr
    _ = (B 2 ∩ Λ₀ : Set G).encard * (R.encard * (E 1 ∩ Λ₀' : Set G).encard) := by ring
    _ ≤ (B 2 ∩ Λ₀ : Set G).encard * (E 2).encard := by gcongr

end GlobalTheory.VolBr
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  first | exact @GlobalTheory.QLog.exists_isLie_add_smul | exact GlobalTheory.QLog.exists_isLie_add_smul | (intros; apply GlobalTheory.QLog.exists_isLie_add_smul <;> assumption)
end
