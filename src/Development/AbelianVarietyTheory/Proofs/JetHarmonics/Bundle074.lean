module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
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
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GermBasic

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Point

variable {V : Type} [CommRing V] [IsDomain V] {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gf_ext {Z : Scheme.{0}} {a b : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left}
    (h₁ : a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left)
    (h₂ : a ≫ UnifPre.gFK (R := V) (G := G) F = b ≫ UnifPre.gFK (R := V) (G := G) F) : a = b := by
  have w : (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ pullback.snd G.hom (jK V) =
      (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ jFK (R := V) F :=
    (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).trans
      (Over.w (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).symm
  have h₃ : a ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ jFK (R := V) F) h₁).trans ((Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) w).symm.trans (Category.assoc _ _ _).symm)))))
  exact pullback.hom_ext h₁ h₃

theorem gf_exists {Z : Scheme.{0}} (p : Z ⟶ Sp F) (g : Z ⟶ G.left) (h : g ≫ G.hom = p ≫ jFK (R := V) F ≫ jK V) :
    ∃ a : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = p ∧
      a ≫ UnifPre.gFK (R := V) (G := G) F = g := by
  let T : Over (TK V).left := Over.mk (p ≫ jFK (R := V) F)
  let u : T ⟶ TFK (R := V) F := Over.homMk p rfl
  let v : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift g (p ≫ jFK (R := V) F) (h.trans (Category.assoc _ _ _).symm)) (pullback.lift_snd _ _ _)
  refine ⟨(lift u v).left, congrArg (fun q => q.left) (lift_fst u v), ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) (lift_snd u v)).trans
    (pullback.lift_fst _ _ _))

variable [Algebra V F] [IsScalarTower V (FractionRing V) F]

theorem exists_jetPt {κ : Type} (z : JetPts G κ) (m : ℕ) :
    ∃ zF : Sp (Jet F κ m) ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      zF ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = spMap (algebraMap F (Jet F κ m)) ∧
      zF ≫ UnifPre.gFK (R := V) (G := G) F = spMap (jetCoef (algebraMap V F) κ m) ≫ (z m).left := by
  refine gf_exists _ _ ?_
  have w : (z m).left ≫ G.hom = spMap (algebraMap V (Jet V κ m)) ≫ 𝟙 _ := Over.w (z m)
  have e : jFK (R := V) F ≫ jK V = spMap (algebraMap V F) :=
    (spMap_comp_eq (algebraMap V (FractionRing V)) (algebraMap (FractionRing V) F)).trans
      (congrArg spMap (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm)
  rw [Category.assoc, w, e, Category.comp_id, spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_alg]

end Point

theorem psJet_sum {F κ : Type} [CommRing F] [Fintype κ] [DecidableEq κ] (m : ℕ) {l : ℕ} (c : Fin l → F)
    (f : Fin l → MvPowerSeries κ F) :
    psJet m (∑ i, c i • f i) = ∑ i, algebraMap F (Jet F κ m) (c i) * psJet m (f i) := by
  have h : psTrunc m (∑ i, c i • f i) = ∑ i, MvPolynomial.C (c i) * psTrunc m (f i) := by

    simp only [psTrunc, map_sum, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]
    exact Finset.sum_comm

  rw [psJet, h, map_sum]
  rfl

theorem val_congr {X Y Y' Z Z' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {φ : Y ⟶ X} {φ' : Y' ⟶ X}
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (1 : ℤ))))
    (t' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ') (fun _ => (1 : ℤ)))) (h : Z ⟶ Y) (h' : Z ⟶ Y')
    (H : ∀ y J, Good L y J → val t h y J = val t' h' y J) (r : Z' ⟶ Z) (y : Z') (J) (hJ : Good L y J) :
    val t (r ≫ h) y J = val t' (r ≫ h') y J := by
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h') :=
    corr_of_val hL fun y J hJ => by rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, H y J hJ]
  rw [← val_pull hJ, ← val_pull hJ, val_corr hJ hc]

theorem main : AGermSt := by
  intro V _ _ _ _ D A G _ _ U κ _ _ z hz τ hτ F _ _ _ _ q
  have hL := U.LG.isLB
  refine ⟨fun σ' f f' hf hf' => ?_, fun l c σ f σ' hf hσ m => ?_, fun htr σ' => ?_⟩
  · refine GermFun.psJet_inj fun m => ?_
    obtain ⟨a, a₁, a₂, ha⟩ := hf m
    obtain ⟨b, b₁, b₂, hb⟩ := hf' m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    refine H1.cst_ext fun y => ?_
    obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
    exact (Units.mul_left_inj _).1 ((ha y J hJ).symm.trans (hb y J hJ))
  · obtain ⟨a, a₁, a₂⟩ := exists_jetPt (F := F) z m
    refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
    refine (SectionScalarValuation.sval_lin _ σ hσ a y hJ).trans ?_
    have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • f i))) =
        ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) * cst (𝟙 _) y (psJet m (f i)) := by
      refine (congrArg (cst (𝟙 _) y) (psJet_sum m c f)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
      exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
    rw [e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨b, b₁, b₂, hb⟩ := hf i m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    rw [hb y J hJ, _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · choose a a₁ a₂ using exists_jetPt (F := F) z
    have hv : ∀ m, ∃ v : Jet F κ m, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F κ m)) (y : Z) (J), Good U.LG.L y J →
        sval σ' (r ≫ a m) y J = cst r y v * (val (τ m) (r ≫ spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val := by
      intro m
      obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet F κ m) hL σ' (a m)
        (GeneratorPullback.powGen U.LG.L _ _ (LB.pullGen U.LG.L _ _ (τ m) (spMap (jetCoef (algebraMap V F) κ m))) q)
        (powGen_isGen_of_isGen _ (pullGen_isGen _ _ _ _ (hτ m) _) q) (fun W _ h => by simp only [a₂ m, _root_.mul_one])
      refine ⟨v, fun Z r y J hJ => (hv Z r y J hJ).trans ?_⟩
      rw [← val_pull hJ]
      exact congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _)
    choose v hv using hv
    have hc : ∀ m, (jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) (v (m + 1)) = v m := by
      intro m
      let ρ := spMap ((jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) : Jet F κ (m + 1) →+* Jet F κ m)
      let ρV := spMap ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)
      have hρ : ρ ≫ spMap (jetCoef (algebraMap V F) κ (m + 1)) = spMap (jetCoef (algebraMap V F) κ m) ≫ ρV := by
        rw [spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_trunc]
      have hzt : ρV ≫ (z (m + 1)).left = (z m).left := congrArg (fun q => q.left) (hz.1 m)
      have ha : ρ ≫ a (m + 1) = a m := gf_ext
        (by rw [Category.assoc, a₁, a₁]; exact spMap_comp_alg _)
        (by rw [Category.assoc, a₂, a₂, ← Category.assoc, hρ, Category.assoc, hzt])
      refine H1.cst_ext fun y => ?_
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e₁ := hv (m + 1) _ ρ y J hJ
      have e₀ := hv m _ (𝟙 _) y J hJ
      rw [Category.id_comp, Category.id_comp] at e₀
      rw [ha, hρ, val_congr hL (τ (m + 1)) (τ m) ρV (𝟙 _) (htr m) _ y J hJ, Category.comp_id] at e₁
      refine Eq.trans ?_ ((Units.mul_left_inj _).1 (e₁.symm.trans e₀))
      exact (ExpansionValueZero.cst_comp (𝟙 _) _ y _).symm.trans (congrArg (fun r => cst r y (v (m + 1))) (Category.id_comp _))
    obtain ⟨f, hf⟩ := GermD.exists_ps_of_jets v hc
    refine ⟨f, fun m => ⟨a m, a₁ m, a₂ m, fun y J hJ => ?_⟩⟩
    have e₀ := hv m _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, ← hf m] at e₀
    exact e₀

end GlobalTheory.GermBasic
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.NumFam

theorem eps_adj (k r : ℕ) (a c : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) (hc : c.val = a.val + 1) :
    PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r c := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ c.val < k - 1 := by omega
  simp only [PI.BesselPeriodGGP.eps48]
  rw [if_neg h1, if_neg h2, hc]
  rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
    simp [h3, h4]
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
    simp [h3, h4]

theorem abs_le_of_lOneNorm_le_coord {n : ℕ} (ν : Fin n → ℤ) (q0 : ℕ) (h : n1 ν ≤ q0) (a : Fin n) : |(ν a : ℝ)| ≤ q0 := by
  have h1 : (ν a).natAbs ≤ n1 ν := by
    unfold n1
    exact Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h2]
  exact_mod_cast h1.trans h

theorem gapOK_mono (k r : ℕ) {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  have ha : aOf r h ≤ aOf r h' := by
    unfold aOf
    gcongr
  exact ⟨h1, h2.trans hh, h3.trans ha, h4.trans ha⟩

private lemma le_bv_and_lam_gap_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ)
    (q0 : ℕ) (H : Num k r lam u b bv ga h q0) :
    h ≤ bv ∧ ∀ a c : Fin (2 * r + k + 1), a < c → 100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hgap, -, hq1, hq2, -⟩ := H
  have hhb : h ≤ bv := by
    have he := eps_adj k r ⟨k - 1, by omega⟩ ⟨k, by omega⟩ (show k ≤ k - 1 + 1 by omega)
      (show k = k - 1 + 1 by omega)
    have h0 := hnd ⟨k - 1, by omega⟩ (show k ≤ k - 1 + 1 by omega)
    have h1 := hnd ⟨k, by omega⟩ (show k ≤ k + 1 by omega)
    have hg := hgap _ _ he
    have hb : |lam ⟨k - 1, by omega⟩ - lam ⟨k, by omega⟩| ≤ bv :=
      abs_sub_le_iff.mpr ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
    linarith
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 →
      100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
    intro a c hac
    have hlt : a < c := Fin.lt_def.mpr (by omega)
    have hlam : lam c < lam a := hanti hlt
    by_cases h1 : k ≤ a.val + 1
    · have hg := hgap a c (eps_adj k r a c h1 hac)
      rw [abs_of_pos (by linarith)] at hg
      linarith
    · by_cases h2 : c.val + 1 < k
      · linarith [hga a c hlt h2]
      · have h3 := hcl a (by omega)
        have h4 := hnd c (by omega)
        linarith [h3.1, h4.2]
  refine ⟨hhb, fun a c hac => ?_⟩
  have h5 : a.val < c.val := hac
  have hcN := c.isLt
  have hle : a ≤ ⟨c.val - 1, by omega⟩ := Fin.le_def.mpr (show a.val ≤ c.val - 1 by omega)
  have h6 := hadj ⟨c.val - 1, by omega⟩ c (show c.val = c.val - 1 + 1 by omega)
  have h7 := hanti.antitone hle
  linarith

theorem num_fam : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  intro k r lam u b bv ga h q0 H
  obtain ⟨hhb, hgaps⟩ := le_bv_and_lam_gap_of_num k r lam u b bv ga h q0 H
  obtain ⟨hk, ⟨hanti, hint⟩, -, -, -, hcl, hnd, hlb, -, -, hgap, hok, hq1, hq2, hbv⟩ := H
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hN7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hN1 (by norm_num)
  have hNc : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have hL := hnd ⟨2 * r + k, by omega⟩ (show k ≤ 2 * r + k + 1 by omega)
  have hLb := hlb ⟨2 * r + k, by omega⟩
  have hLa := neg_le_abs (lam ⟨2 * r + k, by omega⟩)
  have hbvb : bv ≤ b := by linarith [hL.2]
  have h100 : 100 * (q0 : ℝ) ≤ bv := by linarith
  refine ⟨⟨hbvb, by linarith, by linarith, h100, gapOK_mono k r (by linarith) hok⟩, fun ν hν => ?_⟩
  have hνb : ∀ a, -(q0 : ℝ) ≤ ν a ∧ (ν a : ℝ) ≤ q0 := fun a => abs_le.mp (abs_le_of_lOneNorm_le_coord ν q0 hν a)
  have hgap2 : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    linarith [hgaps a c hac, (hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]
  refine ⟨⟨fun a c hac => ?_, fun a => ?_⟩, ⟨hk, by omega, fun a c hac => hgap2 a c hac, fun a ha => ?_,
    fun a ha => ?_, hbv⟩, fun a c he => ?_, fun a c hac => hgap2 a c hac⟩
  · show lam c + (ν c : ℝ) < lam a + ν a
    linarith [hgap2 a c hac]
  · obtain ⟨m, hm⟩ := hint a
    refine ⟨m + ν a, ?_⟩
    show lam a + (ν a : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = ((m + ν a : ℤ) : ℝ)
    push_cast
    linarith
  · refine ⟨?_, ?_, ?_⟩
    · simp [PI.BesselPeriodGGP.eps48, show a.val < k - 1 by omega]
    · show -(bv / 100) ≤ lam a + (ν a : ℝ)
      linarith [(hcl a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ bv / 8 + bv / 100
      linarith [(hcl a ha).2, (hνb a).2]
  · refine ⟨?_, ?_⟩
    · show -2 * bv - bv / 100 ≤ lam a + (ν a : ℝ)
      linarith [(hnd a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ -bv + bv / 100
      linarith [(hnd a ha).2, (hνb a).2]
  · show h / 2 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    have hg := hgap a c he
    rcases le_abs.mp hg with h1 | h1
    · exact le_abs.mpr (Or.inl (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))
    · exact le_abs.mpr (Or.inr (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))

end GlobalTheory.NumFam
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeFRep

theorem entry_le_hs {k r : ℕ} (g : Mx k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem isFRep_cmp (k r l : ℕ) :
    IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  have hm : ∀ g h : Mx k r, cmp l (g * h) = cmp l g * cmp l h := fun g h => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g h).1
  have hc : ∀ g : Mx k r, cmp l gᴴ = (cmp l g)ᴴ := fun g => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g g).2.1
  have h1 : cmp l (1 : Mx k r) = 1 := (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l 1 1).2.2.1
  refine ⟨?_, ?_, h1, fun g _ h _ => hm g h, ?_, ?_, ⟨(l.factorial : ℝ), ?_⟩, ?_⟩
  · rw [← hc, PI.StabPairsW.hpk_conjTranspose]
  · rw [← hm, PI.StabPairsW.hpk_mul_self, h1]
  · intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [← hc, ← hm, ← hm, hg']
  · intro I J
    apply Continuous.continuousOn
    unfold BranchingSupport.cmp
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · intro g _ I J
    have := Matrix.det_le (A := g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2))
      (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (x := B.gN g) (fun i j => entry_le_hs g _ _)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · intro g _ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← hc, ← hm, hu, h1]

end GlobalTheory.WedgeFRep
end

section

noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T T' : Over (Spec (CommRingCat.of R))}

variable {U} in
theorem hasCoords_pull {e : ℕ} {k : T' ⟶ T} {g : GtPt D.toPre T} {g' : GtPt D.toPre T'}
    (h : GtPt.IsPull k.left g g') {Z : Scheme.{0}} {r : Z ⟶ T'.left} {y : Z ⟶ (thickObj R I e G).left} :
    HasCoords U e g (r ≫ k.left) y ↔ HasCoords U e g' r y := by
  rw [hasCoords_iff, hasCoords_iff, h.1, Category.assoc]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun z => forall_congr' fun J =>
    forall_congr' fun hJ => ?_)
  rw [(val_corr hJ (h.2 χ) r).trans (val_pull hJ _ _ _)]

variable {U} in
theorem eq_of_hasCoords {e : ℕ} {g g' : GtPt D.toPre T} {y : T.left ⟶ (thickObj R I e G).left}
    (h : HasCoords U e g (𝟙 _) y) (h' : HasCoords U e g' (𝟙 _) y) : g = g' := by
  rw [hasCoords_iff, Category.id_comp] at h h'
  exact pt_ext (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ z J hJ => (h.2 χ z J hJ).symm.trans (h'.2 χ z J hJ)

theorem isPointOf_iff_thick (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (thickι I e T) (thickHom I e x) := by
  refine ⟨fun h e => h e _ _ _ (thickHom_ι I e x), fun h e Z r y hy => ?_⟩
  have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ thickι I e T = r := ⟨pullback.lift r _ w, pullback.lift_fst _ _ _⟩
  obtain rfl : y = l ≫ thickHom I e x := by
    rw [← cancel_mono (thickι I e G), Category.assoc, thickHom_ι]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

theorem existsUnique_point (hT : IsAdicColimit I T) (g : GtPt D.toPre T) : ∃! x : T ⟶ G, IsPointOf U g x := by
  choose y hy using fun e =>
    exists_hasCoords U e g (thickι I e T) (thickObj R I e T).hom pullback.condition.symm
  refine existsUnique_of_exists_of_unique ?_ fun x x' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    (h.comp_fstG_eq (hy e)).symm.trans (h'.comp_fstG_eq (hy e)))
  obtain ⟨x, hx, -⟩ := hT G.left (fun e => y e ≫ thickι I e G) fun e => by
    have h₁ := (hy (e + 1)).comp (thickMap R I e T)
    rw [thickMap_ι] at h₁
    rw [← Category.assoc, h₁.unique (hy e).succ, Category.assoc, thickMap_ι]
  have hw : x ≫ G.hom = T.hom := hT.hom_ext fun e => by
    have h₁ : thickι I e G ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    rw [reassoc_of% hx e, h₁, reassoc_of% (hy e).1, Over.w]
  refine ⟨Over.homMk x hw, (isPointOf_iff_thick U g _).2 fun e => ?_⟩
  have : thickHom I e (Over.homMk x hw : T ⟶ G) = y e := by
    rw [← cancel_mono (thickι I e G), thickHom_ι]
    exact hx e
  rw [this]
  exact hy e

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T}

theorem existsUnique_lift (hΦ : Represents Φ) (hT : IsAdicColimit I T) (x : T ⟶ G) :
    ∃! w : T ⟶ H, IsPointOf U (Φ T w) x := by
  have pl : ∀ (e : ℕ) (w : T ⟶ H), HasCoords U e (Φ T w) (thickι I e T) (thickHom I e x) ↔
      HasCoords U e (Φ _ (fstG I e T ≫ w)) (𝟙 _) (thickHom I e x) := fun e w => by
    rw [← hasCoords_pull (hΦ.1 _ _ (fstG I e T) w), Category.id_comp]; rfl
  refine existsUnique_of_exists_of_unique ?_ fun w w' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    congrArg (·.left) ((Φ _).injective (eq_of_hasCoords ((pl e w).1 ((isPointOf_iff_thick U _ x).1 h e))
      ((pl e w').1 ((isPointOf_iff_thick U _ x).1 h' e)))))
  have ex : ∀ e, ∃ w : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶ H,
      HasCoords U e (Φ _ w) (𝟙 _) (thickHom I e x) := fun e => by
    obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (U.gt e) (T := (Over.map (thick R I e)).obj (thickObj R I e T))
      (thickHom I e x) (by rw [← Category.assoc, Over.w]; rfl)
    refine ⟨(Φ _).symm ξ, ?_⟩
    rw [Equiv.apply_symm_apply, hasCoords_iff]
    refine ⟨hξ.1.symm.trans (Category.id_comp _).symm, fun χ z J hJ => ?_⟩
    have := (val_corr hJ (hξ.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  choose w hw using ex
  obtain ⟨v, hv, -⟩ := hT H.left (fun e => (w e).left) fun e => by
    let m : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶
        (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) T) := Over.homMk (thickMap R I e T)
      (((congrArg (thickMap R I e T ≫ ·) (Over.w (fstG I (e + 1) T)).symm).trans
        (thickMap_ι_assoc I e T T.hom)).trans (Over.w (fstG I e T)))
    have h₁ := (hw (e + 1)).comp (thickMap R I e T)
    rw [thickMap_thickHom, Category.comp_id, ← Category.id_comp (thickMap R I e T)] at h₁
    have h₂ := (hasCoords_pull (hΦ.1 _ _ m (w (e + 1)))).1 h₁
    exact congrArg (·.left) ((Φ _).injective (eq_of_hasCoords h₂ (hw e).succ))
  have hv' : v ≫ H.hom = T.hom := hT.hom_ext fun e => by
    rw [reassoc_of% hv e, Over.w]
    exact (Over.w (fstG I e T)).symm
  refine ⟨Over.homMk v hv', (isPointOf_iff_thick U _ x).2 fun e => (pl e _).2 ?_⟩
  have : fstG I e T ≫ (Over.homMk v hv' : T ⟶ H) = w e := Over.OverMorphism.ext (hv e)
  rw [this]
  exact hw e

theorem exists_mulEquiv (hG : GlobalFnsSt) (hΦ : Represents Φ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)),
      ∀ T hT w x, J T hT w = x ↔ IsPointOf U (Φ T w) x := by
  choose j hj hu using fun T (hT : IsAdicColimit I T) (w : T ⟶ H) => existsUnique_point U hT (Φ T w)
  have bij : ∀ T hT, Function.Bijective (j T hT) := fun T hT => (Function.bijective_iff_existsUnique _).2 fun x =>
    (existsUnique_congr fun w => ⟨fun h => (hu T hT w x h).symm, fun h => h ▸ hj T hT w⟩).1
      (existsUnique_lift U hΦ hT x)
  exact ⟨fun T hT => MulEquiv.mk' (Equiv.ofBijective _ (bij T hT)) fun w w' =>
      (hu T hT _ _ ((hj T hT w).mul hG (hj T hT w') (hΦ.2 T w w'))).symm,
    fun T hT w x => ⟨fun h => h ▸ hj T hT w, fun h => (hu T hT w x h).symm⟩⟩

end GlobalTheory.TorusModel
end
end
