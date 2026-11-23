module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle124
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIndexOfLocal
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle030
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GsSpMapGermAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle120
public import Formalism.HermitianCurvature.Bundle009
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle122
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem sum_ite_le {ι β : Type} [Fintype ι] (φ : ι → β) (hφ : Function.Injective φ) (y : β)
    [∀ t, Decidable (y = φ t)] (g : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ t, g t ≤ B) :
    (∑ t, if y = φ t then g t else 0) ≤ B := by
  classical
  by_cases h : ∃ t, y = φ t
  · obtain ⟨t, rfl⟩ := h
    rw [Finset.sum_eq_single t]
    · simpa using hg t
    · intro t' _ ht'
      rw [if_neg fun h => ht' (hφ h).symm]
    · simp
  · rw [Finset.sum_eq_zero fun t _ => if_neg fun h' => h ⟨t, h'⟩]
    exact hB

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conj_tauEmb_injective (D : D7) :
    Function.Injective fun t => ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) := by
  intro s t h
  apply tauEmb_injective D
  ext x
  have := RingHom.congr_fun h x
  exact (starRingEnd ℂ).injective this

theorem mul_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (i : ℕ)
    (hP : ∀ t, T * (ext0 (w.aP t) i : ℝ) ≤ A) (hM : ∀ t, T * (ext0 (w.aM t) i : ℝ) ≤ B) (τ : D.host.E →+* ℂ) :
    T * wtA w (τ, i) ≤ A + B := by
  classical
  unfold wtA
  push_cast
  rw [Finset.mul_sum]
  simp only [mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · convert sum_ite_le (DV.tauEmb D) (tauEmb_injective D) τ _ A hA hP
  · convert sum_ite_le _ (conj_tauEmb_injective D) τ _ B hB hM

theorem b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.a Scale.X' Scale.b
  have : 0 < s.x := by linarith [s.one_lt_alt]
  positivity

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) (hx : 3 ≤ s.x) : s.w'' n ≤ s.b' / 3 := by
  unfold Scale.w''
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (b'_pos s).le (by norm_num) (by nlinarith)

theorem first_rows_and_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  intro D L Pm Tp hK j hj hx hkb
  obtain ⟨-, hsz⟩ := GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  obtain ⟨hw, -, hnum⟩ := hsz j hj
  have hb' := b'_pos L.sc
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hw3 := w''_le L.sc D.R.n hn hx
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hbb : L.sc.b' ≤ L.sc.b := by nlinarith
  have hSc : L.Sc ≤ L.sc.b' / 3 := by nlinarith [Pm.kS_le, L.Sc_pos]
  have heta : L.etaSz ≤ L.sc.b' / 3 := by
    have h1 := Pm.teta
    have h2 := L.t_win.1
    have h3 := L.etaSz_pos
    have h0 : 0 ≤ L.sc.w'' D.R.n := by nlinarith [Pm.kS_le, L.Sc_pos]
    have h4 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self h0 L.sc.one_lt_alt.le
    nlinarith
  have hScp := L.Sc_pos
  have hetap := L.etaSz_pos
  refine ⟨fun τ => ?_, fun z => ⟨?_, ?_⟩⟩
  · have := mul_wtA_le (lR Tp hK j) (Tp.TO : ℝ) (2 * L.sc.b + L.Sc) L.etaSz (by linarith) hetap.le 0 ?_ ?_ τ
    · linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).1 ⟨0, h⟩ (by show 0 < D.R.k - 1; omega)
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith [(hw t).2]
      · simp only [Nat.cast_zero, mul_zero]; linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).2.1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).2.2 ⟨0, h⟩
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith
      · simp only [Nat.cast_zero, mul_zero]; linarith
  · rw [hnum z]
    set τ := plOf D z
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      have h1 := (L.win_top j hj.1 hj.2 τ ⟨t, ht⟩ hte.symm).1
      have h2 := L.bT_ge ⟨t, ht⟩
      have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'.le (by linarith)
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h1 := (L.win_thick j hj.1 hj.2 τ hth).1
        linarith
      · exact (L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hth⟩).1
  · rw [hnum z]
    exact (hw _).2

end GlobalTheory.FirstRows
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc

  simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.truncation_frames_local_series E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomLem8

theorem ev_col {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) (R : BranchingSupport.Rep k r) (x : ι → R.H) (e : ι) :
    ev Γ R (fun c => Γ c e) x = x e := by
  unfold ev
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, (star (Γ i e) * Γ i j) = if e = j then 1 else 0 := by
    intro j
    have h := congrFun (congrFun h2 e) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (Γ i e) = Γ e i := by
      have := congrFun (congrFun hH e) i
      rwa [Matrix.conjTranspose_apply] at this
    rw [this]
  simp_rw [← Finset.sum_smul, key]
  simp

theorem transpose_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) : Γᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have : (Γᵀ)ᴴ = Γᵀ := by
    rw [show (Γᵀ)ᴴ = (Γᴴ)ᵀ from rfl, hH]
  rw [this, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

theorem div_step (b t : ℝ) (ht : 0 ≤ t) (L : ℝ≥0∞)
    (h : ENNReal.ofReal (b * t * t) ≤ L * ENNReal.ofReal t) : ENNReal.ofReal (b * t) ≤ L := by
  rcases ht.eq_or_lt with h0 | h0
  · simp [← h0]
  · rw [ENNReal.ofReal_mul' ht] at h
    exact (ENNReal.mul_le_mul_iff_left (by simpa using h0) ENNReal.ofReal_ne_top).1 h

theorem moment_lemma_pieri : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ‖(ρ (Matrix.of x)⁻¹ *ᵥ om) i‖ ^ 2) * ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
  intro hy k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hρ hT
    hS hB hBI hβ I hI y hy'
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hadj, -, hev, hnorm, -⟩ :=
    GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hρ hT
  obtain ⟨hae, hcont, -, hmB⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS
  obtain ⟨-, -, -, hmI⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (hRI I) hS
  have hf := hmI (BI I) hI.1 y hy'
  have hH := hρ.1
  have h2 := hρ.2.1
  have hc := hρ.2.2.2.2.2.1
  have hph : ∀ e, AEStronglyMeasurable
      (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om) νq := by
    intro e
    refine hcont ℂ (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ fun c => Γ c e) om) ?_
    simp only [Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ?_
    exact continuousOn_finsetSum _ fun l _ => (hc j l).mul continuousOn_const
  have hstep : ∀ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (‖Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om‖ ^ 2 *
        ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
    intro e
    have hw : io I e y ∈ R.sm := (hT.raw.io_sm I e).mem y hy'
    have hpair := GlobalTheory.T.tensor_moment_transfer hy k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π u μW μN μG νq om Bm BI β hR hRI hinj
      hT.raw hS hB.1 hBI hβ I hI y hy' (fun c => Γ c e) (io I e y) hw
    have hcs := GlobalTheory.T.norm_sq_integral_inner_weight_le (Formalism.QuantumDeterminants.Mt k r) Wp νq _ _ _ hf (hmB Bm hB.1 _ hw) (hph e)
    rw [hpair] at hcs
    have hiso := hB.2 _ hw
    have hg : ∫⁻ x, ENNReal.ofReal (‖Bm (R.σ (Matrix.of x) (io I e y))‖ ^ 2) ∂νq =
        ENNReal.ofReal (‖io I e y‖ ^ 2) := by
      rw [← hiso]
      unfold PI.BesselPeriodGGP.l2SG
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [hg] at hcs
    have h1 := hadj I y hy' (tm R (fun c => Γ c e) (io I e y)) (fun c => R.smSub.smul_mem _ hw)
    rw [hev, ev_col Γ hH h2] at h1
    have h3 : ‖⟪y, ∑ c, pr I c (tm R (fun c => Γ c e) (io I e y) c)⟫_ℂ‖ = ‖io I e y‖ ^ 2 := by
      rw [norm_inner_symm]
      have h4 := congrArg norm h1
      have hep : ‖(ep I : ℂ)‖ = 1 := by
        rcases hT.ep_sq I with h | h <;> simp [h]
      rw [norm_mul, hep, one_mul, inner_self_eq_norm_sq_to_K] at h4
      rw [← h4]
      simp
    rw [norm_mul, h3] at hcs
    refine div_step _ _ (by positivity) _ ?_
    convert hcs using 2
    ring
  have hsum : ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∑ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hnorm I y hy') (by positivity))
  refine hsum.trans ((Finset.sum_le_sum fun e _ => hstep e).trans (le_of_eq ?_))
  rw [← lintegral_finsetSum']
  · refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.sum_mul]
    have := GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal k r ι ρ Γ Γᵀ d om hρ (transpose_unitary Γ hH h2) _ hx
    rw [← this]
    rfl
  · intro e _
    exact (((hph e).norm.aemeasurable.pow_const 2).mul (hf.norm.aemeasurable.pow_const 2)).ennreal_ofReal

end GlobalTheory.MomLem8
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by
  first | exact @GlobalTheory.splitCasimir_eigenspace_irreducible_standard | exact GlobalTheory.splitCasimir_eigenspace_irreducible_standard | (intros; apply GlobalTheory.splitCasimir_eigenspace_irreducible_standard <;> assumption)
end
