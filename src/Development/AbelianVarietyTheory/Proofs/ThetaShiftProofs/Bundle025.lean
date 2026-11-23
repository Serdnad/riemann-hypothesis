module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle012
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem GlobalTheory.ArcQ.frChg_exists_unique_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  intro E _ _ _ H Dw l Xo c S _ _ g s y
  have hunit : ∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s := by
    intro y' h
    obtain ⟨h1, h2⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y'
    obtain ⟨g', a, hg', h'⟩ := h1 h.1
    obtain ⟨e1, e2⟩ := h2 g g' s a h h'
    subst e1 e2
    exact ⟨hg', a.isUnit⟩
  refine ⟨fun hg hs => ?_, fun y' y'' h' h'' => ?_, hunit, fun y' hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hs
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).exists
  · obtain ⟨hg, a, rfl⟩ := hunit y' h'
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).unique h' h''
  · obtain ⟨g', a, -, h⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 hx
    exact ⟨g', a, h⟩
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
open Filter Topology

namespace GlobalTheory.AbelianLetters

theorem exists_top_le_wchart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Sp ℂ ⟶ X)) : ∃ j, ⊤ ≤ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k (default : PrimeSpectrum ℂ))
  refine ⟨j, fun p _ => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj k

theorem valAt'_unit_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  rw [HolHom.valAt'_eq_valR, HolHom.valR_eq _ _ h]
  exact (f.isUnit.map _).ne_zero

theorem IsRatio.differentiableAt_zero : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  intro _ D g n ex s₀ hb hadd hol hchi u hu x
  obtain ⟨j, hj⟩ := exists_top_le_wchart D.P.isLB (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • 0)).b x)
  have h1 : ∀ z, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (𝟙 D.P.A ^ 1) x) j := by
    intro z
    have := top_le_wchart_nsmul hadd (n := 1) rfl z x j
    rwa [Nat.cast_one, one_smul] at this
  have hS : {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j} ∈ 𝓝 ((n : ℂ) • (0 : Fin g → ℂ)) := by
    filter_upwards [(HolHom.holAt_of_isHolTo hol (Set.mem_univ ((n : ℂ) • (0 : Fin g → ℂ))) _ ((h1 _).1 hj)).1]
      with t ht using (h1 t).2 ht
  have hn : DifferentiableAt ℂ (fun z : Fin g → ℂ => (n : ℂ) • z) 0 := by fun_prop
  have hc : DifferentiableAt ℂ (fun z => chiVal (ex ((n : ℂ) • z)) x j) 0 :=
    ((hchi x j).differentiableAt hS).comp 0 hn
  have h0 := (top_le_wchart_nsmul hadd hb 0 x j).1 hj
  obtain ⟨hev, hd⟩ := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) _ h0
  refine (hc.fun_mul ((hd ((s₀.s x).s j).val).fun_inv (valAt'_unit_ne_zero _ h0 _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (eq_mul_inv_iff_mul_eq₀ (valAt'_unit_ne_zero _ ht _)).2
    (hu x t j ((top_le_wchart_nsmul hadd hb t x j).2 ht)).symm

end GlobalTheory.AbelianLetters
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.AbelianLetters

theorem fderiv_eq_zero_of_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F u G : V → ℂ} {c : ℂ} {z : V}
    (hc : c ≠ 0) (hu : DifferentiableAt ℂ u 0) (hu0 : u 0 = 1) (hG : DifferentiableAt ℂ G 0) (hG0 : G 0 ≠ 0)
    (h : (fun t => F (c • t)) =ᶠ[nhds 0] fun t => u t * G t) (e : fderiv ℂ F 0 z = c⁻¹ * fderiv ℂ G 0 z) :
    fderiv ℂ u 0 z = 0 := by
  have e' := congrArg (· z) (h.fderiv_eq (𝕜 := ℂ))
  rw [fderiv_comp_smul, smul_zero, fderiv_fun_mul hu hG, hu0] at e'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, _root_.one_mul] at e'
  rw [e, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul, left_eq_add, mul_eq_zero] at e'
  exact e'.resolve_left hG0

theorem fderiv_ratio_eq_zero : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  intro _ _ D g n ex sB hb _ hpull hadd hol _ hn u hu hud hu0 v ν z hν hv hval x
  have hv' := (HolHom.isDerivAt0_iff _ _ _).1 hv
  have hH := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0)
  have hp := hpull _ _ v (𝟙 _)
  rw [Category.comp_id] at hp
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ (show Sp ℂ ⟶ _ from (ex 0).b.left) ⁻¹ᵁ
      LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x) j := by
    choose j hj using fun k => exists_chart D.P.isLB (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x k
      ((show Sp ℂ ⟶ _ from (ex 0).b.left) (default : PrimeSpectrum ℂ)))
    exact ⟨j, (HolHom.le_preimage_iff _ _).2 (Set.mem_iInter.2 hj)⟩
  have hvW := (HolHom.le_preimage_dual_iff hv'.1 _).2 hj
  have h1 := (top_le_wchart_pull hp.1 x j).2 hvW
  have h2 := (top_le_wchart_pull hν.1 x j).2 (fun p _ => h1 trivial)
  have e1 := valR_of_isPull hν x j
  have e2 := valR_of_isPull hp x j
  have e3 := HolHom.valR_spMap (epsScaleR ((n : ℂ)⁻¹)) (𝟙 (Sp (DualNumber ℂ)))
    (LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) (sB (epsR ℂ) v).b x) j) h1 (((sB (epsR ℂ) v).s x).s j).val
  rw [Category.comp_id] at e3
  have e4 := congrArg TrivSqZeroExt.snd ((hval x j h2).symm.trans (e1.trans (e3.trans (congrArg _ e2))))
  have e5 : ∀ a : DualNumber ℂ, TrivSqZeroExt.snd (epsScaleR ((n : ℂ)⁻¹) a) = (n : ℂ)⁻¹ * TrivSqZeroExt.snd a := by
    intro a
    simp [epsScaleR]
  replace e4 := e4.trans ((e5 _).trans (congrArg (_ * ·) (hv'.2 _ hj _)))
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e4
  obtain ⟨hev, hd⟩ := hH _ hj
  exact fderiv_eq_zero_of_smul (F := fun z' => chiVal (ex z') x j) (Nat.cast_ne_zero.2 hn.ne') (hud x) (hu0 x)
    (hd (((sB D.P.A (𝟙 _)).s x).s j).val)
    ((HolHom.valR_eq _ _ hj _).trans_ne ((((sB D.P.A (𝟙 _)).s x).s j).isUnit.map (HolHom.evalHom _ _ hj)).ne_zero)
    (hev.mono fun z' hz' => hu x z' j ((top_le_wchart_nsmul hadd (hb _ _) z' x j).2 hz')) e4

end GlobalTheory.AbelianLetters
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_nonvanishing_multiplicative_ratio : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧ ∀ x z z', u x (z + z') = u x z * u x z' := by
  first | exact @GlobalTheory.AbelianLetters.exists_isRatio_mul | exact GlobalTheory.AbelianLetters.exists_isRatio_mul | (intros; apply GlobalTheory.AbelianLetters.exists_isRatio_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.torusCoordinateRatio_eq_torusCoord_over_origin : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧ ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ), (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  first | exact @GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | exact GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | (intros; apply GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.GenDvr

open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1

theorem generates_of_generic_line {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X X' : Scheme.{0}}
    (p : X ⟶ Sp V) [Flat p] {p' : X' ⟶ Sp (FractionRing V)} {φ : X' ⟶ X}
    (hφ : IsPullback φ p' p (spMap (algebraMap V (FractionRing V)))) {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (b : L'.Sec)
    (hb : ∀ s : L'.Sec, ∃ a : FractionRing V, ∀ i, s.f i = constFn p' _ a * b.f i)
    (θ : L.Sec) {g : X} (hg : p g = closedPoint V) (hθ : g ∈ Out.nonzeroLocus θ) (σ : L.Sec) :
    ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i := by
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  have hk₀ : g ∈ L.U k₀ := X.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w, gw'⟩ := hw
  have down := sec_pull_down ((isGen_iff w).1 gw') hL hL'
  obtain ⟨θ', hθ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hφ.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hφ.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f σ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f τ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn p' _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn p _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_pull (𝟙 _) φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk,
      (sec_eq_iff _ _ _ _).1 h₃ k y hk, Category.id_comp, hφ.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : L'.Sec} {a a' : FractionRing V}, (∀ k, s.f k = constFn p' _ a * t.f k) →
      (∀ k, t.f k = constFn p' _ a' * u.f k) → ∀ k, s.f k = constFn p' _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : L'.Sec} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn p' _ a * t.f k) →
      ∀ k, t.f k = constFn p' _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : L.Sec) (r : V), (∀ j, θ.f j = constFn p _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit p g hg hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀⟩ := hb θ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ θ' θ' 0 hθ' hθ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  obtain ⟨σK, hσK⟩ := down σ
  obtain ⟨a, ha⟩ : ∃ a : FractionRing V, ∀ i, σK.f i = constFn p' _ a * θ'.f i := by
    obtain ⟨a, ha⟩ := hb σK
    exact ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀)⟩
  obtain ⟨r, hr⟩ : ∃ r : V, ∀ i, σ.f i = constFn p _ r * θ.f i := by
    by_cases h : IsLocalization.IsInteger V a
    · obtain ⟨r, rfl⟩ := h
      exact ⟨r, inj σ θ σK θ' r hσK hθ' ha⟩
    · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
      obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
      obtain ⟨u, rfl⟩ := unit σ r (inj θ σ θ' σK r hθ' hσK (hr ▸ invc hne ha))
      exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
  refine ⟨r, hr, fun r' hr' => ?_⟩
  by_contra hne
  have e : cst p g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst p g (r' - r) * 0 := by
    rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
  exact un.ne_zero (cst_regular p g (sub_ne_zero.2 hne) e)

theorem generates_of_nonzero_on_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  intro _ h₂ E _ _ _ H Dw l Xo _ T G t' x m₁ m₂ θ ⟨g, hg, hθ⟩ σ
  have := G.semi.smooth
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre h₂.secTwist amplePt Xo.univ m₁
  obtain ⟨w, hw, -⟩ := m₂.lin
  exact generates_of_generic_line G.G.hom m₂.cart.1 G.PP.isLB t'.PP.isLB ⟨w, hw⟩ b (fun s => (hb s).exists) θ hg hθ σ

end GlobalTheory.GenDvr
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.PerFlow

open Matrix
open scoped ComplexConjugate ComplexOrder

section aux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma perFr_mem (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dif_pos τ.2]

lemma perFr_conj (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dif_pos h2, dif_pos h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (u : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ u =
      u + (s * τ.1 X.κ0 * hermC τ.1 X.Gm u (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  rw [EmbeddingHermitianPairs.flowMat_eq, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    EmbeddingHermitianPairs.wv_dot, X.tau_kappa0]
  funext a
  simp
  ring

lemma flow_mem {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ.1 i =
      perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i := by
  simp only [perFr_mem]
  split_ifs with hi
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    have hinv : (X.flowMat ξ τ (s τ))⁻¹ = X.flowMat ξ τ (-s τ) := by
      apply inv_eq_right_inv
      rw [EmbeddingHermitianPairs.flowMat_mul X hξ, add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero]
    have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
      EmbeddingHermitianPairs.hermC_emb _ _ _ _
    rw [hm, Matrix.mul_inv_rev, hinv, ← mulVec_mulVec, flowMat_mulVec, mulVec_add, mulVec_smul, he,
      map_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

lemma flow_conj (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (hi : i < X.p0) :
    perFr X (X.flow ξ s x) v (conjEmb τ.1) i =
      perFr X x v (conjEmb τ.1) i -
        s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i := by
  have hlt : X.p0 - 1 - i < r := by have := X.p0_le; omega
  simp only [perFr_conj X _ _ τ i ⟨_, hlt⟩ rfl]
  have hc : FD.col (mat (X.flow ξ s x) τ) ⟨_, hlt⟩ =
      X.flowMat ξ τ (s τ) *ᵥ FD.col (mat x τ) ⟨_, hlt⟩ := rfl
  have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
    EmbeddingHermitianPairs.hermC_emb _ _ _ _
  have he' : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 v) = conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← he, hermC_conj τ.1 X.Gm_herm]
  have hk : conj (τ.1 X.κ0) = -τ.1 X.κ0 := by
    rw [← EmbeddingHermitianPairs.emb_cc', X.cc_kappa0, map_neg]
  have h2 : conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) = -τ.1 X.κ0 * conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← hk, ← map_mul, ← map_mul]; rfl
  rw [hc, flowMat_mulVec, hermC_add_left, hermC_smul_left, he', h2]
  ring

def blockEquiv : Fin X.p0 ⊕ Fin (r - X.p0) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega))

lemma blockEquiv_inl (a : Fin X.p0) : blockEquiv X (.inl a) = Fin.castLE X.p0_le a := by
  apply Fin.ext; simp [blockEquiv]

lemma blockEquiv_inr (a : Fin (r - X.p0)) : ((blockEquiv X (.inr a) : Fin r) : ℕ) = X.p0 + a := by
  simp [blockEquiv]

def blk (P : Matrix (Fin X.p0) (Fin X.p0) ℂ) (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.reindex (blockEquiv X) (blockEquiv X) (fromBlocks P 0 0 Q)

lemma blk_mul (P P' : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q Q' : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    blk X P Q * blk X P' Q' = blk X (P * P') (Q * Q') := by
  simp [blk, fromBlocks_multiply]

lemma blk_one : blk X 1 1 = 1 := by
  simp [blk]

lemma blk_mulVec_inr (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (w : Fin r → ℂ) (i : Fin (r - X.p0)) :
    (blk X P Q *ᵥ w) (blockEquiv X (.inr i)) = ∑ k, Q i k * w (blockEquiv X (.inr k)) := by
  simp only [mulVec, dotProduct]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type]

lemma col_mul_blk (M : Matrix (Fin r) (Fin r) ℂ) (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (j : Fin X.p0) :
    FD.col (M * blk X P Q) (Fin.castLE X.p0_le j) =
      ∑ k, P k j • FD.col M (Fin.castLE X.p0_le k) := by
  funext a
  simp only [FD.col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ← blockEquiv_inl]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type, mul_comm]

lemma block_change (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ)
    (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ) (hA : ∀ τ, (A τ).det ≠ 0) (hB : ∀ τ, (B τ).det ≠ 0) :
    ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ),
      (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧
      ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  let P : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ :=
    fun τ => ((B τ).submatrix Fin.revPerm Fin.revPerm)ᵀ
  have hP : ∀ τ, (P τ).det ≠ 0 := fun τ => by
    simp only [P, det_transpose, det_submatrix_equiv_self]; exact hB τ
  let x' : Frame X.Ψ r := fun τ => (mat x τ * blk X (P τ) (A τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, mat x' τ = mat x τ * blk X (P τ) (A τ)⁻¹ := fun τ => rfl
  have hone : ∀ τ, blk X (P τ) (A τ)⁻¹ * blk X (P τ)⁻¹ (A τ) = 1 := fun τ => by
    rw [blk_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hP τ)),
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA τ)), blk_one]
  have hcol : ∀ τ j, X.colP x' τ j = ∑ k, P τ k j • X.colP x τ k := fun τ j => by
    unfold Data.colP
    rw [hm, col_mul_blk]
  refine ⟨x', AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩, fun v τ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rw [hm, det_mul]
    refine mul_ne_zero (hx τ).1 fun h0 => ?_
    have := congrArg det (hone τ)
    rw [det_mul, h0] at this
    simp at this
  · have hg : X.gramPos x' τ = (P τ)ᵀ * X.gramPos x τ * ((P τ)ᵀ)ᴴ := by
      ext a b
      rw [Data.gramPos_apply, hcol, hcol, hermC_sum_right]
      simp only [Matrix.mul_apply, hermC_smul_right, hermC_sum_left, hermC_smul_left,
        conjTranspose_apply, transpose_apply, Data.gramPos_apply, Complex.star_def]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hg]
    refine (X.gramPos_posDef hx τ).mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (by rw [det_transpose]; exact hP τ)))
  · have hlt : ∀ k : Fin (r - X.p0), X.p0 + k < r := fun k => by have := k.2; omega
    have hidx : ∀ k : Fin (r - X.p0), (⟨X.p0 + k, hlt k⟩ : Fin r) = blockEquiv X (.inr k) :=
      fun k => Fin.ext (blockEquiv_inr X k).symm
    simp only [perFr_mem, dif_pos (hlt _), hidx]
    rw [hm, Matrix.mul_inv_rev, inv_eq_right_inv (hone τ), ← mulVec_mulVec, blk_mulVec_inr]
  · have hr : ∀ (y : Frame X.Ψ r) (k : Fin X.p0), perFr X y v (conjEmb τ.1) k =
        hermC τ.1 X.Gm (X.colP y τ k.rev) (Data.emb τ.1 v) := fun y k =>
      perFr_conj X y v τ k (Fin.castLE X.p0_le k.rev) (by simp [Fin.val_rev]; omega)
    simp only [hr]
    rw [hcol, hermC_sum_left, ← Equiv.sum_comp Fin.revPerm]
    simp [P, hermC_smul_left]

end aux

theorem perFr_flow_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  intro E _ _ _ r X
  exact ⟨fun ξ hξ s x _ v τ i => ⟨flow_mem X hξ s x v τ i, flow_conj X ξ s x v τ i⟩,
    fun x hx A B hA hB => block_change X x hx A B hA hB⟩

end GlobalTheory.PerFlow
end
