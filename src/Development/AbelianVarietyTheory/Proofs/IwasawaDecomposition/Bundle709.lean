module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle705
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle693
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle694
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle704
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  first | exact @GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | exact GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | (intros; apply GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
  GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem topCoeff_sum' {n : ℕ} {κ : Type} (s : Finset κ) (P : κ → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, P i) = ∑ i ∈ s, topCoeff (P i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_real_smul {n : ℕ} (r : ℝ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (r • P) = (r : ℂ) * topCoeff P := by
  simp only [topCoeff, MvPolynomial.coeff_smul, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem topCoeff_chern_eq_sum_rep : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  intro ι _ m n R
  classical
  have hmem := GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan m n (MvPolynomial (Fin n × Fin n) ℂ)
    (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.1 hmem
  choose ρ hρ using fun i => (g i).2
  refine ⟨Fin k, inferInstance, ρ, f, fun A hA => ?_⟩
  set c : ι × ℕ → MvPolynomial (Fin n × Fin n) ℂ := fun x => (Matrix.charpolyRev (-A x.1)).coeff x.2 with hc
  have hch : ∀ x : ι × ℕ, IsWeightedHomogeneous (1 : Fin n × Fin n → ℕ) (c x) x.2 := fun x =>
    ChernDegree.charpolyRev_coeff_isHomogeneous (-A x.1) (fun i j => (hA x.1 i j).neg) x.2
  have key : ∀ d : ι × ℕ →₀ ℕ, Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d ≠ n →
      topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) = 0 := by
    intro d hd
    have h1 : IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) (monomial d (AddMonoidAlgebra.coeff R d))
        (Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    exact ChernDegree.topCoeff_eq_zero (ChernDegree.aeval_isWeightedHomogeneous h1 c hch) hd
  have e1 : topCoeff (aeval c R) = ∑ d ∈ R.support, topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by
    conv_lhs => rw [R.as_sum]

    rw [map_sum, topCoeff_sum']
  have e2 : topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) =
      ∑ d ∈ R.support with Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d = n,
        topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by

    rw [weightedHomogeneousComponent_apply, map_sum, topCoeff_sum']
  have e3 : topCoeff (aeval c R) = topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) := by
    rw [e1, e2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rfl
    · exact key d h
  have hval := congrFun hfg A
  simp only [Finset.sum_apply, Pi.smul_apply] at hval
  rw [e3, ← hval, topCoeff_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topCoeff_real_smul, ← hρ i]

end GlobalTheory.GoodMetric.ChernSpan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_homogeneous_positive_polFan_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ' : InvFun (𝓞 E)), IsPolFan H.bar q φ' → NoSelfInt H.bar q φ' → IsTwInv H φ' → ∃ φ'' : InvFun (𝓞 E), IsPolFan H.bar q φ'' ∧ NoSelfInt H.bar q φ'' ∧ IsTwInv H φ'' ∧ IsPosFn H φ'' ∧ (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ''.toFun n (fun a b => k * B a b) = k * φ''.toFun n B) ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ'' γ → IsCone H.bar φ' γ := by
  first | exact @GlobalTheory.PolFan.OffDom.exists_extension | exact GlobalTheory.PolFan.OffDom.exists_extension | (intros; apply GlobalTheory.PolFan.OffDom.exists_extension <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  first | exact @GlobalTheory.PrimRay.eq_of_toReal_eq_smul | exact GlobalTheory.PrimRay.eq_of_toReal_eq_smul | (intros; apply GlobalTheory.PrimRay.eq_of_toReal_eq_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh

theorem exists_comb_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} (hxx : x' = x) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk x' ⟶ Z.t.G))
    (hex : IsExpAt Z.t x' ex) (f : EigFrame Z σ x) (τ : E →+* ℂ) (δ : Fin (Dw.mult τ) → Fin g → ℂ)
    (hδ : ∀ b, IsDerivAt0 (fun z => (ex z).left) (δ b) (f.v τ b)) (v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left)
    (hv' : IsTanAtG Z.t x v') (heig : ∀ a, v' ≫ (Z.t.act.act a).left = spMap (epsMul (σ (embK c τ a))) ≫ v')
    (w : Fin g → ℂ) (hw : IsDerivAt0 (fun z => (ex z).left) w v') :
    ∃ a : Fin (Dw.mult τ) → ℂ, IsCombAtG Z.t x (f.v τ) a v' ∧ w = ∑ b, a b • δ b := by
  subst hxx
  obtain ⟨a, ha, -⟩ := f.basis τ v' hv' heig
  have e1 : ex 0 = 1 := by
    have h := hex.1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hd := GlobalTheory.ShFam.Hor.ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e1) (f.tan τ) hδ hv' ha
  obtain ⟨w', -, hu⟩ := hex.2.2 v' hv'
  exact ⟨a, ha, (hu w hw).trans (hu _ hd).symm⟩

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom)

theorem coords_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hg hU d u₀ R _ φR xR fR ev k G τ hev hG hφ hpt
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  choose Pm h1 h2 h3 h4 _ using hP
  obtain ⟨h₀, -⟩ := hpt.self_of_nhds
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let x : (Fin d → ℂ) → (U.X k).dom := fun b =>
    if h : G (L.symm b) ∈ (U.X k).dom then ⟨G (L.symm b), h⟩ else ⟨G u₀, h₀⟩
  have hxb : ∀ b (h : G (L.symm b) ∈ (U.X k).dom), x b = ⟨G (L.symm b), h⟩ := fun b h => dif_pos h
  let P : (Fin d → ℂ) → ((F.Di (ik k)).La →+ (Fin g → ℂ)) := fun b => Pm k (x b)
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x b))
  have hu : ∀ b, F.u (ik k) (P b) =
      p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun b => (h3 k (x b)).symm.trans (ptF_fst (U.un k (x b))).symm
  have hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ := fun b => ptF_snd (U.un k (x b))
  have hgood : ∀ᶠ u in 𝓝 u₀, G u ∈ (U.X k).dom ∧
      ∀ τ' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    (hpt.mono fun u hu => hu.1).and
      (eventually_all.2 fun τ' => eventually_all.2 fun a => eventually_all.2 fun b => hG τ' a b)
  obtain ⟨B₀, hB₀, hB₀o, hu₀⟩ := eventually_nhds_iff.1 hgood
  let B : Set (Fin d → ℂ) := L.symm ⁻¹' B₀
  have hBo : IsOpen B := hB₀o.preimage L.symm.continuous
  have hb₀ : L u₀ ∈ B := by
    show L.symm (L u₀) ∈ B₀
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hu₀
  have hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B := fun a => differentiableOn_pi.2 fun j =>
    (TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun b => G (L.symm b)) (fun b hb => (hB₀ _ hb).1)
      (fun τ' a' c' b hb => (((hB₀ _ hb).2 τ' a' c').comp b L.symm.differentiableAt).differentiableWithinAt)
      _ _ _).congr fun b hb => by
        show Pm k (x b) a j = _
        rw [h1, hxb b (hB₀ _ hb).1]
  let ev' : (Fin d → ℂ) → (R →+* ℂ) := fun b => ev (L.symm b)
  let Ex : (Fin d → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun b z =>
    liftEx Z F (p b) (ik k) (P b) (hu b) z ≫ Z.m.φ
  let Wd : Fin (Dw.mult τ) → (Fin d → ℂ) → Fin g → ℂ := fun i b =>
    if h : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) then h.choose else 0
  have core : ∀ b (h : G (L.symm b) ∈ (U.X k).dom),
      (cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z = spMap (ev (L.symm b)) ≫ xR →
      (ev (L.symm b)).comp φR = σ → ∀ i,
      IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) ∧
      IsCombAtG Z.t ((cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z)
        ((cxFrame Z (U.un k ⟨G (L.symm b), h⟩)).v τ) (fun a => Wd i b (e.symm ⟨τ, a⟩))
        (spMap (dualMap (ev (L.symm b))) ≫ fR.v τ i) := by
    intro b h hx hφb i
    rw [← hxb b h] at hx ⊢
    obtain ⟨gF, hgF⟩ := HolFrames.exists_bc fR (ev (L.symm b)) (φ' := σ) hφb.symm hx
    have hxp : p b ≫ Z.jQ ≫ genι Z = (cxPt Z (U.un k (x b))).1 ≫ genι Z := (Category.assoc _ _ _).symm
    have hExp := isExpAt_pushEx E H Dw l Xo c O β Z g _ _ F (p b) (ik k) (P b) _ (hu b) rfl (h2 k (x b))
    have hδ : ∀ a, IsDerivAt0 (fun z => (pushEx Z F (p b) (ik k) (P b) _ (hu b) rfl z).left)
        (Pi.single (e.symm ⟨τ, a⟩) 1) ((cxFrame Z (U.un k (x b))).v τ a) := by
      intro a
      obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v Z (U.un k (x b))
        (x := (cxPt Z (U.un k (x b))).1 ≫ genι Z) (Category.assoc _ _ _).symm τ a
      have hw0' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m0.toSABMap.φ = (U.un k (x b)).u τ a := hw0
      have hwm' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m.φ = (cxFrame Z (U.un k (x b))).v τ a := hwm
      have hd : IsDerivAt0 (fun z => (F.ex (ik k) (P b) z).left) (Pi.single (e.symm ⟨τ, a⟩) 1)
          (w ≫ Z.m0.toSABMap.φ) := by
        exact (congrArg (IsDerivAt0 _ _) hw0').mpr (h4 k (x b) τ a)
      have := isDerivAt0_comp_hom (isDerivAt0_liftEx Z F (p b) (ik k) (P b) (h2 k (x b)) (hu b) hwt.1 hd) Z.m.φ
      exact (congrArg (IsDerivAt0 _ _) hwm').mp this
    have ht : IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (gF.v τ i) := by
      rw [hxp]; exact gF.tan τ i
    have hex : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      obtain ⟨w, hw, -⟩ := hExp.2.2 _ ht
      exact ⟨w, (hgF τ i) ▸ hw⟩
    have hW : IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      have e0 : Wd i b = hex.choose := dif_pos hex
      rw [e0]
      exact hex.choose_spec
    refine ⟨hW, ?_⟩
    obtain ⟨a, ha, hwa⟩ := exists_comb_of_exp hxp _ hExp (cxFrame Z (U.un k (x b))) τ _ hδ (gF.v τ i)
      (gF.tan τ i) (gF.eig τ i) (Wd i b) ((hgF τ i).symm ▸ hW)
    have hfa : (fun a' => Wd i b (e.symm ⟨τ, a'⟩)) = a := by
      funext a'
      rw [hwa]
      have hi : ∀ j j' : Fin (Dw.mult τ), e.symm ⟨τ, j⟩ = e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
      simp [Finset.sum_apply, Pi.single_apply, hi]
    rw [hfa, ← hgF τ i]
    exact ha
  have ht : Tendsto L.symm (𝓝 (L u₀)) (𝓝 u₀) := by
    simpa using L.symm.continuous.tendsto (L u₀)
  refine ⟨fun u a i => Wd i (L u) (e.symm ⟨τ, a⟩), fun a i => ?_, ?_⟩
  · have hev'' : ∀ t, ∀ᶠ b in 𝓝 (L u₀), DifferentiableAt ℂ (fun b => ev' b t) b := fun t => by
      filter_upwards [ht.eventually (hev t)] with b hb
      exact hb.comp b L.symm.differentiableAt
    have hW : ∀ᶠ b in 𝓝 (L u₀), IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      filter_upwards [ht.eventually hpt, ht.eventually hφ] with b ⟨h, hx⟩ hφb
      exact (core b h hx hφb i).1
    have hd := eventually_differentiableAt_dir Z σ F (ik k) hBo hu (fun b => h2 k (x b)) hPd hs (fR.v τ i) ev' hb₀
      hev'' (Wd i) hW
    filter_upwards [(L.continuous.tendsto u₀).eventually hd] with u hu
    exact (differentiableAt_pi.1 hu (e.symm ⟨τ, a⟩)).comp u L.differentiableAt
  · filter_upwards [hpt, hφ] with u ⟨h, hx⟩ hφu
    refine ⟨h, fun i => ?_⟩
    have c := core (L u)
    rw [ContinuousLinearEquiv.symm_apply_apply] at c
    exact (c h hx hφu i).2

end GlobalTheory.HolCoordEv
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  first | exact @GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | exact GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | (intros; apply GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign.TopPos

open GlobalTheory.GoodMetric.LinSubst

variable {n : ℕ}

def pairForm (u v : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ p : Fin n × Fin n, C (u p.1 * starRingEnd ℂ (v p.2)) * X p

theorem topCoeff_prod_pairForm_fin (k : ℕ) :
    ∃ D : (Fin k → Fin n → ℂ) → ℂ, ∀ u v : Fin k → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  by_cases hk : k = n
  · subst hk
    refine ⟨fun u => (Matrix.of u).det, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, u i (c i) * starRingEnd ℂ (v i (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (Matrix.of u) i (c i)) * (rowSel c).det) *
        ((∏ i, ((Matrix.of v).map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [Matrix.of_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, RingHom.map_det]
    rfl
  · refine ⟨fun _ => 0, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    simp [topCoeff_prod_X_of_ne hk]

theorem topCoeff_prod_pairForm (J : Type) [Fintype J] :
    ∃ D : (J → Fin n → ℂ) → ℂ, ∀ u v : J → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm_fin (n := n) (Fintype.card J)
  let e := (Fintype.equivFin J).symm
  refine ⟨fun u => D (u ∘ e), fun u v => ?_⟩
  rw [← hD, ← e.prod_comp]
  rfl

theorem factorial_mul_det {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (m.factorial : R) * M.det = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) := by
  rw [Finset.sum_comm]
  have h (τ : Equiv.Perm (Fin m)) : ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    have h2 : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : R) * ∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, (M.submatrix id τ) (σ i) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [Matrix.submatrix_apply, id]
          ring
      _ = M.det := by rw [h1, ← mul_assoc, h2, one_mul]
  simp_rw [h]
  simp [Fintype.card_perm]

theorem sqPoly_apply {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (i j : Fin m) :
    sqPoly T i j = ∑ k, pairForm (fun a => T (coordVec a) i k) (fun a => T (coordVec a) j k) := by

  simp only [sqPoly, pairForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
  Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (γ := Fin r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (γ := Fin r)]
  rfl

theorem factorial_mul_det_sqPoly {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    C (m.factorial : ℂ) * (sqPoly T).det = ∑ k : Fin m → Fin r, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      C (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ i, pairForm (fun a => T (coordVec a) (σ i) (k i)) (fun a => T (coordVec a) (τ i) (k i)) := by
  rw [map_natCast, factorial_mul_det]
  simp_rw [sqPoly_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  simp only [map_mul, map_intCast]

theorem topCoeff_prod_det_nonneg {B : Type} [Fintype B] (m r : B → ℕ)
    (T : ∀ b, V n →ₗ[ℂ] Matrix (Fin (m b)) (Fin (r b)) ℂ) :
    0 ≤ topCoeff (∏ b, (sqPoly (T b)).det) := by
  classical
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm (n := n) (Σ b, Fin (m b))
  have h : (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) =
      ∑ k : ∀ b, Fin (m b) → Fin (r b),
        (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) *
        starRingEnd ℂ (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) := by
    rw [← topCoeff_C_mul, map_prod, ← Finset.prod_mul_distrib]
    simp_rw [factorial_mul_det_sqPoly]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, ← Fintype.prod_sigma', hD, Finset.prod_mul_distrib]
    simp only [map_mul, map_prod, map_intCast]
    ring
  have h0 : 0 ≤ (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) := by
    rw [h]
    exact Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hN : (0 : ℝ) < ∏ b, ((m b).factorial : ℝ) :=
    Finset.prod_pos fun b _ => by exact_mod_cast Nat.factorial_pos _
  have e : (∏ b, ((m b).factorial : ℂ)) = ((∏ b, ((m b).factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e] at h0
  have h1 : (0 : ℂ) ≤ (((∏ b, ((m b).factorial : ℝ))⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hN.le)
  have h2 := mul_nonneg h1 h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne', Complex.ofReal_one, one_mul] at h2

end GlobalTheory.PointFormSign.TopPos

theorem GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ)
    (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ) :
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  have h := TopPos.topCoeff_prod_det_nonneg (B := Σ t, Fin (e t)) (fun b => m b.1) (fun b => r b.1) fun b => T b.1
  rw [Fintype.prod_sigma] at h
  refine h.trans_eq (congrArg topCoeff (Finset.prod_congr rfl fun t _ => ?_))
  exact (Finset.prod_const (s := Finset.univ) (sqPoly (T t)).det).trans (by rw [Finset.card_univ, Fintype.card_fin])
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem _root_.GlobalTheory.T.exists_continuous_lattice_vectors_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsArc Z σ φ x ψ r → ∃ (ρ : ℝ) (n : ℕ) (lam : Fin n → ℂ → (Fin g → ℂ)), 0 < ρ ∧ ρ ≤ r ∧ (∀ j, ContinuousOn (lam j) (Metric.ball 0 ρ)) ∧ Submodule.span ℂ (Set.range fun j => lam j 0) = ⊤ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z w, ex (z + w) = ex z * ex w) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ j, ex (lam j u) = 1 := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_lattice_sections | exact GlobalTheory.ShFam.BdArc.exists_lattice_sections | (intros; apply GlobalTheory.ShFam.BdArc.exists_lattice_sections <;> assumption)
end
