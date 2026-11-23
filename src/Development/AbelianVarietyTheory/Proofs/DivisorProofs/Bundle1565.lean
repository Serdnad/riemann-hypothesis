module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem max_principle_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  classical
  choose W ρ hW hρ H using GlobalTheory.T.exists_nhds_nu_le_exp_mul_of_far_bound k X p D hX P s hs hs0 δ hδ
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), (Set.univ : Set (CxPts p σ)) ⊆ ⋃ x ∈ t, W σ x := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (W σ) (fun x _ => hW σ x)
    exact ⟨t, ht⟩
  choose t ht using hcov
  have hlow : ∀ {ι : Type} [Finite ι] (g : ι → ℝ), (∀ i, 0 < g i) → ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ g i := by
    intro ι _ g hg
    rcases isEmpty_or_nonempty ι with h | h
    · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min g
      exact ⟨g i, hg i, hi⟩
  obtain ⟨c, hc, hcle⟩ := hlow (ι := Σ σ : k →+* ℂ, {x // x ∈ t σ}) (fun z => ρ z.1 z.2.1) (fun z => hρ _ _)
  refine ⟨c, hc, fun N f R hf hR => ⟨hf, fun σ y => ?_⟩⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht σ (Set.mem_univ y))
  exact H σ x N f R hf (fun σ' y' h => hR σ' y' ((hcle ⟨σ, ⟨x, hx⟩⟩).trans h)) y hy

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  first | exact @GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | exact GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | (intros; apply GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.HolDict.holShape_of_good | exact GlobalTheory.HolDict.holShape_of_good | (intros; apply GlobalTheory.HolDict.holShape_of_good <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (m : ℕ), Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  first | (exact @GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (exact GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (intros; apply GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.pointSum_comp_mulEquiv) | (exact GlobalTheory.pointSum_comp_mulEquiv) | (intros; apply GlobalTheory.pointSum_comp_mulEquiv  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.darbouxChange_realised_comp_and_reindex : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' := by
  first | exact @GlobalTheory.TowU.RealComp.realised_comp_reix | exact GlobalTheory.TowU.RealComp.realised_comp_reix | (intros; apply GlobalTheory.TowU.RealComp.realised_comp_reix <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem isTopForm_hasInt_finset_sum {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n))
    (he : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (hc : ∀ y, ∃ i, y ∈ (e i).source) {S : Set Y} (hS : MeasurableSet S) {ι : Type}
    {d : ι → κ → Y → ℝ} {t : ι → ℝ} (hd : ∀ a, IsTopForm e (d a) S) (ht : ∀ a, HasInt e (d a) S (t a))
    (s : Finset ι) :
    IsTopForm e (fun i y => ∑ a ∈ s, d a i y) S ∧ HasInt e (fun i y => ∑ a ∈ s, d a i y) S (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨fun _ _ _ _ _ _ => by simp, fun _ => aemeasurable_const⟩, GlobalTheory.T.hasTopFormChartIntegral_zero e S⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    obtain ⟨hF, hI⟩ := ih
    refine ⟨⟨fun i j y hy hi hj => ?_, fun i => ((hd a).meas i).add (hF.meas i)⟩,
      GlobalTheory.T.topFormIntegral_add e he hc hS (hd a) hF (ht a) hI⟩
    rw [(hd a).trans i j y hy hi hj, hF.trans i j y hy hi hj]
    ring

theorem hasInt_sum : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι]
    {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) →
    HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  intro n Y κ _ _ _ _ e he hc S hS ι _ d t hd ht
  exact (isTopForm_hasInt_finset_sum e he hc hS hd ht Finset.univ).2

end GlobalTheory.GoodTop
end
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem exists_goodPatch_of_mem : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hH y hy
  classical
  obtain ⟨ch, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (p := X.str) (σ := σ) y
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  have hhol : IsHoloChart ch.e := ch.holo
  obtain ⟨hsm, hu⟩ := GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hhol hy hc hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun v => H A (ch.e.symm v) () with hG
  have h1 : ((0 : WithTop ℕ∞) + 1) ≤ ∞ := by exact_mod_cast le_top
  have h2 : ((0 : WithTop ℕ∞) + 2) ≤ ∞ := by
    rw [zero_add]
    first
    | exact (WithTop.coe_le_coe (a := (2 : ℕ∞)) (b := ⊤)).2 le_top
    | exact ENat.LEInfty.out
    | simp
    | decide
  have hconn : ∀ (a : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => conn G (ch.e z) (coordVec a) i j) y := fun a i j =>
    ((hsm.conn hu h1 (coordVec a)) i j).continuousAt.comp (ch.e.continuousAt hc)
  have hcurv : ∀ (a b : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => curv G (ch.e z) (coordVec a) (coordVec b) i j) y := fun a b i j =>
    ((hsm.curv hu h2 (coordVec a) (coordVec b)) i j).continuousAt.comp (ch.e.continuousAt hc)
  let C : ℝ := (∑ a : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1)) +
    ∑ a : Fin X.dim, ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m,
      (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
  have hP1 : ∀ a i j, ‖conn G (ch.e y) (coordVec a) i j‖ + 1 ≤ C := by
    intro a i j
    refine le_add_of_le_of_nonneg ?_ (by positivity)
    refine (Finset.single_le_sum (f := fun j => ‖conn G (ch.e y) (coordVec a) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have hP2 : ∀ a b i j, ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1 ≤ C := by
    intro a b i j
    refine le_add_of_nonneg_of_le (by positivity) ?_
    refine (Finset.single_le_sum (f := fun j => ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    refine (Finset.single_le_sum (f := fun b => ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  let T : Set (CxPts X.str σ) := {z | z ∈ ch.e.source ∧ z ∈ ptsIn X.str σ O ∧ A ∈ E.S (under z) ∧
    (∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C) ∧
    (∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C)}
  have hT : T ∈ 𝓝 y := by
    have e1 : ∀ᶠ z in 𝓝 y, ∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a i j
      filter_upwards [(hconn a i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP1 a i j]))
    have e2 : ∀ᶠ z in 𝓝 y, ∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a b i j
      filter_upwards [(hcurv a b i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP2 a b i j]))
    filter_upwards [ch.e.open_source.mem_nhds hc, (isOpen_ptsIn (p := X.str) (σ := σ) O).mem_nhds hy,
      GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA, e1, e2] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨ch.e, ∅, A, interior T, C, mem_interior_iff_mem_nhds.2 hT, ?_⟩
  have hsub : ∀ z ∈ interior T, z ∈ T := fun z hz => interior_subset hz
  refine ⟨hhol, isOpen_interior, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.2.1,
    fun z _ a ha => absurd ha (Finset.notMem_empty a), fun z hz => ?_, fun z hz _ a i j => ?_,
    fun z hz _ a b i j => ?_⟩
  · simp only [Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact (hsub z hz).2.1
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.1 a i j
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.2 a b i j

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_poincareGoodPatch_outside_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch | exact GlobalTheory.GoodTop.exists_goodPatch | (intros; apply GlobalTheory.GoodTop.exists_goodPatch <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | exact GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_mixTop_le_of_weighted <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  first | exact @GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | exact GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | (intros; apply GlobalTheory.GoodTop.mixTop_curvAt_comp_holo <;> assumption)
end
