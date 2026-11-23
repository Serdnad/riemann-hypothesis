module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle004
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ} {f g : CxPts p σ → ℝ}

def levi (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) : ℝ :=
  (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

def dtrans (y : CxPts p σ) (ξ : Fin D → ℂ) : Fin D → ℂ :=
  fun b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (WithLp.toLp 2 ξ) b

variable {c c'}

theorem levi_congr (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S) (h : ∀ z ∈ S, f z = g z)
    (ξ : Fin D → ℂ) : c.levi f y ξ = c.levi g y ξ :=
  congrArg Complex.re (leviV_congr (eventually_of_mem
    ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      congrArg Complex.ofReal (h _ hv.2)) ξ)

theorem levi_add (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (hg : ContDiffAt ℝ 2 (g ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => f z + g z) y ξ = c.levi f y ξ + c.levi g y ξ :=
  (congrArg Complex.re (flA_leviV_add hf hg ξ)).trans (Complex.add_re _ _)

theorem levi_const_mul (a : ℝ) (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => a * f z) y ξ = a * c.levi f y ξ :=
  (congrArg Complex.re (LocalMaximumSecondDerivative.leviV_ofReal_const_mul a hf ξ)).trans (Complex.re_ofReal_mul _ _)

theorem levi_log_normSq {u : CxPts p σ → ℂ} (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S)
    (hu : DifferentiableOn ℂ (u ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (h0 : u y ≠ 0)
    (ξ : Fin D → ℂ) : c.levi (fun z => Real.log (‖u z‖ ^ 2)) y ξ = 0 :=
  congrArg Complex.re (flA_leviV_log_normSq (h := u ∘ c.e.symm)
    (eventually_of_mem ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      hu.differentiableAt ((isOpen_over c.e hS).mem_nhds hv))
    (by rwa [Function.comp_apply, c.e.left_inv hy]) ξ)

theorem levi_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y)) (ξ : Fin D → ℂ) :
    c.levi f y ξ = c'.levi f y (c.dtrans c' y ξ) := by
  have ho := isOpen_over c.e c'.e.open_source
  have hn := ho.mem_nhds (mem_over c.e hy hy')
  have ht : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    (((contDiffOn_piLp 2).2 fun a => contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hU : ContDiffAt ℝ 2 (fun v => (f (c'.e.symm v) : ℂ)) ((c'.e ∘ c.e.symm) (c.e y)) :=
    e ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have := flA_leviV_comp hU ht ξ
  rw [e] at this
  refine congrArg Complex.re (Eq.trans (leviV_congr (eventually_of_mem hn fun v hv => ?_) ξ) this)
  simp only [Function.comp_apply, c'.e.left_inv hv.2]

theorem dtrans_ne_zero (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {ξ : Fin D → ℂ}
    (hξ : ξ ≠ 0) : c.dtrans c' y ξ ≠ 0 := fun h => by
  have hd : transDet c.e c'.e y ≠ 0 := rv_chart c c' hy hy' ▸
    rv_ne_zero _ _ (c.source_subset hy) (c'.source_subset hy')
  have hi := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  have := LinearMap.ker_eq_bot'.1 hi (WithLp.toLp 2 ξ) (PiLp.ext fun b => congrFun h b)
  exact hξ (congrArg WithLp.ofLp this)

end AlgChart

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)} {y : CxPts p σ}

theorem SmoothOn.contDiffAt_two {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    {c : AlgChart p σ D} (hy : y ∈ c.e.source) (hyS : y ∈ S) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) :=
  ((h.chart hS c).contDiffAt ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS))).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_eq_of_add_log {f g : CxPts p σ → ℝ} {u : CxPts p σ → ℂ} (hS : IsOpen S)
    (hf : R.SmoothOn S f) (hu : R.HoloOn S u) (h0 : ∀ z ∈ S, u z ≠ 0)
    (h : ∀ z ∈ S, g z = f z + Real.log (‖u z‖ ^ 2)) {c : AlgChart p σ D} (hy : y ∈ c.e.source)
    (hyS : y ∈ S) (ξ : Fin D → ℂ) : c.levi g y ξ = c.levi f y ξ := by
  rw [AlgChart.levi_congr hS hy hyS h, AlgChart.levi_add (hf.contDiffAt_two hS hy hyS)
    ((hu.smoothOn_log hS h0).contDiffAt_two hS hy hyS),
    AlgChart.levi_log_normSq hS hy hyS (hu.chart hS c) (h0 y hyS), add_zero]

end AnRead

namespace Weight

open AnRead

variable {R R' : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B} {ψ : Weight p σ A}
  {c : AlgChart p σ D} {y : CxPts p σ}

theorem IsSmooth.contDiffAt_two (h : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : ContDiffAt ℝ 2 (φ.φ i ∘ c.e.symm) (c.e y) :=
  (h i).contDiffAt_two (isOpen_ptsIn _) hy hi

theorem IsSmooth.levi_frame (h : φ.IsSmooth R) {i j : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) (ξ : Fin D → ℂ) :
    c.levi (φ.φ i) y ξ = c.levi (φ.φ j) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (B.U i)).inter (isOpen_ptsIn (B.U j)))
    ((h j).mono inter_subset_right) (u := gv p σ B i j)
    (holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2) (fun _ hz => gv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [φ.trans i j z hz.1 hz.2, sub_add_cancel]) hy ⟨hi, hj⟩ ξ

theorem IsSmooth.strictPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, ξ ≠ 0 → 0 < c.levi (φ.φ i) y ξ) : φ.StrictPos R := fun j c' y hy ξ hξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _ (AlgChart.dtrans_ne_zero hy.1 hc hξ)).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem levi_tens (hψ : ψ.IsSmooth R) (hφ : φ.IsSmooth R) {i : (CechPic.tens A B).ι}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ ((CechPic.tens A B).U i)) (ξ : Fin D → ℂ) :
    c.levi ((ψ.tens φ).φ i) y ξ = c.levi (ψ.φ i.1) y ξ + c.levi (φ.φ i.2) y ξ :=
  AlgChart.levi_add (hψ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).1)
    (hφ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).2) ξ

theorem levi_zpow (hφ : φ.IsSmooth R) (n : ℤ) {j : PUnit → B.ι} (hy : y ∈ c.e.source)
    (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) (ξ : Fin D → ℂ) :
    c.levi ((φ.zpow n).φ j) y ξ = n * c.levi (φ.φ (j PUnit.unit)) y ξ := by
  rw [funext (φ.zpow_φ n j)]
  exact AlgChart.levi_const_mul _ (hφ.contDiffAt_two hy hj) ξ

theorem SemiPos.tens (h' : ψ.SemiPos R) (h : φ.SemiPos R) (hψ : ψ.IsSmooth R)
    (hφ : φ.IsSmooth R) : (ψ.tens φ).SemiPos R := fun i c y hy ξ =>
  (add_nonneg (h' _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).1⟩ ξ)
    (h _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).2⟩ ξ)).trans_eq (levi_tens hψ hφ hy.1 hy.2 ξ).symm

theorem SemiPos.zpow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 ≤ n) :
    (φ.zpow n).SemiPos R := fun j c y hy ξ =>
  (mul_nonneg (Int.cast_nonneg hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem SemiPos.pow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (n : ℕ) : (φ.pow n).SemiPos R :=
  h.zpow hφ (Int.natCast_nonneg n)

theorem semiPos_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).SemiPos R := fun i c y hy ξ => by
  have ho := isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hc (a) : ContDiffAt ℂ 2 (e a i ∘ (R.chart c).e.symm) ((R.chart c).e y) :=
    ((contDiffOn_of_differentiableOn D _ _ ho ((he a).2 i c)).contDiffAt
      (ho.mem_nhds (mem_over _ hy.1 hy.2))).of_le (WithTop.coe_le_coe.2 le_top)
  have hs (v) : ∑ j, Complex.normSq ((e ((Fintype.equivFin α).symm j) i ∘ (R.chart c).e.symm) v) =
      ∑ a, ‖e a i ((R.chart c).e.symm v)‖ ^ 2 :=
    Fintype.sum_equiv (Fintype.equivFin α).symm _ _ fun _ => Complex.normSq_eq_norm_sq _
  have := leviV_log_sum_nonneg (fun j => contDiffAt_normSq_comp (hc ((Fintype.equivFin α).symm j)))
    (fun j => logPshAt_normSq (hc _))
    (by rw [hs, (R.chart c).e.left_inv hy.1]; exact h.sum_pos hy.2) ξ
  simp only [hs] at this
  exact this

end Weight

namespace WeightFamily.Reading

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} [Fintype κ] [DecidableEq κ]
  [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] {F : WeightFamily R κ} {B : LB Y}
  {m : Option κ → ℤ} {r : F.Reading B m} {φ : Weight p σ B}

end WeightFamily.Reading

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

def Sys.cocyclesInIdealExtensions {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : Submodule R (Z1 S.F) where
  carrier := {z | S.IsIdealValuedLiftSystemCocycle z}
  add_mem' {a b} ha hb U V f := by
    change a.1 U V f + b.1 U V f ∈ _
    exact Ideal.add_mem _ (ha U V f) (hb U V f)
  zero_mem' U V f := Ideal.zero_mem _
  smul_mem' r z hz U V f := by
    change r • z.1 U V f ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hz U V f)

theorem exists_sys_of_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hR S' hF hN K hN' hsup
  obtain ⟨N, hN⟩ := hN

  have lin := GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) K N hN hsup
  obtain ⟨hKinf, u, hu, hu0, hall⟩ := lin.2 hN'
  have hKN : IsCompl K N := lin.1 hKinf
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀

  have fadd : ∀ (c1 c2 : Cr hI π s₀) (w1 w2 : GlobForm s₀), FormOf hI hk c1 w1 → FormOf hI hk c2 w2 → FormOf hI hk (c1 + c2) (w1 + w2) := by
    rintro c1 c2 w1 w2 ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    exact ⟨f1 + f2, by rw [map_add (f := _), map_add (f := _), h1, h2], by rw [map_add (f := _), Submodule.coe_add, e1, e2]⟩
  have fsmul : ∀ (r : R) (c : Cr hI π s₀) (w : GlobForm s₀), FormOf hI hk c w → FormOf hI hk (r • c) (π r • w) := by
    rintro r c w ⟨f, h, e⟩
    exact ⟨π r • f, by rw [map_smul, h, map_smulₛₗ], by rw [map_smul, Submodule.coe_smul, e]⟩
  have fzero : FormOf hI hk (0 : Cr hI π s₀) 0 := ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; rfl⟩
  have hwd : ∀ (c1 c2 : S'.K hI) (w : GlobForm s₀), FormOf hI hk c1.1 w → FormOf hI hk c2.1 w → u c1 = u c2 := by
    rintro c1 c2 w ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    have hz : cmpForm s₀ (f1 - f2) = 0 := Subtype.ext (by rw [map_sub, Submodule.coe_sub, e1, e2, sub_self]; rfl)
    have hcl := (hG.inj _).2 hz
    rw [map_sub, h1, h2, ← map_sub] at hcl
    have hm := (hR.2 _).1 hcl
    have := hu0 (c1 - c2) (by rw [Submodule.coe_sub]; exact hm)
    rwa [map_sub, sub_eq_zero] at this
  have hex : ∀ c ∈ S'.K hI, ∃ w : GlobForm s₀, FormOf hI hk c w := by
    intro c hc
    have h1 := (ksup S' hR hF c).1 (Submodule.mem_sup_left hc)
    rw [hodgeFiltration_eq_range] at h1
    obtain ⟨f, hf⟩ := h1
    exact ⟨(cmpForm s₀ f).1, f, hf, rfl⟩
  have hexF : ∀ w : GlobForm s₀, ∃ c : S'.K hI, FormOf hI hk c.1 w := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c0, hc0⟩ := hR.1 (Form.cl s₀ f)
    have hm : c0 ∈ S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (ksup S' hR hF c0).2 (by rw [hc0, hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨⟨k, hk'⟩, f, ?_, hf⟩
    rw [← hc0, map_add (f := _), (hR.2 i).2 hi, add_zero]
  choose cw hcw using hexF

  let v : GlobForm s₀ →+ CatCoh.H1 S'.F :=
    { toFun := fun w ↦ -S'.r hI (u (cw w))
      map_zero' := by
        rw [hwd (cw 0) 0 0 (hcw 0) fzero, map_zero, map_zero, neg_zero]
      map_add' := fun a b ↦ by
        rw [hwd (cw (a + b)) (cw a + cw b) (a + b) (hcw _) (fadd _ _ _ _ (hcw a) (hcw b)), map_add (f := _), map_add (f := _),
          neg_add] }
  have hvdef : ∀ w, v w = -S'.r hI (u (cw w)) := fun _ ↦ rfl
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    rw [hvdef, hvdef, hwd (cw (π r • w)) (r • cw w) _ (hcw _) (fsmul r _ _ (hcw w)), map_smul, map_smul, smul_neg]
  have hW : ∀ r, π r = 0 → ∀ m ∈ S'.cocyclesInIdealExtensions, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := by rw [← hk]; exact hr
    apply Subtype.ext
    funext U V a
    change r • m.1 U V a = 0
    rw [Algebra.smul_def]
    have := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj V)) hrI) (hm U V a)
    rw [← sq, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  have trans' := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀
  have hq : ∀ w, ∃ m ∈ S'.cocyclesInIdealExtensions, CatCoh.H1.mk S'.F m = v w := by
    intro w
    obtain ⟨z, z', hz, hmk, -, -⟩ := (trans' S' S' (Sys.LocIso.refl S')).2.2 (-(u (cw w))) (neg_mem (hu (cw w)).1)
    exact ⟨z, hz, by rw [hmk, map_neg]; rfl⟩
  obtain ⟨u', hu's, hu'W, hu'q⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj (Z1 S'.F)
    (CatCoh.H1 S'.F) S'.cocyclesInIdealExtensions hW (CatCoh.H1.mk S'.F) v hv hq
  obtain ⟨S'', Φ, θ, hdef, hθ⟩ := GlobalTheory.T.exists_twist_squareZeroSmoothLiftSystem_by_derivationCocycle R R₀ I hI π hπ hk X₀ s₀ hG.par S' u' hu'W hu's

  have hle : K ≤ S''.K hI := by
    intro k hk'
    obtain ⟨c, rfl⟩ := hall k hk'
    obtain ⟨w, hw⟩ := hex c.1 c.2
    obtain ⟨zw, -, hzw⟩ := (trans' S' S'' Φ).1 (u' w) (hu'W w)
    have hmain := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S' S'' Φ θ hdef c.1 c.2 w hw zw
      (fun U V a ↦ (hzw U V a).trans (hθ w U V a).symm)
    obtain ⟨z, z2, hzI, hz1, hz2, hzz⟩ := (trans' S' S'' Φ).2.2 (u c) (hu c).1
    have heq : u c = u (cw w) := hwd c (cw w) w hw (hcw w)
    have hsum : CatCoh.H1.mk S'.F (z + u' w) = 0 := by
      rw [map_add (f := _), hz1, hu'q w, hvdef, heq, add_neg_cancel]
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (z + u' w)
      (S'.cocyclesInIdealExtensions.add_mem hzI (hu'W w)) hsum
    have h2 : CatCoh.H1.mk S''.F (z2 + zw) = 0 := by
      refine CatCoh.H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
      funext U V a
      rw [(trans' S' S'' Φ).2.1 g hgI U V a, hg]
      change Φ.φ V (z.1 U V a + (u' w).1 U V a) = z2.1 U V a + zw.1 U V a
      rw [map_add (f := _), hzz, hzw]
    rw [map_add (f := _)] at h2
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [Sys.K, LinearMap.mem_ker, map_sub, hmain, ← hz2, h3, sub_neg_eq_add, neg_add_cancel]

  have kinf := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const
  have hF'' : S''.Full hI := (kinf S' S'').2 hF
  have hsup'' : S''.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • ⊤ := by
    ext c
    rw [ksup S'' hR hF'' c, ksup S' hR hF c]
  have hS''N : IsCompl (S''.K hI) N :=
    (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S''.K hI) N hN hsup'').1 ((kinf S'' S').1)
  refine ⟨S'', le_antisymm ?_ hle⟩
  calc S''.K hI = (K ⊔ N) ⊓ S''.K hI := by rw [hKN.sup_eq_top, top_inf_eq]
    _ = K ⊔ N ⊓ S''.K hI := sup_inf_assoc_of_le N hle
    _ = K := by rw [inf_comm, hS''N.inf_eq_bot, sup_bot_eq]
    _ ≤ K := le_rfl

end GlobalTheory.LiftSys
end
end

section

open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMink

theorem sum_embeddings_eq_two_mul {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (g : (K →+* ℂ) → ℝ) (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ : K →+* ℂ, g σ = 2 * ∑ v : InfinitePlace K, g v.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [this, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
  norm_num

theorem slopeMax_sq_le_of_no_short : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ →
    (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) →
    slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) +
      Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  intro K V _ _ _ _ _ _ _ N L La hG hconj hfg h0 hshort
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hX⟩ := hG.some
  rw [(slopeMax_slopeMin_eq hX hfg h0).1]
  have hXu : ∀ v, IsUnit (X v).det := fun v => (hX v).1
  have hnf : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hmink := Formalism.ExtensionFiltration.muMaxMinkowski K V (Fin n) b X hXu L La hfg h0 (by
    intro x hx hx0
    have h1 := hshort x hx hx0
    rw [sum_embeddings_eq_two_mul (fun σ => Real.log (N σ x)) (fun σ => by simp only [hconj])] at h1
    have e : ∀ v : InfinitePlace K, Real.log (N v.embedding x) = Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) :=
      fun v => by rw [(hX v).2 x]
    simp only [e] at h1
    rw [hnf] at h1
    push_cast at h1
    have : (2 * ∑ v : InfinitePlace K, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) / (2 * (Formalism.HN.nPl K : ℝ)) =
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
      field_simp
    linarith)
  haveI : Module.Finite K V := Module.Finite.of_basis b
  have hj : 0 < Formalism.HN.rkK L := by
    have h : Submodule.span K (L : Set V) ≠ ⊥ := by
      intro h
      apply h0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
  have hle : (Formalism.HN.rkK L : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast Submodule.finrank_le _
  have hlog : Real.log (Formalism.HN.rkK L : ℝ) ≤ Real.log (Module.finrank K V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hj) hle
  have hd : Formalism.HN.logDisc K = Real.log |(discr K : ℝ)| := rfl
  rw [hd] at hmink
  linarith

end GlobalTheory.SlopeMink
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X'), L'.IsLB → ∀ x : X, (∀ z : Z, i z ≠ x) → ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ), x ∈ W ∧ i ⁻¹ᵁ W = ⊥ ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' := by
  first | exact @GlobalTheory.PinchLift.exists_gen_away_of_closed | exact GlobalTheory.PinchLift.exists_gen_away_of_closed | (intros; apply GlobalTheory.PinchLift.exists_gen_away_of_closed <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  first | exact @GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | exact GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | (intros; apply GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange <;> assumption)
end
