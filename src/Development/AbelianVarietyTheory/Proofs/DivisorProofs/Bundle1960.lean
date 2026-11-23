module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle299
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle028
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open Function

namespace GlobalTheory.FlagCell2.ChangeOfVariables

theorem part_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  intro M _ _ _ _ _ n A β hβ Ω Φ γ hΩ hinj hloc s T hT hTΩ
  set ρ : A.ι → M → ℝ≥0∞ := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring

  have chart : ∀ (i : A.ι) (P : Set M), MeasurableSet P → P ⊆ (A.e i).source → P ⊆ Ω →
      MeasurableSet (Φ '' P) ∧ A.part β s P =
        ∫⁻ v in Φ '' P, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
    intro i P hP hPs hPΩ
    set g : V n → V n := Φ ∘ (A.e i).symm with hg
    have hQ : MeasurableSet (A.e i '' P) := ChartGlue.measurableSet_image (A.e i) hP hPs
    have hder : ∀ v ∈ A.e i '' P, HasFDerivWithinAt g ((fderiv ℂ g v).restrictScalars ℝ) (A.e i '' P) v := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)).1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjg : Set.InjOn g (A.e i '' P) := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy), (A.e i).left_inv (hPs hz)] at hyz
      rw [hinj (hPΩ hy) (hPΩ hz) hyz]
    have himg : Φ '' P = g '' (A.e i '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    refine ⟨himg ▸ measurable_image_of_fderivWithin hQ hder hinjg, ?_⟩
    rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hP hPs, ChartGlue.chartMeas_apply_of_subset _ _ hP hPs, himg,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hQ hder hinjg]
    refine setLIntegral_congr_fun hQ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hx := hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)
    have hl := A.loc_crd β (⟨(i, y), hPs hy⟩ : A.Pt)
    have hdet : ((fderiv ℂ g (A.e i y)).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ g (A.e i y)).det :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ g (A.e i y) : V n →ₗ[ℂ] V n))
    have hx2 : β ⟨(i, y), hPs hy⟩ = pull (fderiv ℂ g (A.e i y)) (γ (Φ y)) := hx.2
    have hgy : g (A.e i y) = Φ y := by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    beta_reduce
    rw [hdet, hgy]
    simp only [hρ, (A.e i).left_inv (hPs hy)]
    erw [hl, hx2, dens_pull]
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

  rcases Set.eq_empty_or_nonempty T with rfl | ⟨y₀, -⟩
  · simp
  obtain ⟨C, hCc, hCU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun j => (A.e j).source)
    (fun j => (A.e j).open_source)
  obtain ⟨f, hf⟩ := (hCc.insert (A.cover y₀).choose).exists_eq_range (Set.insert_nonempty _ _)
  set U : ℕ → Set M := fun k => (A.e (f k)).source with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => (A.e (f k)).open_source
  set P : ℕ → Set M := fun k => T ∩ disjointed U k with hPdef
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    hT.inter (MeasurableSet.disjointed (fun k => (hUo k).measurableSet) k)
  have hPU : ∀ k, P k ⊆ U k := fun k => Set.inter_subset_right.trans (disjointed_subset U k)
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => Set.inter_subset_left.trans hTΩ
  have hPd : Pairwise (Disjoint on P) := (disjoint_disjointed U).mono fun k l h =>
    h.mono Set.inter_subset_right Set.inter_subset_right
  have hTP : T = ⋃ k, P k := by
    rw [← Set.inter_iUnion, iUnion_disjointed, eq_comm, Set.inter_eq_left]
    intro y _
    have hy : y ∈ ⋃ j, (A.e j).source := Set.mem_iUnion.2 (A.cover y)
    rw [← hCU] at hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨k, rfl⟩ := hf.le (Set.mem_insert_of_mem _ hl)
    exact Set.mem_iUnion.2 ⟨k, hy⟩
  have hIm : ∀ k, MeasurableSet (Φ '' P k) := fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).1
  have hId : Pairwise (Disjoint on fun k => Φ '' P k) := by
    intro k l hkl
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj (hPΩ l hy) (hPΩ k hx) hxy
    subst this
    exact Set.disjoint_left.1 (hPd hkl) hx hy
  rw [hTP, Set.image_iUnion, measure_iUnion hPd hPm, lintegral_iUnion hIm hId]
  exact tsum_congr fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).2

end GlobalTheory.FlagCell2.ChangeOfVariables
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.WeylPacket

theorem det_rev_pow_eq_vdm {r : ℕ} (a : Fin r → ℂ) :
    (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)).det = Formalism.PacketSums.vdm a := by
  have h2 : (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)) =
      (Matrix.vandermonde (a ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [Matrix.vandermonde_apply, Fin.rev_rev]
  have key : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.Ioi i, f i j = ∏ i, ∏ j, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have key2 : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j = ∏ i, ∏ j, if i < j then f i j else 1 :=
    fun f => Finset.prod_congr rfl fun i _ => Finset.prod_filter _ _
  rw [h2, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, Formalism.PacketSums.vdm, key, key2, Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp [Fin.rev_lt_rev]

theorem det_zpow_eq_sum {r : ℕ} (a : Fin r → ℂ) (m : Fin r → ℤ) :
    (Matrix.of fun i j : Fin r => a i ^ m j).det =
      ∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, a i ^ m (w⁻¹ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact Fintype.prod_equiv w _ _ fun i => by simp

end GlobalTheory.WeylPacket


open GlobalTheory.WeylPacket in
theorem GlobalTheory.dsChar_finsum_eq_glChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  intro n ε lam α ι _ y θ hn hα hb hθ
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := id hn
  set m : Fin n → ℤ := fun a => lam a + (((n - 1) / 2 : ℕ) : ℤ) with hmdef
  have hk2 : (n - 1) / 2 = k := by omega
  have hm : ∀ a, ((fun a => (lam a : ℝ)) a) + ((n : ℝ) - 1) / 2 = (m a : ℝ) := by
    intro a
    have hn' : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    simp only [hmdef, hk2, hn']
    push_cast
    ring
  let WK : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {w | ε ∘ w = ε}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        funext x
        have ha' := congrFun ha (b x)
        have hb' := congrFun hb x
        simp only [Function.comp_apply] at ha' hb' ⊢
        rw [Equiv.Perm.mul_apply, ha', hb']
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        funext x
        have := congrFun ha (a⁻¹ x)
        simp only [Function.comp_apply] at this ⊢
        rw [show a (a⁻¹ x) = x from by simp] at this
        exact this.symm }
  haveI : Fintype WK := Fintype.ofFinite _
  have hmem : ∀ w, w ∈ WK ↔ w ∈ compactWeyl ε := by
    intro w
    show ε ∘ w = ε ↔ _
    simp [compactWeyl]
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ compactWeyl ε := by simp [compactWeyl]
  have hy : Function.Injective y := by
    intro q q' h
    have := hb.1 (a₁ := (⟨1, h1⟩, q)) (a₂ := (⟨1, h1⟩, q')) (by simp [h])
    exact congrArg Prod.snd this
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i
    obtain ⟨⟨w, q⟩, -⟩ := hb.2 1
    have := hθ q (y q i)
    rw [show (y q)⁻¹ (y q i) = i from by simp] at this
    rw [← this]
    exact Complex.exp_ne_zero _
  set T : Finset (Equiv.Perm (Fin n)) := Finset.univ.image y with hT
  let eT : ι ≃ T := Equiv.ofBijective (fun q => ⟨y q, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩)
    ⟨fun q q' h => hy (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
      exact ⟨q, rfl⟩⟩
  let e : compactWeyl ε × ι ≃ WK × T :=
    Equiv.prodCongr (Equiv.subtypeEquivRight fun w => (hmem w).symm) eT
  have hbij : Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin n)))⁻¹ * (p.1 : Equiv.Perm (Fin n))) :=
    (Equiv.bijective_comp e _).1 hb
  have hPS := GlobalTheory.packetSum n WK T hbij m α hα0 hα
  have hsign : (-1 : ℂ) ^ halfDim ε = 1 := by
    have hpq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : Fin n => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpq
    have := GlobalTheory.signEven _ _ (by rw [hpq]; exact hn)
    rw [halfDim]
    exact_mod_cast this
  have hterm : ∀ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) =
      Formalism.PacketSums.numK WK m (fun i => α ((y q)⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α ((y q)⁻¹ i)) := by
    intro q
    rw [dsChar_eq ε hm (θ q), hsign, one_mul]
    simp only [hθ q]
    congr 1
    · rw [Formalism.PacketSums.numK, Finset.sum_subtype (compactWeyl ε) (fun w => (hmem w).symm)]
      rfl
    · rw [Formalism.PacketSums.vdm]
      exact Finset.prod_congr rfl fun i _ => Finset.prod_congr (by ext j; simp) fun _ _ => rfl
  have hexp : ∀ j : Fin n, hiWt lam j + ((j.rev : ℕ) : ℤ) = m j := by
    intro j
    have := j.isLt
    simp only [hiWt, hmdef, Fin.val_rev]
    omega
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => hterm q,
    ← Finset.sum_image (f := fun g : Equiv.Perm (Fin n) => Formalism.PacketSums.numK WK m (fun i => α (g⁻¹ i)) /
      Formalism.PacketSums.vdm (fun i => α (g⁻¹ i))) (fun q _ q' _ h => hy h), ← hT, hPS, glChar, det_rev_pow_eq_vdm,
    ← det_zpow_eq_sum]
  congr 2
  ext i j
  simp only [Matrix.of_apply, hexp j]
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
open GlobalTheory.TrEll

noncomputable section
namespace GlobalTheory.RealSigns

def weylSub {n : ℕ} (ε : Fin n → Bool) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ε ∘ ⇑w = ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    ext i; simp

theorem mem_weylSub {n : ℕ} (ε : Fin n → Bool) (w : Equiv.Perm (Fin n)) :
    w ∈ weylSub ε ↔ w ∈ GlobalTheory.HCChar.compactWeyl ε := by
  simp [weylSub, GlobalTheory.HCChar.compactWeyl]

theorem of_cosets (hR : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i)) : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  intro D V S M ρ P hc
  have hR' := hR D V S M P ρ hc (weylSub (M.ε ρ)) (mem_weylSub (M.ε ρ))
  obtain ⟨T, b, hbij, hconj⟩ := hR'
  have hfin : (XSet P (placeOf D ρ).Completion V.gram).Finite :=
    Set.finite_coe_iff.1 (Finite.of_equiv _ b.symm)
  have h1 := @GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow D.host.F D.host.E _ _ _ _ _ D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank P
    (placeOf D ρ) (embOverOf D ρ)
  have hnorm : ∀ i, ‖cxRoots (embOverOf D ρ).1 P i‖ = 1 := by
    obtain ⟨Ψ, h3⟩ := h1 (by convert hc using 0)
    exact h3.2.2.2.2.2
  have hexp : ∀ z : ℂ, ‖z‖ = 1 → Complex.exp (Complex.arg z * Complex.I) = z := fun z hz => by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rwa [hz, Complex.ofReal_one, one_mul] at h
  refine ⟨hfin, fun q => (b q : Equiv.Perm (Fin V.rank)),
    fun q a => Complex.arg (cxRoots (embOverOf D ρ).1 P (((b q : Equiv.Perm (Fin V.rank)))⁻¹ a)), ?_,
    fun q a => hexp _ (hnorm _), ?_⟩
  · let e : GlobalTheory.HCChar.compactWeyl (M.ε ρ) ≃ weylSub (M.ε ρ) :=
      { toFun := fun w => ⟨w.1, (mem_weylSub _ _).2 w.2⟩, invFun := fun w => ⟨w.1, (mem_weylSub _ _).1 w.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact hbij.comp (Equiv.prodCongr e b).bijective
  · intro q
    have hq : HasCls P (placeOf D ρ).Completion V.gram (gam q.2.choose_spec.choose_spec.2) q.1 :=
      ⟨_, _, q.2.choose_spec.choose_spec.2, q.2.choose_spec.choose_spec.1, rfl⟩
    have hc2 := hconj q (gam q.2.choose_spec.choose_spec.2) hq
    obtain ⟨g, hg⟩ := hc2
    refine ⟨g⁻¹, (congrArg (fun h => frameMat M ρ (h * gam q.2.choose_spec.choose_spec.2 * g⁻¹)) (inv_inv g)).trans (hg.trans ?_)⟩
    exact congrArg Matrix.diagonal (funext fun a => (hexp _ (hnorm _)).symm)

end GlobalTheory.RealSigns
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.geometricAction_coveringGroup_of_core_equivariance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  first | exact @GlobalTheory.geoAct_of_eqAt | exact GlobalTheory.geoAct_of_eqAt | (intros; apply GlobalTheory.geoAct_of_eqAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_unique_on_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  first | exact @GlobalTheory.WeilUniq.weilDatum_unique | exact GlobalTheory.WeilUniq.weilDatum_unique | (intros; apply GlobalTheory.WeilUniq.weilDatum_unique <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory



theorem rdIndep_of_lawsM : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ := by
  intro D T h j hj σ hσ
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdIndep_laws T.Q.c GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny GlobalTheory.abelianSchemeLaws_all.2.secTwist (T.U j) σ (h.evalWD j hj)
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ (T.Q.Xo j) T.Q.c)
    (h.unf j hj σ hσ)

end GlobalTheory
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.CMImag

theorem exists_imag_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : ∀ x, τ (σ x) = star (τ x) := h.2.2.2 τ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hTC := h.2.1
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hconj x
    rw [hall x] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMImag
end

section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.thetaFunction_rationalTranslate_mem : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT | exact GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT | (intros; apply GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT <;> assumption)
end
