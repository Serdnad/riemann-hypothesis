module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle246
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolDiff

variable {n : ℕ}

def rmul (w : Mat n) : CLof (Mat n) (Mat n) :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ w)

theorem rmul_apply (w z : Mat n) : rmul w z = z * w := rfl

def rmulLin : Mat n →ₗ[ℝ] CLof (Mat n) (Mat n) where
  toFun := rmul
  map_add' a b := by
    ext1 z
    simp [rmul_apply, mul_add]
  map_smul' c a := by
    ext1 z
    simp [rmul_apply]

theorem continuous_rmul : Continuous (rmul : Mat n → CLof (Mat n) (Mat n)) :=
  LinearMap.continuous_of_finiteDimensional rmulLin

theorem exists_unit_of_mem {g : Mat n} (h : g ∈ GLs n) : ∃ y : G n, y.val = g := by
  have : IsUnit g := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem isCompact_lift {K : Set (Mat n)} (hK : IsCompact K) (hs : K ⊆ GLs n) :
    IsCompact (Units.val ⁻¹' K : Set (G n)) := by
  refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_).2 hK
  intro g hg
  obtain ⟨y, hy⟩ := exists_unit_of_mem (hs hg)
  exact ⟨y, hy⟩

theorem exists_compact_support {K B : Set (Mat n)} (hK : IsCompact K) (hKs : K ⊆ GLs n)
    (hB : IsCompact B) (hBs : B ⊆ GLs n) :
    ∃ S : Set (G n), IsCompact S ∧ ∀ z ∈ B, ∀ u : G n, z * (u⁻¹ : G n).val ∈ K → u ∈ S := by
  refine ⟨(fun p : G n × G n => p.1⁻¹ * p.2) ''
    ((Units.val ⁻¹' K : Set (G n)) ×ˢ (Units.val ⁻¹' B : Set (G n))), ?_, ?_⟩
  · exact ((isCompact_lift hK hKs).prod (isCompact_lift hB hBs)).image
      ((continuous_fst.inv).mul continuous_snd)
  · intro z hz u hu
    obtain ⟨y, rfl⟩ := exists_unit_of_mem (hBs hz)
    refine ⟨(y * u⁻¹, y), ⟨?_, hz⟩, ?_⟩
    · simpa using hu
    · simp

end GlobalTheory.CompanionTheory.PresSobA.MolDiff


open GlobalTheory.CompanionTheory.PresSobA.MolDiff in
theorem GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, ∀ z ∈ GLs n, DifferentiableAt ℝ (Mol μ φ (⇑x)) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ x z hz
  obtain ⟨hsm, hcs, hsub⟩ := hφ
  have hc1 : Continuous φ := hsm.continuous
  have hdφ : Differentiable ℝ φ := hsm.differentiable (by simp)
  have hcf : Continuous (fderiv ℝ φ) := hsm.continuous_fderiv (by simp)
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  obtain ⟨B, hBn, hBs, hBc⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hz)
  obtain ⟨S, hSc, hS⟩ := MolDiff.exists_compact_support hcs hsub hBc hBs
  have hinv : Continuous (fun u : G n => (u⁻¹ : G n).val) :=
    Units.continuous_val.comp continuous_inv
  have hmul : Continuous (fun p : Mat n × G n => p.1 * (p.2⁻¹ : G n).val) :=
    continuous_fst.matrix_mul (hinv.comp continuous_snd)
  let g : Mat n → G n → CLof (Mat n) ℝ := fun z u =>
    (fderiv ℝ φ (z * (u⁻¹ : G n).val)).comp (MolDiff.rmul (u⁻¹ : G n).val)
  have hg : Continuous (fun p : Mat n × G n => g p.1 p.2) :=
    (hcf.comp hmul).clm_comp (MolDiff.continuous_rmul.comp (hinv.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hBc.prod hSc).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨C0, hC0⟩ := hc1.bounded_above_of_compact_support hcs
  have hxS : IntegrableOn (⇑x) S μ := by
    haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hSc.measure_lt_top⟩
    exact ((Lp.memLp x).restrict S).integrable (by norm_num)
  let bound : G n → ℝ := S.indicator fun u => max C C0 * ‖x u‖
  have hbi : Integrable bound μ := IntegrableOn.integrable_indicator (hxS.norm.const_mul _) hSc.measurableSet
  have hout : ∀ z' ∈ B, ∀ u : G n, u ∉ S → z' * (u⁻¹ : G n).val ∉ tsupport φ :=
    fun z' hz' u hu h => hu (hS z' hz' u h)
  let F : Mat n → G n → V := fun z u => φ (z * (u⁻¹ : G n).val) • x u
  let F' : Mat n → G n → CLof (Mat n) V := fun z u => (g z u).smulRight (x u)
  have hFm : ∀ z', AEStronglyMeasurable (F z') μ := fun z' =>
    ((hc1.comp (continuous_const.matrix_mul hinv)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable x)
  have hF'm : AEStronglyMeasurable (F' z) μ := by
    have hgz : Continuous (g z) := hg.comp (Continuous.prodMk_right z)
    let L : CLof (Mat n) ℝ →L[ℝ] V →L[ℝ] CLof (Mat n) V :=
      StrongDual.smulRightL ℝ (Mat n) V
    exact L.aestronglyMeasurable_comp₂
      hgz.aestronglyMeasurable (Lp.aestronglyMeasurable x)
  have hFb : ∀ u, ‖F z u‖ ≤ bound u := by
    intro u
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F, norm_smul]
      exact mul_le_mul_of_nonneg_right ((hC0 _).trans (le_max_right _ _)) (norm_nonneg _)
    · simp only [bound, Set.indicator_of_notMem hu, F]
      rw [image_eq_zero_of_notMem_tsupport (hout z (mem_of_mem_nhds hBn) u hu)]
      simp
  have hF'b : ∀ᵐ u ∂μ, ∀ z' ∈ B, ‖F' z' u‖ ≤ bound u := by
    refine ae_of_all _ fun u z' hz' => ?_
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F', ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right ((hC (z', u) ⟨hz', hu⟩).trans (le_max_left _ _))
        (norm_nonneg _)
    · have h0 : g z' u = 0 := by
        show (fderiv ℝ φ (z' * (u⁻¹ : G n).val)).comp _ = 0
        rw [fderiv_of_notMem_tsupport ℝ (hout z' hz' u hu)]
        exact ContinuousLinearMap.zero_comp _
      simp only [bound, Set.indicator_of_notMem hu, F', h0]
      simp
  have hd : ∀ᵐ u ∂μ, ∀ z' ∈ B, HasFDerivAt (F · u) (F' z' u) z' := by
    refine ae_of_all _ fun u z' _ => ?_
    have h1 : HasFDerivAt (fun w : Mat n => w * (u⁻¹ : G n).val) (MolDiff.rmul (u⁻¹ : G n).val) z' :=
      (MolDiff.rmul (u⁻¹ : G n).val).hasFDerivAt
    exact ((hdφ _).hasFDerivAt.comp z' h1).smul_const (x u)
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hBn
    (Eventually.of_forall hFm) (hbi.mono' (hFm z) (ae_of_all _ hFb)) hF'm hF'b hbi hd).differentiableAt
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwUg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem twUg_map (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) :
    (twUg σ B).comp (PAlg.mapUg (PAlg.twMap σ f)) = (PAlg.mapUg f).comp (twUg σ A) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (l : (PAlg.tw σ A).U)) (RingHom.ext fun x => ?_)
  change twUg σ B (PAlg.mapUg (PAlg.twMap σ f) (algebraMap _ _ x)) = PAlg.mapUg f (twUg σ A (algebraMap _ _ x))
  rw [PAlg.mapUg_algebraMap, twUg_algebraMap, twUg_algebraMap, PAlg.mapUg_algebraMap, PAlg.twU_mapU]

theorem twUg_cToUg (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : ℂ_[l]) :
    twUg σ A ((PAlg.tw σ A).cToUg x) = A.cToUg (galCp σ x) := by
  have h : ((twUg σ A).comp (PAlg.tw σ A).cToUg).comp
        ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) =
      (A.cToUg.comp (galCp σ : ℂ_[l] →+* ℂ_[l])).comp ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : OC l)) (RingHom.ext fun y => ?_)
    have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y) = (y : ℂ_[l]) :=
      (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).commutes y
    have e2 : ((galOC σ y : OC l) : ℂ_[l]) = galCp σ (y : ℂ_[l]) := rfl
    change twUg σ A ((PAlg.tw σ A).cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))) =
      A.cToUg (galCp σ ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y)))
    rw [e, PAlg.cToUg_coe, twUg_algebraMap, PAlg.twU_oC, ← e2, PAlg.cToUg_coe]
  obtain ⟨y, rfl⟩ := (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).surjective x
  exact RingHom.congr_fun h y

theorem twUg_kb (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : PadicAlgCl l) :
    twUg σ A (kb (PAlg.tw σ A) x) = kb A (σ x) := by
  change twUg σ A ((PAlg.tw σ A).cToUg (clToC l x)) = A.cToUg (clToC l (σ x))
  rw [twUg_cToUg]
  exact congrArg A.cToUg (galCp_coe σ x)

theorem twUg_comp_algebraMap (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ((twUg σ A).comp (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug)).comp (PAlg.twUEquiv σ A).symm.toRingHom =
      algebraMap A.U A.Ug := by
  refine RingHom.ext fun x => ?_
  change twUg σ A (algebraMap _ _ ((PAlg.twUEquiv σ A).symm x)) = algebraMap A.U A.Ug x
  rw [twUg_algebraMap]
  exact congrArg (algebraMap A.U A.Ug) ((PAlg.twUEquiv σ A).apply_symm_apply x)

theorem geomPt_galMap (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ =
      Spec.map (CommRingCat.ofHom (twUg σ A)) ≫
        geomPt M (PAlg.tw σ A) ((pxTw M.p (okToOC l K) σ (galOC_okToOC σ)).app A y) := by
  refine gb_ext M ?_ ?_
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst_assoc, geomPt_fst, geomPt_fst]
    change _ = _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (PAlg.twUEquiv σ A).symm.toRingHom) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, twUg_comp_algebraMap]
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, geomPt_snd, ← Category.assoc, geomPt_snd,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext fun x => twUg_kb σ A x).symm

end GlobalTheory.CompanionTheory.TwUg

theorem GlobalTheory.CompanionTheory.TwUg.twUg_prop : CrystallineSemistableComparison.E.TwUg := fun _ _ _ σ =>
  ⟨fun _ _ f => GlobalTheory.CompanionTheory.TwUg.twUg_map σ f, fun A x => GlobalTheory.CompanionTheory.TwUg.twUg_kb σ A x,
    fun M A y => GlobalTheory.CompanionTheory.TwUg.geomPt_galMap M σ A y⟩
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FResProof

theorem pull_square {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {σ : R₀ →+* R₁} {C₀ C₁ : Type 1}
    [Category.{0} C₀] [Category.{0} C₁] {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₀ ⥤ ModuleCat.{0} R₁}
    {F₀' : C₁ ⥤ ModuleCat.{0} R₀} {F₂ : C₁ ⥤ ModuleCat.{0} R₁} (m₁ : Mor F₀ F₁ σ) (e : Mor F₁ F₂ (RingHom.id R₁))
    (a : Mor F₀ F₀' (RingHom.id R₀)) (m₂ : Mor F₀' F₂ σ) (j : ℕ)
    (h : ∀ z : Cn F₀ j, e.pullC j (m₁.pullC j z) = m₂.pullC j (a.pullC j z)) (y : CH.H F₀ j) :
    e.pull j (m₁.pull j y) = m₂.pull j (a.pull j y) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext x; rfl

theorem primRes_id {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : primRes (𝟙 U) ζ = ζ :=
  Subtype.ext (by
    change (𝟙 U : U ⟶ U).appTop.hom ζ.1 = ζ.1
    simp)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mG (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) :
    Mor (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L (probe H r (G ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P)
    (n j : ℕ) (y : CH.H (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L j) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull j ((lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).pull j y) =
      (lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j ((mG H r M G n).pull j y) :=
  pull_square (lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n) (Mor.restrict (modF (AcrEl M.P n)) G)
    (mG H r M G n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) j (fun z => rfl) y

theorem pull_sch_id (q : ℕ) (i : ℤ) (j : ℕ) (X : Scheme.{0}) (x : Ht q (sch.obj X) j i) :
    pull _ (sch.map (𝟙 X)) _ j x = x := by
  rw [CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]



theorem et_restrict (hE : EtNat) (hg : InGen) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C]
    (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j i) :
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    (mG H r M G n).pull j ((pts H r M (𝟭 _) n).et i j x) = (pts H r M G n).et i j x := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine (hE hg (l ^ n) (El M.P) C (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n)
    (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M) (gb M) (pts H r M (𝟭 _) n) (pts H r M G n) (𝟙 _)
    (mG H r M G n) (fun c => 𝟙 _) (fun φ => ?_)
    (fun c f => (lcRes_id _ f).symm) (fun c => ?_) i
    (Or.inr fun c => primRes_id _) j x).trans (congrArg _ (pull_sch_id _ _ _ _ x))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.CompanionTheory.FResProof

theorem GlobalTheory.CompanionTheory.FResProof.fRes : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FRes := by
  intro hE E hN l _ H r K M C _ G n i j x
  exact (GlobalTheory.CompanionTheory.FResProof.square hN H r M G n j _).trans
    (congrArg _ (GlobalTheory.CompanionTheory.FResProof.et_restrict hE E.gen H r M G n i j x))
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FRootCls

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem rho_succ (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem pow_div_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ, Nat.mul_comm, Nat.mul_div_cancel _ h]

theorem zetaX_succ (r : Roots l) (M : Model l K) (n : ℕ) :
    (r.zetaX M n).1 = (r.zetaX M (n + 1)).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_succ]
  change (pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1) =
    ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ (n + 1)).1)) ^ l
  rw [rho_succ r n, map_pow, map_pow]

theorem primRes_zetaX (r : Roots l) (M : Model l K) (n : ℕ) (A : PAlg l) (y : M.P.obj A) :
    primRes (geomPt M A y) (r.zetaX M n) = r.zeta A n := by
  refine Subtype.ext ?_
  change (geomPt M A y).appTop.hom ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1)) =
    toΓ A.Ug (kb A (r.ρ n).1)
  rw [← toΓ_nat (kb A), ← geomPt_snd M A y, Scheme.Hom.comp_appTop]
  rfl

def lcRing (hL : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) : LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hL l H A hA n).2.1
  map_mul' := (hL l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_one (hL : LcSpec) (hM : MorCup) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0
      (oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))) = oneH (AcrEl M.P n) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) (El M.P) (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))
    (AcrEl M.P n) (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => lcRing hL H c.1.obj c.1.property n) (fun _ _ => rfl)).1

def rootSys (hO : InOp) (hR : InRed) (hRR : RedRoot) (r : Roots l) (M : Model l K) (i : ℤ) : Hl l (sch.obj (gb M)) (0 : ℕ) i :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  ⟨fun n => rootClass i (r.zetaX M n), fun n =>
    hRR hO hR (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) i (gb M) (r.zetaX M (n + 1)) (r.zetaX M n) (zetaX_succ r M n)⟩

theorem etVal (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    (pts H r M (𝟭 _) n).et i 0 (rootClass i (r.zetaX M n)) =
      oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n)) :=
  hEt hg (l ^ n) (El M.P) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M) (pts H r M (𝟭 _) n)
    (r.zetaX M n) (fun c => primRes_zetaX r M n _ _) i

theorem eM_root (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    eM hN H r M n i 0 (rootClass i (r.zetaX M n)) = oneH (AcrEl M.P n) := by
  refine Eq.trans (congrArg ((lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0) (etVal hEt hg hN H r M n i)) ?_
  exact lcMor_one hL hM hN H r M n

theorem eM_rootSys (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hRR : RedRoot) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) (i : ℤ) (n : ℕ) : eM hN H r M n i 0 ((rootSys E.op E.red hRR r M i).1 n) = oneH (AcrEl M.P n) :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  eM_root hL hM hEt E.gen hN H r M n i

theorem froot : CrystallineSemistableComparison.E.EtRoot → CrystallineSemistableComparison.E.RedRoot → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FRoot :=
  fun hEt hRR hM hL E hN _ _ H r _ M i => ⟨rootSys E.op E.red hRR r M i, eM_rootSys hL hM hEt hRR E hN H r M i⟩

end GlobalTheory.CompanionTheory.FRootCls
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl

    rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl

  rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.fontaine_lattice_dpow_closed : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  first | exact @GlobalTheory.CompanionTheory.LatCHc.hc_k | exact GlobalTheory.CompanionTheory.LatCHc.hc_k | (intros; apply GlobalTheory.CompanionTheory.LatCHc.hc_k <;> assumption)
end
