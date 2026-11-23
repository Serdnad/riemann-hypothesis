module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRep
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelsReadOnProductPrimeFieldGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle184
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (EmbOver htInf htFin compInf compFin infProj opNorm)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt infNorm)
open GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem infEmb_tmul_one_eq_extensionEmbedding {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {w : InfinitePlace F} {τ : E →+* ℂ} (hτ : τ.comp (algebraMap F E) = w.embedding)
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) (b : Ainf F) :
    θ (b ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (b w) := by
  have hc : Continuous fun b : Ainf F => InfinitePlace.Completion.extensionEmbedding w (b w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have key := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hθ.2 hc ?_
  · exact congrFun key b
  funext x
  simp only [Function.comp_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', hθ.1,
    ← RingHom.comp_apply, hτ]
  simp

theorem htInf_eq_infMat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (t : EmbOver E w)
    [StarRing E] {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb t.1 θ) (g : HA (AF F) σ J) :
    htInf F w (bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J g)) =
      max 1 (max (opNorm (infMat σ J θ g)) (opNorm (infMat σ J θ g⁻¹))) := by
  have hre := infEmb_tmul_one_eq_extensionEmbedding t.2 hθ
  have hz : ∀ z : AF F ⊗[F] E, GlobalTheory.AdelicU.infEmb t (compInf F E w z) =
      θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have e : (fstA F a) ⊗ₜ[F] x = ((fstA F a) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by simp
      simp only [GlobalTheory.AdelicU.compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, GlobalTheory.AdelicU.infEmb_tmul]
      rw [e, map_mul, hre, hθ.1]
      rfl
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hm : ∀ k : HA (AF F) σ J, ((bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J k) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _).map (GlobalTheory.AdelicU.infEmb t) = infMat σ J θ k := by
    intro k
    ext i j
    exact hz _
  show max 1 (max (GlobalTheory.AdelicU.normInf F w _) (GlobalTheory.AdelicU.normInf F w _)) = _
  rw [GlobalTheory.AdelicU.normInf_eq_opNorm h t, GlobalTheory.AdelicU.normInf_eq_opNorm h t, ← map_inv (bc (compInf F E w)),
    ← map_inv (GlobalTheory.AdelicU.matHom _ σ J), hm, hm]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem htInf_eq_infHt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    htInf D.host.F (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (bc (compInf D.host.F D.host.E _) (Formalism.L2.Theta.matHom V g)) = infHt θ V τ g := by
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have ht : (tauE D τ).comp (algebraMap D.host.F D.host.E) =
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hcm.1.isReal _))).symm
  exact (htInf_eq_infMat hcm V.gram ⟨_, ht⟩ (hθ τ) g).trans rfl

private theorem htFin_eq_one_of_mem_GinfC {g : GA D V} (hg : g ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)) = 1 := by
  have hk : Formalism.L2.Theta.finHom V g = 1 := hg
  have hz : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, compFin D.host.F D.host.E v z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]
  have h1 : bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g) = 1 := by
    apply Units.ext
    ext i j
    have hij : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) =
        ((1 : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix _ _ _) i j := by
      rw [← hk]; rfl
    show compFin D.host.F D.host.E v (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) = _
    rw [hz, hij, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  refine (GlobalTheory.AdelicU.htOf_eq_one).2 ⟨?_, ?_⟩ <;> simpa using GlobalTheory.AdelicU.normFin_one_le D.host.F v

theorem height_eq_prod_infHt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    height V g = ∏ τ, (infHt θ V τ g : ℝ) := by
  have hinf : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) =
      ∏ τ, infHt θ V τ g :=
    (Fintype.prod_bijective _ (GlobalTheory.CMTypePlaces.places_bijective D) _ _
      fun τ => (htInf_eq_infHt V hθ τ g).symm).symm
  show ((GlobalTheory.AdelicU.heightGL D.host.F (Formalism.L2.Theta.matHom V g) : NNReal) : ℝ) = _
  rw [GlobalTheory.AdelicU.heightGL, hinf]
  simp only [htFin_eq_one_of_mem_GinfC V hg, finprod_one, mul_one, NNReal.coe_prod]

theorem normInf_le_height (hθ : IsInfFam θ) : ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g := by
  refine ⟨2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ), fun g => ?_⟩
  have hb : ∀ τ, (infHt θ V τ g : ℝ) ≤ height V g := fun τ => by
    have := htInf_le_height V g (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
    rwa [htInf_eq_infHt V hθ τ g] at this
  have he : ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤
      2 * height V g := by
    intro τ i j
    have h1 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j
    have h2 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j
    have h3 : infNorm θ V τ g ≤ infHt θ V τ g := le_max_of_le_right (le_max_left _ _)
    have h4 : infNorm θ V τ g⁻¹ ≤ infHt θ V τ g := le_max_of_le_right (le_max_right _ _)
    have h3' : (infNorm θ V τ g : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h3).trans (hb τ)
    have h4' : (infNorm θ V τ g⁻¹ : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h4).trans (hb τ)
    have e3 : (infNorm θ V τ g : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖ := rfl
    have e4 : (infNorm θ V τ g⁻¹ : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹)‖ := rfl
    linarith
  calc normInf θ V g = ∑ τ, ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := rfl
    _ ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, 2 * height V g := by
        gcongr with τ _ i _ j _
        exact he τ i j
    _ = 2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ) * height V g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem height_le_normInf_pow (hθ : IsInfFam θ) : ∃ d : ℕ, ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · refine ⟨0, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, pow_zero]
    simp [GlobalTheory.SmoothForms.HeightCoset.infHt_rank_zero θ V h0]
  · refine ⟨Fintype.card D.what₂.Tau, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun τ _ => NNReal.coe_nonneg _)
      (fun τ _ => GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hpos τ g)

theorem normInf_height_comparison (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) :
    (∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g) ∧
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ GinfC V, height V g ≤ C * (1 + normInf θ V g) ^ d := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  refine ⟨⟨C, hC⟩, 1, d, fun g hg => ?_⟩
  have h0 : 0 ≤ normInf θ V g := by
    unfold Formalism.L2.Theta.normInf
    positivity
  calc height V g ≤ normInf θ V g ^ d := hd g hg
    _ ≤ (1 + normInf θ V g) ^ d := pow_le_pow_left₀ h0 (by linarith) d
    _ = 1 * (1 + normInf θ V g) ^ d := (one_mul _).symm

private theorem exists_coset_bound_of_modGrowthExp (V : HSp D) {d : ℕ} (hd : ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d) {A : ℕ}
    {f : GA D V → ℂ} (hf : ModGrowthExp V A f) (x : GA D V) :
    ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ (d * A) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := nonneg_of_growth hC
  refine ⟨C * height V x ^ A, fun g hg => ?_⟩
  have h1 : height V (x * g) ≤ height V x * normInf θ V g ^ d :=
    (height_mul_le V x g).trans (mul_le_mul_of_nonneg_left (hd g hg) (height_pos V x).le)
  calc ‖f (x * g)‖ ≤ C * height V (x * g) ^ A := hC _
    _ ≤ C * (height V x * normInf θ V g ^ d) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h1 A) hC0
    _ = C * height V x ^ A * normInf θ V g ^ (d * A) := by rw [mul_pow, ← pow_mul]; ring

variable {V}

theorem exists_modGrowthExp_le_normInf_pow (hθ : IsInfFam θ) (A : ℕ) :
    ∃ N : ℕ, ∀ f : GA D V → ℂ, ModGrowthExp V A f →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  exact ⟨d * A, fun f hf x => exists_coset_bound_of_modGrowthExp V hd hf x⟩

theorem UnifModGrowth.growth (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) :
    ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := exists_modGrowthExp_le_normInf_pow (V := V) hθ A
  exact ⟨N, fun l hl x => hN _ (hA l hl) x⟩

theorem UnifModGrowth.isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hz : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) :
    IsAutFunSm θ V φ :=
  { toIsAutFun := ha, smooth := hs, zfin := hz, growth := h.growth hθ }

end GlobalTheory.Grow

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertSph Matrix Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LatAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_integral (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

theorem smul_mem_latAt (X : Spc F E n) (w : Pl (F := F)) {b : AF F} (hb : evFin F w b ∈ w.adicCompletionIntegers F)
    {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : z ∈ latAt X w) : b • z ∈ latAt X w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hb hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (v : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice L hL v

theorem exists_int_mulVec_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L, c • (N *ᵥ y) ∈ L := by
  have key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L := by
    intro L' hL'
    induction L', hL' using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨c, hc, hx⟩ := exists_int_smul_mem L hL (N *ᵥ x)
      refine ⟨c, hc, fun y hy => ?_⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_smul, smul_comm]
      exact L.smul_mem r hx
    | sup A B _ _ hA hB =>
      obtain ⟨c, hc, hA⟩ := hA
      obtain ⟨d, hd, hB⟩ := hB
      refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Matrix.mulVec_add, smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact zsmul_mem (hA a ha) d
      · rw [mul_smul]; exact zsmul_mem (hB b hb) c
  exact key L hL.fg

theorem eventually_incM (X : Spc F E n) (hL : X.L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, incM F N *ᵥ z ∈ latAt X w := by
  obtain ⟨c, hc, hN⟩ := exists_int_mulVec_mem X.L hL N
  filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    have h1 : (a • fun i => inclR (F := F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w :=
      AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩
    have h2 := smul_mem_latAt X w hw h1
    convert h2 using 1
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    ext i
    have hc' : (c : F) ≠ 0 := Int.cast_ne_zero.2 hc
    have h3 : (incM F N *ᵥ fun i => inclR (F := F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) :=
      (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm
    rw [h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem eventually_single (X : Spc F E n) (hL : X.L.IsFullLattice E) (i j : Fin n) (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, Matrix.single i j t *ᵥ z ∈ latAt X w := by
  induction t using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs
      · simp [inclR, TensorProduct.smul_tmul']
      · simp
    filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz
    rw [h, Matrix.smul_mulVec]
    exact smul_mem_latAt X w hw (h2 z hz)
  | add s t hs ht =>
    filter_upwards [hs, ht] with w h1 h2 z hz
    rw [Matrix.single_add, Matrix.add_mulVec]
    exact add_mem (h1 z hz) (h2 z hz)

theorem eventually_mulVec_mem (X : Spc F E n) (hL : X.L.IsFullLattice E) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, M *ᵥ z ∈ latAt X w := by
  have h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)
  filter_upwards [h] with w hw z hz
  rw [Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]
  refine sum_mem fun i _ => ?_
  rw [Matrix.sum_mulVec]
  exact sum_mem fun j _ => hw i j z hz

theorem exists_finset_keeps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  intro F E _ _ _ _ _ σ n X hL g
  have h := (eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))
  refine ⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
  exact ⟨hw.1 z hz, hw.2 z hz⟩

end GlobalTheory.LatAlmostAll
end
end

section

noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)


end GlobalTheory.KStableLie

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heisenbergVacuum_unique_of_selfDual : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ v, Fixes W Λ v → ∃ c : ℂ, v = c • s := by
  first | exact @GlobalTheory.SphTheta.vacuum_unique_of_selfDual | exact GlobalTheory.SphTheta.vacuum_unique_of_selfDual | (intros; apply GlobalTheory.SphTheta.vacuum_unique_of_selfDual <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  first | exact @GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | exact GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | (intros; apply GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.outer_irr_iso_weylRep_of_pos : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ), 0 < n → ∀ (lam : ι → ℕ → ℤ) (μ : ι → DomWeight n), (∀ τ (i : Fin n), (μ τ).w i = lam τ i) → Iso (outer fun τ => irr n (μ τ)) (weylRep n lam) := by
  first | exact @GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | exact GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | (intros; apply GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levels_read_on_product_primeFieldGL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.IsGrp F → ∀ b : Bool, ∃ (Φ : G ≃* GProd D) (L₁ : D.nd.PlG 0 → GlobalTheory.BadShare.Lev (D.host.g 0) D.R.r) (L₂ : D.nd.PlG 1 → GlobalTheory.BadShare.Lev (D.host.g 1) D.R.r), (∀ g : G, g ∈ (F.lvl b).P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) ∧ (∀ g : (F.lvl b).P, D.what₂.embLL (((F.lvl b).ψ⁻¹ g : D.what₂.LLˣ) : D.what₂.LL) = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) ∧ (∀ g : G, GlobalTheory.BadShare.AllUnip (Φ g).1 ∨ GlobalTheory.BadShare.AllUnip (Φ g).2 → ∃ (k : Fin 2) (PP : R.Pg), CharP (kP PP.1) (D.host.g k) ∧ IsNilpotent ((R.eG g PP).val - 1)) ∧ ∀ (g : G) (γ : G0g D.nd), (∀ v, γ ⟨0, v⟩ = (Φ g).1 v) → (∀ v, γ ⟨1, v⟩ = (Φ g).2 v) → D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff γ := by
  first | exact @GlobalTheory.LevelsProd.levels_prod | exact GlobalTheory.LevelsProd.levels_prod | (intros; apply GlobalTheory.LevelsProd.levels_prod <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adjointHalfDatum_stabilizerPair_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (r : ℕ) (hS : r ≤ S.rank) (hT : r ≤ T.rank), T.rank = r → ∀ g h, finE S g ∈ St βS → finE T h ∈ St βT → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → redFn βS PP (finE S g) ∈ blockTri (blk2 r)) → (∀ PP ∈ Pg, upperLeftBlock hS (redFn βS PP (finE S g)) = upperLeftBlock hT (redFn βT PP (finE T h))) → ∀ x, adjDatum S T βS βT Pg Q ξ a (actO S T g h x) = (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hS (redFn βS PP (finE S g)))))⁻¹ * ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) * adjDatum S T βS βT Pg Q ξ a x := by
  first | exact @GlobalTheory.AdjDatumMove.adjDatum_actO | exact GlobalTheory.AdjDatumMove.adjDatum_actO | (intros; apply GlobalTheory.AdjDatumMove.adjDatum_actO <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotent_twisted_group_endomorphism : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  first | exact @GlobalTheory.UnitaryIdemCut.exists_cut | exact GlobalTheory.UnitaryIdemCut.exists_cut | (intros; apply GlobalTheory.UnitaryIdemCut.exists_cut <;> assumption)
end
