module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ArchSignChar

def nrm : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)))
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem nrm_val (z : ℂˣ) : ((nrm z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_nrm (z : ℂˣ) : ‖((nrm z : ℂˣ) : ℂ)‖ = 1 := by
  rw [nrm_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_nrm : Continuous nrm := by
  have h0 : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)
  have hc : Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) h0
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  exact hc.inv₀ fun z => div_ne_zero z.ne_zero (h0 z)

def normChar {R : Type} [CommRing R] (θ : R →+* ℂ) : Rˣ →* Circle :=
  GlobalTheory.unitaryCharToCircle (nrm.comp (Units.map θ.toMonoidHom)) fun _ => norm_nrm _

theorem normChar_val {R : Type} [CommRing R] (θ : R →+* ℂ) (x : Rˣ) :
    ((normChar θ x : Circle) : ℂ) = θ x / ((‖θ x‖ : ℝ) : ℂ) := rfl

theorem continuous_normChar {R : Type} [CommRing R] [TopologicalSpace R] (θ : R →+* ℂ) (hθ : Continuous θ) :
    Continuous (normChar θ) :=
  Continuous.subtype_mk (Units.continuous_val.comp (continuous_nrm.comp (Continuous.units_map _ hθ))) _

theorem ofReal_div_norm (r : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ)) = if r < 0 then -1 else 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
  · rw [abs_of_pos (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)), div_self (Complex.ofReal_ne_zero.2 hr)]

theorem sq_eq_one (z : Circle) (h : z * z = 1) : z = 1 ∨ z = -1 := by
  have h3 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact Or.inl (Circle.ext h4)
  · exact Or.inr (Circle.ext (by rw [h4]; simp))

theorem exists_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) : ∃ θ : AF F ⊗[F] E →+* ℂ, Continuous θ ∧
      ∀ a : AF F, θ (algebraMap (AF F) (AF F ⊗[F] E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => by
    change InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (AF F) x).1 w) = _
    rw [AdeleRing.algebraMap_fst_def, InfiniteAdeleRing.algebraMap_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AF F ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine ⟨θ, ?_, fun a => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (a ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]; rfl

def archIdele (F : Type) [Field F] [NumberField F] : ((w : InfinitePlace F) → (w.Completion)ˣ) →* (AF F)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.toMonoidHom)

def archPart {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) : (w : InfinitePlace F) → (w.Completion)ˣ :=
  MulEquiv.piUnits (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F) b).1

theorem eq_archIdele {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) :
    b = archIdele F (archPart b) := by
  apply Units.ext
  refine Prod.ext rfl ?_
  exact hb

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem local_sign {K : Type} [Field K] {w : InfinitePlace K} (hw : w.IsReal) (χ : (w.Completion)ˣ →* Circle)
    (hχ : ∀ s, χ (s * s) = 1) (t : (w.Completion)ˣ) :
    χ t = if InfinitePlace.Completion.ringEquivRealOfIsReal hw (t : w.Completion) < 0 then χ (-1) else 1 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  have ht : e (t : w.Completion) ≠ 0 := (map_ne_zero e).2 t.ne_zero
  split_ifs with h
  · have hpos : 0 < -e t := neg_pos.2 h
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = -1 * (s * s) := by
      have hs0 : e.symm (Real.sqrt (-e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, map_mul, map_neg, map_one,
        RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
      ring
    rw [hs, map_mul, hχ, mul_one]
  · have hpos : 0 < e t := lt_of_le_of_ne (not_lt.1 h) (Ne.symm ht)
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = s * s := by
      have hs0 : e.symm (Real.sqrt (e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_mk0, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
    rw [hs, hχ]

theorem eta_eq_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (η : (AF F)ˣ →* Circle)
    (hsq : ∀ b, η (b * b) = 1) (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) [DecidableEq (InfinitePlace F)] :
    η b = ∏ w, if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0
      then η (archIdele F (Pi.mulSingle w (-1))) else 1 := by
  calc η b = η (archIdele F (archPart b)) := congrArg η (eq_archIdele b hb)
    _ = η (archIdele F (∏ w, Pi.mulSingle w (archPart b w))) := by rw [Finset.univ_prod_mulSingle]
    _ = ∏ w, η (archIdele F (Pi.mulSingle w (archPart b w))) := by rw [map_prod, map_prod]
    _ = _ := Finset.prod_congr rfl fun w _ =>
      local_sign (IsTotallyReal.isReal w) ((η.comp (archIdele F)).comp (MonoidHom.mulSingle (fun u : InfinitePlace F => (u.Completion)ˣ) w))
        (fun s => by
          change η (archIdele F (Pi.mulSingle w (s * s))) = 1
          rw [Pi.mulSingle_mul, map_mul]
          exact hsq _) (archPart b w)

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem exists_arch_sign_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  intro F E _ _ _ _ _ σ hcm η _ hsq
  classical
  haveI : IsTotallyReal F := hcm.1
  choose θ hθc hθ using fun w : InfinitePlace F => exists_coord (F := F) (E := E) w
  let c : InfinitePlace F → Circle := fun w => η (archIdele F (Pi.mulSingle w (-1)))
  let g : InfinitePlace F → ((AF F ⊗[F] E)ˣ →* Circle) := fun w => if c w = 1 then 1 else normChar (θ w)
  have hval : ∀ w b, normChar (θ w) (ideleMap F E b) =
      if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0 then -1 else 1 := by
    intro w b
    have hne : (b : AF F).1 w ≠ 0 := (archPart b w).ne_zero
    apply Circle.ext
    rw [normChar_val]
    have e1 : θ w ((ideleMap F E b : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) : ℝ) : ℂ) := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      exact hθ w b
    rw [e1, ofReal_div_norm _ ((map_ne_zero _).2 hne)]
    split_ifs <;> simp
  have hgc : ∀ w, Continuous (g w) := fun w => by
    by_cases h : c w = 1
    · simp only [g, h, if_true]; exact continuous_const
    · simp only [g, h, if_false]; exact continuous_normChar _ (hθc w)
  have happ : ∀ x, (∏ w, g w) x = ∏ w, g w x := fun x => MonoidHom.finsetProd_apply _ _ _
  have hc2 : ∀ w, c w = 1 ∨ c w = -1 := fun w => sq_eq_one _ (by simp only [c]; rw [← map_mul]; exact hsq _)
  refine ⟨∏ w, g w, ?_, fun b => ?_, fun b hb => ?_⟩
  · have : ⇑(∏ w, g w) = fun x => ∏ w, g w x := funext happ
    rw [this]; exact continuous_finsetProd _ fun w _ => hgc w
  · apply sq_eq_one
    rw [happ, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply, mul_one]
    · simp only [g, h, if_false]
      rw [hval]; split_ifs <;> simp
  · rw [happ, eta_eq_prod η hsq b hb]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply]
      change 1 = if _ then c w else 1
      rw [h]; split_ifs <;> rfl
    · have h' : c w = -1 := (hc2 w).resolve_left h
      simp only [g, h, if_false]
      rw [hval]
      change _ = if _ then c w else 1
      rw [h']

end GlobalTheory.ArchSignChar
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem analyticAt_ratVal_holoChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) {y : CxPts X.str σ} (hy : y ∈ e.source)
    {g : X.Fn} (hg : RegAt (under y) g) : AnalyticAt ℂ (fun v => ratVal g (e.symm v)) (e y) := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_
    exact (e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn

theorem changeFrame_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  intro F _ σ X m E e he y hy A A' hA hA'
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y) :=
    analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))
  refine ⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    rw [Matrix.det_transpose, e.left_inv hy]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit
  · have h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m,
        AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x :=
      eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt
    filter_upwards [h] with x hx η
    ext i j
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]
    rfl

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop.Piola

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem hasFDerivAt_dbar_apply {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u : E) :
    HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ (Complex.I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : ∀ a : E, HasFDerivAt (fun x => fderiv ℝ f x a)
      ((ContinuousLinearMap.apply ℝ ℂ a).comp (fderiv ℝ (fderiv ℝ f) z)) z :=
    fun a => (ContinuousLinearMap.apply ℝ ℂ a).hasFDerivAt.comp z hD.hasFDerivAt
  exact ((h u).add ((h (Complex.I • u)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem dbar_dbar_symm {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  rw [dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf w),
    dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (Complex.I • w), hs (Complex.I • v) w, hs (Complex.I • v) (Complex.I • w)]
  ring_nf

theorem dbar_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → E → ℂ} {z : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) (u : E) :
    dbar (fun x => ∏ i ∈ s, g i x) z u = ∑ k ∈ s, dbar (g k) z u * ∏ i ∈ s.erase k, g i z := by
  have h := HasFDerivAt.finsetProd (fun i hi => (hg i hi).hasFDerivAt)
  rw [dbar_eq_of_hasFDerivAt h]
  simp only [antilinPart_apply, dbar_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.GoodTop.Piola

namespace GlobalTheory.GoodTop

theorem piola_dbar {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n)
    (hf : ∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) :
    ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  have e : ∀ w : Equiv.Perm (Fin n),
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ∑ k ∈ Finset.univ.erase j, dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := fun w =>
    Piola.dbar_finset_prod (g := fun i x => dbar (f i) x (coordVec (w i))) _
      (fun i hi => (Piola.hasFDerivAt_dbar_apply (hf i (Finset.ne_of_mem_erase hi)) _).differentiableAt) _
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  set T : Equiv.Perm (Fin n) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) *
    (dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i))) with hT
  have h1 : ∀ w, T (w * Equiv.swap j k) = -T w := by
    intro w
    have hp : ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec ((w * Equiv.swap j k) i)) =
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)]
    simp only [hT]
    rw [hp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Piola.dbar_dbar_symm (hf k hkj) (coordVec (w k)) (coordVec (w j)), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hkj.symm]
    simp
  have h2 : ∑ w, T w = -∑ w, T w := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k)) T]
    exact Finset.sum_congr rfl fun w _ => h1 w
  show ∑ w, T w = 0
  linear_combination (1 / 2 : ℂ) * h2

end GlobalTheory.GoodTop
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma le_fintype_sum_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.exists_bound_smooth_data : ∀ {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) →
    ContDiffOn ℝ ∞ ρ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ K, |ρ v| ≤ C ∧
      (∀ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ ≤ C) ∧
      (∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ ≤ C) ∧
      ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ ≤ C := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ
  let F : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => |ρ v|
    + ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖
    + ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖
    + ∑ a, ∑ b, ∑ i, ∑ j,
        ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖
  have hFc : ContinuousOn F K := by
    intro v hv
    have hvU : v ∈ U := hKU hv
    have hρv : ContDiffAt ℝ ∞ ρ v := hρ.contDiffAt (hU.mem_nhds hvU)
    have h1 : ContinuousAt ρ v := hρv.continuousAt
    have h2 : ∀ b, ContinuousAt
        (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x (_root_.GlobalTheory.GoodMetric.coordVec b)) v :=
      fun b => continuousAt_dbar_ofReal_of_contDiffAt_one (hρv.of_le (by simp)) _
    have h3 : ∀ a i j, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) i j) v := fun a i j =>
      ((hG₀ v hvU).1.conn (j := 0) (hG₀ v hvU).2 (by simp)
        (_root_.GlobalTheory.GoodMetric.coordVec a) i j).continuousAt
    have h4 : ∀ a b i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G₀ x
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j) v :=
      fun a b i j =>
      ((hG₀ v hvU).1.curv (j := 0) (hG₀ v hvU).2
        (by rw [zero_add]; exact WithTop.coe_le_coe.2 le_top)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j).continuousAt
    apply ContinuousAt.continuousWithinAt
    simp only [F]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFc
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  have hFv : F v ≤ max C 0 := ((le_abs_self _).trans (hC v hv)).trans (le_max_left _ _)
  have hA : 0 ≤ |ρ v| := abs_nonneg _
  have hB : 0 ≤ ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v
      (_root_.GlobalTheory.GoodMetric.coordVec b)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC3 : 0 ≤ ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  have hD : 0 ≤ ∑ a, ∑ b, ∑ i, ∑ j,
      ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [F] at hFv
  refine ⟨by linarith, fun b => ?_, fun a i j => ?_, fun a b i j => ?_⟩
  · have := le_fintype_sum_of_nonneg
      (fun b => ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖)
      (fun _ => norm_nonneg _) b
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun a => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun b => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) b
    have e4 := le_fintype_sum_of_nonneg
      (fun a => ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith

end GlobalTheory.GoodTop
end
