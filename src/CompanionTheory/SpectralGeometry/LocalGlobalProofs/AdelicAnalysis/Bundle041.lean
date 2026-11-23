module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle004
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianRankOneHomeomorphBase
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocFv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology

theorem isOpenEmbedding_units_val (K : Type) [Field K] [TopologicalSpace K] [ContinuousInv₀ K]
    [ContinuousMul K] [T1Space K] : IsOpenEmbedding (Units.val : Kˣ → K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [this]
  exact isOpen_compl_singleton

theorem isLocR_of_ultrametric (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    (h2 : (2 : K) ≠ 0) : IsLocR K := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  have h1 : (1 : K) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source 1 h1
  obtain ⟨r, hr0, hrε, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < 1 :=
    ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hsub : Metric.closedBall (1 : K) r ⊆ e.source :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  let U : Subgroup Kˣ :=
    { carrier := Units.val ⁻¹' Metric.closedBall (1 : K) r
      one_mem' := by simp [hr0.le]
      mul_mem' := by
        intro a b ha hb
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm, Units.val_mul] at ha hb ⊢
        have : (a : K) * b - 1 = a * (b - 1) + (a - 1) := by ring
        rw [this]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
        rwa [norm_mul, hna, one_mul]
      inv_mem' := by
        intro a ha
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm] at ha ⊢
        have h0 : (a : K) ≠ 0 := a.ne_zero
        have : (((a⁻¹ : Kˣ)) : K) - 1 = -((a : K)⁻¹ * (a - 1)) := by
          rw [Units.val_inv_eq_inv_val]; field_simp; ring
        rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul] }
  have hval := isOpenEmbedding_units_val K
  have hU : IsOpen (U : Set Kˣ) := hopen.preimage Units.continuous_val
  have e1 : IsOpenEmbedding (fun u : U => ((u : Kˣ) : K)) := hval.comp hU.isOpenEmbedding_subtypeVal
  have hmem : ∀ u : U, ((u : Kˣ) : K) ∈ e.source := fun u => hsub u.2
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hval, U, hU, ?_⟩
  refine IsOpenEmbedding.of_comp _ hval ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact Units.continuous_val.comp (continuous_subtype_val.pow 2)
  · intro u w h
    simp only [Function.comp, Units.val_pow_eq_pow_val] at h
    refine e1.injective (e.injOn (hmem u) (hmem w) ?_)
    rw [he]; exact h
  · intro s hs
    have himg : (Units.val ∘ fun u : U => ((u : Kˣ) ^ 2 : Kˣ)) '' s =
        e '' ((fun u : U => ((u : Kˣ) : K)) '' s) := by
      rw [he, Set.image_image]
      simp [Function.comp, Units.val_pow_eq_pow_val]
    rw [himg]
    refine e.isOpen_image_of_subset_source (e1.isOpenMap s hs) ?_
    rintro _ ⟨u, -, rfl⟩
    exact hmem u

theorem isLocR_Fv : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (v.adicCompletion F) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
      (Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toDist)
  haveI : ProperSpace (v.adicCompletion F) := Formalism.BasicNotions.Examples₂.LocF.proper v
  have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  exact isLocR_of_ultrametric (v.adicCompletion F) h2

end GlobalTheory.CompanionTheory.SW.LocFv
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarInv

def tupEquiv {K A : Type} [AddCommGroup K] [TopologicalSpace K] [AddCommGroup A] [TopologicalSpace A]
    {M d : ℕ} (Φ : K ≃ₜ (Fin d → A)) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y) :
    (Fin 1 → Fin M → K) ≃ₜ+ (Fin M × Fin d → A) where
  toFun X p := Φ (X 0 p.1) p.2
  invFun Y _ i := Φ.symm fun k => Y (i, k)
  left_inv X := by
    funext a i
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp
  right_inv Y := by
    funext p
    simp
  map_add' X Y := by
    funext p
    simp [hadd]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (Φ.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  continuous_invFun := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact Φ.symm.continuous.comp (continuous_pi fun k => continuous_apply (i, k))

theorem map_eq_of_conj {V W : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ W) (μ : Measure V)
    (T : V → V) (G : W → W) (hG : Measurable G) (hc : ∀ x, e (T x) = G (e x))
    (hinv : (μ.map e).map G = μ.map e) : μ.map T = μ := by
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hT : T = e.symm ∘ G ∘ e := by
    funext x
    simp [← hc x]
  calc μ.map T = ((μ.map e).map G).map e.symm := by
        rw [Measure.map_map hG he, Measure.map_map hes (hG.comp he), hT]
    _ = (μ.map e).map e.symm := by rw [hinv]
    _ = μ := by
        rw [Measure.map_map hes he]
        simp

end GlobalTheory.CompanionTheory.SW.HaarInv

open GlobalTheory.CompanionTheory.SW.HaarInv in
theorem GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ _ h
  obtain ⟨⟨i3, i4, i5⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  letI : MeasurableSpace (AF F) := borel (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨iR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hBor 1 M
  let b := Module.finBasis F E
  obtain ⟨B, -, hBdet, hB⟩ := GlobalTheory.CompanionTheory.SW.CoordMat.coord_orthogonal F E σ hσ M J hJ _ b
  obtain ⟨g, hg, hconj⟩ := hB (AF F) h
  let Φ := GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (AF F) b
  have hadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by
    funext k
    simp [Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo]
  let e := tupEquiv (M := M) Φ hadd
  have hcomm : ∀ X, e.toHomeomorph (actW (AF F) σ J h X) = (fun x => g *ᵥ x) (e.toHomeomorph X) := by
    intro X
    have := hconj X
    funext p
    have hp := congrFun this p
    simpa [e, tupEquiv, Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo] using hp
  have hdet : IsUnit (B.map (algebraMap F (AF F))).det := by
    have : (B.map (algebraMap F (AF F))).det = algebraMap F (AF F) B.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    exact (Ne.isUnit hBdet).map _
  haveI : (μ.map e.toHomeomorph).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hinv : (μ.map e.toHomeomorph).map (fun x => g *ᵥ x) = μ.map e.toHomeomorph :=
    GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq (AF F) (GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one F) _ (μ.map e.toHomeomorph) (B.map (algebraMap F (AF F))) g hdet hg
  exact map_eq_of_conj e.toHomeomorph μ (actW (AF F) σ J h) (fun x => g *ᵥ x)
    (continuous_const.matrix_mulVec continuous_id).measurable hcomm hinv
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfDens

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
  [Algebra F R]

theorem sigR_sigR (hs : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [sigR, hs]
  | add a c ha hc => rw [map_add (f := _), map_add (f := _), ha, hc]

theorem sigR_inclR (y : E) : sigR R σ (inclR R y) = inclR R (σ y) := by
  simp [sigR, inclR]

theorem sigR_hR (hs : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by

  simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R hs, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gramR_mem (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := fun a c => sigR_hR R hs hJ (X c) (X a)

end Alg

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e_half_trace {σ : E →ₐ[F] E} {M d : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → Ainf F ⊗[F] E,
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) =
        cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y))
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (gramR (Ainf F) σ J X 0 0)) w =
      (1 / 2 : ℝ) * (xw e b X w ⬝ᵥ (B.map (ρ w) *ᵥ xw e b X w)) := by
  let ew : Ainf F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)
  have hew : ∀ a, ew a = e a w := fun _ => rfl
  have hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w := RingHom.ext fun x => hρ x w
  have hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0) := rfl
  have hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew := by
    rw [← hcomp]
    ext i j
    rfl
  have hhalf : ρ w (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [← hew, map_mul, hew, hρ, hhalf]
  show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _
  rw [hB, hx, hm, RingHom.map_dotProduct]
  have hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) =
      (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0)) :=
    funext fun i => RingHom.map_mulVec ew _ _ i
  rw [hv]

end Real

theorem infDens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM d b B hB ρ e he hρ Pm laminf hlam hmap Dinf hDc hD0 hDinf U hU
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
  haveI : SigmaFinite laminf := inferInstance
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at h1
    simpa using h1.symm
  have hs : ∀ x, σ (σ x) = x := HermOne.sig_sig hcm
  set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.2 (Real.sqrt_nonneg _)

  let tt := HermOne.hermHomeo (Ainf F) (σ := σ) hcm
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ) := tt.trans eH
  have hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) *
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)) :=
    fun _ => rfl
  have hpush : (coordHerm (Ainf F) σ b laminf 1).map τ = ENNReal.ofReal κ • volume := by
    have h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt := rfl
    rw [h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable,
      HermOne.map_coordHerm (Ainf F) hcm b laminf, hmap]
  set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' U with hU'def
  have hU' : MeasurableSet U' := τ.symm.measurable hU
  have hpre : τ ⁻¹' U' = U := by
    ext S
    simp [hU'def]

  have hR1 : ∫⁻ S in U, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))))
        ∂(coordHerm (Ainf F) σ b laminf 1) =
      ENNReal.ofReal (κ ^ (2 * M)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have h2 := setLIntegral_map (μ := coordHerm (Ainf F) σ b laminf 1) (g := τ)
      (f := fun y => ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y)) hU'
      (continuous_const.mul hDc).measurable.ennreal_ofReal τ.measurable
    rw [hpre, hpush] at h2
    simp only [hτ] at h2
    rw [← h2, Measure.restrict_smul, lintegral_smul_measure]
    have h3 : ∀ y, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y) =
        ENNReal.ofReal (κ ^ (2 * M - 1)) * ENNReal.ofReal (Dinf y) :=
      fun y => ENNReal.ofReal_mul (pow_nonneg hκ0 _)
    simp only [h3]
    rw [lintegral_const_mul _ (hDc.measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul hκ0, ← pow_succ', show 2 * M - 1 + 1 = 2 * M by omega]

  let Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ) :=
    fun X w => xw e b X w
  have hcoord := (GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b laminf hlam M).2.1
  have hΦm : Measurable Φ := by
    have hc : Continuous fun (z : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) =>
        e (z p) w :=
      continuous_pi fun w => continuous_pi fun p =>
        (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))
    exact hc.measurable.comp hcoord.measurable
  have hpushL := GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he laminf hlam hmap
  let Q : (InfinitePlace F → Fin M × Fin d → ℝ) → (InfinitePlace F → ℝ) :=
    fun x w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))
  have hQc : Continuous Q := by
    refine continuous_pi fun w => continuous_const.mul ?_
    exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
  let G : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)))
  have hGm : Measurable G := by
    have hc : Continuous fun x : InfinitePlace F → Fin M × Fin d → ℝ =>
        Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)) := by
      refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact hc.measurable.ennreal_ofReal
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U) = Φ ⁻¹' (Q ⁻¹' U') := by
    ext X
    have hmem := gramR_mem (Ainf F) hs hJ.1 X
    have hQ : Q (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩ := by
      funext w
      rw [hτ]
      exact (e_half_trace b B hB ρ e hρ X w).symm
    simp only [Set.mem_preimage, hU'def]
    rw [hQ, Homeomorph.symm_apply_apply]
    constructor
    · rintro ⟨S, hS, hSX⟩
      have : (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S := Subtype.ext hSX.symm
      rwa [this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hL1 : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X)
        ∂(coordW (Ainf F) b laminf 1 M) =
      ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have hA : MeasurableSet (Q ⁻¹' U') := hQc.measurable hU'
    have h2 := setLIntegral_map (μ := coordW (Ainf F) b laminf 1 M) hA hGm hΦm
    rw [hset]
    have h3 : ∀ X, ENNReal.ofReal (gaussQ e b Pm X) = G (Φ X) := fun _ => rfl
    simp only [h3]
    rw [← h2]
    have h4 : (coordW (Ainf F) b laminf 1 M).map Φ =
        ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) :=
      hpushL
    rw [h4, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    exact congrArg _ (hDinf U' hU')
  rw [hL1, hR1, hd, mul_comm M 2]

end GlobalTheory.CompanionTheory.SW.BB.InfDens
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFib R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → IsOpen (Unt σ R n) ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧ (∀ S, S ∉ Unt σ R n → m S = 0) ∧ (∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → IsCompact D → D ⊆ Unt σ R n → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem haar_fundamental_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, hbH, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  haveI := hbH
  obtain ⟨hcount, U, hU, hUd⟩ := rational_countable_discrete F E σ hσ M J hJ
  haveI := hcount
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hmem : ∀ γ : HA (AF F) σ J, γ ∈ Γ → HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J :=
    fun γ hγ => Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨-, D, hD, hDs⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
    (HA (AF F) σ J) Γ ⟨U, hU, fun γ hγ hγU => hUd γ hγU (hmem γ hγ)⟩
  have hfd : ∀ μ : Measure (HA (AF F) σ J), IsFDH F E σ M J μ D := fun μ =>
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDs
  refine ⟨⟨Measure.haar, inferInstanceAs (Measure.IsHaarMeasure _)⟩, fun μ hμ => ?_⟩
  haveI : μ.IsHaarMeasure := hμ
  refine ⟨⟨D, hfd μ⟩, ⟨D, hD, hfd μ, fun h => ?_⟩, fun 𝓕 h𝓕 => ?_⟩
  · obtain ⟨γ, hγ, -⟩ := hDs h
    exact ⟨γ, hmem _ γ.2, hγ⟩
  · haveI : MeasurableConstSMul (HFinIn (AF F) σ J) (HA (AF F) σ J) :=
      ⟨fun c => (continuous_const.mul continuous_id :
        Continuous fun x : HA (AF F) σ J => (show HA (AF F) σ J from c.1) * x).measurable⟩
    haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
    have h𝓕' : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := h𝓕
    exact h𝓕'.measure_ne_zero (NeZero.ne μ)

end GlobalTheory.CompanionTheory.SW
end
