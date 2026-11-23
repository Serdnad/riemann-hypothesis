module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_of_isStdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (fun x => ψ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ z in 𝓝 x, ψ x = ψ z := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
    have hz' : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have e : z = x + (z - x) := by abel
    rw [e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]
  exact continuousAt_const.congr h

theorem continuous_star_E [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous

end GlobalTheory.JR.FourDesc

open GlobalTheory.JR.FourDesc in
theorem GlobalTheory.JR.fourB_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  intro F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf
  haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI := M.mE
  haveI := M.bE
  letI := M.mU
  haveI := M.bU
  haveI := M.haarE
  haveI := M.haarU
  haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE := ⟨_, rfl⟩
  haveI : SigmaFinite P := by rw [hP]; infer_instance
  haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne
  haveI : SigmaFinite ν := IsFiniteMeasure.toSigmaFinite ν
  haveI : IsFiniteMeasureOnCompacts ν := ⟨fun s _ => measure_lt_top ν s⟩
  haveI : IsFiniteMeasureOnCompacts (P.prod ν) := Measure.prod.instIsFiniteMeasureOnCompacts P ν
  haveI : SecondCountableTopology E := secondCountable_of_proper
  have hSC : SecondCountableTopology (Fin r → E) :=
    TopologicalSpace.secondCountableTopology_iInf (ι := Fin r) fun i =>
      TopologicalSpace.secondCountableTopology_induced (Fin r → E) E (fun f => f i)
  haveI : OpensMeasurableSpace ((Fin r → E) × Matrix.unitaryGroup (Fin r) E) :=
    Prod.opensMeasurableSpace (h := ⟨Or.inl hSC⟩)
  have hψc := continuous_of_isStdChar hψ
  have htr : Continuous (fun e : E => Algebra.trace F E e) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)
  have hfc : Continuous f := hf.1.continuous
  have hαcont : Continuous α := hα.continuous
  have hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E),
      star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro g v w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  let jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E)) :=
    fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)
  have hjg : ∀ g y, jg g y = g.1 *ᵥ j y := fun g y => rfl
  have hjgI : ∀ g, A.IsIsom x (jg g) := fun g y y' => by rw [hjg, hjg, hstar, hx]
  have I := GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x
  have hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := (I j hx).1
  have hmapj : Measure.map j μ = P := by rw [hP]; exact (I j hx).2 μ hμ
  have hmapg : ∀ g, Measure.map (jg g) μ = P := fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ
  have hjc : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjm : Measurable j := hjc.measurable
  have hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v) :=
    fun g => continuous_const.matrix_mulVec continuous_id
  have hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P := by
    intro g
    have e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g) := funext fun y => (hjg g y).symm
    conv_lhs => rw [← hmapj]
    rw [Measure.map_map (hgc g).measurable hjm, e, hmapg g]
  have hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) →
      ∫ g, h g ∂ν = ∫ g, h g ∂M.μU := by
    intro h hh
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hh
  funext y
  let G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ := fun v g =>
    f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))
  have hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam)) := by
    unfold actU
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
    · fun_prop
    · fun_prop
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y) := by fun_prop
    exact ((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul
      (hψc.comp (htr.comp h1))
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image
      (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_
    rintro ⟨v, g⟩ hvg
    by_contra hne
    apply hvg
    have h1 : f (actU g (Ax, v, lam)) ≠ 0 := fun h => hne (by simp [G, h])
    have h2 : α g ≠ 0 := fun h => hne (by simp [G, h])
    refine ⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [actU, Prod.mk.injEq, and_true]
    rw [Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  have hGi : Integrable (Function.uncurry G) (P.prod ν) := hGc.integrable_of_hasCompactSupport hGs
  have hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P := by
    have e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y') := by
      intro y'
      simp only [Et.descFn, hker, G]
      rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]
    simp only [fourB, e]
    rw [← hmapj, integral_map hjm.aemeasurable (by
      rw [hmapj]; exact (hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]
  rw [hL, integral_integral_swap hGi]
  simp only [Et.descFn]
  rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]
  congr 1
  funext g
  have e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) *
      ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ) := by
    intro v
    simp only [G, actU, hstar]
    ring
  simp_rw [e1]
  rw [integral_mul_const]
  congr 1
  have hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) := by
    have h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1) := by fun_prop
    have h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam)) := by fun_prop
    exact (hfc.comp h2).mul (hψc.comp (htr.comp h1))
  have key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) =
      ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) (g.1 *ᵥ v) ∂P :=
    integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)
  rw [hPg g] at key
  rw [key.symm]
  simp only [fourU]
  rw [hP]
  rfl
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem weilHyp_rg : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ Φ : A.K × A.K → ℂ, Hyp.rg A 1 Φ = Φ) ∧ ∀ (g h : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), Hyp.rg A g (Hyp.rg A h Φ) = Hyp.rg A (g * h) Φ := by
  intro F E _ _ _ _ _ A
  refine ⟨fun Φ => ?_, fun g h Φ => ?_⟩
  · funext p
    simp [Hyp.rg]
  · funext p
    have hm : ((g * h : Matrix.SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) =
        (g : Matrix (Fin 2) (Fin 2) A.K) * (h : Matrix (Fin 2) (Fin 2) A.K) := Matrix.SpecialLinearGroup.coe_mul g h
    unfold Hyp.rg
    rw [hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    congr 1
    ext <;> ring

theorem weilHyp_nS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x z : A.K) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => A.psiK ψ (z * x * (p.1 * p.2)) * Φ p) = Hyp.rg A (nS z) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν ψ x z Φ
  funext p
  simp only [Hyp.pt, Hyp.rg, nS, fourB, Hyp.kx, Et.psiK]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add]
  congr 1
  funext b
  rw [show x * b * (p.1 * z + p.2) = z * x * (p.1 * b) + x * b * p.2 by ring, map_add (f := _), AddChar.map_add_eq_mul]
  ring

theorem weil_hyperbolic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  intro F E _ _ _ _ _ A ψ hψ hK hL x μ hμ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField F E A hK hL
  obtain ⟨hci, hcc, hN, hker, hsm, hunit⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK F E A ψ hψ x
  have hνH : ν.IsAddHaarMeasure := hν.1
  have hT := GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hνH
  have hDD := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ (x : A.K) ν hν
  obtain ⟨hTcc, hTci⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e hci hcc
  obtain ⟨hTrg, hTneg, hTsc, hTmul, hTlin⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations F E A
  obtain ⟨hpsi, hkerlc⟩ := GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ
  obtain ⟨hrg1, hrgm⟩ := weilHyp_rg F E A
  have hlin := GlobalTheory.T.hyperbolicPartialFourier_linear_on_test F E A ψ hψ (x : A.K) ν hνH
  set P := Hyp.pt A ν ψ (x : A.K) with hP
  have h4 : ∀ Φ, IsTest Φ → P (P (P (P Φ))) = Φ := by
    intro Φ hΦ
    rw [hDD Φ hΦ, hDD _ (hTneg Φ hΦ)]
    funext p
    simp
  have hW : ∀ g φ, Hyp.wHyp A e ν ψ x g φ = fun y => P (P (P (Hyp.rg A g (P (fun p => φ (Hyp.cc A e p)))))) (Hyp.ci A e y) :=
    fun _ _ => rfl

  have hkey : ∀ g φ (Φ' : A.K × A.K → ℂ), IsTest Φ' → Hyp.rg A g (P (fun p => φ (Hyp.cc A e p))) = P Φ' →
      Hyp.wHyp A e ν ψ x g φ = fun y => Φ' (Hyp.ci A e y) := by
    intro g φ Φ' hΦ' h
    rw [hW, h, h4 Φ' hΦ']
  have hetaK : ∀ s : A.Kˣ, A.etaK s = 1 := by
    intro s
    have h1 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.1 (Hyp.cc A e ((s : A.K), 1)) (hunit s)
    rwa [hN, mul_one] at h1
  refine ⟨Hyp.wHyp A e ν ψ x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g φ hφ
    rw [hW]
    exact hTci _ (hT _ (hT _ (hT _ (hTrg g _ (hT _ (hTcc φ hφ))))))
  · intro φ hφ
    rw [hW, hrg1, h4 _ (hTcc φ hφ)]
    funext y
    show φ (Hyp.cc A e (Hyp.ci A e y)) = φ y
    rw [hcc]
  · intro g h φ hφ
    have hin : (fun p => Hyp.wHyp A e ν ψ x h φ (Hyp.cc A e p)) = P (P (P (Hyp.rg A h (P (fun p => φ (Hyp.cc A e p)))))) := by
      funext p
      rw [hW]
      simp only [hci]
    rw [hW (g * h) φ, hW g (Hyp.wHyp A e ν ψ x h φ), hin, h4 _ (hTrg h _ (hT _ (hTcc φ hφ))), hrgm]
  · intro g c φ φ' hφ hφ'
    have hc1 : (fun p => (c • φ + φ') (Hyp.cc A e p)) = c • (fun p => φ (Hyp.cc A e p)) + (fun p => φ' (Hyp.cc A e p)) := rfl
    have t1 := hTcc φ hφ
    have t2 := hTcc φ' hφ'
    have hrl : ∀ (Φ Φ' : A.K × A.K → ℂ), Hyp.rg A g (c • Φ + Φ') = c • Hyp.rg A g Φ + Hyp.rg A g Φ' := fun _ _ => rfl
    rw [hW, hW, hW, hc1, hlin c _ _ t1 t2, hrl, hlin c _ _ (hTrg g _ (hT _ t1)) (hTrg g _ (hT _ t2)),
      hlin c _ _ (hT _ (hTrg g _ (hT _ t1))) (hT _ (hTrg g _ (hT _ t2))),
      hlin c _ _ (hT _ (hT _ (hTrg g _ (hT _ t1)))) (hT _ (hT _ (hTrg g _ (hT _ t2))))]
    rfl
  · intro φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro z y
      have hΦ : IsTest (fun p : A.K × A.K => A.psiK ψ (z * (x : A.K) * (p.1 * p.2)) * φ (Hyp.cc A e p)) :=
        hTmul _ _ (hpsi.comp_continuous (by fun_prop)) (hTcc φ hφ)
      rw [hkey (nS z) φ _ hΦ (weilHyp_nS F E A ν ψ (x : A.K) z _).symm]
      simp only
      rw [← hN, hcc]
    · intro s y
      have hΦ : IsTest (fun p : A.K × A.K => (A.absK (s : A.K) : ℂ) * φ (Hyp.cc A e ((s : A.K) * p.1, (s : A.K) * p.2))) :=
        hTmul _ _ (IsLocallyConstant.const _) (hTsc s _ (hTcc φ hφ))
      rw [hkey (mS s) φ _ hΦ (GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction F E A ν hνH ψ (x : A.K) s (fun p => φ (Hyp.cc A e p))).symm]
      simp only
      rw [hetaK, one_mul, ← hsm, hcc]
    · intro y
      rw [one_mul]
      exact GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL F E A ψ (x : A.K) e ν μ hT hDD (fun Φ hΦ => hTrg _ Φ hΦ) hTcc hcc (hker ψ (x : A.K))
        (hkerlc (x : A.K)) (GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords F E A ψ hψ x e he hse ν μ hν hμ) φ hφ y

end GlobalTheory.JR
end

section

noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]


omit [NeZero e] in
theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ

  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
  Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
end
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL.Tconn

theorem N_vpow {K : Type} [NormedField K] (e A' : ℕ) :
    N K (((X : K⟦X⟧) ^ e) ^ A') = ((e * A' : ℕ) : K⟦X⟧) * ((X : K⟦X⟧) ^ e) ^ A' := by
  ext n
  rw [coeff_N, ← pow_mul, ← map_natCast (C (R := K)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem N_lpow {K : Type} [NormedField K] (l b : ℕ) : N K ((l : K⟦X⟧) ^ b) = 0 := by
  rw [← Nat.cast_pow]; exact Derivation.map_natCast _ _

theorem part_top {K O κ : Type} {a : ℕ} [NormedField K] [CommRing O] [Algebra O K]
    (V : Submodule O (Vec K a κ)) : GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ V = V := by
  ext v; simp [GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part]

end GlobalTheory.CokerL.Tconn

theorem GlobalTheory.CokerL.Tsub_conn : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F A' b hred x hx
  have hIS := (hred.2.2 ι κ η H D₁ D₂ F).2.1
  have hMH := (hred.2.1 κ η H D₂).1
  have hvS : ((X : K⟦X⟧) ^ e) ^ A' ∈ S O K e := pow_mem (pow_mem HasU.X_mem e) A'
  have hHigh : ∀ (f : K⟦X⟧), f ∈ S O K e → ∀ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod,
      f • q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod := fun f hf q hq =>
    (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • D₂.MM).smul_mem (⟨f, hf⟩ : S O K e) hq
  have hnat : ∀ (n : ℕ) (q : Vec K a κ) (V : Submodule O (Vec K a κ)), q ∈ V → ((n : K⟦X⟧)) • q ∈ V :=
    fun n q V hq => by
      rw [Nat.cast_smul_eq_nsmul]; exact V.nsmul_mem hq n
  obtain ⟨x12, h12, x3, h3, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨x1, h1, x2, h2, rfl⟩ := Submodule.mem_sup.1 h12
  rw [map_add (f := _), map_add (f := _)]
  refine add_mem (add_mem ?_ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := h1
    change D₂.toPhiMod.conn (((X : K⟦X⟧) ^ e) ^ A' • y) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_vpow, mul_smul]
    refine add_mem ?_ ?_
    · have : ((e * A' : ℕ) : K⟦X⟧) • y ∈ (F.imL.restrictScalars O) := hnat _ _ _ hy
      rw [smul_comm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, this, rfl⟩)
    · have hc := hIS y (by
        rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top]
        exact Submodule.mem_sup_left hy)
      rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
      rw [← hpq, smul_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨p, hp, rfl⟩))
        (Submodule.mem_sup_right (hHigh _ hvS q hq))
  · obtain ⟨z, hz, rfl⟩ := h2
    change D₂.toPhiMod.conn (((l : K⟦X⟧) ^ b) • z) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_lpow, zero_smul, zero_add]
    have hzM : z ∈ D₂.MM := PhiMod.ext_mono _ (A_le_S l e) hz
    have hc : D₂.conn z ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) := by
      rw [GlobalTheory.CokerL.Tconn.part_top]
      exact BKDat.conn_mem_MM D₂ hzM
    rw [hMH.MM_eq, GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
    change (l : K⟦X⟧) ^ b • D₂.toPhiMod.conn z ∈ _
    rw [← hpq, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨p, hp, rfl⟩)) ?_
    refine Submodule.mem_sup_right ?_
    rw [← Nat.cast_pow]
    exact hnat _ _ _ hq
  · have := hMH.conn_high x3 (by rw [GlobalTheory.CokerL.Tconn.part_top]; exact h3)
    rw [GlobalTheory.CokerL.Tconn.part_top] at this
    exact Submodule.mem_sup_right this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | (intros; apply GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a → ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧ ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  first | exact @GlobalTheory.CuspGeneric.mir_exists_row | exact GlobalTheory.CuspGeneric.mir_exists_row | (intros; apply GlobalTheory.CuspGeneric.mir_exists_row <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untilt_norm_ultrametric_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Per.Fl l), ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤ max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧ (x.untilt = 0 → x = 0) := by
  first | exact @GlobalTheory.TiltAbs.untilt_ultrametric_definite | exact GlobalTheory.TiltAbs.untilt_ultrametric_definite | (intros; apply GlobalTheory.TiltAbs.untilt_ultrametric_definite <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Formalism.Per.Acris l, ((l : ℕ) : Formalism.Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : Formalism.Per.Acris l)}) (Formalism.Per.Acris l) ∧ (∀ (k : ℕ) (x : Formalism.Per.Acris l), ∃ d : ↥(Formalism.Per.Acris0 l), x - algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k}) ∧ ∀ (k : ℕ) (d : ↥(Formalism.Per.Acris0 l)), algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k} ↔ d ∈ Ideal.span {((l : ℕ) : ↥(Formalism.Per.Acris0 l)) ^ k} := by
  intro l _
  obtain ⟨hc, ht, hd, hv⟩ := GlobalTheory.MemLoc.acris_basic l
  refine ⟨ht, hc, fun k x => ?_, fun k d => ?_⟩
  · obtain ⟨s, z, hz⟩ := hd x k
    exact ⟨s, Ideal.mem_span_singleton.2 ⟨z, by rw [hz, add_sub_cancel_left]⟩⟩
  · rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact hv d k

end GlobalTheory.Per
end
