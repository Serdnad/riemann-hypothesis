module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_sum {κ : Type} [Fintype κ] (g : κ → AF F) : evI F (∑ i, g i) = ∑ i, evI F (g i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem mul_realAd_eq_zero {a : AF F} (ha : evI F a = 0) (t : ℝ) : a * realAd F t = 0 := by
  have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
  have h2 : (realAd F t).2 = 0 := rfl
  show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
  rw [h1, h2, zero_mul, mul_zero]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trForm {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
      (∑ i, (LinearMap.mulRight ℝ (evI F (y i))).comp (LinearMap.proj i)))

theorem trForm_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    trForm F y z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * evI F (y i)) := by
  simp [trForm, LinearMap.sum_apply]


variable (F) in
def mult {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (trForm F y))

theorem mult_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = -(2 * Real.pi * Complex.I) * (trForm F y z : ℂ) := by
  simp [mult]


variable (F) in
def heisD {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    SInf F κ →ₗ[ℂ] SInf F κ :=
  (LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v + SchwartzMap.smulLeftCLM ℂ (⇑(mult F y))).toLinearMap

theorem heisD_apply {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) (f : SInf F κ)
    (z : κ → mixedEmbedding.mixedSpace F) :
    heisD F v y f z = fderiv ℝ f z v + mult F y z * f z := by
  have h : (⇑(mult F y)).HasTemperateGrowth := (mult F y).hasTemperateGrowth
  simp [heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem exists_heisLine_deriv {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  refine ⟨heisD F v y₁, fun f r hr x => ?_⟩
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add (f := _),
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

end GlobalTheory.HeisDeriv


open GlobalTheory.HeisDeriv in
theorem GlobalTheory.HeisDeriv.exists_actsD_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) :=
  fun M ψ hψ u _ => exists_heisLine_deriv M ψ hψ u
end
end

section

noncomputable section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.FiniteAdelicPoints

theorem exists_functional {ι V : Type} [AddCommGroup V] [Module ℂ V] (p : ι → V) (a : ι → ℂ)
    (h : ∀ (s : Finset ι) (c : ι → ℂ), ∑ i ∈ s, c i • p i = 0 → ∑ i ∈ s, c i * a i = 0) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ i, Λ (p i) = a i := by
  classical

  let P : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ p
  let A : (ι →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ a

  have hk : LinearMap.ker P ≤ LinearMap.ker A := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h0 : ∑ i ∈ c.support, c i • p i = 0 := by
      simpa [P, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    simpa [A, Finsupp.linearCombination_apply, Finsupp.sum] using h c.support c h0

  let B : LinearMap.range P →ₗ[ℂ] ℂ :=
    ((LinearMap.ker P).liftQ A hk).comp (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend B
  refine ⟨Λ, fun i => ?_⟩
  have hp : P (Finsupp.single i 1) = p i := by simp [P]
  have hA : A (Finsupp.single i 1) = a i := by simp [A]
  calc Λ (p i) = Λ (P (Finsupp.single i 1)) := by rw [hp]
    _ = B ⟨P (Finsupp.single i 1), LinearMap.mem_range_self P _⟩ := by rw [← hΛ]; rfl
    _ = A (Finsupp.single i 1) := by
      simp only [B, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = a i := hA

theorem sum_prod_apply {ι P : Type} {X : P → Type} [∀ v, Nonempty (X v)] (s : Finset ι) (φ : ι → ∀ v, X v → ℂ)
    (l : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) (T : Finset P) :
    ∀ c : ι → ℂ, (∀ y : ∀ v, X v, ∑ i ∈ s, c i * ∏ v ∈ T, φ i v (y v) = 0) →
      ∑ i ∈ s, c i * ∏ v ∈ T, l v (φ i v) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    simpa using hc (fun v => Classical.arbitrary (X v))
  | insert w T hw ih =>
    intro c hc

    have key : ∀ y : ∀ v, X v, ∑ i ∈ s, (c i * l w (φ i w)) * ∏ v ∈ T, φ i v (y v) = 0 := by
      intro y
      have hfun : (∑ i ∈ s, (c i * ∏ v ∈ T, φ i v (y v)) • φ i w) = 0 := by
        funext t
        have hupd : ∀ i, ∏ v ∈ T, φ i v (Function.update y w t v) = ∏ v ∈ T, φ i v (y v) := fun i =>
          Finset.prod_congr rfl fun v hv => by
            rw [Function.update_of_ne (fun h => hw (by rw [← h]; exact hv))]
        have h1 := hc (Function.update y w t)
        simp only [Finset.prod_insert hw, Function.update_self, hupd] at h1
        rw [Finset.sum_apply, Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring

      have h2 := congrArg (l w) hfun

      rw [map_sum, map_zero] at h2
      simp only [map_smul, smul_eq_mul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h3 := ih (fun i => c i * l w (φ i w)) key
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_insert hw]
    ring

variable {F : Type} [Field F] [NumberField F]


open Classical in
def finAd (T : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then y v else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [hv, if_false]
    exact zero_mem _⟩

def adPt {κ : Type} (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F :=
  fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x k), finAd T fun v => y v k)


open Classical in
theorem pure_apply {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hφ : ∀ v ∉ T, φ v 0 = 1) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (adPt T x y) = f x * ∏ v ∈ T, φ v (y v) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

  have h1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (adPt T x y i)) = x := by
    funext i
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)

  have h2 : ∀ v, (fun i => GlobalTheory.AdelicU.evFin F v (adPt T x y i)) =
      fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := fun v => by
    funext i
    rfl
  rw [h1]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [h2 v]
    simp only [if_pos hv]
  · intro v hv
    by_contra hvT
    have hvT' : v ∉ T := by simpa using hvT
    have h0 : (fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) = 0 := by
      funext i
      simp [hvT']
    rw [Function.mem_mulSupport, h2 v, h0] at hv
    exact hv (hφ v hvT')

theorem exists_functional_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)
    (hvac : ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, vac v =
      Set.indicator {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ (i : κ), x i ∈ HeightOneSpectrum.adicCompletionIntegers F v}
        (1 : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ))
    (lam : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ℂ)
    (l : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : Set.Finite {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | l v (vac v) ≠ 1}) :
    ∃ (Λ : ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) →ₗ[ℂ] ℂ),
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ v = vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l v (φ v) := by
  classical

  obtain ⟨Λ, hΛ⟩ := exists_functional
    (ι := {q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ × ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) //
      ∀ᶠ v in Filter.cofinite, q.2 v = vac v})
    (fun q => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure q.1.1 q.1.2) (fun q => lam q.1.1 * ∏ᶠ v, l v (q.1.2 v)) (by
    intro s c hc

    have f1 := Filter.eventually_cofinite.1 hvac
    have f2 := s.finite_toSet.biUnion fun q _ => Filter.eventually_cofinite.1 q.2
    let T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := ((hl.union f1).union f2).toFinset
    have hout : ∀ v ∉ T, l v (vac v) = 1 ∧ (∀ q ∈ s, q.1.2 v = vac v) ∧ vac v 0 = 1 := by
      intro v hv
      simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe,
        not_or, not_exists, not_not, ne_eq] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      refine ⟨hv0, fun q hq => hv2 q hq, ?_⟩
      rw [hv1]
      have hz : (0 : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈
          {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
        fun i => zero_mem _
      rw [Set.indicator_of_mem hz, Pi.one_apply]

    have hrel : ∀ (x : κ → mixedEmbedding.mixedSpace F) (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        ∑ q ∈ s, c q * (q.1.1 x * ∏ v ∈ T, q.1.2 v (y v)) = 0 := by
      intro x y
      have h0 := congrFun hc (adPt T x y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [pure_apply q.1.1 q.1.2 T (fun v hv => by rw [(hout v hv).2.1 q hq, (hout v hv).2.2]) x y]

    have hrel2 : ∀ y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v,
        ∑ q ∈ s, (c q * lam q.1.1) * ∏ v ∈ T, q.1.2 v (y v) = 0 := by
      intro y
      have hz : ∑ q ∈ s, (c q * ∏ v ∈ T, q.1.2 v (y v)) • q.1.1 = 0 := by
        ext x
        simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply]
        rw [← hrel x y]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      have h0 := congrArg lam hz

      rw [map_sum, map_zero] at h0
      simp only [map_smul, smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring

    have h3 := sum_prod_apply s (fun q v => q.1.2 v) l T (fun q => c q * lam q.1.1) hrel2
    rw [← h3]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · ring
    · intro v hv
      by_contra hvT
      rw [Function.mem_mulSupport, (hout v (by simpa using hvT)).2.1 q hq] at hv
      exact hv (hout v (by simpa using hvT)).1)
  exact ⟨Λ, fun f φ hφ => hΛ ⟨(f, φ), hφ⟩⟩

end GlobalTheory.FiniteAdelicPoints

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.MatrixLeftInverseLift

theorem matrix_left_inverse_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  intro F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂
  choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)
  let Zm : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of Z
  have hZm : ∀ u, evFin F v u = 0 → u • Zm = 0 := by
    intro u hu; ext i j; simpa [Zm] using hZA i j u hu
  have hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N := by
    intro π N hπ
    ext i j
    have h := hπ i j
    by_cases hij : i = j
    · subst hij; simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]
    · simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]
  have hM₁ := hmap π₁ N₁ hZ₁
  have hM₂ := hmap π₂ N₂ hZ₂
  refine ⟨Zm + 1, ?_, hM₁, hM₂⟩
  have hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]; abel
  have hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0 := by
    intro u hu
    rw [hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]; simp
  have hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0 := by
    intro π N hM hN
    have : π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1 := by
      rw [map_sub, map_mul, map_one]
    change π.mapMatrix ((Zm + 1) * K - 1) = 0
    rw [this]; change (Zm + 1).map π * K.map π - 1 = 0
    rw [hM, hN, sub_self]
  have e₁ := hπ π₁ N₁ hM₁ h₁
  have e₂ := hπ π₂ N₂ hM₂ h₂
  rw [← sub_eq_zero]
  ext i j
  apply hinj
  · intro u hu
    have := congrArg (fun m => m i j) (hAt u hu)
    simpa using this
  · simpa using congrArg (fun m => m i j) e₁
  · simpa using congrArg (fun m => m i j) e₂

end GlobalTheory.MatrixLeftInverseLift
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TwistBlockK

theorem atK_sub_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  intro F E _ _ _ _ _ d v g Y hg hY u hu
  have hgu := hg u hu
  have hYu : u • Y = 0 := hY u hu
  rw [smul_sub, sub_eq_zero] at hgu
  have h11 : u • g.toBlocks₁₁ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have h22 : u • g.toBlocks₂₂ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  have h12 : u • g.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have h21 : u • g.toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply] using this
  rw [smul_sub, smul_add, ← Matrix.smul_mul, hYu, Matrix.zero_mul, add_zero,
    smul_comm u (⅟(2 : AF F))]
  simp only [smul_add, h11, h12, h21, h22, add_zero]
  rw [← add_smul, invOf_two_add_invOf_two, one_smul, sub_self]

end GlobalTheory.TwistBlockK
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Matrix

namespace GlobalTheory.FockVacStab

theorem mat_mul_mat_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (k : UA σ X.J) : mat k * mat k⁻¹ = 1 ∧ mat k⁻¹ * mat k = 1 := by
  constructor
  · show (k * k⁻¹).1.1 = 1
    simp
  · show (k⁻¹ * k).1.1 = 1
    simp

end GlobalTheory.FockVacStab
end
