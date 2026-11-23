module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

theorem measurePreserving_piCurry_symm {V : Type} [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    {X : ∀ v, α v → Type} [∀ v a, MeasurableSpace (X v a)] (μ : ∀ v a, Measure (X v a))
    [∀ v a, SigmaFinite (μ v a)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm (Measure.pi fun v => Measure.pi fun a => μ v a)
      (Measure.pi fun p : Σ v, α v => μ p.1 p.2) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun v => Set.univ.pi fun a => s ⟨v, a⟩ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    exact Iff.rfl
  rw [e, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

theorem measurePreserving_of_normSq {ι V : Type} [Fintype ι] [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v))) (hbij : Function.Bijective T)
    (hn : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) :
    MeasurePreserving T volume (Measure.pi fun _ => volume) := by

  let F : (∀ v, EuclideanSpace ℝ (α v)) →ₗ[ℝ] EuclideanSpace ℝ (Σ v, α v) :=
    { toFun := fun z => WithLp.toLp 2 (fun p : Σ v, α v => z p.1 p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hFn : ∀ z, ‖F z‖ ^ 2 = ∑ v, ‖z v‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hF : MeasurePreserving F (Measure.pi fun v => volume) volume := by
    have h1 := measurePreserving_pi (fun v => (volume : Measure (EuclideanSpace ℝ (α v))))
      (fun v => (volume : Measure (α v → ℝ)))
      (fun v => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (α v))
    have h2 := measurePreserving_piCurry_symm (X := fun v (_ : α v) => ℝ) (fun _ _ => (volume : Measure ℝ))
    have h3 := PiLp.volume_preserving_toLp (Σ v, α v)
    simp only [← MeasureTheory.volume_pi] at h2
    exact (h3.comp (h2.comp h1))
  have hGn : ∀ x, ‖F (T x)‖ = ‖x‖ := by
    intro x
    have := hFn (T x)
    rw [hn x] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  let G : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Σ v, α v) := ⟨F ∘ₗ T, hGn⟩
  have hFi : Function.Injective F := by
    intro z z' h
    funext v
    ext a
    have := congrArg (fun w : EuclideanSpace ℝ (Σ v, α v) => w ⟨v, a⟩) h
    exact this
  have hFs : Function.Surjective F := by
    intro w
    exact ⟨fun v => WithLp.toLp 2 (fun a => w ⟨v, a⟩), rfl⟩
  have hGs : Function.Surjective G := (hFs.comp hbij.2)
  let Ge := LinearIsometryEquiv.ofSurjective G hGs
  have hGe : MeasurePreserving Ge volume volume := Ge.measurePreserving
  let Fe : (∀ v, EuclideanSpace ℝ (α v)) ≃ᵐ EuclideanSpace ℝ (Σ v, α v) :=
    { toEquiv := Equiv.ofBijective F ⟨hFi, hFs⟩
      measurable_toFun := hF.measurable
      measurable_invFun := by
        have : ⇑(Equiv.ofBijective F ⟨hFi, hFs⟩).symm =
            fun (w : EuclideanSpace ℝ (Σ v, α v)) (v : V) => (WithLp.toLp 2 (fun a => w ⟨v, a⟩) : EuclideanSpace ℝ (α v)) := by
          funext w
          apply (Equiv.ofBijective F ⟨hFi, hFs⟩).injective
          rw [Equiv.apply_symm_apply]
          rfl
        rw [this]
        exact Measurable.of_eval fun v =>
          (PiLp.volume_preserving_toLp (α v)).measurable.comp
            (Measurable.of_eval fun a => (measurable_pi_apply _).comp (PiLp.volume_preserving_ofLp _).measurable) }
  have hFe : MeasurePreserving Fe (Measure.pi fun v => volume) volume := hF
  have key := hFe.symm.comp hGe
  convert key using 1
  funext x
  show T x = Fe.symm (F (T x))
  exact (Fe.symm_apply_apply (T x)).symm

def piProdEquiv {V : Type} (A B : V → Type) [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSpace (B v)] :
    (∀ v, A v × B v) ≃ᵐ (∀ v, A v) × (∀ v, B v) where
  toFun z := (fun v => (z v).1, fun v => (z v).2)
  invFun p v := (p.1 v, p.2 v)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (Measurable.of_eval fun v => measurable_fst.comp (measurable_pi_apply v)).prodMk
    (Measurable.of_eval fun v => measurable_snd.comp (measurable_pi_apply v))
  measurable_invFun := Measurable.of_eval fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk ((measurable_pi_apply v).comp measurable_snd)

theorem measurePreserving_piProdEquiv {V : Type} [Fintype V] (A B : V → Type) [∀ v, MeasurableSpace (A v)]
    [∀ v, MeasurableSpace (B v)] (μ : ∀ v, Measure (A v)) (ν : ∀ v, Measure (B v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] :
    MeasurePreserving (piProdEquiv A B) (Measure.pi fun v => (μ v).prod (ν v))
      ((Measure.pi fun v => μ v).prod (Measure.pi fun v => ν v)) := by
  refine ⟨(piProdEquiv A B).measurable, ?_⟩
  refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
    (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
    · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
  · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
    rw [MeasurableEquiv.map_apply]
    rw [show (piProdEquiv A B) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        (Set.univ.pi fun i ↦ s i ×ˢ t i) by
        ext; simp [Set.mem_pi, forall_and, piProdEquiv]]
    simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end PI.AprimeInfG
end
end

section

noncomputable section

open Matrix TensorProduct

namespace HcS.UG

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  simp [cT, Matrix.map_one]

def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def Upq (p q : ℕ) : Subgroup (GL (Fin p ⊕ Fin q) ℂ) := UJ (starRingEnd ℂ) (Jpq p q)

end Points

section Split

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

end Split

section Abstract

variable {G : Type} [Group G]

end Abstract

section Tj

variable {L : Type} [Field L]

end Tj

section Coeff

variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]

end Coeff

section More

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

end More

open NumberField IsDedekindDomain

end HcS.UG
end
end

section

noncomputable section

namespace PI.AprimeInfW

open Topology Filter

private theorem local_right_inverse_lemma {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : E → E) (f' : E ≃L[ℝ] E) (a : E)
    (hf : HasStrictFDerivAt F (f' : E →L[ℝ] E) a) :
    ∃ φ : E → E, ContinuousAt φ (F a) ∧ φ (F a) = a ∧ ∀ᶠ y in 𝓝 (F a), F (φ y) = y :=
  ⟨hf.localInverse F f' a, hf.localInverse_continuousAt, hf.localInverse_apply_image,
    hf.eventually_right_inverse⟩

theorem exists_local_solve {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      ∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y := by
  have hs : ∀ a b : Fin N → ℝ, e.symm (a + b) = e.symm a + e.symm b := fun a b =>
    e.injective (by rw [he]; simp)
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun z w => e (B (e.symm z) (e.symm w))
  have hb1 : ∀ z z' w, b (z + z') w = b z w + b z' w := fun z z' w => by
    simp only [b]; rw [hs, hB1, he]
  have hb2 : ∀ z w w', b z (w + w') = b z w + b z w' := fun z w w' => by
    simp only [b]; rw [hs, hB2, he]
  have hpair : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => (e.symm p.1, e.symm p.2) :=
    (e.symm.continuous.comp continuous_fst).prodMk (e.symm.continuous.comp continuous_snd)
  have hbc : Continuous fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2 :=
    e.continuous.comp (hBc.comp hpair)
  have hb3 : ∀ (c : ℝ) z w, b (c • z) w = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun z => b z w) fun z z' => hb1 z z' w)
      (hbc.comp (continuous_id.prodMk continuous_const)) c z
  have hb4 : ∀ (c : ℝ) z w, b z (c • w) = c • b z w := fun c z w =>
    map_real_smul (AddMonoidHom.mk' (fun w => b z w) fun w w' => hb2 z w w')
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun z => e (L (e.symm z))
  have hl1 : ∀ z z', l (z + z') = l z + l z' := fun z z' => by
    simp only [l]; rw [hs, hL, he]
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  let lc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  let β₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hb3 hb2 hb4
  let βc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ β₂)
  have hF : ∀ z, e (B (e.symm z) (e.symm z) + L (e.symm z)) = βc z z + lc z := fun z => by
    rw [he]; rfl
  have hD' : ∀ u, βc (e x0) u + βc u (e x0) + lc u = (2 : ℝ) • u := fun u => by
    show e (B (e.symm (e x0)) (e.symm u)) + e (B (e.symm u) (e.symm (e x0))) + e (L (e.symm u))
      = (2 : ℝ) • u
    rw [← he, ← he, e.symm_apply_apply, hD, he, e.apply_symm_apply, two_smul]
  have hder : HasStrictFDerivAt (fun z => βc z z + lc z)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)) (e x0) := by
    have h1 := (βc.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id (e x0))
      (hasStrictFDerivAt_id (e x0))).add lc.hasStrictFDerivAt
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    change _ = (2 : ℝ) • u
    rw [← hD' u]
    rfl
  let f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
    (fun u => by simp [smul_smul]) (fun u => by simp [smul_smul])
  have hf : HasStrictFDerivAt (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z)))
      (f' : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (e x0) := by
    have hfun : (fun z => e (B (e.symm z) (e.symm z) + L (e.symm z))) = fun z => βc z z + lc z :=
      funext hF
    rw [hfun]
    exact hder.congr_fderiv (ContinuousLinearMap.ext fun u => rfl)
  obtain ⟨φ, h1, h2, h3⟩ := local_right_inverse_lemma _ f' (e x0) hf
  simp only [e.symm_apply_apply] at h1 h2 h3
  refine ⟨fun y => e.symm (φ (e y)), ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (h1.comp e.continuous.continuousAt)
  · simp only [h2, e.symm_apply_apply]
  · exact (e.continuous.continuousAt.tendsto.eventually h3).mono fun y hy => e.injective hy

end PI.AprimeInfW
end
end
