module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.WeilBound.ThetaLifts.WeilDomination.FacNeGauss
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle085
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaLineSmoothF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Form

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)

theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ (x + x') y = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ x (y + y') = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_zero_right (y : WOF F E nS nT) : symplOHF σ JS JT ξ y 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ y 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT ξ 0 y = 0 := by
  have := symplOHF_add_left σ JS JT ξ 0 0 y
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem sum_reorder {A : Type} [CommRing A] {m n : ℕ} (c : A → A) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (x y : Matrix (Fin n) (Fin m) A) :
    ∑ a, ∑ b, ∑ c', ∑ d, P a b * c (y c' b) * Q c' d * x d a =
      ∑ i, ∑ j, ∑ k, ∑ l, c (yᵀ i j) * P k i * Q j l * xᵀ k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Matrix.transpose_apply]; ring

theorem snd_symplOHF (x y : WOF F E nS nT) (h : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ x y) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : sndA F (symplOF σ JS JT ξ x y) = 0 := by
    unfold symplOF hOF
    rw [sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero (sndA F) σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (Or.inr ?_)
    ext i j
    exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem continuous_symplOHF {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ (x t) (y t) := by
  apply GlobalTheory.WeilContF.continuous_symplOHF <;> assumption

end Form

theorem exists_log {ψ : AddChar (AF F) ℂ} {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by
        simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

theorem contDiff_deriv_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)

end GlobalTheory.ThetaLineSmoothF
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.NormOne

theorem algebraMap_norm_eq_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (β : Module.Basis (Fin 2) R A) (h0 : β 0 = 1) (C : R) (hC : β 1 * β 1 = algebraMap R A C)
    (s : A →ₐ[R] A) (hs : s (β 1) = -β 1) (z : A) :
    algebraMap R A (Algebra.norm R z) = z * s z := by
  apply GlobalTheory.Published.algebraMap_norm_of_basis_one_sqrt <;> assumption

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have h1 := h.2.2.2 τ x
    rw [hc x] at h1
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]
    exact h1.symm
  exact (NumberField.InfinitePlace.isComplex_mk_iff.mp (h.2.1.isComplex _)) hr

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (bE : Module.Basis (Fin 2) F E) (c : F), bE 0 = 1 ∧ σ (bE 1) = -bE 1 ∧ bE 1 * bE 1 = algebraMap F E c := by
  obtain ⟨x, hx⟩ := exists_moved h
  set θ := x - σ x with hθ
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, invol h]; ring
  have hθ0 : θ ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0).symm
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add (f := _), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower, map_one, hσθ, map_zero] at h2
    have h3 : (2 * t) • θ = 0 := by
      have : (2 * t) • θ = (s • (1 : E) + t • θ) - (s • 1 + t • -θ) := by
        rw [smul_neg, mul_smul, two_smul]; abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
      · exact absurd h4 hθ0
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero, smul_eq_zero] at hst
    exact hst.resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let bE := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑bE = ![(1 : E), θ] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : bE 0 = 1 := by rw [hb]; rfl
  have hb1 : bE 1 = θ := by rw [hb]; rfl
  set p := bE.repr (θ * θ) 0
  set q := bE.repr (θ * θ) 1
  have hsq : θ * θ = p • (1 : E) + q • θ := by
    have h5 := bE.sum_repr (θ * θ)
    rw [Fin.sum_univ_two, hb0, hb1] at h5
    exact h5.symm
  have hsq' : θ * θ = p • (1 : E) - q • θ := by
    have h6 := congrArg σ hsq
    rw [map_mul, hσθ, map_add (f := _), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower, map_one, hσθ, neg_mul_neg, smul_neg] at h6
    rw [h6, sub_eq_add_neg]
  have hq : q = 0 := by
    have h7 : (2 * q) • θ = 0 := by
      have : (2 * q) • θ = (p • (1 : E) + q • θ) - (p • (1 : E) - q • θ) := by
        rw [mul_smul, two_smul]; abel
      rw [this, ← hsq, ← hsq', sub_self]
    rcases smul_eq_zero.mp h7 with h8 | h8
    · exact (mul_eq_zero.mp h8).resolve_left two_ne_zero
    · exact absurd h8 hθ0
  refine ⟨bE, p, hb0, by rw [hb1]; exact hσθ, ?_⟩
  rw [hb1, hsq, hq, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

theorem norm_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ z : AE F E, z * cA σ z = 1 → Algebra.norm (AF F) z = 1 := by
  intro F E _ _ _ _ _ σ h z hz
  obtain ⟨bE, c, h0, h1, hc⟩ := exists_basis h
  let β := Algebra.TensorProduct.basis (AF F) bE
  have hβ : ∀ i, β i = (1 : AF F) ⊗ₜ[F] bE i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hβ0 : β 0 = 1 := by rw [hβ, h0]; rfl
  have hβC : β 1 * β 1 = algebraMap (AF F) (AE F E) (algebraMap F (AF F) c) := by
    rw [hβ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hc, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one (A := E) c, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one (A := AF F) c]
    rfl
  have hs : cA σ (β 1) = -β 1 := by
    rw [hβ, cA, Algebra.TensorProduct.map_tmul, h1, TensorProduct.tmul_neg]
    rfl
  have key := algebraMap_norm_eq_mul β hβ0 _ hβC (cA σ) hs z
  rw [hz] at key
  have e : ∀ r : AF F, β.repr (algebraMap (AF F) (AE F E) r) 0 = r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, ← hβ0, map_smul, Module.Basis.repr_self]
    simp
  rw [← e (Algebra.norm (AF F) z), key, ← map_one (algebraMap (AF F) (AE F E)), e]

end GlobalTheory.NormOne
end

section

noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace GlobalTheory.GaussNonvanish

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd, ← map_pow]
  rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  exact pow_lt_one' h (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  have h1 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c) - 1) ≤
      valuation k (ϖ : k) ^ c := by
    have := (mk_eq_mk_iff hϖ c (Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) 1).1
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one])
    simpa [rep] using this
  have h2 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) = 1 := by
    have := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt_one hϖ hc))
    simpa using this
  rw [map_mul] at h2
  refine le_antisymm (rep_le_one _) ?_
  calc (1 : ValueGroupWithZero k) = _ := h2.symm
    _ ≤ _ := mul_le_of_le_one_right' (rep_le_one _)

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have := val_rep_unit hϖ hc y
  rw [h, map_zero] at this
  exact zero_ne_one this

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  rw [show a = b + (a - b) by ring, hadd, hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  have hlt : valuation k ((a : k) - b) < valuation k (b : k) := by
    rw [hb]; exact h.trans_lt (val_pow_lt_one hϖ hc1)
  have ha : valuation k (a : k) = 1 := ((valuation k).map_eq_of_sub_lt hlt).trans hb
  have hw : a * b⁻¹ ∈ unitCong (ϖ ^ c) := by
    refine ⟨by simp [ha, hb], ?_⟩
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ b.ne_zero]
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one, Units.val_pow_eq_pow_val, map_pow]
    exact h
  have := hc _ hw
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

end Generic
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

end Sums
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  apply PositivityTheory.ThK.GaussNe.exists_condLE <;> assumption

end Main
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end Place
end GlobalTheory.GaussNonvanish
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (v : D), GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = ((∑ a, ∑ b, Z a b • E a b v : D) : H) := by
  first | exact @GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum | exact GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum | (intros; apply GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum <;> assumption)
end
