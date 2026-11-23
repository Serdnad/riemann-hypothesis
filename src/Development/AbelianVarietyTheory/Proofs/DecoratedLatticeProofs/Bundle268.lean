module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn



theorem shift_char_realPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  intro D ψ hψ θ hθ μ hμ
  have hstar : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  set y : D.host.E := -D.host.xi0 / μ with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y := by
    rw [hy_def, map_div₀, map_neg, conj_xi0_alt, ← hstar μ, hμ.2, neg_neg, div_neg, neg_div]
  have hyF : y ∈ D.host.F := (IsCMField.complexConj_eq_self_iff D.host.E y).1 hyc
  have hy0 : y ≠ 0 := div_ne_zero (neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) hμ.1
  let lam : D.host.F := ⟨y, hyF⟩
  have hlam : algebraMap D.host.F D.host.E lam = y := rfl
  have hlam0 : lam ≠ 0 := fun h => hy0 (by rw [← hlam, h, map_zero])
  refine ⟨lam, hlam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψ.1.1.comp (continuous_const.mul continuous_id)
    · intro x; exact hψ.1.2.1 _
    · intro a
      rw [shift, AddChar.mulShift_apply, ← map_mul]
      exact hψ.1.2.2.1 _
    · obtain ⟨x, hx⟩ := hψ.1.2.2.2
      refine ⟨algebraMap D.host.F (AF D.host.F) lam⁻¹ * x, ?_⟩
      rw [shift, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hlam0, map_one, one_mul]
      exact hx
  ·
    have hreal : ∀ τ, (tauE D τ y).im = 0 := by
      intro τ
      have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
      rw [hyc] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    refine ⟨fun τ => -(tauE D τ y).re, ?_, ?_⟩
    · intro x
      have e1 : psiInf D.host.F (shift ψ lam) x =
          psiInf D.host.F ψ (algebraMap D.host.F (Ainf D.host.F) lam * x) := by
        simp only [psiInf, shift, AddChar.mulShift_apply]
        congr 1
        show (algebraMap D.host.F (Ainf D.host.F) lam * x, algebraMap D.host.F (Af D.host.F) lam * 0) = _
        rw [mul_zero]; rfl
      rw [e1, hψ.2.2 θ hθ]
      congr 1
      have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
        intro ρ
        have e3 : (algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
            (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
            ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one, hlam]
        rw [e3, map_mul, (hθ ρ).1]
      simp only [e2]
      have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
        intro ρ
        apply Complex.ext <;> simp [hreal ρ]
      simp only [e4, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring
    · intro τ
      have h1 : |(tauE D τ y).re| = ‖tauE D τ y‖ := by
        rw [← Complex.abs_re_eq_norm.2 (hreal τ)]
      rw [abs_neg, h1, hy_def, map_div₀, map_neg, norm_div, norm_neg]

end GlobalTheory.StdUnn
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem tmulOne_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem scal_gen (σ : E →ₐ[F] E) (μ : E) (hμ : μ ≠ 0)
    (r : ∀ w : InfinitePlace F, w.Completion) (hr : ∀ w, r w ≠ 0)
    (hN : ∀ w, ((1 : w.Completion) ⊗ₜ[F] (μ * σ μ) : w.Completion ⊗[F] E) = 4 * (r w ⊗ₜ[F] (1 : E)) ^ 4)
    (u₀ : (AF F ⊗[F] E)ˣ) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * (u : AF F ⊗[F] E) * sigR (AF F) σ (u : AF F ⊗[F] E) = inclR (AF F) μ ∧
      (∀ v, compFin F E v u = compFin F E v u₀) ∧
      ∀ w, compInf F E w ((ε : AF F ⊗[F] E) * sigR (AF F) σ (ε : AF F ⊗[F] E)) = 4 := by
  set c := sigR (AF F) σ with hc
  set e : AF F ⊗[F] E := pairA F 1 0 ⊗ₜ[F] (1 : E) with he
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have hee : e * e = e := by rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  have hce : c e = e := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hfe : ∀ v, compFin F E v e = 0 := by
    intro v
    refine (tmulOne_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, show sndA F (pairA F 1 0) = 0 from rfl, map_zero, TensorProduct.zero_tmul]
  have hie : ∀ w, compInf F E w e = 1 := by
    intro w
    refine (tmulOne_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, show fstA F (pairA F 1 0) = 1 from rfl, map_one, Algebra.TensorProduct.one_def]
  let R : AF F := pairA F (fun w => r w) 1
  let R' : AF F := pairA F (fun w => (r w)⁻¹) 1
  have hRR : R * R' = 1 := Prod.ext (funext fun w => mul_inv_cancel₀ (hr w)) (mul_one (1 : Af F))
  set a : AF F ⊗[F] E := R ⊗ₜ[F] (1 : E) with ha
  set a' : AF F ⊗[F] E := R' ⊗ₜ[F] (1 : E) with ha'
  have haa : a * a' = 1 := by
    rw [ha, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hRR, Algebra.TensorProduct.one_def]
  have hca : c a = a := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hia : ∀ w, compInf F E w a = r w ⊗ₜ[F] (1 : E) := fun w =>
    tmulOne_map F E (evInf F w) (AlgHom.id F E) _
  have hu0 : (u₀ : AF F ⊗[F] E) * ↑u₀⁻¹ = 1 := Units.mul_inv u₀
  set x : AF F ⊗[F] E := e * a + (1 - e) * u₀ with hx
  set x' : AF F ⊗[F] E := e * a' + (1 - e) * ↑u₀⁻¹ with hx'
  have hxx : x * x' = 1 := by
    rw [hx, hx']
    linear_combination (2 - a * ↑u₀⁻¹ - (u₀ : AF F ⊗[F] E) * a') * hee + e * e * haa + (1 - e) * (1 - e) * hu0
  let U : (AF F ⊗[F] E)ˣ := ⟨x, x', hxx, by rw [mul_comm]; exact hxx⟩

  have hshape : ∀ y, c (e * a + (1 - e) * y) = e * a + (1 - e) * c y := by
    intro y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hce, hca]
  have hread : ∀ w y, compInf F E w (e * a + (1 - e) * y) = r w ⊗ₜ[F] (1 : E) := by
    intro w y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hie, hia]; ring
  let M : (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F) : E →+* AF F ⊗[F] E).toMonoidHom (Units.mk0 μ hμ)
  let P : (AF F ⊗[F] E)ˣ := U * Units.map c.toMonoidHom U
  refine ⟨U, M * P⁻¹, ?_, ?_, ?_⟩
  · have h1 : ((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U) = 1 := by
      have := Units.inv_mul P
      simpa [P] using this
    calc ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * U * c U
        = (M : AF F ⊗[F] E) * (((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U)) := by
          rw [Units.val_mul]; ring
      _ = inclR (AF F) μ := by rw [h1, mul_one]; rfl
  · intro v
    change compFin F E v x = _
    rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, hfe]; ring
  · intro w
    set φ := compInf F E w with hφ
    set ρ : w.Completion ⊗[F] E := r w ⊗ₜ[F] (1 : E) with hρdef
    have hρ : ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
      rw [hρdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ (hr w), Algebra.TensorProduct.one_def]
    have hP : (P : AF F ⊗[F] E) = x * c x := rfl
    have hM : (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] μ := rfl
    have hε : ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (x * c x) = M := by
      rw [← hP, ← Units.val_mul, inv_mul_cancel_right]
    have hε' := congrArg c hε
    rw [map_mul, map_mul] at hε'
    have hall : (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *
        ((x * c x) * (c x * c (c x))) = (M : AF F ⊗[F] E) * c M := by
      rw [← hε', ← hε]; ring
    have hφx : φ x = ρ := hread w _
    have hφcx : φ (c x) = ρ := by rw [hx, hshape, hread]
    have hφccx : φ (c (c x)) = ρ := by rw [hx, hshape, hshape, hread]
    have hcM : c (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] σ μ := by
      rw [hM, hc]
      change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] μ) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hφ1 : ∀ z : E, φ ((1 : AF F) ⊗ₜ[F] z) = (1 : w.Completion) ⊗ₜ[F] z := by
      intro z
      rw [hφ]
      change Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] z) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have hrhs : φ ((M : AF F ⊗[F] E) * c M) = 4 * ρ ^ 4 := by
      rw [map_mul, hcM, hM, hφ1, hφ1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hN w]
    have key := congrArg φ hall
    have hB : φ ((x * c x) * (c x * c (c x))) = ρ * ρ * (ρ * ρ) := by
      rw [map_mul, map_mul, map_mul, hφx, hφcx, hφccx]
    rw [map_mul φ _ ((x * c x) * (c x * c (c x))), hB, hrhs] at key
    linear_combination ((r w)⁻¹ ⊗ₜ[F] (1 : E)) ^ 4 * key -
      (φ (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) - 4) *
        (1 + ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 2 + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 3) * hρ
end

private theorem scal_pos (D : D7) (μ : D.host.E) (hμ : μ ≠ 0) (w : InfinitePlace D.host.F) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)
      (algebraMap D.host.F w.Completion ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩) := by
  set hw := NumberField.IsTotallyReal.isReal w
  set n : D.host.F := ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩ with hn
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  let φ : D.host.E →ₐ[D.host.F] ℂ := by
    exact IsAlgClosed.lift
  have h1 : φ (algebraMap D.host.F D.host.E n) = w.embedding n := φ.commutes n
  have h2 : (algebraMap D.host.F D.host.E n) = μ * star μ := rfl
  have h3 : φ (star μ) = starRingEnd ℂ (φ μ) :=
    IsCMField.complexEmbedding_complexConj D.host.E (φ : D.host.E →+* ℂ) μ
  rw [h2, map_mul, h3, Complex.mul_conj] at h1
  have h4 : ((InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) : ℂ) = w.embedding n := by
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  have h5 : 0 < Complex.normSq (φ μ) := Complex.normSq_pos.2 (by simpa using hμ)
  have h6 := h4.trans h1.symm
  have h7 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) = Complex.normSq (φ μ) := by
    exact_mod_cast h6
  rw [h7]; exact h5

private theorem scal_root (F E : Type) [Field F] [Field E] [Algebra F E] (w : InfinitePlace F) (hw : w.IsReal) (n : F)
    (hn : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion n)) :
    ∃ r : w.Completion, r ≠ 0 ∧
      ((1 : w.Completion) ⊗ₜ[F] (algebraMap F E n) : w.Completion ⊗[F] E) = 4 * (r ⊗ₜ[F] (1 : E)) ^ 4 := by
  set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set t := f (algebraMap F w.Completion n) with ht
  have h0 : 0 < √(√(t / 4)) := by positivity
  have h4 : 4 * (f.symm √(√(t / 4))) ^ 4 = algebraMap F w.Completion n := by
    apply f.injective
    rw [map_mul, map_pow, map_ofNat, RingEquiv.apply_symm_apply, ← ht, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    ring
  refine ⟨f.symm √(√(t / 4)), (map_ne_zero f.symm).2 h0.ne', ?_⟩
  have h5 := congrArg (Algebra.TensorProduct.includeLeftRingHom : w.Completion →+* w.Completion ⊗[F] E) h4
  rw [map_mul, map_pow, map_ofNat, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply] at h5
  rw [h5, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_scal_real : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  intro D μ hμ u₀
  choose r hr hN using fun w : InfinitePlace D.host.F =>
    scal_root D.host.F D.host.E w _ _ (scal_pos D μ hμ.1 w)
  exact scal_gen D.host.F D.host.E D.sp.cm.sig μ hμ.1 r hr hN u₀

end GlobalTheory.StdUnn
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem weyl_cols {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin n) R)
    (T M : Matrix (Fin (n + n)) (Fin (n + n)) R) (hT : T.submatrix id finSumFinEquiv = Matrix.fromCols X Y)
    (h : T * blk4 0 1 (-1) 0 = M * T) : M * X = -Y ∧ M * Y = X := by
  have hJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    simp [blk4]
  have h2 := congrArg (fun N : Matrix (Fin (n + n)) (Fin (n + n)) R => N.submatrix id finSumFinEquiv) h
  beta_reduce at h2
  rw [Matrix.submatrix_mul _ _ id finSumFinEquiv finSumFinEquiv finSumFinEquiv.bijective, hJ,
    Matrix.submatrix_mul _ _ id id finSumFinEquiv Function.bijective_id, Matrix.submatrix_id_id, hT,
    Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols] at h2
  obtain ⟨hX, hY⟩ := Matrix.fromCols_inj h2
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero] at hX hY
  exact ⟨hX.symm, hY.symm⟩

theorem weyl_unscale {R : Type} [CommRing R] {k l m : ℕ} (M : Matrix (Fin k) (Fin l) R) (Y : Matrix (Fin l) (Fin m) R)
    (X : Matrix (Fin k) (Fin m) R) {a b : R} (hab : b * a = 1) (h : M * (a • Y) = X) : M * Y = b • X := by
  rw [← h, Matrix.mul_smul, smul_smul, hab, one_smul]

theorem weyl_kill {R : Type} [CommRing R] {k l m : ℕ} (P : Matrix (Fin k) (Fin l) R) (X Z : Matrix (Fin l) (Fin m) R)
    {b : R} (h : P * X = 0) (hZ : Z = b • X) : P * Z = 0 := by
  rw [hZ, Matrix.mul_smul, h, smul_zero]

theorem mem_GQ_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) (h0 : mt S g ⬝ d.j0 ∈ GlobalTheory.MixModel.ratMx D S.rank S₀.rank)
    (hY : mt S g ⬝ d.jY ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) : g ∈ GQ S := by
  rw [mem_GQ_iff, ← Matrix.mul_one (mt S g), ← d.sum_eq_one, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact add_mem (add_mem (ratMx_mul hX (rat_mem _)) (ratMx_mul h0 (rat_mem _))) (ratMx_mul hY (rat_mem _))

theorem rat_Tm_cols {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).submatrix id finSumFinEquiv =
      Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY) := by
  funext i j
  rcases j with j | j
  · exact congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inl j))
  · exact (congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inr j))).trans (map_mul (incA D) μ _)

theorem chart_weyl : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  intro D A μ hμ κ hκ g hg
  have h := hκ g
  rw [hg] at h
  obtain ⟨e1, hY⟩ := weyl_cols _ _ _ _ (rat_Tm_cols A μ) h
  have hμ0 : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have e2 := weyl_unscale _ _ _ hμ0 hY
  refine ⟨⟨mem_GQ_of_hypDec (dblDec A) g ?_ ?_ ?_, weyl_kill _ _ _ (dblDec A).pY_jX e2⟩, e1, e2⟩
  · exact Set.mem_of_eq_of_mem e1 (neg_mem (ratMx_smul μ (rat_mem (dblDec A).e')))
  · exact ⟨0, Matrix.ext fun _ j => Fin.elim0 j⟩
  · exact Set.mem_of_eq_of_mem e2 (ratMx_smul μ⁻¹ (rat_mem (dblDec A).e))

end GlobalTheory.StdUnn
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem gram_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E) (μ : E)
    (hμ : star μ = -μ) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    ((Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm)ᴴ * G *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = μ • blk4 0 1 (-1) 0 := by
  have h : (Matrix.fromCols e (μ • e'))ᴴ * G * Matrix.fromCols e (μ • e') = μ • Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.conjTranspose_smul, hμ, Matrix.fromBlocks_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_neg, neg_smul, Matrix.neg_mul, neg_zero]
  ext i j
  exact congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem fromRows_mul_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E)
    (μ : E) (hμ : μ ≠ 0) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    (Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G))).submatrix finSumFinEquiv.symm id *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = (1 : Matrix (Fin (n + n)) (Fin (n + n)) E) := by
  have h : Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G)) * Matrix.fromCols e (μ • e') = 1 := by
    rw [Matrix.fromRows_mul_fromCols]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, Matrix.fromBlocks_one]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm, ← h]
  rfl

end General

theorem Tm_gram_inv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  intro D A μ hμ
  have h₄ : (dblDec A).eᴴ * (dblSp A).gram * (dblDec A).e' = 1 := by
    have := congrArg Matrix.conjTranspose (dblDec A).e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  have hi := fromRows_mul_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.1
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄
  exact ⟨gram_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.2
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄, Matrix.isUnit_det_of_left_inverse hi, Matrix.inv_eq_left_inv hi⟩

end GlobalTheory.StdUnn
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem flat_swSec_eq_sect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  intro D ψ A B χB omh hW ν 𝓨 _ θ _ μ _ κ _ omS hT lam _ a p f hf Φ hΦ
  have h0 : s0 B A.rank = sZero A B := by unfold s0 sZero; ring
  have h3 : ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := fun g => by
    rw [hT (g * p) _ (hW.om_pres _ f hf) Φ hΦ, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
      mul_inv_cancel_right]
  refine ⟨h0, fun z g => ?_, h3⟩
  have hp : 0 < absA D (aP A p) := hom_pos _ _
  have h1 : npow (absA D (aP A p)) (sZero A B - z) * npow (absA D (aP A p)) (z - sZero A B) = 1 := by
    rw [← npow_add hp, show sZero A B - z + (z - sZero A B) = 0 by ring, npow_zero]
  have h2 : hgtStd A a κ p (κ (g * p)) = hgt A a g * absA D (aP A p) := by
    rw [hgtStd, MulEquiv.symm_apply_apply, mul_inv_cancel_right]
  have h4 : sch ψ A B ν 𝓨 (omh (g, 1) f) 0 = swSec A B omh ν 𝓨 f g := mixS_dblDec_zero A B ψ ν 𝓨 _ 0
  have h5 : flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g =
      swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B) := rfl
  rw [h5, sect, h3, h4, h2, h0, npow_mul]
  linear_combination (-(swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B))) * h1

end GlobalTheory.StdUnn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem rangeX_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG t
  have hm := hG.core.models
  exact GlobalTheory.DefiniteMult.range_top R hm.inf hm.cX hm.prX hm.HX t

end GlobalTheory.ChainTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  first | exact @GlobalTheory.ChainOnto.ValPart.valPart_mem | exact GlobalTheory.ChainOnto.ValPart.valPart_mem | (intros; apply GlobalTheory.ChainOnto.ValPart.valPart_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_heckeParameters_linearIndependent : ∀ D : D7, ParIndep D := by
  first | exact @GlobalTheory.ChainOnto.parIndep | exact GlobalTheory.ChainOnto.parIndep | (intros; apply GlobalTheory.ChainOnto.parIndep <;> assumption)
end
