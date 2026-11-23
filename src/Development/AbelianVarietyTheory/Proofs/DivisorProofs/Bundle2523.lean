module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Formalism.GradedWeylDivisibility.FinalD
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF

theorem continuous_transportF_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
    Φ hΦ z
  have hstd := hω.std
  have hψ := hstd.1

  have hth : ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w := by
    intro w
    have hex : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
        ∃ (g : GAF σ JS) (h : GAF σ JT),
          mtF σ JT h = p.1.1.1 ∧ mtF σ JS g = (p.2⁻¹).1.1ᵀ := fun p =>
      GlobalTheory.T.exists_unitaryPair_partner_cmExtension F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB p.1 p.2
    choose g h hh hg using hex
    have hθ : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
      ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.continuous_thetaTransform_schwartz_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ⟩
    have hhU : ∀ p, matHomF σ JT (h p) = p.1.1 := fun p => Units.ext (hh p)
    have hgU : ∀ p, (matHomF σ JS (g p))⁻¹.1 = p.2.1.1ᵀ := by
      intro p
      apply Units.inv_eq_of_mul_eq_one_right
      change mtF σ JS (g p) * _ = 1
      rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    have hcH' : Continuous fun p => matHomF σ JT (h p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JT (h p)) = fun p => p.1.1.1 := funext fun p => hh p
        rw [e]
        exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
      · have e : (fun p => (matHomF σ JT (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
        rw [e]
        exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
    have hcG' : Continuous fun p => matHomF σ JS (g p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JS (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
        rw [e]
        exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
      · have e : (fun p => (matHomF σ JS (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
        rw [e]
        exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    have hcH : Continuous h := continuous_induced_rng.2 hcH'
    have hcG : Continuous g := continuous_induced_rng.2 hcG'
    have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w =
        ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w := fun p =>
      congrFun (htr p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
    exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, pureA F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      GlobalTheory.T.weilDatumTransport_archimedeanSlice_schwartz_bounds F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
        Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.SchwartzMajorant.exists_summable_majorant F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → F) → AddChar (κ → AF F) ℂ := fun a =>
    B.ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = B.ψ ((fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
      B.ψ (⅟(2 : AF F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.2.2.2
    refine ⟨Pi.single i (algebraMap F (AF F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF F, B.ψ (-t) * B.ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul B.ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, B.ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.continuousAt_charSeries_coef_zero e (fun a y => hψ.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilContF
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.DelStd

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  omega

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Fin.pos a
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, hn, dif_pos] at *
  omega

theorem linInd_map {σ P : Type} [Fintype P] (K : Type) [Field K] [CharZero K] (b : P → MvPolynomial σ ℤ)
    (hb : LinearIndependent ℤ b) : LinearIndependent K fun i => MvPolynomial.map (Int.castRingHom K) (b i) := by
  classical
  let e := Fintype.equivFin P
  have h1 : LinearIndependent ℤ (b ∘ e.symm) := hb.comp _ e.symm.injective
  have h1' := h1.map' (MvPolynomial.basisMonomials σ ℤ).repr.toLinearMap (LinearEquiv.ker _)
  have h2 := GlobalTheory.LatBC.linInd_mapRange (O := ℤ) (K := K) (P := σ →₀ ℕ) (Int.castRingHom K) (fun _ _ h => Int.cast_injective h) h1'
  have h3 := h2.comp e e.injective
  refine LinearIndependent.of_comp (MvPolynomial.basisMonomials σ K).repr.toLinearMap ?_
  convert h3 using 1
  funext i
  ext m
  have hZ : ∀ f : MvPolynomial σ ℤ, (MvPolynomial.basisMonomials σ ℤ).repr f m = AddMonoidAlgebra.coeff f m := fun _ => rfl
  have hK : ∀ f : MvPolynomial σ K, (MvPolynomial.basisMonomials σ K).repr f m = AddMonoidAlgebra.coeff f m := fun _ => rfl
  simp [hZ, hK, MvPolynomial.coeff_map]

theorem detPol_ne_zero (C : Type) [Field C] (n : ℕ) : detPol C n ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) C

theorem map_detPol {R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (n : ℕ) :
    MvPolynomial.map f (detPol R n) = detPol C n := by
  unfold detPol
  rw [RingHom.map_det]
  congr 1
  ext a s : 2
  simp

theorem linInd_det {P : Type} {C : Type} [Field C] {n : ℕ} (k : ℕ) (b : P → MvPolynomial (Fin n × Fin n) C)
    (hb : LinearIndependent C b) : LinearIndependent C fun i => detPol C n ^ k * b i := by
  have := hb.map' (LinearMap.mulLeft C (detPol C n ^ k)) (LinearMap.ker_eq_bot.2
    (mul_right_injective₀ (pow_ne_zero k (detPol_ne_zero C n))))
  exact this

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_sum {C : Type} [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {P : ι → Type} [∀ τ, Fintype (P τ)]
    (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) C) (a : ∀ τ, P τ → C) :
    (ten fun τ => ∑ j, a τ j • u τ j) = ∑ i : ∀ τ, P τ, (∏ τ, a τ (i τ)) • ten fun τ => u τ (i τ) := by
  unfold ten

  simp only [map_sum, map_smul]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_smul]

theorem map_map_int {σ R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (b : MvPolynomial σ ℤ) :
    MvPolynomial.map f (MvPolynomial.map (Int.castRingHom R) b) = MvPolynomial.map (Int.castRingHom C) b := by
  rw [MvPolynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom C)]

theorem latD_coords {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (lamW : ι → ℕ → ℕ) (F : Frame l ι n)
    (hF : ∀ x : F.O, ‖F.emb x‖ ≤ 1) {P : ι → Type} [∀ τ, Fintype (P τ)] (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l))
    (hu : ∀ τ, ∀ x0 ∈ weyl F.O n n le_rfl (res n (lamW τ)), ∃ a : P τ → F.O,
      MvPolynomial.map F.emb x0 = ∑ j, F.emb (a j) • u τ j)
    {z : NablaT (PadicAlgCl l) n lamW} (hz : z ∈ F.latD lamW) :
    ∃ r : (∀ τ, P τ) → PadicAlgCl l, (∀ i, ‖r i‖ ≤ 1) ∧
      mulMap (PadicAlgCl l) n lamW z = ∑ i, r i • ten fun τ => u τ (i τ) := by
  unfold Frame.latD at hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, x, hx, rfl⟩ := hy
    choose x0 hx0 hx1 using hx
    choose a ha using fun τ => hu τ (x0 τ) (hx0 τ)
    refine ⟨fun i => F.emb c * ∏ τ, F.emb (a τ (i τ)), fun i => ?_, ?_⟩
    · beta_reduce
      rw [← map_prod, ← map_mul]; exact hF _
    · rw [map_smul, mulMap_tprod]
      have : (fun τ => (x τ : MvPolynomial (Fin n × Fin n) (PadicAlgCl l))) = fun τ => ∑ j, F.emb (a τ j) • u τ j := by
        funext τ; rw [← hx1, ha]
      rw [this, ten_sum u fun τ j => F.emb (a τ j), Finset.smul_sum]
      simp only [smul_smul]
  | zero => exact ⟨0, fun i => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨s, hs, hy⟩ := hy
    refine ⟨r + s, fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr i) (hs i)), ?_⟩
    rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_smul]
  | neg x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    refine ⟨-r, fun i => by simpa using hr i, ?_⟩
    rw [map_neg, hx, ← Finset.sum_neg_distrib]
    simp only [Pi.neg_apply, neg_smul]

theorem smul_mem_locP {K M : Type} [Field K] [NumberField K] [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) M) (x : M) (a : K) (s t : 𝓞 K)
    (hs : s ∉ w.asIdeal) (hst : (s : K) * a = t) (hx : x ∈ L) : a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  refine ⟨s, hs, ?_⟩
  have h1 : s • a • x = t • x := by
    rw [← algebraMap_smul K s, ← algebraMap_smul K t, smul_smul]
    exact congrArg (· • _) hst
  rw [h1]
  exact L.smul_mem _ hx

theorem mem_localization_standardWeylLattice : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → (∀ x : F.O, ‖F.emb x‖ ≤ 1) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, Φ v ∈ F.latD lamW → (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ l _ w e0 ι _ _ n lam lamW c F Φ hw hF hS hΦ v hv
  classical
  choose P fP b hb hspan hdual using fun τ => GlobalTheory.T.exists_integral_weylBasis_spanning_all_rings n (lam τ).natW (natW_anti (lam τ))

  let bK : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) K := fun τ i => MvPolynomial.map (Int.castRingHom K) (b τ i)
  let u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l) := fun τ i =>
    detPol (PadicAlgCl l) n ^ lamW τ (n - 1) * MvPolynomial.map (Int.castRingHom (PadicAlgCl l)) (b τ i)
  have hKspan := (tensorBasis K K ι n n P (fun τ => nablaSq K n (lam τ)) bK (fun τ => linInd_map K _ (hb τ))
    (fun τ => (hdual τ K).symm)).2
  have huind := (tensorBasis (PadicAlgCl l) (PadicAlgCl l) ι n n P _ u
    (fun τ => linInd_det _ _ (linInd_map (PadicAlgCl l) _ (hb τ))) (fun τ => rfl)).1
  have hbK : ∀ τ i, bK τ i ∈ nablaSq K n (lam τ) := fun τ i => by
    unfold nablaSq
    rw [hdual τ K]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i : ∀ τ, P τ, (ten fun τ => bK τ (i τ)) ∈ VV K lam := fun i =>
    Submodule.subset_span ⟨_, fun τ => hbK τ (i τ), rfl⟩
  have hv0 : (v : Pol K ι n) ∈ Submodule.span K (Set.range fun i : ∀ τ, P τ => ten fun τ => bK τ (i τ)) := by
    have h2 : (v : Pol K ι n) ∈ tensorLat K K fun τ => nablaSq K n (lam τ) := v.2
    rw [← hKspan] at h2
    exact h2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv0
  have hveq : v = ∑ i, a i • (⟨_, hmem i⟩ : VV K lam) := by
    apply Subtype.ext
    rw [← ha]
    simp
  have hΦi : ∀ i, mulMap (PadicAlgCl l) n lamW (Φ ⟨_, hmem i⟩) = ten fun τ => u τ (i τ) := fun i => by
    obtain ⟨y, hy, hyΦ⟩ := hΦ (fun τ => bK τ (i τ)) ⟨_, hmem i⟩ (fun τ => hbK τ (i τ)) rfl
    rw [hyΦ, mulMap_tprod]
    congr 1
    funext τ
    rw [hy, liftPol, map_map_int]
  have hΦv : mulMap (PadicAlgCl l) n lamW (Φ v) = ∑ i, e0 (a i) • ten fun τ => u τ (i τ) := by

    rw [hveq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, hΦi]
  obtain ⟨r, hr, hrv⟩ := latD_coords lamW F hF u (fun τ x0 hx0 => by
    rw [res_eq hS τ, GlobalTheory.T.mem_weylLattice_add_iff_det_pow_mul] at hx0
    obtain ⟨g, hg, rfl⟩ := hx0
    rw [hspan τ F.O] at hg
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F.O).1 hg
    refine ⟨d, ?_⟩

    rw [map_mul, map_pow, map_detPol, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [u, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_map_int]
    ring) hv
  have hra : ∀ i, e0 (a i) = r i :=
    (Fintype.linearIndependent_iffₛ.1 huind) (fun i => e0 (a i)) r (hΦv.symm.trans hrv)
  rw [← ha]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨s, hs, t, hst⟩ := (GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place K l w e0 hw (a i)).1 (hra i ▸ hr i)
  refine smul_mem_locP w _ _ _ s t hs hst (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
  refine ⟨MvPolynomial.map (Int.castRingHom (𝓞 K)) (b τ (i τ)), ?_, ?_⟩
  · unfold delSq
    rw [hspan τ (𝓞 K)]
    exact Submodule.subset_span ⟨_, rfl⟩
  · exact map_map_int (algebraMap (𝓞 K) K) _

end GlobalTheory.FrameRead.DelStd
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isPhi_mem_latN_of_frame_injective_shift : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW := by
  first | exact @GlobalTheory.FrameRead.lift_nabStd_mem_latN | exact GlobalTheory.FrameRead.lift_nabStd_mem_latN | (intros; apply GlobalTheory.FrameRead.lift_nabStd_mem_latN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr
  have hfin := GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpt := GlobalTheory.T.continuous_transportedWeilOperator_groupVariable D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hbd := GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpres := (GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local D.host.F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice D.host.F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilCont
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  first | exact @GlobalTheory.ParPt.exists_unique_of_globForm | exact GlobalTheory.ParPt.exists_unique_of_globForm | (intros; apply GlobalTheory.ParPt.exists_unique_of_globForm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) ∧ ∀ t : T, IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧ (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧ IsFinF W.ψ W.θ true FA FW (X.f t) ∧ IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧ (∀ P g h, thetaKO (X.ω t) g h (fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧ ∀ P g h, thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.BotDict.bottom_dictionary | exact GlobalTheory.BotDict.bottom_dictionary | (intros; apply GlobalTheory.BotDict.bottom_dictionary <;> assumption)
end
