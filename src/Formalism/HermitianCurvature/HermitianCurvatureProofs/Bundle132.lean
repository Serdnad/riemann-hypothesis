module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Aesop.Main
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

@[expose] public section

section

open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem cslice_continuous (c : Fin r → ℂ) : Continuous (fun x : Mt k r => (c, Matrix.of x)) :=
  continuous_const.prodMk continuous_id

theorem int_cpt_gen (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Θ : RadSp k r z z' π π') (c : Fin r → ℂ) (v : Wq) (K : Set (Mx k r)) (hKc : IsCompact K)
    (hKG : K ⊆ {g | 0 < GGl k r z z' g}) (hc : c ∈ OmX r)
    (f : Mt k r → ℂ) (hf : (f = fun x => ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ) ∨
      (f = fun x => ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ))
    (hΦ0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    Integrable f μ := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) s := by
    intro Ξ
    have h1 := (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s) (fun x hx => by rw [hs] at hx; exact hx)
    exact h1.clm_apply continuousOn_const
  have hcont : ContinuousOn f s := by
    rcases hf with rfl | rfl
    · exact (hA Φ).inner (hA Θ)
    · exact (hA Θ).inner (hA Φ)
  have hzero : ∀ x, (c, Matrix.of x) ∉ DomR k r z z' ∨ Matrix.of x ∉ K → f x = 0 := by
    intro x hx
    have hΦx : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 := by
      rcases hx with hx | hx
      · exact radSp_zero_off Φ (x := (c, Matrix.of x)) hx
      · by_cases hg : Matrix.of x ∈ Glev k r (Fin.last r)
        · exact hΦ0 _ hg hx
        · exact radSp_zero_off Φ (x := (c, Matrix.of x)) (fun h => hg h.2.1)
    rcases hf with h | h
    · subst h
      show ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_left]
    · subst h
      show ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_right]
  obtain ⟨C, hC⟩ : ∃ C : Set (Mt k r), C = (fun g : Mx k r => (Matrix.of.symm g : Mt k r)) '' (K ∩ Glev k r (Fin.last r)) :=
    ⟨_, rfl⟩
  have hCmem : ∀ x, x ∈ C ↔ Matrix.of x ∈ K ∧ Matrix.of x ∈ Glev k r (Fin.last r) := by
    intro x
    rw [hC]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Matrix.of.apply_symm_apply]
      exact hg
    · intro hx; exact ⟨Matrix.of x, hx, rfl⟩
  have hCc : IsCompact C := by
    rw [hC]
    exact (hKc.inter_right (P.Qx5.Glev_closed _)).image continuous_id
  have hCs : C ⊆ s := by
    intro x hx
    rw [hCmem] at hx
    rw [hs]
    exact ⟨hc, hx.2, hKG hx.1⟩
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hcont.mono hCs)
  have hmeas : Measurable f := measurable_of_continuousOn_zero hsm hcont (fun x hx => hzero x (Or.inl (by rw [hs] at hx; exact hx)))
  have hbound : ∀ x, ‖f x‖ ≤ C.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]; exact hM x hx
    · rw [Set.indicator_of_notMem hx]
      have : f x = 0 := by
        apply hzero
        by_cases hd : (c, Matrix.of x) ∈ DomR k r z z'
        · right; intro hK; exact hx ((hCmem x).2 ⟨hK, hd.2.1⟩)
        · left; exact hd
      rw [this, norm_zero]
  refine Integrable.mono' ?_ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (integrable_indicator_iff hCc.measurableSet).mpr
    (integrableOn_const (hμ.finite_compact C hCc).ne)

end Cpt

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt' (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  obtain ⟨K, hKc, hKG, hK0⟩ := hK
  refine pairAt_t_adj_cpt P z z' π π' hP X μ hμ Φ Ψ c hc ⟨K, hKc, hKG, hK0⟩ Y a b (fun m => ?_) (fun m => ?_)
  · exact int_cpt_gen μ hμ Ψ (X.t Y a b Φ) c _ K hKc hKG hc _ (Or.inl rfl) (fun g hg hgK => (hK0 g hg hgK).2)
  · exact int_cpt_gen μ hμ Φ (X.t (star Y) b a Ψ) c _ K hKc hKG hc _ (Or.inr rfl) (fun g hg hgK => (hK0 g hg hgK).1)

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

open Matrix MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

private lemma scalar_pow_mul_diagonal {A S : Type} [Ring A] [Fintype S] [DecidableEq S] (a : A) (n : ℕ)
    (D : Ix S → A) :
    (Matrix.scalar (Ix S) a) ^ n * Matrix.diagonal D = Matrix.diagonal (fun e => a ^ n * D e) := by
  rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem dw_pt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (ws : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 ws)
    (Y₀ : ℝ) (e : Ix S) (p : Polynomial ℂ)
    (hp : ∀ ρ : M.Ty P, p.eval (M.xC P ρ (Y₀ : ℂ)) = Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)
    (y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) (hx : (c, g) ∈ DomR P.k P.r z z')
    (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ) (hBs : IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs) (v : Wq) :
    (act ((Fr.ofWord L st ws).d L) y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
      (((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) ^ ws.length) •
        (y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
          (Polynomial.aeval (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2)) p v) := by
  have hD' := hD
  obtain ⟨hPl, -, hAL, hQQ, hq, -, -, hLS⟩ := hD'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := id hAL
  obtain ⟨κ, hκx, hκxi, -⟩ := Formalism.FourierDecayAlt.P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual
    Formalism.FourierDecayAlt.P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hxiw : ∀ l ∈ ws, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1) := by
    intro l hl
    obtain ⟨-, h1, h2, -⟩ := hw.1.2.2.1 l hl
    exact ⟨(hκxi _ h1).symm, (hκxi _ h2).symm⟩
  have hc : (Fr.ofWord L st ws).c =
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e := by
    rw [← Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr L st st' rfl rfl ws hxiw,
      (Formalism.FourierDecayAlt.P.c_diagonal _ S P.r L st' (M.Ty P) κ (M.x0 P l0) (fun Y => hκx Y) (fun Y => rfl) ws).2.2,
      ← hq]
  have hd : (Fr.ofWord L st ws).d L = Matrix.diagonal (fun e => (L.ζ * L.ζb * L.GGi) ^ ws.length *
      κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)) := by
    rw [Fr.FrameData.d, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_N, hc]
    exact scalar_pow_mul_diagonal _ _ _
  set K := κ (fun ρ => M.xC P ρ (Y₀ : ℂ)) with hKdef
  have hs : M.sgn P l0 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hK : K.1 = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have t := hLS.tau (Y₀ : ℂ)
    rw [hQQ, hκx, Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul, map_smul] at t
    have t1 := congrArg (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) t
    rw [map_mul, map_smul, Matrix.smul_apply, map_smul] at t1
    change M.sgn P l0 • X.t (Y₀ : ℂ) 1 1 = L.GG.1 * (M.sgn P l0 • K.1) at t1
    rw [hGG, mul_smul_comm] at t1
    have h4 : X.fn 4 * K.1 = X.t (Y₀ : ℂ) 1 1 := (smul_right_injective _ hs t1).symm
    have h54 : X.fn 5 * X.fn 4 = 1 := by
      have := congrArg Prod.fst L.GGi_GG
      rw [hGGi, hGG] at this
      exact this
    rw [← h4, ← mul_assoc, h54, one_mul]
  have hκf : κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e) = Polynomial.aeval K p :=
    Formalism.FourierDecayAlt.P5.Kfp.kappa_aeval (NFData.mk L κ (fun _ => 0)) (Y₀ : ℂ) p _ hp
  have hκf1 : (κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 = Polynomial.aeval K.1 p := by
    rw [hκf]
    exact (Polynomial.aeval_algHom_apply (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) K p).symm
  have hT : ∀ (Ψ : RadSp P.k P.r z z' π π') (w : Wq),
      ((K.1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g w =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2) w) := by
    intro Ψ w
    rw [hK]
    exact Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hPl.2.1 hPl.2.2.1 hPl.2.2.2.2.2.2.2.1 hPl.2.2.2.2.2.2.2.2.1 hx Bs hBs _ Ψ w
  have hA := Formalism.FourierDecayAlt.P5.Kfp.aeval_act K.1 _ hT p
  have hpow := Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply X L hAL ws.length
    ((κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 (y e)) (c, g) hx
  have hmul : ∀ a b : Pr (RadSp P.k P.r z z' π π'), (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  rw [hd, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.act_diagonal, hmul, Module.End.mul_apply, hpow,
    _root_.smul_apply, hκf1, hA]
  congr 1
  simp only [fnVal]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
  rfl

end

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (a : ℂ) (X : Wq →L[ℂ] Wp) : B.hsVec (a • X) = a • B.hsVec X := by
  simp only [B.hsVec, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  rfl

theorem tc_hsVec_sum {ι : Type} (s : Finset ι) (X : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [B.hsVec, ContinuousLinearMap.zero_apply]
    exact WithLp.toLp_zero 2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [B.hsVec, ContinuousLinearMap.add_apply]
    exact WithLp.toLp_add 2 _ _

theorem tc_gq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    B.gq Bs x = Q.wCell P.k P.r (Fin.last P.r) x.1 * NF.muZ P.k P.r Bs.μsec x.2 := by
  show bigCell P.k P.r x.1 (Bs.μsec x.2) = _
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r x.1 (Bs.μsec x.2)).1, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  rfl

theorem tc_sqrt_wq (k r : ℕ) (TT : ℝ) (x : MA.E r) :
    Real.sqrt (MA.wq k x TT) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) *
        wR k TT x.2 := by
  unfold MA.wq wR
  rw [Real.sqrt_mul (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)]
  congr 1
  have h : ∏ l : Fin r, Complex.normSq (x.1 l) ^ (MA.Mdim k r l - 1) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hM : MA.Mdim k r a = Formalism.QuantumDeterminants.Mdim k r a := rfl
    rw [if_pos (by simp), Complex.normSq_eq_norm_sq, hM, ← pow_mul, ← pow_mul, mul_comm]
  rw [h, Real.sqrt_sq (Finset.prod_nonneg fun a _ => by split_ifs <;> positivity)]

theorem tc_rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ := by
  funext q
  simp only [rawJ, rawR, Q.resG, tc_gq, tc_sqrt_wq]
  rw [tc_hsVec_smul, inner_smul_right]
  push_cast
  ring

theorem tc_mu (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∧
      Q.wCell P.k P.r (Fin.last P.r) q.1.1 * NF.muZ P.k P.r Bs.μsec q.1.2 ∈ OmB Bs := by
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hTT]; exact q.2.2
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
    linarith
  have h := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hG hGG
  exact ⟨hG, h.2, fun a => h.1 ⟨(a : ℕ) + 1, by omega⟩ (by show (a : ℕ) + 1 ≤ P.r; omega)⟩

theorem tc_famR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) :
    FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs})
      (Q.resG P.k P.r (Fin.last P.r) J) := by
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  refine ⟨?_, ?_, fun q => (tc_mu P Bs hpl q).2, ?_⟩
  · have hw : ContDiffOn ℝ ∞ (fun c : Fin P.r → ℂ => Q.wCell P.k P.r (Fin.last P.r) c) (OmX P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
    have hm : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
        {x | x.1 ∈ OmX P.r} :=
      Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
    exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1
  · intro c hc
    refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
    rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hhm : h * m ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
    have hcomm : Q.wCell P.k P.r (Fin.last P.r) c * (h * m) = (h * m) * Q.wCell P.k P.r (Fin.last P.r) c :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last P.r) c _ (fun a _ => a.isLt) hhm
    have hwg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
    have e : Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) =
        h * m * (Q.wCell P.k P.r (Fin.last P.r) c * g) * (h' * m') := by
      rw [← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c), ← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c),
        hcomm, Matrix.mul_assoc (h * m)]
    show Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) ∈ OmB Bs
    rw [e]
    exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
      ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩
  · exact Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
      (Fin.last P.r)

end

theorem gauge_transition_chain_holds : GTrChain := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ J hJ
  refine ⟨tc_famR P Bs hpl J hJ, fun e ρ => tc_rawJ P Bs e J ρ, fun e ρ Y => ?_⟩
  rw [tc_rawJ]
  funext q
  have hmu := tc_mu P Bs hpl q
  have hcv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) (OmB Bs) (Y : ℂ)
    Bs.z_mem Bs.z'_mem (isDom_omP Bs.z_mem Bs.z'_mem) J hJ q.1.1 q.2.1 _ hmu.1 hmu.2
  simp only [rawR, Finset.sum_apply]
  rw [hcv]
  simp only [Finset.sum_apply, tc_hsVec_sum, inner_sum, Finset.mul_sum, Fin.val_last]

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
end

section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieJ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem jfScale : Formalism.FourierDecayAlt.P.PTie.JFScale := by
  intro k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'
  have hW := Bs.haarW
  have hW' := Bs.haarW'
  rw [hz] at hW
  rw [hz'] at hW'
  obtain ⟨a, ha⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW
  obtain ⟨a', ha'⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'
  obtain ⟨b, hb⟩ := haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN
  have := sfinite_of_haar Bs'.haarW
  have := sfinite_of_haar Bs'.haarW'
  have := sfinite_of_haar Bs'.haarN
  refine ⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩
  funext g
  simp only [B.JF, Pi.smul_apply]
  rw [hz, hz', hπ, hπ', ha, ha', hb]
  unfold besselJ
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [integral_smul_measure, Complex.coe_smul]
  congr 2
  ring

end Formalism.FourierDecayAlt.P.PTieJ

namespace Formalism.FourierDecayAlt.P

theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def sumU (P : M.Par) : ℂ := ∑ i ∈ Finset.Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ))

def GTCCurvScal : Prop :=
  ∀ (P : M.Par), 2 ≤ P.k → ∀ ρ : M.Ty P,
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i) ∧
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i) ∧
    (∀ ex : Finset ℕ, (∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) →
      ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i)

def GTCCurvPolyOfScal : Prop := GTCCurvScal → GTCCurvPoly

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
