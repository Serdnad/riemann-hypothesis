module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle042
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle032
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle043
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle047
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle044
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle026
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle038
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle045
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocalIsometryAlt

variable {D : D7}

theorem eq_of_tens {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {m n : ℕ} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D m n} (hx₀ : Ψ x₀ ≠ 0)
    {g₁ g₂ : (Fin m → Fin n → ℂ) → ℂ} (h : tens θ τ fr g₁ Ψ = tens θ τ fr g₂ Ψ) : g₁ = g₂ := by
  funext u
  obtain ⟨x, hx1, hx2, hx3⟩ := OG.exists_slice hθ τ x₀ (fr * Matrix.of u)
  have h1 := congrFun h x
  rw [OG.tens_at τ hfr _ _ x (Matrix.of u) hx1, OG.tens_at τ hfr _ _ x (Matrix.of u) hx1, hΨ.1 x x₀ hx2 hx3] at h1
  exact mul_right_cancel₀ hx₀ h1

theorem int_cmul {m n : ℕ} (k : ℂ) (h : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ u, ‖k * h u‖ ^ 2 = ‖k‖ ^ 2 * ∫ u, ‖h u‖ ^ 2 := by
  simp_rw [norm_mul, mul_pow]
  exact integral_const_mul _ _

def rmulEquiv {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show Matrix.of (u + v) * a = Matrix.of u * a + Matrix.of v * a
        rw [← Matrix.add_mul]; rfl
      map_smul' := fun c u => by
        show Matrix.of (c • u) * a = c • (Matrix.of u * a)
        ext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_assoc]
      left_inv := fun u => by
        show Matrix.of u * a * a⁻¹ = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]; rfl
      right_inv := fun u => by
        show Matrix.of u * a⁻¹ * a = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]; rfl }

theorem int_comp {m n : ℕ} (R : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : (Fin m → Fin n → ℂ) → ℝ, Continuous F → ∫ u, F (R u) = c * ∫ u, F u := by
  obtain ⟨c1, hc1, h1⟩ := PlanchH.haar_linR (m := m) (n := n) (R.trans FTD.Lc)
  obtain ⟨c2, hc2, h2⟩ := PlanchH.haar_linR (m := m) (n := n) FTD.Lc
  refine ⟨c1 / c2, div_pos hc1 hc2, fun F hF => ?_⟩
  have hG : Continuous (fun w => F (FTD.Lc.symm w)) := hF.comp FTD.Lc.symm.continuous
  have e1 := h1 _ hG
  have e2 := h2 _ hG
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply] at e1 e2
  rw [e1, e2]
  field_simp

theorem norm_phase {m n : ℕ} (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (b * gramX ε u).trace).re = 0 := by
    have hgram : (gramX ε u)ᴴ = gramX ε u := by
      ext i j

      simp [Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]
    have htrace : star (b * gramX ε u).trace = (b * gramX ε u).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hgram, hb, Matrix.trace_mul_comm]
    rw [← Complex.conj_eq_iff_re.1 htrace]
    simp
  rw [hre, Real.exp_zero]

end PositivityTheory.Rg.Sw.Glob.LocalIsometryAlt

namespace PositivityTheory.Rg.Sw.Glob

theorem local_isometry_of_hypotheses (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hD : Decomp) (hN : LNe)
    (hP : PlanchLoc) (hZ : AwayNZ) : LocalL2Isometry := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨Ψ₀, x₀, hΨ₀, hx₀⟩ := hZ D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hl0 : tLoc l τ ≠ 0 := by
    unfold tLoc
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hN D ψ θ l hC.hψ hC.hθ hC.hl τ)

  have huniq : ∀ y f (hf : IsSch f) g, (ω (ι y) ⟨tens θ τ fr f Ψ₀, hΨ₀.2 f hf⟩).1 = tens θ τ fr g Ψ₀ → L y f = g :=
    fun y f hf g h => LocalIsometryAlt.eq_of_tens hC.hθ hfr hΨ₀ hx₀ ((hL.2 y Ψ₀ hΨ₀ f hf).symm.trans h)
  have hmul : ∀ y₁ y₂ f, IsSch f → L (y₁ * y₂) f = L y₁ (L y₂ f) := by
    intro y₁ y₂ f hf
    apply huniq _ f hf
    have e2 : ω (ι y₂) ⟨tens θ τ fr f Ψ₀, hΨ₀.2 f hf⟩ = ⟨tens θ τ fr (L y₂ f) Ψ₀, hΨ₀.2 _ (hL.1 y₂ f hf)⟩ :=
      Subtype.ext (hL.2 y₂ Ψ₀ hΨ₀ f hf)
    rw [map_mul, map_mul, mul_apply_eq_comp, e2, hL.2 y₁ Ψ₀ hΨ₀ _ (hL.1 y₂ f hf)]

  let Iso : GR n → Prop := fun y => ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2
  have hIso_mul : ∀ y₁ y₂, Iso y₁ → Iso y₂ → Iso (y₁ * y₂) := by
    rintro y₁ y₂ ⟨κ₁, hκ₁, h₁⟩ ⟨κ₂, hκ₂, h₂⟩
    refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun f hf => ?_⟩
    rw [hmul y₁ y₂ f hf, h₁ _ (hL.1 y₂ f hf), h₂ f hf, mul_assoc]
  have hIso_n : ∀ y (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → Iso y := by
    intro y b hb hyb
    refine ⟨1, one_pos, fun f hf => ?_⟩
    have hLf : L y f = fun u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u := by
      apply huniq y f hf
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hyb]
      simp only [tens, mul_assoc]
    rw [hLf, one_mul]
    congr 1
    funext u
    rw [norm_mul, LocalIsometryAlt.norm_phase ε _ b hb u, one_mul]
  have hone : ∀ f (hf : IsSch f), L 1 f = f := by
    intro f hf
    apply huniq 1 f hf
    rw [map_one, map_one, one_apply_eq_self]
  have hzero : ∀ y, L y (fun _ => 0) = fun _ => 0 := by
    intro y
    have h0 : IsSch (fun _ : Fin V.rank → Fin n → ℂ => (0 : ℂ)) := ⟨0, by ext u; simp⟩
    apply huniq y _ h0
    have : (⟨tens θ τ fr (fun _ => 0) Ψ₀, hΨ₀.2 _ h0⟩ : schwartzA θ V.rank n) = 0 :=
      Subtype.ext (funext fun x => by simp [tens])
    rw [this, map_zero]
    funext x
    simp [tens]
  have hIso_m : ∀ y (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → Iso y := by
    intro y a ha hya
    obtain ⟨C, Am, hA1, hA2, hA3, hAf⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
    have hLf : ∀ f, IsSch f → L y f = fun u => C * f (Matrix.of u * a) := by
      intro f hf
      apply huniq y f hf
      funext x
      rw [hAf]
      have hx1 : compAt θ τ (HMul.hMul x Am : Mx D V.rank n) = compAt θ τ x * a := by
        rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
      have hx2 : Ψ₀ (HMul.hMul x Am : Mx D V.rank n) = Ψ₀ x :=
        hΨ₀.1 _ _ (fun τ' h => by rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' h, Matrix.mul_one])
          (by rw [Matrix.map_mul, hA3, Matrix.mul_one])
      have hm : (fr⁻¹ * (compAt θ τ x * a) : Matrix (Fin V.rank) (Fin n) ℂ) =
          (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) * a := by
        rw [← Matrix.mul_assoc]
        rfl
      have e1 : f (fr⁻¹ * (compAt θ τ x * a)) = f (Matrix.of (fr⁻¹ * compAt θ τ x) * a) := congrArg f hm
      change C * (f (fr⁻¹ * compAt θ τ (HMul.hMul x Am : Mx D V.rank n)) * Ψ₀ (HMul.hMul x Am : Mx D V.rank n)) =
        C * f (Matrix.of (fr⁻¹ * compAt θ τ x) * a) * Ψ₀ x
      rw [hx1, hx2, e1, mul_assoc]
    have hC0 : C ≠ 0 := by
      intro hC0
      obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
      have h1 : L y f0 = fun _ => 0 := by
        rw [hLf f0 hf0, hC0]
        funext u
        simp
      have h2 : L (y⁻¹ * y) f0 = f0 := by
        rw [inv_mul_cancel]
        exact hone f0 hf0
      rw [hmul y⁻¹ y f0 hf0, h1, hzero] at h2
      have := congrFun h2 0
      rw [hf00] at this
      exact zero_ne_one this
    obtain ⟨c, hc, hcomp⟩ := LocalIsometryAlt.int_comp (LocalIsometryAlt.rmulEquiv (m := V.rank) a ha)
    refine ⟨‖C‖ ^ 2 * c, mul_pos (pow_pos (norm_pos_iff.2 hC0) 2) hc, fun f hf => ?_⟩
    rw [hLf f hf, LocalIsometryAlt.int_cmul]
    obtain ⟨S, rfl⟩ := hf
    have hcont : Continuous (fun u => ‖S u‖ ^ 2) := S.continuous.norm.pow 2
    change ‖C‖ ^ 2 * ∫ u, (fun u => ‖S u‖ ^ 2) (LocalIsometryAlt.rmulEquiv (m := V.rank) a ha u) = _
    rw [hcomp _ hcont, mul_assoc]
  have hIso_nb : ∀ y (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbar c → Iso y := by
    intro y c hc hyc
    obtain ⟨κ, γ, hκ, hγ, hsch, hform⟩ := GenOpsH.gen_nbar hU hW hS hF hC y c hc hyc
    have hγ0 := hγ ⟨Ψ₀, x₀, hΨ₀, hx₀⟩
    obtain ⟨c1, hc1, hP1⟩ := hP V.rank n ε (tLoc l τ) hl0
    obtain ⟨c2, hc2, hP2⟩ := hP V.rank n ε (-tLoc l τ) (neg_ne_zero.2 hl0)
    have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
    refine ⟨‖γ⁻¹‖ ^ 2 * ‖κ‖ ^ 2 * c1 * (‖κ⁻¹‖ ^ 2 * c2), ?_, fun f hf => ?_⟩
    · have h1 : 0 < ‖γ⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hγ0)
      have h2 : 0 < ‖κ‖ := norm_pos_iff.2 hκ
      have h3 : 0 < ‖κ⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hκ)
      positivity
    have hLf := huniq y f hf _ (hform Ψ₀ hΨ₀ f hf)
    have hg : IsSch (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
        (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) :=
      (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) _ hc' (hsch f hf).1
    rw [hLf, LocalIsometryAlt.int_cmul, LocalIsometryAlt.int_cmul, hP1 _ hg]
    have e2 : (∫ v, ‖Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
        (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)‖ ^ 2) = ∫ v, ‖κ⁻¹ * ftLoc ε (-tLoc l τ) f v‖ ^ 2 := by
      congr 1
      funext v
      rw [norm_mul, LocalIsometryAlt.norm_phase ε _ (-c) hc' v, one_mul]
    rw [e2, LocalIsometryAlt.int_cmul, hP2 f hf]
    ring
  intro y
  obtain ⟨y₁, y₂, y₃, y₄, rfl, ⟨t, ht⟩, ⟨c, hc, hc'⟩, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD n y
  have h1 : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact hIso_mul _ _ (hIso_mul _ _ (hIso_mul _ _ (hIso_n y₁ _ h1 ht) (hIso_nb y₂ c hc hc')) (hIso_m y₃ a ha ha'))
    (hIso_n y₄ b hb hb')

end PositivityTheory.Rg.Sw.Glob
end
end

section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw_of' (hV : VacK) (hG : GZSch) : GaussLaw := by
  have hT : TensInj := tensInj_of awayIn
  exact gaussLaw_of hT (lawN_of unipTau hT) (lawM_of hT) hV (locMul_of hT) hG lNe

end PositivityTheory.Rg.Sw.Glob
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

theorem norm_ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ‖ker ε t v u‖ = 1 := by
  unfold ker
  rw [show Complex.I * ((2 * t : ℝ) : ℂ) * ((((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) =
      ((2 * t * ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ker (ε : Fin m → Bool) (t : ℝ) (v : Fin m → Fin n → ℂ) : Continuous (ker ε t v) := by
  unfold ker
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp ?_)))
  have h2 : Continuous fun u : Fin m → Fin n → ℂ => Matrix.of u := continuous_id
  have h : Continuous fun u : Fin m → Fin n → ℂ => ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u) :=
    continuous_const.matrix_mul h2
  exact h.matrix_trace

def Aw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)



theorem weyl_tens {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {l : D.what₂.Tau → ℝ} (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) {χ : (AE D)ˣ →* Circle}
    (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure] {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (Ψ : Mx D V.rank n → ℂ)
    (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (Aw ψ V θ τ fr μ Ψ) := by
  funext x
  rw [hω.weyl w hw]
  have e1 : ∀ y, (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n).1 y * ψ (trA (Matrix.trace (inner V x y))) =
      (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u) (piF θ τ fr y) * Bw ψ V θ τ fr Ψ x y :=
    fun y => integrand_eq hθ hl hfr f Ψ x y
  simp_rw [e1]
  obtain ⟨S, hS⟩ := hf
  have hfc : Continuous f := hS ▸ S.continuous
  obtain ⟨C, hC⟩ := sch_decay f ⟨S, hS⟩
  have hk := kap_spec hθ hfr.1 μ hΨ hψ x (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u)
    ((hfc.mul (continuous_ker ε (tLoc l τ) (piF θ τ fr x))).measurable)
    ⟨C, fun u => by rw [norm_mul, norm_ker, mul_one]; exact hC u⟩
  rw [hk]
  simp only [tens, Aw, ftLoc_eq_ker, one_mul]
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Sw.Glob.FTH
end
end
