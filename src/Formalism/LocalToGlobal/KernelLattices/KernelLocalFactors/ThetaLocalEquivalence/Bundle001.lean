module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.KernelLattices.Bundle002
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Bundle003
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Bundle002
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

theorem Seam.vec_gmap {n : ℕ} (γ : UF X.E n) (x : Sp X.E n) : s.vec (γ.1 x) = (s.matU γ).mulVec (s.vec x) := by
  have h := toGLm_mulVec γ.1 x
  rw [← h]
  funext i

  simp only [Seam.vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Seam.matU]
  rfl

theorem Seam.lat_gmap {n : ℕ} (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (gmap γ.1 N) = SDLat.smulLat (s.matU γ) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  simp only [SDLat.smulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact ⟨s.vec x0, (s.mem_lat N _).2 ⟨x0, hx0, rfl⟩, (s.vec_gmap γ x0).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    exact ⟨γ.1 x0, ⟨x0, hx0, rfl⟩, s.vec_gmap γ x0⟩

theorem Seam.matU_mem (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    (letI := D.host.cmStar; s.matU γ ∈ Matrix.unitaryGroup (Fin n) D.host.E) := by
  let _ := D.host.cmStar
  have h : Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) * 1 *
      ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ γ
  rw [Matrix.mul_one] at h
  have key : star (s.matU γ) = (Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)).map s.iE := by
    ext i j
    rw [Matrix.star_apply, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    simp only [Seam.matU, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    rw [hok.2]
  rw [Matrix.mem_unitaryGroup_iff', key, Seam.matU, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem Seam.det_matU {n : ℕ} (γ : UF X.E n) : (s.matU γ).det = s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := by
  rw [← TE.det_ufGL]
  exact (RingHom.map_det s.iE.toRingHom _).symm

theorem Seam.prod_emb (hok : s.Ok) (z : X.E) : ∏ τ : X.Tau, X.embC s.σ₀ τ z = ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE z) :=
  Fintype.prod_equiv s.iT _ _ fun τ => hok.1 τ z

end SeamU

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem chiLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (ambOf s B χ cD : Amb X).ChiLaw a b := by
  obtain ⟨-, -, -, hχ, -, hok, -⟩ := hN
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN'
  show Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) = _ * _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  rw [s.lat_gmap, s.lat_gmap]
  have h := Formalism.L2.PairingIndexBounds.Eq.character_factor_unitary_action χ hχ (Formalism.L2.PairingIndexBounds.Eq.detSmul D) (Formalism.L2.PairingIndexBounds.Eq.norm_one_unit_ideal D) ha hb (s.lat N) (s.lat N')
    ⟨s.matU γ, s.matU_mem hok γ⟩ ⟨s.matU γ', s.matU_mem hok γ'⟩ (s.sd_lat hok hN) (s.sd_lat hok hN')
  simp only at h
  rw [h]
  have u1 := Matrix.det_of_mem_unitary (s.matU_mem hok γ)
  have p1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det) = (∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ := by
    rw [s.prod_emb hok, ← Finset.prod_inv_distrib, ← s.det_matU]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.PairingIndexBounds.Eq.emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  have p2 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det = ∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := by
    rw [s.prod_emb hok, ← s.det_matU]
  show Base.chiFac χ a b (s.lat N) (s.lat N') * ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det)) ^ (b / 2) *
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det) ^ (a / 2)) = _
  rw [p1, p2, inv_pow, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
  rfl

end Chi

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Omega

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem TE.contDiff_opU_top (H : Sesq (VCx ι a b)) (x : VCx ι a b) (F : VCx ι a b → ℂ) (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opU H x F) := by
  unfold opU
  have h1 : ContDiff ℂ ⊤ fun z : VCx ι a b => F (z + x) := hF.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℂ ⊤ fun z : VCx ι a b => H z x :=
    (LinearMap.toContinuousLinearMap (H.flip x)).contDiff
  exact h1.mul (Complex.contDiff_exp.comp (((contDiff_const.mul h2)).sub contDiff_const))

theorem TE.contDiff_sumU_top (H : Sesq (VCx ι a b)) (α : VCx ι a b → ℂ) (S : Finset (VCx ι a b)) (F : VCx ι a b → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (sumU H α S F) := by
  unfold sumU
  exact ContDiff.sum fun x _ => contDiff_const.mul (TE.contDiff_opU_top H x F hF)

theorem indOmega_of {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (h : A.EOmega a b) :
    A.IndOmega a b Sall D := by
  intro N N' c x hR
  unfold Amb.thInd xiInd xiS
  exact contDiff_const.mul (contDiff_const.mul (TE.contDiff_opU_top _ _ _ (TE.contDiff_sumU_top _ _ _ _ (h N N' hR.1 hR.2.1))))

end Omega

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem even_rankN (R : Ranks) (j : ℕ) : Even (R.N j) := by
  unfold Ranks.N
  exact R.k_even.add (Even.mul_left R.t_odd.add_one j)

theorem wtLaw_step (u : Pr.Word) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩) :
    WtLaw (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) e := by
  have hNi : 0 < R.N i := R.N_pos i
  have hNi1 : 0 < R.N (i + 1) := R.N_pos _
  have hlt : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [nuLast_eq W u i hi τ]
    have h1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, by rw [Nat.add_sub_cancel]; omega⟩ := by
      unfold DomWeight.detShift
      exact dite_eq_left hNi
    have h2 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
      unfold DomWeight.detShift
      exact dite_eq_left hNi
    have h3 := Wts.nuW_eq_true W u hi τ ⟨R.N i - 1, by omega⟩
    unfold sExp' at h3
    rw [← he τ] at h3
    rw [h1, h2]
    obtain ⟨q, hq⟩ := even_rankN R (i + 1)
    have hq2 : R.N (i + 1) / 2 = q := by omega
    have hq3 : (R.N (i + 1) : ℚ) = q + q := by exact_mod_cast hq
    have h5 : ((((W.nuW u (i + 1) τ).w ⟨R.N i - 1, by rw [Nat.add_sub_cancel]; omega⟩ + (q : ℤ) - e τ : ℤ)) : ℚ) =
        (((W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ : ℤ) : ℚ) := by
      push_cast
      rw [h3, hq3]
      ring
    rw [hq2]
    exact_mod_cast h5
  · have h2 : (W.lamTrue u (i + 1) τ).detShift = (W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ := by
      unfold DomWeight.detShift
      exact dite_eq_left hNi1
    have h3 := Wts.lamTrue_new W u hi τ (⟨R.N (i + 1) - 1, by omega⟩ : Fin (R.N (i + 1)))
      (show ¬ (R.N (i + 1) - 1 < R.N i) by omega)
    unfold sExp at h3
    rw [← he τ, Nat.add_sub_cancel] at h3
    rw [h2]
    obtain ⟨q, hq⟩ := even_rankN R i
    have hq2 : R.N i / 2 = q := by omega
    have hq3 : (R.N i : ℚ) = q + q := by exact_mod_cast hq
    have h5 : (((e τ - (q : ℤ) : ℤ)) : ℚ) = ((-(W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ : ℤ) : ℚ) := by
      push_cast
      rw [h3, hq3]
      ring
    rw [hq2]
    exact_mod_cast h5

end Wt

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem top_cast {m2 : ℕ} (hm : R.m = m2 + 2) :
    (ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
        (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho ↔
      ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
        (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) ∧
    (A.AnaStep (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ↔
      A.AnaStep (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) := by
  have gen : ∀ k, k = m2 + 1 + 1 →
      (ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u k)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
          (colValF W sel mu u (m2 + 1)).rho (colVal W u k (Pr.vT u) (rowSG Pr sel mu)).rho ↔
        ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
          (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) ∧
      (A.AnaStep (R.N (m2 + 1)) (R.N k) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ↔
        A.AnaStep (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) := by
    intro k hk
    subst hk
    exact ⟨Iff.rfl, Iff.rfl⟩
  exact gen R.m hm

end Step

end Formalism.L2.Ker
end
end
