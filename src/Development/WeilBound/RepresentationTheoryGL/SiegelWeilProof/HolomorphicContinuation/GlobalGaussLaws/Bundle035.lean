module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle023
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle031
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ProdF
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle033
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle029
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

variable {D : D7}



theorem incl_trA (z : AE D) : algebraMap (AF D.host.F) (AE D) (trA z) = z + cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [trA]
  | tmul a e =>
    simp only [trA]
    rw [GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul (AF D.host.F) a e]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h : (Algebra.trace D.host.F D.host.E e : D.host.E) = e + star e := GlobalTheory.TraceAddStar.trace_eq_add_star e
    calc (a * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)) ⊗ₜ[D.host.F] (1 : D.host.E)
        = a ⊗ₜ[D.host.F] ((Algebra.trace D.host.F D.host.E e : D.host.F) : D.host.E) := by
          rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl
      _ = a ⊗ₜ[D.host.F] e + cA D (a ⊗ₜ[D.host.F] e) := by
          rw [h, TensorProduct.tmul_add]; rfl
  | add x y hx hy =>
    simp only [trA, map_add (f := _)] at hx hy ⊢
    rw [hx, hy]; abel



theorem psi_eq_of_fin {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (a : AF D.host.F) (ha : finPart D (algebraMap (AF D.host.F) (AE D) a) = 0) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * psiT D τ (algebraMap (AF D.host.F) (AE D) a)) := by
  have hsnd : sndA D.host.F a = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (S := Af D.host.F) (algebraMap D.host.F D.host.E).injective
    rw [map_zero]
    exact ha
  have ha' : a = pairA D.host.F (fstA D.host.F a) 0 := Prod.ext rfl hsnd
  have h1 : ψ a = psiInf D.host.F ψ (fstA D.host.F a) := by
    conv_lhs => rw [ha']
    rfl
  rw [h1, hl, eq_thetaC D hθ]
  rfl



theorem psi_trA_tau {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) (z : AE D) (hz : ∀ τ', τ' ≠ τ → psiT D τ' z = 0)
    (hzf : finPart D z = 0) :
    ψ (trA z) = Complex.exp (Complex.I * ((4 * Real.pi * l τ : ℝ) : ℂ) * ((psiT D τ z).re : ℂ)) := by
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (trA z)) = 0 := by
    rw [incl_trA, RingHom.map_add (f := _), hzf, cA, Formalism.IndefR.Eqv.finPart_sigR, hzf, RingHom.map_zero, add_zero]
  rw [psi_eq_of_fin hθ hl _ hfin, incl_trA]
  have hs : ∑ τ', (l τ' : ℂ) * psiT D τ' (z + cA D z) = (l τ : ℂ) * (2 * ((psiT D τ z).re : ℂ)) := by
    rw [Finset.sum_eq_single τ]
    · rw [RingHom.map_add (f := _), cA, psiT_sigR, Complex.add_conj]; push_cast; ring
    · intro τ' _ hne
      rw [RingHom.map_add (f := _), cA, psiT_sigR, hz τ' hne, map_zero, add_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h
  rw [hs]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF
  PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ PositivityTheory.Rg.Sw.Glob.VacK

private theorem cnt_true_add_cnt_false {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem vacK_of : GZSch → LawN → LawNbar → LocMul → LNe → VacK := by
  intro hGZ hN hNb hLM hLNe
  unfold PositivityTheory.Rg.Sw.Glob.VacK
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL e hlev k hk
  have hl0 : l τ ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ
  have hc0 : 0 < cLoc l τ := VacF.cpos hl0
  have hSch : ∀ K : ℂ, IsSch (DG (m := V.rank) (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    fun K => VacE.isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc0 VacF.tabs K
  obtain ⟨u, u', φ, hu, hu', hφ, hkm⟩ := VacG.kak (mR k) hk
  have hdu : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  have hdu' : IsUnit u'.det := Matrix.isUnit_det_of_left_inverse hu'
  have hk_eq : k = VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1 *
      VacB.mkG (mM u') (VacB.inG_mM u' hdu') := by
    apply Subtype.ext
    apply Units.ext
    change mR k = mR (VacB.mkG (mM u) (VacB.inG_mM u hdu)) * mR (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) *
      mR (VacB.mkG (mM u') (VacB.inG_mM u' hdu'))
    rw [VacB.mR_mkG, VacB.mR_mkG, VacB.mR_mkG]
    exact hkm
  have hLM' := hLM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC L hL
  have h1 : L (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hlev _ u' hdu' (VacB.mR_mkG _ _) _ (hSch 1)]
    exact VacH.levF_unitary e u' hu' 1 _
  have h2 := VacJ.rot_gen hC hl0 hN hNb hLM hGZ L hL e hlev φ hφ
    (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)))
  have h3 : ∀ K : ℂ, L (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    intro K
    rw [hlev _ u hdu (VacB.mR_mkG _ _) _ (hSch K)]
    exact VacH.levF_unitary e u hu K _
  have hLk : L k (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
        (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
        (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hk_eq, hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1)
      (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) _ (hSch 1), h1,
      hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) _ (hSch _), h2, h3]
  have hsu : star u.det = u.det⁻¹ := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hsu' : star u'.det = u'.det⁻¹ := by
    have h := congrArg Matrix.det hu'
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hm : (V.rank : ℤ) = ((cnt (epsT (tLoc l τ) ε) true + cnt (epsT (tLoc l τ) ε) false : ℕ) : ℤ) := by
    rw [cnt_true_add_cnt_false]
  have hX : (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _
  have hXinv : ∏ j, Complex.exp (-(Complex.I * (φ j : ℂ))) = (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    simp only [Complex.exp_neg, Finset.prod_inv_distrib]
  have hK : 1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
      (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
      (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e)) =
      jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) := by
    rw [VacI.jF_kak e _ _ k u u' φ hu hu' hφ hkm, VacK.prodF, hsu, hsu', hm, hXinv]
    exact VacK.alg _ _ _ hdu.ne_zero hdu'.ne_zero hX e _ _
  rw [VacC.vac_eq, hLk]
  funext v
  rw [VacC.dg_const, VacC.dg_const, hK]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
