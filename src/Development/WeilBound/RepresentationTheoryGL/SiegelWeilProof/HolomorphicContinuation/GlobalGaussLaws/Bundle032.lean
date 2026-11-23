module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle307
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle028
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle029
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle023
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle030
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilEH

attribute [local irreducible] famC

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have e : (-(Complex.I / 2)) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, ← sub_smul, smul_smul]
    have : -(Complex.I / 2) * (Complex.I - -Complex.I) = 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, one_smul]
  rw [e]; exact Matrix.PosDef.one


theorem exch (hDR : DReal) (hDB : DBound) (hDC : DCalc) (hDL : DifferenceQuotientIsometryExchange) (hCD : ContDeriv) (hSS : SchScale) (hSF : SchFP)
    (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {ε : Fin V.rank → Bool} {t c : ℝ} (hc : 0 < c)
    (htc : |t| = c) {e : ℤ}
    (hG : ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε t c Z) = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y Z * gZf ε t c (actZ y Z) u)
    {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y'' : GR n) {κ : ℝ} (hκ : 0 < κ)
    (hL2 : ∀ f, IsSch f → ∫ u, ‖L y'' f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) (r : ℕ) :
    L y'' (fP c ((dil c X ^ r) 1)) = fun u => iteratedDeriv r (fun s : ℝ => famC ε t c e y'' X s u) 0 := by
  have hg0 : gZf ε t c (Complex.I • 1) = fP c (1 : PX V.rank n) := (DilAH.fP_one ε t c hc).symm
  have hg0s : IsSch (gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) : (Fin V.rank → Fin n → ℂ) → ℂ) := by
    rw [hg0]; exact hSF _ _ c hc 1
  have hbase : ∀ (y : GR n) (s : ℝ), L (y * a s) (gZf ε t c (Complex.I • 1)) = famC ε t c e y X s := by
    intro y s
    rw [hG _ _ isSiegel_I, hDR _ _ ε t c e y X a ha s]
  set Gf : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ := fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s
    with hGf
  set Ef : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ :=
    fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e y'' X s' u) s with hEf
  obtain ⟨hC1, hC2⟩ := hDC V.rank n ε t c e X hc htc
  obtain ⟨hB1, hB2, -⟩ := hDB V.rank n ε t c e X hc htc
  have hGs : ∀ r s, IsSch (Gf r s) := by
    intro r s
    have : Gf r s = fun u => (Real.exp (s * (V.rank : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j)) := by
      funext u; exact hC1 s r u
    rw [this]
    exact hSS _ _ _ s X _ (hSF _ _ c hc _)
  have hstrip : IsOpen (stripS X) := DBoundBH.isOpen_stripS X
  have hR : ∀ s : ℝ, (s : ℂ) ∈ stripS X := fun s j => by simp [div_pos Real.pi_pos]

  set F : ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun z u => famC ε t c e y'' X z u with hF
  have hFd : ∀ u, DifferentiableOn ℂ (fun z => F z u) (stripS X) := fun u => hB1 y'' u
  have hFc : ContinuousOn (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => F p.1 p.2) (stripS X ×ˢ Set.univ) := by
    have hcont : Continuous (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => ((y'', p) : GR n × (ℂ × (Fin V.rank → Fin n → ℂ)))) :=
      continuous_const.prodMk continuous_id
    exact hB2.comp hcont.continuousOn fun p hp => ⟨Set.mem_univ _, hp⟩
  have hEr : ∀ r u, (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F s' u) s) = fun s : ℝ => iteratedDeriv r (fun z => F z u) s :=
    fun r u => DilCH.iteratedDeriv_ofReal hstrip (hFd u) hR r
  have key : ∀ r s, L y'' (Gf r s) = Ef r s := by
    intro r
    induction r with
    | zero =>
      intro s
      have e1 : Gf 0 s = L (a s) (gZf ε t c (Complex.I • 1)) := by
        funext u; rw [← one_mul (a s), hbase]; simp [hGf]
      have e2 : Ef 0 s = famC ε t c e y'' X s := by funext u; simp [hEf]
      rw [e1, e2, ← DilCH.L_mul hL hθ hfr hΨ hx₀ y'' (a s) hg0s, hbase]
    | succ r ih =>
      intro s
      refine hDL V.rank n (L y'') κ hκ (fun f hf => hL.1 y'' f hf)
        (fun f g hf hg => DilCH.L_sub hL hθ hfr hΨ hx₀ y'' hf hg)
        (fun a' f hf => DilCH.L_smul hL hθ hfr hΨ hx₀ y'' a' hf) hL2 (Gf r) (Gf (r + 1) s) (Ef (r + 1) s) s
        (hGs r) (hGs (r + 1) s) ?_ (hC2 r s) ?_
      ·
        have hcd := hCD V.rank n (stripS X) hstrip F hFc hFd (r + 1)
        have : Ef (r + 1) s = fun u => iteratedDeriv (r + 1) (fun z => F z u) (s : ℂ) := by
          funext u; simp only [hEf]; rw [show (fun s' : ℝ => famC ε t c e y'' X s' u) = fun s' : ℝ => F s' u from rfl,
            congrFun (hEr (r + 1) u) s]
        rw [this]
        exact hcd.comp_continuous (f := fun u : Fin V.rank → Fin n → ℂ => ((s : ℂ), u))
          (continuous_const.prodMk continuous_id) fun u => ⟨hR s, Set.mem_univ _⟩
      · intro u
        simp only [ih]
        have hd : HasDerivAt (fun s' : ℝ => Ef r s' u) (Ef (r + 1) s u) s := by
          have e3 : (fun s' : ℝ => Ef r s' u) = fun s' : ℝ => iteratedDeriv r (fun z => F z u) s' := hEr r u
          have e4 : Ef (r + 1) s u = iteratedDeriv (r + 1) (fun z => F z u) s := congrFun (hEr (r + 1) u) s
          rw [e3, e4, iteratedDeriv_succ]
          exact ((DilCH.diffOn_iteratedDeriv hstrip (hFd u) r).differentiableAt
            (hstrip.mem_nhds (hR s))).hasDerivAt.comp_ofReal
        have := hd.tendsto_slope_zero
        refine this.congr fun h => ?_
        simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]
  have e0 : Gf r 0 = fP c ((dil c X ^ r) 1) := by
    funext u; rw [show Gf r 0 u = _ from hC1 0 r u]; simp
  rw [← e0, key r 0]

end PositivityTheory.Rg.Sw.Glob.DilEH
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GCSchH

theorem gCSch : GCSch := by
  intro m n ε t c hc htc Z Z' hZ hZ'
  set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS
  set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'
  set B := qB S S' c Z Z' with hB
  have hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u)) := by
    funext u
    simp only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]
    rfl
  have hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef := by
    have h := hZ.transpose
    rwa [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose] at h
  have hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef := by
    have h := hZ'.transpose
    unfold IsSiegel at h
    rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.conjTranspose_transpose] at h
    rwa [Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]
  have hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re) := by
    intro u
    rw [hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]
    have e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im := by
      intro a; rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]
    simp only [e2, Finset.sum_neg_distrib, im_quad]
    ring
  have hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re := by
    intro u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
    rw [hre]
    apply mul_pos hc
    have n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP1 _
    have n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP2 _
    cases hb : epsT t ε a
    · have haS : a ∈ S' := by simp [hS', hb]
      have p2 := Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩
      linarith
    · have haS : a ∈ S := by simp [hS, hb]
      have p1 := Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩
      linarith
  obtain ⟨κ, hκ, hco⟩ := coercive_of_pos B hpos
  obtain ⟨g, hg, -⟩ := GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco
  refine ⟨g, ?_⟩
  rw [hgC]
  funext u
  exact hg u

theorem gZSch : GZSch := by
  intro m n ε t c hc htc Z hZ
  show IsSch (gC ε t c Z Zᴴ)
  exact gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)

end PositivityTheory.Rg.Sw.Glob
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

open GaussH

theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
