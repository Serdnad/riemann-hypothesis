module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperTheory.V.Lit.Dr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

theorem UpperTheory.V.Lit.Dr.geoProper :
    GeoProper := by
  intro E _ _ _ a ho U Ξ hU K hK hKc s s'
  obtain ⟨C, hC⟩ := boundInf E a K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective s'
  have hT : ∀ i j : Fin a, IsCompact
      ((fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val i j) '' (U : Set (GL (Fin a) (Af E)))) := by
    intro i j
    refine hU.image ?_
    have h1 : Continuous fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val :=
      Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)
    exact h1.matrix_elem i j
  have hF := Set.Finite.pi' fun i : Fin a => Set.Finite.pi' fun j : Fin a => finField E C _ (hT i j)
  have hinj : Function.Injective fun (γ : (⊤ : Subgroup (GL (Fin a) E))) (i j : Fin a) => γ.1.val i j := by
    intro γ δ h
    exact Subtype.ext (Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  refine (hF.preimage hinj.injOn).subset ?_
  rintro γ ⟨hσ, p, hp, hp'⟩ i j
  refine ⟨fun w => ?_, ?_⟩
  · have h := hC _ p hp hp'
    have h2 : ‖toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w‖ ≤ C :=
      ((norm_le_pi_norm _ w).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))).trans h
    have h3 : toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w
        = pInf E (algebraMap E (Ad E) (γ.1.val i j)) w := rfl
    rwa [h3, pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h2
  · rw [geo_σ, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq] at hσ
    refine ⟨_, hσ, ?_⟩
    have h4 : x' * (x'⁻¹ * (GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • x)) * x⁻¹
        = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 := by
      rw [smul_eq_mul]; group
    beta_reduce
    rw [h4]
    rfl
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

theorem gauge : Gauge := by
  intro E _ _ _ a ha ho U Ξ hU
  obtain ⟨f, hf, hfe⟩ := normFin E a U hU
  obtain ⟨δ, hδs, hδp, hδh, hδe⟩ := normInf E a
  have hN : a * Fintype.card (InfinitePlace E) ≠ 0 :=
    Nat.mul_ne_zero (by omega) Fintype.card_ne_zero
  generalize a * Fintype.card (InfinitePlace E) = N at hδh hN
  refine ⟨fun s p => (δ p * f s) ^ (-(N : ℝ)⁻¹), fun s => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact (((hδs.mul contDiff_const).contDiffAt (x := p)).rpow_const_of_ne
      (mul_pos (hδp p hp) (hf s)).ne').contDiffWithinAt
  · intro p hp
    exact Real.rpow_pos_of_pos (mul_pos (hδp p hp) (hf s)) _
  · intro t ht p hp
    beta_reduce
    rw [hδh, mul_assoc, Real.mul_rpow (pow_pos ht N).le (mul_pos (hδp p hp) (hf s)).le,
      Real.rpow_neg (pow_pos ht N).le, Real.pow_rpow_inv_natCast ht.le hN]
  · intro γ s p _
    beta_reduce
    have h0 : |((Algebra.norm ℚ γ.1.val.det : ℚ) : ℝ)| ≠ 0 := by
      rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
      exact γ.1.det_ne_zero
    rw [geo_ρ, geo_σ, hfe, hδe]
    congr 1
    field_simp

end UpperTheory.V.Lit.Dr
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrBasic :
    CorrBasic := by
  intro E _ _ _ a U Ξ q α w hc
  have two : ∀ (s : GL (Fin a) (Af E) ⧸ U) (p : HV E a) (v : Fin q → HV E a),
      w s p (fun i => (2 : ℝ) • v i) = (∏ _i : Fin q, (2 : ℝ)) • w s p v := fun s p v =>
    (w s p).toContinuousMultilinearMap.map_smul_univ (fun _ => (2 : ℝ)) v
  have hs : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g (sand g⁻¹ p) = p := fun g p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hs' : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g⁻¹ (sand g p) = p := fun g p => by
    simpa using hs g⁻¹ p
  constructor
  · intro h s p hp v i hi
    obtain ⟨g, rfl⟩ := hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have h0 : α (fun j => hv.symm (sand g⁻¹ (v j))) = 0 := by
      refine h _ i ?_
      rw [hi, hs']
      rfl
    have h1 := hc g x (fun j => hv.symm (sand g⁻¹ (v j)))
    simp only [LinearEquiv.apply_symm_apply, hs] at h1
    rw [h0, map_zero, two, Pi.zero_apply, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1).resolve_left (Finset.prod_ne_zero_iff.2 fun _ _ => two_ne_zero)
  · intro h X i hi
    apply (evFacts E a Ξ.d).1
    rw [map_zero]
    funext y
    set g := GeneralLinearGroup.map (pInf E) y
    set x := GeneralLinearGroup.map (pFin E) y
    have hy : infGL E a g * finGL E a x = y := infGL_mul_finGL y
    have h1 := hc g x X
    have hX : hv (X i) = hOne E a := congrArg hv (Subtype.ext hi)
    rw [two, h _ _ ⟨g, rfl⟩ (fun j => sand g (hv (X j))) i (by rw [hX]), smul_zero, hy] at h1
    have h2 := congrArg (fun v => Ξ.mat g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem mat_cancel {E : Type} [Field E] {a : ℕ} (Ξ : AlgRep E a) (g : GL (Fin a) (Cinf E))
    {v v' : Fin Ξ.d → ℂ} (h : Ξ.mat g *ᵥ v = Ξ.mat g *ᵥ v') : v = v' := by
  have h2 := congrArg (fun z => Ξ.mat g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] using h2

private theorem sand_surj {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ v))) = v := by
  rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul,
    ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem corrUniq : CorrUniq := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α α' w h h' => ?_, fun α w w' h h' => ?_⟩
  · refine AlternatingMap.ext fun X => (evFacts E a Ξ.d).1 (funext fun g => ?_)
    rw [← infGL_mul_finGL g]
    exact mat_cancel Ξ _ ((h _ _ X).symm.trans (h' _ _ X))
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      refine ContinuousAlternatingMap.ext fun v => ?_
      have e := (h g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).trans
        (h' g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).symm
      simp only [sand_surj] at e
      exact e
    · rw [(w.2 s).2 p hp, (w'.2 s).2 p hp]

end UpperTheory.V.Lit.Dr
end
end
