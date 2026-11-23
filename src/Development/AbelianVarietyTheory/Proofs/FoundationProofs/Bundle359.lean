module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevel
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem shCoc_wsum_props : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (ρ : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin 2) (Fin 2) (Qbar l)) (cf : Coef l) (ι : Type) [Fintype ι] (cw : ι → Qbar l)
  (Yx : ι → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ i r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Yx i r)) →
  (∀ i r, Yx i r = push (redL l r) (Yx i (r + 1))) →
  (∀ i r y j, Continuous fun s => Yx i r s y j) →
  (∀ i r s u j, Yx i r s u j ∈ cf.O) → (∀ i, cw i ∈ cf.O) →
  (∀ r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (fun s y => ∑ i, cw i • Yx i r s y)) ∧
  (∀ r, (fun s y => ∑ i, cw i • Yx i r s y) = push (redL l r) (fun s y => ∑ i, cw i • Yx i (r + 1) s y)) ∧
  (∀ r y j, Continuous fun s => (∑ i, cw i • Yx i r s y) j) ∧
  (∀ r s u j, (∑ i, cw i • Yx i r s u) j ∈ cf.O) := by
  intro l _ Ω _ _ ρ cf ι _ cw Yx hC hP hCont hO hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s t x
    have := fun i => hC i r s t x
    simp only [this, Finset.sum_add_distrib, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · intro r
    funext s y
    simp only [push]
    conv_lhs => rw [show (∑ i, cw i • Yx i r s y) = ∑ i, cw i • push (redL l r) (Yx i (r + 1)) s y from by
      simp only [← hP]]
    simp only [push, Finset.smul_sum]
    exact Finset.sum_comm
  · intro r y j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hCont i r y j)
  · intro r s u j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hw i) (hO i r s u j)

end GlobalTheory.K4
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.jet

theorem jet_bound_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (hGT : G ∈ Th D (tor0 D cc δ) L L')
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (n : D.what₂.Tau → ℕ) (B : ℝ) (hB : 1 ≤ B) (hn : ∀ τ, (n τ : ℝ) ≤ 2 * B)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) (T : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
    ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤
      ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 *
        (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
          normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) *
          (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  have hg1 : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2 Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hg1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.T.galois_data_exists D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
    (by omega)
  have hgal := (GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [GlobalTheory.ConjJet.comb_one]; exact hA)
    (by rw [GlobalTheory.ConjJet.comb_one]; exact hAU y hy)).1
  rw [GlobalTheory.ConjJet.comb_one] at hgal
  have hdiff := GlobalTheory.ConjJet.U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1
  obtain ⟨hmem, hcj⟩ := (GlobalTheory.ConjSeries.taylor_fnConj D a d Qbar ρ (U D (tor0 D cc δ) y G)
    (by rw [hgal]; exact hdiff) (by rw [hgal]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ hne)).2 (hAU y hy) n T
  refine ⟨hmem, ?_⟩
  rw [hcj, hgal]
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  refine (GlobalTheory.MinorBound.minor_bound D a d n _ _ (area (lamConj Qbar ρ (lamOf D cc δ))) B
    (by rw [hΛ]; exact GlobalTheory.ConjJet.area_pos D hg1 cc' δ' hc') hB ?_ hn hdiff fun z => ?_).2 T
  · have := GlobalTheory.ConjJet.normSq_nonneg D (torConj D (tor0 D cc δ) Qbar ρ)
      (La D (torConj D (tor0 D cc δ) Qbar ρ) L L') (fnConj D Qbar ρ G)
    positivity
  · have := GlobalTheory.ConjJet.sup_perm D hg1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh y' z
    rw [GlobalTheory.ConjJet.Hf_re, ← mul_div_assoc] at this
    exact this

theorem vacuum_mem_thetaSpace_pair (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_jet_bound : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  intro D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy n B hB hn ρ t0' ht' T
  have hGT := vacuum_mem_thetaSpace_pair D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t0' ht'
  rw [← hN]
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc Qbar ρ hdata
  · exact jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB hn ρ hfix T
  · obtain ⟨hmem, hle⟩ := jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB
      hn (rhoBar Qbar ρ) hfix T
    refine ⟨hmem, ?_⟩
    obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [GlobalTheory.ConjJet.U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [GlobalTheory.ConjJet.cj_bar, (hbar a d L L' G).1, htor, hn2, hL, GlobalTheory.ConjJet.area_conj] at hle
    exact hle

end GlobalTheory.ArchFree.jet
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem norm_le_one_of_isIntegral_zl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) :
    ‖(a : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_zl l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

theorem norm_unit_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (u : c.Oˣ) :
    ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem_coefO c u
  have h3 := norm_le_one_of_mem_coefO c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem mem_coefO_of_memE_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l),
    MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  intro l _ c x hE hx
  obtain ⟨k, hk⟩ := hE
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  set y : c.O := ⟨_, hk⟩ with hy
  set L : c.O := (l : c.O) ^ k with hL
  have hLval : ((L : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k := by simp [hL]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hL0 : L ≠ 0 := by
    intro h
    have : ((L : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    rw [hLval] at this
    exact pow_ne_zero k hl0 this
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  by_cases hy0 : y = 0
  · have : (l : PadicAlgCl l) ^ k * x = 0 := by
      have := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy0
      simpa [hy] using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero k hl0)
    · rw [h]; exact c.O.zero_mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ z : c.O, z ≠ 0 → ∃ n : ℕ, ‖(z : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n ∧
      ϖ ^ n ∣ z ∧ z ∣ ϖ ^ n := by
    intro z hz
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [h, Subalgebra.coe_mul, norm_mul, norm_unit_coefO, one_mul, Subalgebra.coe_pow, norm_pow]
    · exact ⟨(u : c.O), by rw [h, mul_comm]⟩
    · exact ⟨((u⁻¹ : c.Oˣ) : c.O), by rw [h, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨a, hya, hdy, -⟩ := key y hy0
  obtain ⟨b, hLb, -, hdL⟩ := key L hL0
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := norm_le_one_of_mem_coefO c ϖ
  have hϖ0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hyx : ((y : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * x := rfl
  have hLlt : ‖((L : c.O) : PadicAlgCl l)‖ < 1 := by
    rw [hLval, norm_pow, hnl]
    exact pow_lt_one₀ (by positivity) hlt1 (by omega)
  have hϖlt : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    rcases lt_or_eq_of_le hϖ1 with h | h
    · exact h
    exfalso
    rw [hLb, h, one_pow] at hLlt
    exact lt_irrefl _ hLlt
  have hab : b ≤ a := by
    have hle : ‖(ϖ : PadicAlgCl l)‖ ^ a ≤ ‖(ϖ : PadicAlgCl l)‖ ^ b := by
      rw [← hya, ← hLb, hyx, hLval, norm_mul]
      calc ‖(l : PadicAlgCl l) ^ k‖ * ‖x‖ ≤ ‖(l : PadicAlgCl l) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := mul_one _
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 hle
  have hdiv : L ∣ y := dvd_trans hdL (dvd_trans (pow_dvd_pow ϖ hab) hdy)
  obtain ⟨z, hz⟩ := hdiv
  have : (l : PadicAlgCl l) ^ k * x = (l : PadicAlgCl l) ^ k * (z : PadicAlgCl l) := by
    rw [← hyx, hz, Subalgebra.coe_mul, hLval]
  rw [mul_left_cancel₀ (pow_ne_zero k hl0) this]
  exact z.2

end GlobalTheory.Ord2
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Kill

variable {l : ℕ} [Fact l.Prime]

theorem mem_of_memE (c : Coef l) {x : Qbar l} (hE : MemE c x) (hx : ‖x‖ ≤ 1) : x ∈ c.O := by
  obtain ⟨k, hk⟩ := hE
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hn : ‖(l : Qbar l) ^ k * x‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx
  obtain ⟨w, hw, e⟩ := Rec.exists_eq_pow_mul_of_norm_le hk hn
  have : x = w := mul_left_cancel₀ (pow_ne_zero k hl0) e
  rw [this]; exact hw

theorem adj_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    M.adjugate i j ∈ c.O := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [c.O.neg_mem, hM]

theorem norm_mulVec_le (c : Coef l) {A : Matrix (Fin 2) (Fin 2) (Qbar l)} (hA : ∀ i j, A i j ∈ c.O)
    {v : Fin 2 → Qbar l} (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin 2) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
  · rw [norm_mul]; exact mul_le_one₀ (Rec.norm_le_one_of_mem (hA _ _)) (norm_nonneg _) (hv _)

end GlobalTheory.Ord2.Kill

namespace GlobalTheory.Ord2


open Kill in
theorem exists_pow_smul_cob1_of_cv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l),
    (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∃ r : ℕ, ∀ (n : ℕ) (a : G ℚ Ω → Fin 2 → Qbar l)
      (y : Fin 2 → Qbar l), (∀ s i, a s i ∈ c.O) → VecE c y → (∀ s, Cv n (a s) (mat W s *ᵥ y - y)) →
      Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ r • a s) := by
  intro l _ Ω _ _ W c hW ⟨g, hg⟩
  set M := mat W g - 1 with hMdef
  have hMO : ∀ i j, M i j ∈ c.O := fun i j => by
    simp only [M, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hW g i j) c.O.one_mem
    · simpa using hW g i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hd : 0 < ‖M.det‖ := norm_pos_iff.2 hg
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hd hlinv
  refine ⟨r, fun n a y ha hy h => ?_⟩
  have hlr : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ)⁻¹ ^ r := by rw [norm_pow, Rec.norm_natCast_l]
  have hlr1 : ‖((l : ℕ) : Qbar l) ^ r‖ ≤ 1 := by rw [hlr]; exact pow_le_one₀ hlpos.le hlinv.le
  have hln1 : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ 1 := by
    rw [norm_pow, Rec.norm_natCast_l]; exact pow_le_one₀ hlpos.le hlinv.le

  have hMy : ∀ j, ‖(M *ᵥ y) j‖ ≤ 1 := by
    intro j
    have e : (M *ᵥ y) j = a g j - (a g j - (mat W g *ᵥ y - y) j) := by
      simp [M, Matrix.sub_mulVec]
    rw [e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (Rec.norm_le_one_of_mem (ha g j)) ?_)
    rw [norm_neg]
    exact (h g j).trans hln1

  have hdy : ∀ i, ‖M.det * y i‖ ≤ 1 := by
    intro i
    have e : M.det * y i = (M.adjugate *ᵥ (M *ᵥ y)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [e]
    exact norm_mulVec_le c (adj_mem c hMO) hMy i
  have hx : ∀ i, ((l : ℕ) : Qbar l) ^ r * y i ∈ c.O := by
    intro i
    apply mem_of_memE c
    · obtain ⟨k, hk⟩ := hy
      refine ⟨k, ?_⟩
      have e : (l : Qbar l) ^ k * (((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r * ((l : Qbar l) ^ k * y i) := by
        ring
      rw [e]
      exact c.O.mul_mem (natPow_mem c r) (hk i)
    · have h1 := hdy i
      rw [norm_mul] at h1 ⊢
      calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖y i‖ ≤ ‖M.det‖ * ‖y i‖ := by
            gcongr; rw [hlr]; exact hr.le
        _ ≤ 1 := h1
  refine ⟨fun i => ((l : ℕ) : Qbar l) ^ r * y i, hx, fun s _ i => ?_⟩
  have e : (((l : ℕ) : Qbar l) ^ r • a s) i - (mat W s *ᵥ (fun i => ((l : ℕ) : Qbar l) ^ r * y i) -
      fun i => ((l : ℕ) : Qbar l) ^ r * y i) i = ((l : ℕ) : Qbar l) ^ r * (a s i - (mat W s *ᵥ y - y) i) := by
    have : (fun i => ((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r • y := by
      funext i; simp
    rw [this, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold Cg
  rw [e, norm_mul]
  calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖a s i - (mat W s *ᵥ y - y) i‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hlr1 (h s i) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_coefficientRing_finiteExtension_padic : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E → ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CoefJoin.coef_of_finite | exact GlobalTheory.CoefJoin.coef_of_finite | (intros; apply GlobalTheory.CoefJoin.coef_of_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.norm_le_pow_iff_dvd : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O), ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  first | exact @GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | exact GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | (intros; apply GlobalTheory.Coef.norm_le_norm_pow_iff_dvd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_prime_pow_mul_deep_congruenceLevel : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 1)‖) → ∃ h g' : Γ, (∀ i j, ‖((r h : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) ∧ (∀ i j, ‖((r g' : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 2)‖) ∧ g = h ^ l * g' := by
  first | exact @GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level | exact GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level | (intros; apply GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.transported_weylLattice_hermitianDuality : NabDelDual := by
  first | exact @GlobalTheory.TransDual.nabDelDual | exact GlobalTheory.TransDual.nabDelDual | (intros; apply GlobalTheory.TransDual.nabDelDual <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places : ∀ D : D7, odd3 D := by
  first | exact @GlobalTheory.InertSign.vacuum_inert | exact GlobalTheory.InertSign.vacuum_inert | (intros; apply GlobalTheory.InertSign.vacuum_inert <;> assumption)
end
