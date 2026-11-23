module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle054
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle056
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle281
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ConjLatticeCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem conj_lattice_core :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hC := GlobalTheory.ConjLattice.containsData hM
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := hC.1
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => GlobalTheory.ConjLattice.lamConj_spec GlobalTheory.ConjLattice.uniformization_holds M ρ'
    (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  have hfix : ∀ ρ' : M →ₐ[ℚ] ℂ, EquidistributedConjugates.FixesK D M ρ' → ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ,
      x ≠ 0 ∧ lamConj M ρ' (lamOf D cc δ) = lamOf D c x := by
    intro ρ' hρ'
    obtain ⟨cc', δ', hc', -, he⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ ⟨hcc, hδ⟩ M ρ'
      (GlobalTheory.ConjEquidistrib.fixK_of_fixesK D M ρ' hm hρ') h2 h3 1 one_pos
    exact ⟨cc', hc'.1.1, δ', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc' hc'.1 δ' hc'.2, he⟩
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · exact hfix ρ hρ
  · have hρ' : EquidistributedConjugates.FixesK D M (EquidistributedConjugates.conjEmb M ρ) :=
      (GlobalTheory.ConjEquidistrib.fixesK_conjEmb_iff D M ρ hm).2 hρ
    obtain ⟨c, hc, x, hx, hxe⟩ := hfix _ hρ'
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds
        GlobalTheory.ConjLattice.uniformization_holds
    have hmap : (lamConj M ρ (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj =
        lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [GlobalTheory.ConjLattice.discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [GlobalTheory.ConjLattice.eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [GlobalTheory.ConjLattice.eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj := by
      rw [← hmap, GlobalTheory.ConjLattice.map_cj_map_cj]
    refine ⟨c.map (GlobalTheory.ConjLattice.conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx,
      by rw [hback, hxe, GlobalTheory.ConjLattice.lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (GlobalTheory.ConjLattice.conjO D).injective] at hbot
    exact hc hbot

end GlobalTheory.ConjLatticeCore
end
end

section

noncomputable section

namespace GlobalTheory.SatBc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem satU_eq_of_bcParam_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ,
      GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' →
      ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU α α' e φ hφ
  have e1 := congrArg (Multiset.map fun z : ℂˣ => (z : ℂ)) (add_right_cancel e)
  refine GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq _ (SatU ϖ q φ)
    (fun γ hγ => GlobalTheory.SatakeWeyl.satWeyl L ϖ σ q n (n / 2) hU (by omega) (by omega) γ hγ φ hφ) _ _
    (fun i => (α i).ne_zero) ?_
  simpa [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBc
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes


theorem _root_.GlobalTheory.T.exists_bound_abs_localLatticeCompletion_entries : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := by
  first | exact @GlobalTheory.absFin_latLoc_le | exact GlobalTheory.absFin_latLoc_le | (intros; apply GlobalTheory.absFin_latLoc_le <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda


open Formalism.L2.Th1 in
theorem mulBy_coefLe_of_kernel_prime_to :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  intro L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker
  have hβp : ι β ≠ 0 := by
    intro h
    rw [h, norm_zero] at hβ
    exact zero_ne_one hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, map_zero] at hβp
    exact hβp rfl
  have hW : E.IntCurve (E.curveL l L ι) := E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hΔ : (E.curveL l L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htwo := E.ScaledModelNorms.norm_two l hl
  have hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨S, hS⟩ := F.kerRepsExist L β hβ0 hst
  obtain ⟨neg, -, hE⟩ := F.endoZInstance L β S hβ0 hst hS
  have hb2 : (E.curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hEp := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
  rw [← E.wpBridge l L ι] at hEp
  have hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β) := by
    rw [hb2]
    simpa using hEp
  have hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    have := E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD)
      (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2
    simpa using this
  obtain ⟨hLP, hXW, hA, -, -⟩ := C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC
  have hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l] := by
    intro x hx
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv, hx, inv_one]
  have hM := A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1
    hC.2.2.2.2
  have key := C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι))
    (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι))
    ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ)))
    (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    (fun P : S => E.xT (E.curveL l L ι) (E.ptOf l L ι (P : ℂ))) (ι β)
    ((ι β)⁻¹ * ((Fintype.card S : ℂ_[l]) + 1)) hLP hXW hA (hinv _ htwo)
    ⟨hEp', by rw [← mul_assoc, mul_inv_cancel₀ hβp, one_mul], ?_, ?_, fun P => (hint P).1, hβ.le,
      hinv _ hβ, by rw [hb2, zero_div, mul_zero]; exact zero_mem _⟩
  · exact fun n => key n
  · intro P
    rw [hb2, zero_div, map_zero, add_zero]
    exact E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2
  · intro P n
    unfold E.xT
    beta_reduce
    rw [E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]
    refine (hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1
    show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
    rw [norm_div, htwo, div_one]
    exact (hint P).2

end GlobalTheory.Honda

end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧ ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  first | exact @GlobalTheory.KJInf.Vn_unit_irreducible | exact GlobalTheory.KJInf.Vn_unit_irreducible | (intros; apply GlobalTheory.KJInf.Vn_unit_irreducible <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf.VnStable

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem lft_rename (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (p : MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (rename (Prod.mk τ) p) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) p) := by
  have : (lft g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ : MvPolynomial (Fin a × Fin a) ℂ →ₐ[ℂ] PY ι a => φ p) this

theorem lft_ten (g : ι → Matrix (Fin a) (Fin a) ℂ) (f : ι → MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (ten f) = ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ)) := by
  simp only [ten, map_prod, lft_rename]

theorem lft_frDet (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    lft g (frDet ℂ a τ : PY ι a) = (g τ).det • (frDet ℂ a τ : PY ι a) := by
  unfold frDet
  rw [AlgHom.map_det]
  have hM : (lft g).mapMatrix (Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a)) =
      (g τ).map C * Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a) := by
    ext α s
    simp [lft, Matrix.mul_apply]
  rw [hM, Matrix.det_mul, smul_eq_C_mul]
  congr 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem prod_mem_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A) (x : ι → A)
    (h : ∀ τ ∈ s, x τ ∈ M τ) : ∏ τ ∈ s, x τ ∈ ∏ τ ∈ s, M τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Submodule.one_le.mp le_rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact Submodule.mul_mem_mul (h i (Finset.mem_insert_self _ _))
      (ih fun τ hτ => h τ (Finset.mem_insert_of_mem hτ))

theorem fg_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A)
    (h : ∀ τ, (M τ).FG) : (∏ τ ∈ s, M τ).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i).mul ih

theorem ten_mem_prod (lam : ι → DomWeight a) (f : ι → MvPolynomial (Fin a × Fin a) ℂ)
    (hf : ∀ τ, f τ ∈ delSq ℂ a (lam τ)) :
    ten f ∈ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
  unfold ten
  exact prod_mem_prodS _ _ _ (fun τ _ => Submodule.mem_map_of_mem (hf τ))

theorem cspan_fd (lam : ι → DomWeight a) : FiniteDimensional ℂ (CSpan lam) := by
  have hP : (∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap).FG := by
    apply fg_prodS
    intro τ
    apply Submodule.FG.map
    haveI := (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).1
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  have hle : CSpan lam ≤ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro p ⟨f, hf, rfl⟩
    exact ten_mem_prod lam f hf
  haveI : FiniteDimensional ℂ ↥(∏ τ, ((delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap : Submodule ℂ (PY ι a))) :=
    (Submodule.fg_iff_finiteDimensional _).mp hP
  exact Submodule.finiteDimensional_of_le hle

theorem lft_cspan (lam : ι → DomWeight a) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    ∀ p ∈ CSpan lam, lft g p ∈ CSpan lam := by
  intro p hp
  unfold CSpan at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [lft_ten]
    exact Submodule.subset_span ⟨_, fun τ => (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).2.2.1 (g τ) (f τ) (hf τ), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.KJInf.VnStable


open GlobalTheory.KJInf.VnStable in
theorem GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ),
    FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  intro ι _ a lam n
  haveI := cspan_fd lam
  refine ⟨?_, ?_⟩
  · unfold Vn; infer_instance
  · intro g F hF
    unfold Vn at hF ⊢
    obtain ⟨p, hp, rfl⟩ := hF
    have hD : lft g (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) = C (∏ τ, (g τ).det ^ n τ) * ∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ := by
      rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, lft_frDet, smul_eq_C_mul, mul_pow, map_pow]
    refine ⟨(∏ τ, (g τ).det ^ n τ) • lft g p, Submodule.smul_mem _ _ (lft_cspan lam g p hp), ?_⟩
    simp only [LinearMap.mulRight_apply, map_mul, hD, smul_eq_C_mul]; ring
end
end

section

noncomputable section

namespace GlobalTheory.Core.Ht2.LastDatumS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
open GlobalTheory.TopStep GlobalTheory.ColNorms.LastDatum

theorem smallDatum_xiCpl2_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : _root_.Formalism.L2.Col.Fields) (s : Seam D X) (Pr : _root_.Formalism.L2.Col.Primes X) (W : _root_.Formalism.L2.Col.Wts X Pr.Word N.R) (Ch : _root_.Formalism.L2.Col.Chars X Pr N.R.m) (G : _root_.Formalism.L2.Col.ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : _root_.Formalism.L2.Col.LocCst X (_root_.Formalism.L2.Col.rowSG Pr sel mu)) (I : _root_.Formalism.L2.Col.ChIdx X Pr N.R (_root_.Formalism.L2.Col.QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : _root_.Formalism.L2.Col.ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : _root_.Formalism.L2.Col.RowPt Pr N.R sel mu), ∀ Y ∈ _root_.Formalism.L2.Col.ybSet sel mu cst p.deco.1.N, SmallDatum (_root_.Formalism.L2.Col.Sall sel mu u) p.deco.1.N (_root_.Formalism.L2.Col.tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (_root_.Formalism.L2.Col.XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hY
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hI := H.2.2.2.2.2.2.1
  have hT : TilOk Pr sel mu u := by
    refine tilOk_of hPr u fun P hP => ?_
    have hmu : mu = mu0 X.F X.E X.K Sg := H.2.2.2.2.1
    rw [hmu, _root_.Formalism.L2.Col.twistPrimes_trivialTuple_empty sel Sg] at hP
    simp at hP
  have key := EntryDatum.smallDatum_prod (K := X.K) (S := _root_.Formalism.L2.Col.Sall sel mu u) p.deco.1 (_root_.Formalism.L2.Col.tilQ sel mu u d).1 (_root_.Formalism.L2.Col.tilQ sel mu u d).2
    (_root_.Formalism.L2.Col.frsF sel mu p) (tilFr hT d) (frsF_mem p) (fun P => (tilFr_isLiftFr hT d P).1)
    (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P y => locTop Ch sel mu cst (N.R.m - 2) P y ((_root_.Formalism.L2.Col.frsF sel mu p P).symm (_root_.Formalism.L2.Col.repY Y))) (fun _ => 1)
    (fun P => locSmall_locTop hI.hm hI.cst_ok H.2.2.2.2.2.1 (h1 P.1 P.2) (repY_int p hY (h1 P.1 P.2)))
  rw [Finset.prod_const_one] at key
  convert key using 1
  funext x
  unfold _root_.Formalism.L2.Col.XiCpl2
  simp only [locTop_tilFr]

end GlobalTheory.Core.Ht2.LastDatumS
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosetsS

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (GlobalTheory.CouplingCosets.finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosetsS
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.MovedDatumS

theorem omPhi_locSmall_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 1 < N.R.m → ∀ (P : rowSG Pr sel mu) (h : AutY X N.R i) (h' : AutY X N.R (i + 1)), h ∈ stabL X.E _ (lamYat (Pr := Pr) i P.1) → h' ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1) → LocSmall (Formalism.L2.Col.qOf P.1) (lamYat (Pr := Pr) (R := N.R) i P.1) (lamYat (Pr := Pr) (R := N.R) (i + 1) P.1) (omPhi Ch sel mu cst i P h h') 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi P h h' hh hh'
  have hP : P.1 ∈ Pr.vGs :=
    (GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H).1 P.1 P.2
  have hs : cst.sharp = true := H.2.2.2.2.2.1
  unfold omPhi muAt
  unfold lamYat LocE.lamY at hh hh' ⊢
  refine GlobalTheory.ColNorms.MovedDatum.locSmall_om _ _ _ hh hh' ?_
  unfold PhiAt
  rw [hs]
  simp only [if_pos hP, if_true]
  have hq0 : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hN : ∀ j, N.R.N j = N.R.k + j * N.R.t + j := fun j => by unfold Ranks.N; ring
  have h2 := N.R.two_le_m
  refine GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small X.E X.K P.1 _ _ _ _ _ _ _ (i + 1) _ _ _ _ hq0 (Ideal.absNorm_mem _) ?_ ?_ ?_ ?_ ?_
  · rw [hN, Nat.add_sub_cancel]; unfold Formalism.L2.Col.cOf Ranks.r; omega
  · rw [hN, hN, add_mul]; unfold Formalism.L2.Col.cOf; omega
  · rw [hN]; omega
  · rw [hN]; omega
  · unfold Ranks.r; omega

end GlobalTheory.Core.Ht2.MovedDatumS
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis : ∀ (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) I.E), IsZBasis I e →
    (∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) →
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J := by
  first | exact @GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | exact GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | (intros; apply GlobalTheory.CuspGeo.unitary_of_trForm_zBasis <;> assumption)
end
