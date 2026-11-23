module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle124
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalLevelRelIndexAtLevelPrimeSelfDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle127
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle126
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section


theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
end

section

namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.rational_vectors_same_length_one_unitary_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.RatOrbit.rational_sphere_orbit | exact GlobalTheory.RatOrbit.rational_sphere_orbit | (intros; apply GlobalTheory.RatOrbit.rational_sphere_orbit <;> assumption)
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_adelic_unitary_complement_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  first | exact @GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | exact GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | (intros; apply GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.StdCharUnique

variable (F : Type) [Field F] [NumberField F]

theorem sum_mult_re_eq_trace (x : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← InfinitePlace.card_filter_mk_eq, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr (by congr) fun φ hφ => ?_
  have hw : InfinitePlace.mk φ = w := (Finset.mem_filter.1 hφ).2
  subst hw
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem traceInf_add (x y : Ainf F) : traceInf F (x + y) = traceInf F x + traceInf F y := by
  rw [traceInf, traceInf, traceInf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (x + y) w = x w + y w from rfl, map_add (f := _), Complex.add_re, mul_add]

theorem continuous_traceInf : Continuous (traceInf F) := by
  refine continuous_finsetSum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp ?_)
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [← sum_mult_re_eq_trace, traceInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  simp

theorem existsUnique_isStdChar : ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => (traceInf F x : ℂ)) fun a b => by
    rw [traceInf_add, Complex.ofReal_add]
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.StdAdelicChar.exists_char_of_trace F L
    (Complex.continuous_ofReal.comp (continuous_traceInf F)) fun x => by
      show ((traceInf F (algebraMap F (Ainf F) x) : ℝ) : ℂ) = _
      rw [traceInf_algebraMap, Complex.ofReal_ratCast]
  have hψ : IsStdChar F ψ := ⟨h1, fun x => by
    rw [h2, stdInf]
    congr 1
    show _ * ((traceInf F x : ℝ) : ℂ) = _
    push_cast
    ring⟩
  exact ⟨ψ, hψ, fun ψ' h' => GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h'.1 hψ.1
    fun x => (h'.2 x).trans (hψ.2 x).symm⟩

theorem existsUnique_isStdChar_cm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
      ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ :=
  fun F _ _ _ _ _ _ _ _ _ _ _ => existsUnique_isStdChar F

end GlobalTheory.StdCharUnique

end
end

section

namespace GlobalTheory.LevelIndex

theorem selfDualLatticeIndex_stabiliserLevelIndexFormula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel.indexKU_iff.mp
    (GlobalTheory.LevelIndex.indexKU_of_selfDualOverBase
      (GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice))

end GlobalTheory.LevelIndex
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.cpSeries_bounded_theta_level_value_one : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ G : ℂ → ℂ) (a : ℕ), d.Prime → d % 16 = 7 → Split d q → q ≠ 2 → IsOK d M.L → M.MChart ω → IsTh d θ → Differentiable ℂ G → G 0 = 1 → (∀ x, InOK d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)) ^ a = G z) → (∀ z, G z = 0 → PrimeTo d q z) → Bd 1 (hat M.ι (C ω * logS) G) := by
  first | exact @GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level | exact GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level | (intros; apply GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.algebraicJets_of_algebraic_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  first | exact @GlobalTheory.algJets_of_taylor | exact GlobalTheory.algJets_of_taylor | (intros; apply GlobalTheory.algJets_of_taylor <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolRatioUp

theorem volRatio_up : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) →
    D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  intro D hT h2 W P Q hW hWs hPQ U hU hUs
  have hUr : U.rank = P + Q + 1 := by
    have := Formalism.BasicNotions.sig_sum U hU D.host.φ₀
    rw [hUs] at this
    simp only at this
    omega
  have hWr : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hWs] at this
    exact this.symm
  obtain ⟨x, -, W', ι, -, -, hW'ok, hW's, hratio⟩ :=
    h2 U (P + 1) Q hU hUs (by omega) true (by simp)
  have hW's' : ∀ τ, W'.sig τ = (P, Q) := fun τ => by
    have := hW's τ
    simpa using this
  have hW'r : W'.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W' hW'ok D.host.φ₀
    rw [hW's'] at this
    exact this.symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D W W' hW hW'ok (by rw [hWr, hW'r])
    (fun τ => by rw [hWs, hW's'])
  have hvol : D.vol W = D.vol W' :=
    (GlobalTheory.VolIndepClosed.volIndep D).2.2 hT W W' P Q ⟨hW, hWs⟩ ⟨hW'ok, hW's'⟩ φ hφ
  rw [hvol, hratio, hUr]

end GlobalTheory.VolRatioUp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem nuRow_zero_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (hk : 0 < D.R.k) :
    nuRow D u j τ 0 ≤ ((((D.hcW u τ).u ⟨0, hk⟩ : ℚ)) : ℝ) + wSz D j τ := by
  unfold nuRow srcPar
  rw [dite_eq_left hk]
  have h1 : 1 ≤ D.R.N j := by unfold Ranks.N; omega
  have h1' : (1 : ℝ) ≤ D.R.N j := by exact_mod_cast h1
  have h2 : (0 : ℝ) ≤ D.R.N (j - 1) := Nat.cast_nonneg _
  push_cast
  linarith

theorem nuRow_nonneg_le_ten_mul : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ nuRow (Fm.D x i) u j τ l ∧ nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.HCEntries.entries eps Fm
  refine ⟨x0, fun x hx hx1 i u j hj τ l hl => ?_⟩
  obtain ⟨hw, hu, -⟩ := h x hx hx1 i
  obtain ⟨-, hw3, hwe⟩ := hw j hj τ
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have h3 := (abs_le.1 (hu u τ ⟨0, hk⟩)).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

end GlobalTheory
end
