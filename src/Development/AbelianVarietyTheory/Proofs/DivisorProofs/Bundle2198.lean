module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle302
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle001
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.components_peterssonOrthogonal_and_masses : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  first | exact @GlobalTheory.CompPetOrth.orthogonal_mass_idem | exact GlobalTheory.CompPetOrth.orthogonal_mass_idem | (intros; apply GlobalTheory.CompPetOrth.orthogonal_mass_idem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem squareModelW₁_good : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig B X Y r s r' s' hB hX hY
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hH := (hM.vtx _ hR).haar_fund
  obtain ⟨dom, hh, hd⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_conjugateUnitaryAdelicIso (spW₁ G i j) (-1) (neg_ne_zero.2 one_ne_zero) hJ _ _ hH.1 hH.2
  let M0 : Model D.sp.cm.sig X Y := ⟨co, fun _ => 0, (M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ), dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  refine ⟨co, fun v => if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose, dom, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hh, hd⟩
  · change M0.IsVac B.ψ v (if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
      then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose)
    by_cases h : M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    exact if_pos hv

end GlobalTheory.FunObj
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | exact GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | (intros; apply GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.skewHermitianLattice_selfDual_smul_transpose_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∀ (t : F), t ≠ 0 → ∀ (s₁ s₂ : E), w.valuation E s₁ = 1 → w.valuation E s₂ = 1 →
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) →
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) →
  GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  first | exact @GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose | exact GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose | (intros; apply GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.archimedean_splittings_differ_by_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character | exact GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character | (intros; apply GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK


theorem _root_.GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  first | exact @GlobalTheory.KInfPol.pol_stable_kInf | exact GlobalTheory.KInfPol.pol_stable_kInf | (intros; apply GlobalTheory.KInfPol.pol_stable_kInf <;> assumption)
end

section

open Formalism.BasicNotions

namespace GlobalTheory.Theta0MeanLeC

theorem theta0MeanLeC : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D :=
  (GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber GlobalTheory.LatticePeriodEtaObj.latticePeriodEta_obj GlobalTheory.ThetaWeberObj.thetaWeberStatement).1.2.2

end GlobalTheory.Theta0MeanLeC
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.LinkLev

theorem spack_X_eq_of_heq {D : D7} {F F' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F = F') (P : GlobalTheory.Mem.SRe.SPack D F)
    (P' : GlobalTheory.Mem.SRe.SPack D F') (h : HEq P P') : P.X = P'.X := by
  subst hF
  rw [eq_of_heq h]

theorem conjLevel_of_setting_eq {D : D7} (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X')
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : Formalism.L2.Theta.GA D (D.sp.Y 0) ≃* X.B.I.GA) (hι : ι = (Formalism.L2.SG.RowsJoinPinned.iotaX X h).toMulEquiv)
    (t t' : Formalism.L2.Theta.GA D (Yc D 0)) (ht : t = t') (J : Set (Formalism.L2.Theta.GA D (Yc D 0)))
    (χ : Formalism.L2.Theta.GA D (Yc D 0) → ℂ)
    (hc : Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ J χ (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X')
      (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X' (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' k))) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ J χ (ι ⁻¹' seeKS X) (fun k => seeChiS X (ι k)) := by
  subst hX
  subst hι
  subst ht
  exact hc

theorem of_setting_eq {D : D7}
    (P : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.L2.Theta.GA D (D.sp.Y 0) → Prop)
    (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X') (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)) (ht : t = t') (hP : P X' h' t') :
    P X h t := by
  subst hX
  subst ht
  exact hP

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levels_withErr_updS (R : RealDat3 D A3 Ks) (kap : ℝ) (lam e) (F : Face3 D A3) (Dc Sp Zsc)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt ((R.updS kap lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X h t) ↔
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (GlobalTheory.Mem.SRe.JR R.toRealDat F.lv2) (GlobalTheory.Mem.SRe.chiR R.toRealDat F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt R.toRealDat F.lv2 X h t) := Iff.rfl

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr



theorem levels_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (x : TwIn ex) (ax : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (GlobalTheory.Mem.SRe.JR t.r.z.R.toRealDat t.r.z.F.lv2) (GlobalTheory.Mem.SRe.chiR t.r.z.R.toRealDat t.r.z.F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt t.r.z.R.toRealDat t.r.z.F.lv2 X h s) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 X h s := by
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact (levels_withErr_updS _ _ _ _ _ _ _ _ _ _ _).2 hs

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev


end GlobalTheory.Mem.R3.LinkLev
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem Ray.surjective_quasiCompact_q {oa : D.OAct O} (Y : Ray oa) :
    Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_surj
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.RayEv
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.LatFull.CMInt

theorem exists_denom {K : Type} [Field K] [NumberField K] (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (c : K) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ x ∈ J, IsIntegral ℤ ((N : K) * (x * c)) := by
  obtain ⟨a, ha, h⟩ := (J * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := h (x * c) (FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mem_spanSingleton_self _ _))
  rw [Algebra.smul_def] at hw
  have : (a : K) * (x * c) = (w : K) := hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem exists_denom_eval {K σ : Type} [Field K] [NumberField K] [Finite σ]
    (J : (σ →₀ ℕ) → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : σ → K) (d : ℕ) :
    ∃ N : K, N ≠ 0 ∧ ∀ G : MvPolynomial σ K, G.IsHomogeneous d → (∀ μ, AddMonoidAlgebra.coeff G μ ∈ J μ) →
      IsIntegral ℤ (N * MvPolynomial.eval x G) := by
  classical
  choose M hM0 hM using fun μ : σ →₀ ℕ => exists_denom (J μ) (∏ i ∈ μ.support, x i ^ μ i)
  let S := (Finsupp.finite_of_degree_le (σ := σ) d).toFinset
  refine ⟨((∏ μ ∈ S, M μ : 𝓞 K) : K), ?_, fun G hG hJ => ?_⟩
  · have : (∏ μ ∈ S, M μ : 𝓞 K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => hM0 μ
    exact fun h => this (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [MvPolynomial.eval_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun μ hμ => ?_
    have hS : μ ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := hG (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this.le
    rw [← Finset.prod_erase_mul _ _ hS]
    have e : (((∏ ν ∈ S.erase μ, M ν) * M μ : 𝓞 K) : K) = ((∏ ν ∈ S.erase μ, M ν : 𝓞 K) : K) * (M μ : K) :=
      map_mul (algebraMap (𝓞 K) K) _ _
    rw [e, mul_assoc]
    exact (RingOfIntegers.isIntegral_coe _).mul (hM μ _ (hJ μ))

theorem coeff_mem_of_loc {K : Type} [Field K] [NumberField K] {g : ℕ} {B : Type} [Fintype B] {m : B → ℕ}
    (e : (Σ b, Fin (m b)) ≃ Fin g) (T abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (G : MvPolynomial (FrVar m) K) (n : ℕ) (hT : T.Good) (hℓ : ∀ j, (ℓ j).Good)
    (hloc : ∀ p, Step5Loc e T abelian₂ ℓ U G n p) (μ : FrVar m →₀ ℕ) :
    AddMonoidAlgebra.coeff G μ ∈ (lineNN T ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
  classical
  refine coeff_mem_of_local K g ℓ T (FrVar m) _ μ n _ hT hℓ fun p => ?_
  obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hloc p
  refine ⟨t, cl, ht, hcl, ?_⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
  have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
  obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
    (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
  have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
      Set.range (algebraMap V K') := by
    refine ⟨w, ?_⟩
    rw [map_div₀, map_mul, map_prod]
    simp only [map_pow]
    rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
  have h1 := (hind _).mp hrange
  calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
      = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
          p.valuation K (t ^ n) := by
        rw [← map_mul, div_mul_cancel₀ _ htn]
    _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

theorem exists_det_ne_zero_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (hG : G ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr G Y ≠ 0 := by
  classical
  have hev : ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K m b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly m _ Y]
    simp only [evalFr, map_prod]
  have hD : (∏ b, FieldPoly.blockDetPoly K m b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  have hP := mul_ne_zero hD hG
  obtain ⟨x, hx⟩ : ∃ x : FrVar m → K, MvPolynomial.eval x ((∏ b, FieldPoly.blockDetPoly K m b) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  refine ⟨X, fun b => ?_, right_ne_zero_of_mul hx⟩
  have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact left_ne_zero_of_mul hx
  exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)

theorem exists_frame_bounded_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F₀ ∈ sec Xo c a n, (∀ G, IsFrPoly F₀ z.y G → G ≠ 0) → ∃ (y : FrPt Xo c z.K) (N : z.K), N * evR Xo c F₀ y ≠ 0 ∧ ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F₀ hF₀ hne
  classical
  obtain ⟨G₀, hG₀, -⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F₀ hF₀
  obtain ⟨Y, hY, hY0⟩ := exists_det_ne_zero_evalFr_ne_zero G₀ (hne G₀ hG₀)
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c z.K z.y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit)
  rw [Units.val_one] at hy
  have hval : ∀ (F : Rul Xo c) (G : MvPolynomial (FrVar Dw.mult) z.K), IsFrPoly F z.y G →
      evR Xo c F y = evalFr G Y := fun F G hG => by
    have h1 := hG z.K (AlgHom.id c.F z.K) z.y y Y (fun b => (hY b).isUnit) (GlobalTheory.Frames.frMapUniq_refl z.y) hy
    have h2 : MvPolynomial.map (AlgHom.id c.F z.K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hgood : z.Tl.dual.Good ∧ ∀ k, (z.ℓ k).Good := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, -⟩, ⟨-, -, -, hℓ⟩, -⟩ := hz
    refine ⟨(degree_algebraic z.K z.Tl z.Tl hT hT).2.2.1, fun k => ?_⟩
    have h := hℓ k
    change (z.letters.ℓ k).Good
    generalize z.letters = L at h
    revert h
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  obtain ⟨N, hN, hint⟩ := exists_denom_eval
    (fun μ : FrVar Dw.mult →₀ ℕ => (lineNN z.Tl.dual z.ℓ (fun v : FrVar Dw.mult => z.e ⟨v.1, v.2.2⟩) μ n).I)
    (fun v : FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ)))
  refine ⟨y, N, by rw [hval F₀ G₀ hG₀]; exact mul_ne_zero hN hY0, fun F hF hv => ?_⟩
  obtain ⟨G, hG, hh⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F hF
  rw [hval F G hG]
  exact hint G hh (coeff_mem_of_loc z.e z.Tl.dual z.LamL z.ℓ z.U G n hgood.1 hgood.2
    (LocClause.step5Loc_cmPt E H Dw l Xo c z f La hz a n F hF hv G hG))

end GlobalTheory.LatFull.CMInt
end

section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤ growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  first | exact @GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | exact GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | (intros; apply GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms <;> assumption)
end
