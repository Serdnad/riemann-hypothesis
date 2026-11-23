module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle592
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle532
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle070
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section


theorem _root_.GlobalTheory.T.unit_almost_everywhere_facts : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  first | exact @GlobalTheory.CompanionTheory.UnitAEPair.main | exact GlobalTheory.CompanionTheory.UnitAEPair.main | (intros; apply GlobalTheory.CompanionTheory.UnitAEPair.main <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist


set_option maxHeartbeats 1600000 in
theorem orbEx : IdemEx → ApproxId → Dens → TopX → AlgRich → AlgStab → SigLaw → HermScale → OrbEx := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro _hIE hAI hDens hTop hAR hAS hSL hHS D n r t hn V hV ψ hψ θ hθ b₀ hb S e hS he fib μt hfib hfibs
      hfibi hμt lam hlam hIntg
    obtain ⟨i1, i2, i3, i4, i5, hemb, i7, i8, i9⟩ := hTop D V.rank r t e
    have hT2 : ∀ a b : ℕ, T2Space (Formalism.IndefR.Datum.Mx D a b) := by
      intro a b
      obtain ⟨j1, -, -, -, -, -, -, -, -⟩ := hTop D a 0 b 1
      let f : Formalism.IndefR.Datum.Mx D a b → PositivityTheory.Rg.Rsw.Em.XS D a 0 b 1 :=
        fun x => ⟨((0 : Formalism.IndefR.Datum.Mx D a 0), x), one_smul _ _, one_smul _ _⟩
      have hf : Continuous f := (continuous_const.prodMk continuous_id).subtype_mk _
      constructor
      intro x y hxy
      obtain ⟨U, W, hU, hW, hxU, hyW, hUW⟩ := t2_separation (x := f x) (y := f y)
        (fun h => hxy (congrArg (fun w => (Subtype.val w).2) h))
      exact ⟨f ⁻¹' U, f ⁻¹' W, hU.preimage hf, hW.preimage hf, hxU, hyW, hUW.preimage f⟩
    haveI := hT2 t t
    haveI := hT2 r r
    obtain ⟨hσfin, hσY, -, hσU, hσS, hσG⟩ :=
      hSL D r t V b₀ S e hS he fib μt hfib hfibs hfibi hμt
    obtain ⟨gk, Gk, hgG, htend, hdec⟩ := hAI D t ψ hψ S e hS lam hlam
    have hRich := hAR D θ hθ V.rank r t n hn S e hS
    let k : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) → PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e → ℂ :=
      fun x z => PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x))
        (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z))
    have hkc : Continuous (fun p : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) × PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
        PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val p.1)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val p.2))) :=
      GlobalTheory.CompanionTheory.OrbExist.continuous_pch₂ hψ
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
        ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp (continuous_subtype_val.comp continuous_snd))
    have hD := hDens (PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e) (↥(PositivityTheory.Rg.Rsw.L.hermS D t e))
      (PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)) lam k (PositivityTheory.Rg.Rsw.Em.algA θ hn S e)
      {z | PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z) = 0}
      {z | PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀)}
      gk (fun j z => Gk j (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)))
      hσfin hkc.measurable (fun x z => (hψ.2.1 _).le) hRich.1
      (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val) continuous_const)
      (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_ip_fst (r := r) (t := t) V).comp continuous_subtype_val)
        continuous_const)
      hσY
      (fun j => ⟨(hgG j).1, (hgG j).2.1, fun z _ => (hgG j).2.2 _ (GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _)⟩)
      htend
      (fun C hC _ hCZ ε hε => by
        have hC' : IsCompact ((fun z : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
            PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) '' C) :=
          hC.image ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val)
        filter_upwards [hdec _ hC'.isClosed (by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _, GlobalTheory.CompanionTheory.OrbExist.qv_smul V b₀ e _ z.2.2,
            fun h0 => Set.disjoint_left.1 hCZ hz h0⟩) ε hε] with j hj z hz
        exact hj _ ⟨z, hz, rfl⟩)
      hIntg
    obtain ⟨ν, hνfin, hνsupp, hνint, hνcov⟩ := hD
    have hYae : ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)),
        PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀) :=
      MeasureTheory.ae_iff.2 hσY
    refine ⟨ν, ⟨?_, ?_, ?_, ?_, ?_⟩, hνint⟩
    · refine ⟨fun K hK => ?_⟩
      rw [hemb.map_apply]
      exact hνfin.lt_top_of_isCompact
        ((GlobalTheory.CompanionTheory.OrbExist.isClosed_fixed (a := V.rank) (r := r) (t := t)
          e).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
    · rw [hemb.map_apply]
      refine measure_mono_null ?_ hνsupp
      intro z hz hYZ
      exact hz ⟨z.2.1, z.2.2, hYZ.1, hYZ.2⟩
    · intro h hh
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftU V r t h
      have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
        refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS (Formalism.L2.Theta.matHom V h) 1 hh (by simp) Θ
            (fun z => ?_) f hf
          rw [GlobalTheory.CompanionTheory.OrbExist.mm_jn, Units.val_one]
          exact (Matrix.mul_one _).symm
        · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσU h hh Θ fun z => rfl) fun x =>
            Filter.Eventually.of_forall fun z => by
              show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
                PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                  (PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).1,
                    PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).2))
              simp only [PositivityTheory.Rg.Rsw.L.qv, PositivityTheory.Rg.Rsw.L.yv, GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.ip_mt]
      have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiU V r t h) 1 hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiU V r t h).continuous.measurable (fun z => rfl) hcov
      rw [one_smul] at this
      exact this
    · intro y hy
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftS V.rank y
      have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
        refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.shU hn y) (by simp)
            (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 y 0 1 (by simp) hy (by simp) (by simp)) Θ
            (fun z => ?_) f hf
          rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
            PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
            fun X => Matrix.one_mul X]
          refine Eq.trans ?_ (GlobalTheory.CompanionTheory.ColumnSplitting.jnBl D n t V.rank r hn (Subtype.val z).1 (Subtype.val z).2 y).symm
          show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1
            ((Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y) = _
          rw [add_comm]
        · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσS y hy Θ fun z => rfl) fun x =>
            hYae.mono fun z hz => by
              show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
                PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                  ((Subtype.val z).1, (Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y))
              rw [GlobalTheory.CompanionTheory.OrbExist.qv_shear V b₀ hb e _ _ y hz hy]
      have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiS V.rank y) 1 hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiS V.rank y).continuous.measurable (fun z => rfl) hcov
      rw [one_smul] at this
      exact this
    · intro g hg
      let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
        GlobalTheory.CompanionTheory.EisM.liftG V.rank r g
      obtain ⟨c, hc, hcmap⟩ := hHS D t S e hS lam hlam g⁻¹ (GlobalTheory.CompanionTheory.OrbExist.smul_inv_sub e g hg)
      have hκ : ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ V.rank *
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ ^ t =
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) := by
        rw [map_inv, GlobalTheory.CompanionTheory.OrbExist.absA_inv]
        exact GlobalTheory.CompanionTheory.OrbExist.kap _ (GlobalTheory.CompanionTheory.OrbExist.absA_ne D _) V.rank r t hV
      have hkG : ∀ x, ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)), k x z = k (c x) (Θ z) :=
        fun x => Filter.Eventually.of_forall fun z => by
          show PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
            PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val (c x))) (PositivityTheory.Rg.Rsw.L.qv V b₀
              ((Subtype.val z).1, PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
                (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))))
          rw [hc x, ← GlobalTheory.CompanionTheory.OrbExist.pch_conj, GlobalTheory.CompanionTheory.OrbExist.qv_col, GlobalTheory.CompanionTheory.OrbExist.conj_cancel]
      have hcov : MeasureTheory.Measure.map Θ ν =
          ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) • ν := by
        refine hνcov Θ _ fun f hf => ⟨?_, ?_⟩
        · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.colU hn g) (by simp)
            (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 0 0 (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))
              (by simp) (by simp) (by simp) hg) Θ (fun z => ?_) f hf
          rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
            PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
            fun X => Matrix.one_mul X]
          refine Eq.trans ?_ (GlobalTheory.CompanionTheory.OrbExist.jn_bl hn (Subtype.val z).1 (Subtype.val z).2 1 0 0
            (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))).symm
          show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1 (PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
            (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))) = _
          simp only [PositivityTheory.Rg.Rsw.L.mm, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
        · rw [GlobalTheory.CompanionTheory.OrbExist.trans_int _ lam k f Θ c _ _ (hσG g hg Θ fun z => rfl) hcmap hkG, hκ]
      exact GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g) _ hemb.measurable
        Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g).continuous.measurable (fun z => rfl) hcov

end GlobalTheory.CompanionTheory.OrbExist

end
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.hermitian_form_polynomial_in : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := by
  first | exact @GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | exact GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | (intros; apply GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval <;> assumption)
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.SphereCover

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K]

theorem exists_sphere {T : Type} [AddCommGroup T] [Module K T] [Module.Finite K T]
    [TopologicalSpace T] [IsModuleTopology K T] (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) (A : Set T) (hA : IsCompact A) :
    ∃ (P : Set T) (k : ℕ), IsCompact P ∧ IsOpen P ∧ (0 : T) ∉ P ∧
      ∀ X ∈ A, X ≠ 0 → ∃ (i : ℕ), ∃ Y ∈ P, X = (π ^ ((i : ℤ) - k)) • Y := by
  haveI : ContinuousAdd T := IsModuleTopology.toContinuousAdd K T
  haveI : ContinuousSMul K T := IsModuleTopology.toContinuousSMul K T
  let c : T ≃ₗ[K] (Fin (Module.finrank K T) → K) := (Module.finBasis K T).equivFun
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  obtain ⟨C, hC⟩ : ∃ C, ∀ X ∈ A, ‖c X‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hA.image hc).isBounded.exists_norm_le
    exact ⟨C, fun X hX => hC _ ⟨X, hX, rfl⟩⟩
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < (‖π‖⁻¹) ^ k :=
    pow_unbounded_of_one_lt C ((one_lt_inv₀ hπ).2 h1)
  have himg : c.symm '' Metric.sphere 0 1 = c ⁻¹' Metric.sphere 0 1 := by
    ext X
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hX
      exact ⟨c X, hX, by simp⟩
  refine ⟨c.symm '' Metric.sphere 0 1, k, (isCompact_sphere _ _).image hc', ?_, ?_, ?_⟩
  · rw [himg]
    exact (IsUltrametricDist.isClopen_sphere 0 one_ne_zero).isOpen.preimage hc
  · rw [himg]
    simp
  · intro X hX hX0
    have hw : c X ≠ 0 := by simpa using hX0
    obtain ⟨l, hl⟩ : ∃ l, c X l ≠ 0 := Function.ne_iff.1 hw
    haveI : Nonempty (Fin (Module.finrank K T)) := ⟨l⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup (Finset.univ) Finset.univ_nonempty
      (fun i => ‖c X i‖₊)
    have hnorm : ‖c X‖ = ‖c X m‖ := by
      rw [← coe_nnnorm, Pi.nnnorm_def, hm, coe_nnnorm]
    have hm0 : c X m ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact hw (norm_eq_zero.1 hnorm)
    obtain ⟨j, hj⟩ := hv _ hm0
    rw [← hnorm] at hj
    have hjk : -(k : ℤ) ≤ j := by
      have : ‖π‖ ^ j ≤ ‖π‖ ^ (-(k : ℤ)) := by
        rw [← hj, zpow_neg, zpow_natCast, ← inv_pow]
        exact ((hC X hX).trans hk.le)
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hπ h1).1 this
    have hY : ‖c ((π ^ (-j)) • X)‖ = 1 := by
      rw [map_smul, norm_smul, norm_zpow, hj, ← zpow_add₀ hπ.ne']
      simp
    refine ⟨(j + k).toNat, (π ^ (-j)) • X, ?_, ?_⟩
    · rw [himg]
      simpa using hY
    · have : (((j + k).toNat : ℕ) : ℤ) - k = j := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [this, smul_smul, ← zpow_add₀ h0]
      simp

end Abstract

section Cover

variable {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
  [Algebra K R] [Module.Finite K R] [TopologicalSpace R] [IsModuleTopology K R]

theorem linearIndependent_of_ne_zero (hR : IsField R) {M : ℕ} {X : Fin 1 → Fin M → R}
    (hX : X ≠ 0) : LinearIndependent R X := by
  haveI : IsDomain R := hR.isDomain
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : X 0 ≠ 0 := fun h => hX (funext fun p => by
    obtain rfl : p = 0 := Subsingleton.elim _ _
    exact h)
  obtain ⟨l, hl⟩ : ∃ l, X 0 l ≠ 0 := Function.ne_iff.1 h0
  have h1 := congrFun hg l
  simp only [Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right hl

theorem exists_cover (hR : IsField R) (π : K) (h0 : π ≠ 0) (h1 : ‖π‖ < 1)
    (hv : ∀ a : K, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j) {M : ℕ} (hM : 2 ≤ M)
    (A : Set (Fin 1 → Fin M → R)) (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → R)) (u : ι → Rˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → R | LinearIndependent R X} ∧
      Summable (fun i => ‖Algebra.norm K (u i : R)‖₊ ^ (M - 1)) ∧
      A ∩ {X : Fin 1 → Fin M → R | LinearIndependent R X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → R) (p : Fin 1) (k : Fin M) => (u i : R) * X p k) '' P := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨P, k, hPc, hPo, hP0, hcov⟩ := exists_sphere π h0 h1 hv A hA
  let w : Kˣ := Units.mk0 π h0
  let u : ℕ → Rˣ := fun i => Units.map (algebraMap K R).toMonoidHom (w ^ ((i : ℤ) - k))
  have hu : ∀ i : ℕ, (u i : R) = algebraMap K R (π ^ ((i : ℤ) - k)) := fun i => by
    change algebraMap K R ((w ^ ((i : ℤ) - k) : Kˣ) : K) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨ℕ, inferInstance, P, u, hPc, hPo, ?_, ?_, ?_⟩
  · intro X hX
    exact linearIndependent_of_ne_zero hR fun h => hP0 (h ▸ hX)
  · have hd : 0 < Module.finrank K R := Module.finrank_pos
    have hπ : 0 < ‖π‖₊ := nnnorm_pos.2 h0
    have hlt : ‖π‖₊ < 1 := by exact_mod_cast h1
    set e : ℕ := Module.finrank K R * (M - 1) with he
    have he0 : e ≠ 0 := Nat.mul_ne_zero hd.ne' (by omega)
    have hq : ‖π‖₊ ^ e < 1 := pow_lt_one₀ hπ.le hlt he0
    have hs := (NNReal.summable_geometric hq).mul_left ((‖π‖₊ ^ (-(k : ℤ))) ^ e)
    refine hs.congr fun i => ?_
    rw [hu, Algebra.norm_algebraMap, nnnorm_pow, nnnorm_zpow, sub_eq_add_neg,
      zpow_add₀ hπ.ne', zpow_natCast, he]
    ring
  · rintro X ⟨hXA, hXf⟩
    have hX0 : X ≠ 0 := by
      intro h
      have h2 : LinearIndependent R X := hXf
      exact h2.ne_zero 0 (by rw [h]; rfl)
    obtain ⟨i, Y, hY, hXY⟩ := hcov X hXA hX0
    refine Set.mem_iUnion.2 ⟨i, Y, hY, ?_⟩
    rw [hXY]
    funext p l
    simp [hu, Algebra.smul_def]

end Cover

theorem exists_uniformizer {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ a : Fv F v, a ≠ 0 → ∃ j : ℤ, ‖a‖ = ‖π‖ ^ j := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    decide
  refine ⟨ϖ, hϖ0, Valued.toNormedField.norm_lt_one_iff.2 h1, fun a ha => ?_⟩
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hn : ‖a * ϖ ^ k‖ = 1 := le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hu.le)
    (not_lt.1 fun h => (Valued.toNormedField.norm_lt_one_iff.1 h).ne hu)
  have hϖn : ‖ϖ‖ ≠ 0 := norm_ne_zero_iff.2 hϖ0
  refine ⟨-k, ?_⟩
  rw [norm_mul, norm_zpow] at hn
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hn

theorem coverF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ h M hM v hF A hA
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : ProperSpace (Fv F v) := GlobalTheory.CompanionTheory.DictLoc.properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨π, h0, h1, hv⟩ := exists_uniformizer v
  exact exists_cover hF π h0 h1 hv hM A hA

end GlobalTheory.CompanionTheory.WeilSiegel.SphereCover
end
end
