module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle158
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle531
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Bundle005
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle464
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle442
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.RealZetaTw


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in
theorem realZetaTw : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → RealZetaQ D := by
  intro hHC D hA hgap c w₁ hw k hk s s' hs hs' p hp m X hmX
  obtain ⟨hWexp, hvac⟩ := GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum D hgap c w₁ hw k hk s s' hs hs' p hp hk
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsI⟩ := hs
  obtain ⟨hr', -, hsI'⟩ := hs'
  have hspar : s.par = parB (Ptw D) k := hsI.par
  have hspar' : s'.par = parB (Ptw D) (k + 1) := hsI'.par
  have hsrank' : s'.V.rank = D.R.rankY (k + 1) := hsI'.rank
  obtain ⟨χS, χT, hW, hexp⟩ := hWexp
  have hCT := (hA.2 hgap).1
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hSe : ∀ τ, alS D ⟨k, hk⟩ τ = expS D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alS, expS]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hTe : ∀ τ, alT D ⟨k, hk⟩ τ = expT D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alT, expT]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hpar : ∀ τ, s.par τ = parB (Ptw D) ((⟨k, hk⟩ : Fin D.R.m) : ℕ) τ := fun τ => by rw [hspar]
  have hpar' : ∀ τ, s'.par τ = parB (Ptw D) (((⟨k, hk⟩ : Fin D.R.m) : ℕ) + 1) τ := fun τ => by rw [hspar']
  have hLL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.1 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ)
  have hZL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.2 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, ?_⟩
  intro mR hmR
  set z : GinfC s.V → ℂ := zReal p m X (glue Φ) (fun τ => ⟨w τ, hwsm τ⟩) with hzdef
  have hfac := GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, fun τ => hwk τ, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · rintro a ⟨ha, hfr⟩
    refine ⟨0, div_pos (by exact_mod_cast D.R.t_odd.pos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac a ha hfr
      (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one₀ (fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : D.R.t ≤ s'.V.rank := by
      rw [hsrank', Formalism.BasicNotions.Ranks.rankY]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor mR z mf Hf C s'.V.rank D.R.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.RealZetaTw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mean_theta_orbit : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsum : ∀ n : flagN d, HasSum (term ψ d W vS (om (n.1, 1) Ψ)) (om (n.1, 1) Ψ 0) :=
    fun n => (hT _ (hw.om_pres _ _ hΨ)).2.2.2.2
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  have hbd : ∀ n : flagN d, ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤
      ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := fun n => by
    have := hC 1 1 n.1 n.2
    rwa [mul_one] at this
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hpart : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ‖∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ ≤
        M * max (C * (height V 1 * quotHeight W 1) ^ A) 0 := by
    intro S n
    rw [tsum_mul_left, norm_mul]
    refine mul_le_mul (hThb n) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hThb n))
    have h1 : ‖∑' x : S, term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
      enorm_tsum_le_tsum_enorm.trans
        ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans (hbd n))
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [toReal_enorm, ENNReal.toReal_ofReal'] at h2
  have hmeas : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      AEStronglyMeasurable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) := by
    intro S
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset S))
      (f := fun s n => ∑ x ∈ s, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun s => ?_)
      (Filter.Eventually.of_forall fun n => ?_)
    · exact (continuous_finsetSum _ fun x _ => hTh.cont.mul (hcont x.1)).aestronglyMeasurable
    · exact (((hsum n).summable.mul_left (Th n.1)).subtype (fun x => x ∈ S)).hasSum
  have : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  have hint : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      Integrable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) :=
    fun S => Integrable.of_bound (hmeas S) _ (Filter.Eventually.of_forall (hpart S))

  have h61 := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E => GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x
  let Sb : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := {x | gramQ W x ≠ gramQ W x₀}
  let Sj : Fin ρ → Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := fun j => {x | gramQ W x = gramQ W x₀ ∧
    ((∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
      ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0)}
  have hpt : ∀ n : flagN d, Th n.1 * om (n.1, 1) Ψ 0 =
      (∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      (∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      ∑ j, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 := by
    intro n
    have hs : Summable fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x := (hsum n).summable.mul_left _
    rw [← ((hsum n).mul_left (Th n.1)).tsum_eq]
    have ht : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
        ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 =
          ∑' x, S.indicator (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x) x := fun S => tsum_subtype S (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x)
    rw [ht, ht, Finset.sum_congr rfl fun j _ => ht (Sj j)]
    rw [← Summable.tsum_finsetSum (fun j _ => hs.indicator _), ← Summable.tsum_add (hs.indicator _) (hs.indicator _),
      ← Summable.tsum_add ((hs.indicator _).add (hs.indicator _)) (summable_sum fun j _ => hs.indicator _)]
    congr 1
    funext x
    by_cases hg : gramQ W x = gramQ W x₀
    · have h1 : x ∉ Sb := fun h => h hg
      rw [Set.indicator_of_notMem h1, zero_add]
      by_cases hl : LinearIndependent D.host.E x.transpose
      · have h2 : x ∈ Orb W x₀ := ⟨hl, hg⟩
        have h3 : ∀ j, x ∉ Sj j := fun j h => (h61 x).1.2 ⟨j, h.2⟩ hl
        rw [Set.indicator_of_mem h2, Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero]
      · have h2 : x ∉ Orb W x₀ := fun h => hl h.1
        obtain ⟨j, hj⟩ := (h61 x).1.1 hl
        rw [Set.indicator_of_notMem h2, zero_add, Finset.sum_eq_single j
          (fun j' _ hj' => Set.indicator_of_notMem (fun (h : x ∈ Sj j') => hj' ((h61 x).2.1 j' j h.2 hj)) _)
          (fun h => (h (Finset.mem_univ j)).elim), Set.indicator_of_mem (show x ∈ Sj j from ⟨hg, hj⟩)]
    · have h1 : x ∈ Sb := hg
      have h2 : x ∉ Orb W x₀ := fun h => hg h.2
      have h3 : ∀ j, x ∉ Sj j := fun j h => hg h.1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
        Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero, add_zero]
  have e1 : ∫ n in vN.𝓝, ∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have e2 : ∀ j, ∫ n in vN.𝓝, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.dependentFrames_firstRelation_mean_zero D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add ?_ ?_, integral_add ?_ ?_,
    integral_finsetSum _ ?_, e1, Finset.sum_eq_zero fun j _ => e2 j, zero_add, add_zero]
  · exact fun j _ => hint _
  · exact hint _
  · exact hint _
  · exact (hint _).add (hint _)
  · exact integrable_finsetSum _ fun j _ => hint _

end GlobalTheory.Unf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.BesselIntegrand

theorem handFB_smul_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handFB s vL Y Ξ h₁ := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem unfF_eq_besFun : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  intro D hD ψ σ J B s vL Y G Φ hΦ h h₁ n
  have h1 : IsThetaFunO ψ J.W B.V (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦ
  have h2 : IsThetaFunO ψ J.W B.V (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := s.weil.om_pres _ _ h1
  have e : s.om (1, n.1 * embA B.d B.o h₁ * h) Φ = s.om (1, n.1) (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      one_mul, one_mul]
  have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s _ h1 1 h₁
  rw [map_one] at c
  unfold unfF besFun rTrans
  rw [e, GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B s _ h2 n.1 n.2, c, handFB_smul_om]
  ring

end GlobalTheory.Unf.FB.BesselIntegrand
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelSection

theorem fock_mem_degenerate : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) := by
  intro D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp a ha g
    exact GlobalTheory.StdUnn.SiegelLaw.value_zero_parabolic D n V ψ χ θ μ ω hω Φ p hp a ha g
  · exact GlobalTheory.T.continuous_weilSchrodinger_standardUnn_eval_zero D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω Φ
  · have hfin := GlobalTheory.T.fockVector_schrodingerModel_isKFinite D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
    let L : schwartzA θ V.rank n →ₗ[ℂ] (G D n → ℂ) :=
      { toFun := fun Ψ g => (ω g Ψ).1 0
        map_add' := fun Ψ₁ Ψ₂ => by funext g; simp
        map_smul' := fun c Ψ => by funext g; simp }
    rw [isKFinite_iff]
    refine ⟨(Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}).map L, inferInstance, ?_⟩
    intro k hk
    have e : (fun g : G D n => (ω (g * k) Φ).1 0) = L (ω k Φ) := by
      funext g; simp [L, map_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.StdUnn.SiegelSection
end

section

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false :=
  fun h => oneOn_singleton_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global (GlobalTheory.rowNGP_of_siegelWeil h)

end GlobalTheory.Core.Diag
end
