module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.realCentre_acts_by_character_on_isotypic_slices : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → ∃ χ₃ : GA D S → ℂ, ∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v := by
  first | exact @GlobalTheory.CentreTarget.centre_target_char | exact GlobalTheory.CentreTarget.centre_target_char | (intros; apply GlobalTheory.CentreTarget.centre_target_char <;> assumption)
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

namespace GlobalTheory.MiTop

theorem miStar2_of_anchored : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ), OpsUnit X V U → Anchored X eV sEE V U c → UnitAt X c → X.MIstar2 eV sEE := by
  intro K _ _ _ Bs A X fc eV sEE V U c hOp hAn hUn
  choose p b hp hb hid using hAn
  refine ⟨⟨V, fun u => p u / (b u * c u Bs.μ0), U, fun u t => c u t / c u Bs.μ0⟩, ?_, ?_, ?_⟩
  · refine ⟨hOp.1, hOp.2, ⟨fun u t => div_ne_zero (hUn.1 u t) (hUn.1 u Bs.μ0), fun u w k hk => hUn.2 u w k hk⟩,
      fun u => div_self (hUn.1 u Bs.μ0)⟩
  · intro u t φ F
    have h := hid u t φ F
    have hc := hUn.1 u Bs.μ0
    have hbu := hb u
    dsimp only
    field_simp
    linear_combination h
  · intro u
    exact div_ne_zero (hp u) (mul_ne_zero (hb u) (hUn.1 u Bs.μ0))

end GlobalTheory.MiTop
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitIota

open GlobalTheory.AdelicU.Supp GlobalTheory.LFun.ConjPlace
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem sigR_compFin' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v z) = compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem continuous_complEquiv_symm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    Continuous (complEquiv hE h hτ).symm := by
  let _ : Algebra (Fv F v) (w.adicCompletion E) := (GlobalTheory.LFun.complMap h).toAlgebra
  have : ContinuousSMul (Fv F v) (w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ (GlobalTheory.LFun.SplitChart.continuous_complMap h)
  let _ : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  let f : Fv F v ≃ₐ[Fv F v] w.adicCompletion E :=
    { complEquiv hE h hτ with commutes' := fun a => rfl }
  have : FiniteDimensional (Fv F v) (w.adicCompletion E) := f.toLinearEquiv.finiteDimensional
  have : IsModuleTopology (Fv F v) (w.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  exact IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap

theorem continuous_compW {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    Continuous fun a : AF F ⊗[F] E => GlobalTheory.LFun.toCompl h (compFin F E v a) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) ((GlobalTheory.LFun.toCompl h).comp (compFin F E v)) ?_
  have e : (((GlobalTheory.LFun.toCompl h).comp (compFin F E v)).comp (algebraMap (AF F) (AF F ⊗[F] E)) :
      AF F → w.adicCompletion E) = fun a => GlobalTheory.LFun.complMap h (evFin F v a) := by
    funext a
    exact (GlobalTheory.LFun.toCompl_tmul h (evFin F v a) (1 : E)).trans (by rw [map_one, mul_one])
  rw [e]
  exact (GlobalTheory.LFun.SplitChart.continuous_complMap h).comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)

theorem exists_iota_gen {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    ∃ ι : w.adicCompletion E →+ AF F ⊗[F] E, Continuous ι ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (ι x)) = x) ∧
      (∀ x, GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι x))) = 0) ∧
      (∀ x, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * ι x = ι x) ∧
      (∀ a x, a * ι x = ι (GlobalTheory.LFun.toCompl h (compFin F E v a) * x)) ∧
      (∀ a, algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) * a =
        ι (GlobalTheory.LFun.toCompl h (compFin F E v a)) +
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (ι (GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ a))))) ∧
      ι 1 = singleTens E v (splitIdem hE τ) := by
  set c := complEquiv hE h hτ
  have hcw : ∀ y, GlobalTheory.LFun.toCompl h y = c (splitProj τ y) := fun y => toCompl_eq hE h hτ y
  have hcc : Continuous c.symm := continuous_complEquiv_symm hE h hτ
  let s : w.adicCompletion E →+ Fv F v ⊗[F] E :=
    (splitAlgEquiv hE τ).symm.toRingEquiv.toAddEquiv.toAddMonoidHom.comp
      ((AddMonoidHom.inl _ _).comp c.symm.toAddEquiv.toAddMonoidHom)
  have s1 : ∀ x, splitProj τ (s x) = c.symm x := fun x => splitProj_symm hE τ _
  have s2 : ∀ x, splitProj (τ.comp σ) (s x) = 0 := fun x => splitProj_comp_symm hE τ _
  have hs1 : s 1 = splitIdem hE τ := by
    show (splitAlgEquiv hE τ).symm (c.symm 1, 0) = _
    rw [map_one]; rfl
  have hsc : Continuous s :=
    (continuous_splitAlgEquiv_symm hE τ).comp ((continuous_id.prodMk continuous_const).comp hcc)
  clear_value s
  have hst : Continuous (singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hpl : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (singleFin v 1)) = singleTens E v 1 := rfl
  refine ⟨(singleTens E v).toAddMonoidHom.comp s, hst.comp hsc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (singleTens E v (s x))) = x
    rw [compFin_singleTens_self, hcw, s1, RingEquiv.apply_symm_apply]
  · intro x
    show GlobalTheory.LFun.toCompl h (compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s x)))) = 0
    rw [sigR_singleTens, compFin_singleTens_self, hcw, ← splitProj_comp, s2, map_zero]
  · intro x
    show _ * singleTens E v (s x) = singleTens E v (s x)
    rw [hpl, singleTens_mul, compFin_singleTens_self, one_mul]
  · intro a x
    show a * singleTens E v (s x) = singleTens E v (s _)
    rw [mul_comm, singleTens_mul]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_mul, s1, s1, hcw, map_mul, RingEquiv.symm_apply_apply, mul_comm]
    · rw [map_mul, s2, s2, zero_mul]
  · intro a
    show _ = singleTens E v (s _) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v (s _))
    rw [hpl, singleTens_mul, one_mul, sigR_singleTens, ← map_add (f := _)]
    refine congrArg _ (split_ext hE τ ?_ ?_)
    · rw [map_add (f := _), s1, hcw, RingEquiv.symm_apply_apply, ← splitProj_comp, s2, add_zero]
    · rw [map_add (f := _), s2, zero_add, splitProj_comp_sigR hE, s1, hcw, RingEquiv.symm_apply_apply,
        ← sigR_compFin', splitProj_comp]
  · show singleTens E v (s 1) = _
    rw [hs1]

end GlobalTheory.Core.Rk.SplitIota

open scoped TensorProduct


open GlobalTheory.Core.Rk.SplitIota in
theorem GlobalTheory.Core.Rk.SplitIota.exists_iota : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∃ ι : w.adicCompletion D.host.E →+ AE D, Continuous ι ∧ (∀ x, cw h (ι x) = x) ∧ (∀ x, cw h (cA D (ι x)) = 0) ∧ (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * ι x = ι x) ∧ (∀ a x, a * ι x = ι (cw h a * x)) ∧ (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * a = ι (cw h a) + cA D (ι (cw h (cA D a)))) ∧ IsSplitIdem D (ι 1) ∧ Continuous (cw h) := by
  intro D q w h hs
  have hE := isCMExt_host D
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
  have hPu : P.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hP
  have hQu : Q.under (𝓞 D.host.F) = q := HeightOneSpectrum.ext hQ
  obtain ⟨w', hw', hw'u⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' ∧ w'.under (𝓞 D.host.F) = q := by
    by_cases e : w = P
    · exact ⟨Q, e ▸ hPQ, hQu⟩
    · exact ⟨P, e, hPu⟩
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hw' h hw'u
  obtain ⟨ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_iota_gen hE h hτ
  exact ⟨ι, h1, h2, h3, h4, h5, h6, GlobalTheory.AdelicU.Supp.isSplitIdem_iff_exists.2 ⟨q, τ, h7⟩, continuous_compW h⟩
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

noncomputable section

namespace GlobalTheory.Core.Rk.SecPar

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar

open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

theorem cw_incA {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = q)
    (x : D.host.E) : cw h (incA D x) = algebraMap D.host.E (w.adicCompletion D.host.E) x := by
  show toCompl h (compFin _ _ q (1 ⊗ₜ x)) = _
  simp [compFin, toCompl]

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartUnip

open Matrix

theorem rat_Tm {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY)).submatrix id finSumFinEquiv.symm := by
  ext i j
  rcases h : finSumFinEquiv.symm j with k | k <;>
    simp [rat, Tm, HypDec.jX, HypDec.jY, Matrix.submatrix_apply, h, Matrix.map_apply]

theorem cancel_mul {R : Type*} [CommRing R] {k a m : ℕ} {P : Matrix (Fin k) (Fin (m + m)) R}
    {M : Matrix (Fin k) (Fin a) R} {N : Matrix (Fin a) (Fin m ⊕ Fin m) R}
    (h : P = M * N.submatrix id finSumFinEquiv.symm) : P.submatrix id finSumFinEquiv = M * N := by
  subst h
  ext i s
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

theorem unscale {R : Type*} [CommRing R] {k m : ℕ} {X Y Z : Matrix (Fin k) (Fin m) R} {b : Matrix (Fin m) (Fin m) R}
    {u v : R} (huv : u * v = 1) (h : X * b + v • Y = v • Z) : Z = Y + X * (u • b) := by
  have h3 := congrArg (fun M => u • M) h
  simp only [smul_add, smul_smul, huv, one_smul] at h3
  rw [Matrix.mul_smul, add_comm, h3]

theorem skew_of_image {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (c : Mx D ρ ρ)
    (hY : mt S g ⬝ d.jY = d.jY + d.jX ⬝ c) : c ∈ skewA D ρ := by
  have h0 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jY)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary S g), d.gram_YY]
  rw [hY] at h0
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
    d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at h0
  exact mem_skewA.2 (eq_neg_of_add_eq_zero_left h0)

theorem chart_unip : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 →
    ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  intro D A μ hμ κ hκ g b hg
  have hT := hκ g
  rw [hg, rat_Tm, blk4, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks] at hT
  have hT' := cancel_mul hT
  rw [mul_fromCols, Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id] at hT'
  obtain ⟨h1, h2⟩ := fromCols_inj hT'
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero] at h1
  rw [Matrix.mul_one, Matrix.mul_smul] at h2
  have hunit : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have hX : mt (dblSp A) g ⬝ (dblDec A).jX = (dblDec A).jX := h1.symm
  have hY : mt (dblSp A) g ⬝ (dblDec A).jY = (dblDec A).jY + (dblDec A).jX ⬝ (incA D μ⁻¹ • b) :=
    unscale hunit h2
  refine ⟨⟨incA D μ⁻¹ • b, skew_of_image (dblDec A) g _ hY⟩, rfl, ?_⟩
  refine (dblDec A).ga_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · rw [hX, HypDec.nC_jX]
  · rw [hY, HypDec.nC_jY]

end GlobalTheory.ChartUnip
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unimod

theorem hform_frame {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J B : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform σ J (B *ᵥ x) (B *ᵥ y) = ∑ i, σ (x i) * ((Formalism.UG.cT σ B * J * B) *ᵥ y) i := by
  have h1 : ∀ (u w : Fin n → R), Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := fun u w => by
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : (fun i => σ ((B *ᵥ x) i)) = (B.map σ) *ᵥ (fun i => σ (x i)) := funext fun i => RingHom.map_mulVec σ B x i
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem gram_int {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (O : Subring R) (hσ : ∀ z ∈ O, σ z ∈ O)
    (J B C H' : Matrix (Fin n) (Fin n) R) (L : (Fin n → R) → Prop) (hBC : B * C = 1)
    (hH : Formalism.UG.cT σ B * J * B * H' = 1)
    (hf : ∀ y, (∀ i, y i ∈ O) ↔ L (B *ᵥ y)) (hd : ∀ y, L y ↔ ∀ x, L x → Formalism.UG.hform σ J x y ∈ O) :
    (∀ i j, (Formalism.UG.cT σ B * J * B) i j ∈ O) ∧ ∀ i j, H' i j ∈ O := by
  have hs : ∀ i k : Fin n, (Pi.single i 1 : Fin n → R) k ∈ O := fun i k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  constructor
  · intro i j
    have h := (hd _).1 ((hf _).1 (hs j)) _ ((hf _).1 (hs i))
    rw [hform_frame, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
    simpa using h
  · intro i j
    have h : L (B *ᵥ (H' *ᵥ Pi.single j 1)) := by
      refine (hd _).2 fun x hx => ?_
      have e : x = B *ᵥ (C *ᵥ x) := by rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
      have hz : ∀ k, (C *ᵥ x) k ∈ O := (hf _).2 (e ▸ hx)
      rw [e, hform_frame]
      refine sum_mem fun k _ => mul_mem (hσ _ (hz k)) ?_
      rw [Matrix.mulVec_mulVec, hH, Matrix.one_mulVec]
      exact hs j k
    simpa using (hf _).2 h i

theorem compFin_cA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_gram {D : D7} (A : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (b : Mx D A.rank A.rank) :
    (adj b * gA A * b).map (compFin D.host.F D.host.E v) =
      Formalism.UG.cT (sigR _ D.sp.cm.sig) (b.map (compFin D.host.F D.host.E v)) * JR (Fv D.host.F v) A.gram *
        b.map (compFin D.host.F D.host.E v) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  funext i j; exact compFin_cA v _

theorem gram_unimodular : ∀ (D : D7) (A : HSp D) (b : GL (Fin A.rank) (AE D)), _root_.GlobalTheory.AdelicU.IsLatticeFrame (frameLat A) b → ∃ Hm : GL (Fin A.rank) (AE D), Hm.1 = adj b.1 * gA A * b.1 ∧ IntGL Hm := by
  intro D A b hb
  have h1 : adj b.1 * adj (b⁻¹).1 = 1 := by
    rw [← adj_mul, Units.inv_mul, adj_one]
  have h2 : adj (b⁻¹).1 * adj b.1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  let Hm : GL (Fin A.rank) (AE D) :=
    (⟨adj b.1, adj (b⁻¹).1, h1, h2⟩ * ⟨gA A, giA A, gA_mul_giA A, giA_mul_gA A⟩ * b : (Mx D A.rank A.rank)ˣ)
  have hH : Hm.1 = adj b.1 * gA A * b.1 := rfl
  have key := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
    gram_int (sigR _ D.sp.cm.sig) (intLoc D.host.F D.host.E v) (fun z hz => sigR_mem_intLoc _ hz)
      (JR (Fv D.host.F v) A.gram) (b.1.map (compFin D.host.F D.host.E v)) ((b⁻¹).1.map (compFin D.host.F D.host.E v))
      ((Hm⁻¹).1.map (compFin D.host.F D.host.E v)) (fun y => y ∈ latLoc D.host.F (frameLat A) v)
      (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← map_gram, ← hH, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hb v) (fun y => by
        have := SelfDual.isSelfDualAt_frameLat D A v
        exact (SetLike.ext_iff.1 this) y)
  refine ⟨Hm, hH, fun i j v => ?_, fun i j v => (key v).2 i j⟩
  have := (key v).1 i j
  rw [← map_gram, ← hH] at this
  exact this

end GlobalTheory.StdUnn.Unimod
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.LeviChart

variable {D : D7}

theorem rat_Tm (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY)).submatrix id finSumFinEquiv.symm := by
  ext i j
  rcases h : finSumFinEquiv.symm j with k | k <;>
    simp [rat, Tm, HypDec.jX, HypDec.jY, Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, h]

theorem doubledBasisSkewColumnMatrix_adelic_mul_blockDiagonal (A : HSp D) (μ : D.host.E) (a d : Mx D A.rank A.rank) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * blk4 a 0 0 d =
      (Matrix.fromCols ((dblDec A).jX * a) ((incA D μ • (dblDec A).jY) * d)).submatrix id finSumFinEquiv.symm := by
  rw [rat_Tm, blk4, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem mul_Tm (A : HSp D) (μ : D.host.E) (M : Mx D (A.rank + A.rank) (A.rank + A.rank)) :
    M * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (M * (dblDec A).jX) (M * (incA D μ • (dblDec A).jY))).submatrix id finSumFinEquiv.symm := by
  rw [rat_Tm, ← Matrix.mul_fromCols, Matrix.submatrix_mul _ _ id id _ Function.bijective_id, Matrix.submatrix_id_id]

end GlobalTheory.StdUnn.LeviChart


open GlobalTheory.StdUnn.LeviChart in
theorem GlobalTheory.StdUnn.chart_levi : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (a : GL (Fin A.rank) (AE D)), mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) → g = (dblDec A).levi a := by
  intro D A μ hμ κ hκ g a hg
  have h := hκ g
  rw [hg, doubledBasisSkewColumnMatrix_adelic_mul_blockDiagonal, mul_Tm] at h
  have h' := congrArg (fun M : Mx D _ _ => M.submatrix id finSumFinEquiv) h
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  obtain ⟨hX, hY⟩ := Matrix.fromCols_inj h'
  have hc : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  refine (dblDec A).ga_ext ?_ ?_ ?_
  · rw [HypDec.levi_jX, hX]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [HypDec.levi_jY]
    have h2 := congrArg (fun M => incA D μ⁻¹ • M) hY
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul] at h2
    exact h2.symm

end
end
