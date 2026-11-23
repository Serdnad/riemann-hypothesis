module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle719
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle315
public import Mathlib.RingTheory.KrullDimension.PID
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

theorem compAt_eq_map (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem compAt_mt_of_suppAt {e : AE D} (he : infPart D e = 0) (hce : infPart D (cA D e) = 0) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  ext i j
  have h1 := hg i j
  have e1 : Formalism.L2.Theta.mt V g i j = (e + cA D e) * (Formalism.L2.Theta.mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [h1, Matrix.sub_apply, sub_add_cancel]
  simp only [compAt, Matrix.map_apply]
  rw [e1]
  simp only [map_add, map_mul, he, hce, add_zero, zero_mul, map_zero, zero_add]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.one_apply_ne hij]

theorem compAt_mt_inv {V : HSp D} {g : GA D V} {θ : InfFam D} {τ : D.what₂.Tau} (hg : compAt θ τ (Formalism.L2.Theta.mt V g) = 1) :
    compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) = 1 := by
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
    rw [compAt_eq_map, compAt_eq_map, ← Matrix.map_mul, hm, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hg, Matrix.mul_one] at h2

theorem integrableOn_mul_right_iff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    IntegrableOn (fun g => f (g * k)) 𝓕 μ ↔ IntegrableOn f 𝓕 μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h𝓕.integrableOn_iff h2 (fun γ g => by simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hf γ γ.2 _)]
  exact hmp.integrableOn_comp_preimage hemb

end GlobalTheory.BotTranslate

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)



theorem translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  intro D T L sc G W i j A A' WW X Y hX hY g g' h κ κ' hκ hκ' hg hg' hh c hc
  obtain ⟨⟨t₀, hc₀⟩, P, P', H⟩ := hc
  have hYi := hY.is
  have hψ := hYi.isVac.1
  have hθ := hYi.isVac.2.inf
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have bA := GlobalTheory.BotFrames.isStd_B_eq hX.std hY.std
  have bA' := GlobalTheory.BotFrames.isStd_B_eq hX.std' hY.std'
  have bW := GlobalTheory.BotFrames.isStd_B_eq hX.stdW hY.stdW
  have he := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum (hYi.idem t)
  have hce := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum (hYi.idem t)
  have cg : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A (g t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg t).1 W.θ τ)
  have cg' : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A' (g' t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg' t).1 W.θ τ)
  have ch : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt WW (h t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hh t).1 W.θ τ)
  set Y₁ := GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) with hY₁

  have hK : ∀ t Q h'' g'', Y₁.ker W.ψ W.θ t Q h'' g'' = κ t * Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.fst t) hYi.isVac.2.theta
    have c0 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm (g t)⁻¹)) = 1 := cg t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hYi.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      ((ofSgn true A).symm (g t)⁻¹) (h t)⁻¹ (fun τ => by rw [c0 τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [c0 τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f t) tf Q).2
    have key' : Y.ω t ((g t)⁻¹, (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q) =
        pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q :=
      key
    show thetaKO (Y.ω t) g'' h'' (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        (κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q) =
      κ t * thetaKO (Y.ω t) (g'' * (g t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q)
    rw [sA, sW, bA, bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key']
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  have hK' : ∀ t Q h'' g'', Y₁.ker' W.ψ W.θ t Q h'' g'' = κ' t * Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g' t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.snd t) hYi.isVac'.2.theta
    have hw : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hYi.weil' t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (Y.ω' t) hw hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      (g' t)⁻¹ (h t)⁻¹ (fun τ => by rw [cg' t τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [cg' t τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f' t) tf Q).2
    show thetaKO (Y.ω' t) g'' h'' (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B
        (κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) Q) =
      κ' t * thetaKO (Y.ω' t) (g'' * (g' t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) Q)
    rw [sA', sW, bA', bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key]
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

  haveI := hYi.meas.1
  haveI := hYi.meas'.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A Y.m hYi.meas.1).1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A' Y.m' hYi.meas'.1).1
  have mk : ∀ k : GA D A, Measure.map (fun x => x * k) Y.m = Y.m := fun k => MeasureTheory.map_mul_right_eq_self Y.m k
  have mk' : ∀ k : GA D A', Measure.map (fun x => x * k) Y.m' = Y.m' := fun k => MeasureTheory.map_mul_right_eq_self Y.m' k
  have hI : ∀ t Q h'', Y₁.I W.ψ W.θ t Q h'' = κ t * Y.I W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd, Y₁.ker W.ψ W.θ t Q h'' x ∂Y.m = κ t * ∫ x in Y.fd, Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m
    simp_rw [hK]
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t Q _)
  have hI' : ∀ t Q h'', Y₁.I' W.ψ W.θ t Q h'' = κ' t * Y.I' W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd', Y₁.ker' W.ψ W.θ t Q h'' x ∂Y.m' = κ' t * ∫ x in Y.fd', Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m'
    simp_rw [hK']
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t Q _)
  refine ⟨⟨t₀, mul_ne_zero (div_ne_zero (hκ t₀) (hκ' t₀)) hc₀⟩, P, P', fun t => ⟨fun h'' => ⟨?_, ?_⟩, ?_, fun h'' => ?_⟩⟩
  · show IntegrableOn (Y₁.ker W.ψ W.θ t P h'') Y.fd Y.m
    rw [show Y₁.ker W.ψ W.θ t P h'' = fun x => κ t * Y.ker W.ψ W.θ t P (h'' * (h t)⁻¹) (x * (g t)⁻¹) from funext (hK t P h'')]
    exact ((integrableOn_mul_right_iff (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t P _)).2 ((H t).1 _).1).const_mul _
  · show IntegrableOn (Y₁.ker' W.ψ W.θ t P' h'') Y.fd' Y.m'
    rw [show Y₁.ker' W.ψ W.θ t P' h'' = fun x => κ' t * Y.ker' W.ψ W.θ t P' (h'' * (h t)⁻¹) (x * (g' t)⁻¹) from funext (hK' t P' h'')]
    exact ((integrableOn_mul_right_iff (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t P' _)).2 ((H t).1 _).2).const_mul _
  · obtain ⟨h₀, hne⟩ := (H t).2.1
    refine ⟨h₀ * h t, ?_⟩
    rw [hI', mul_inv_cancel_right]
    exact mul_ne_zero (hκ' t) hne
  · rw [hI, hI', (H t).2.2]
    field_simp [hκ' t]

end GlobalTheory.BotTranslate

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleDiv

open IsLocalRing

theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

theorem formallyEtale_of_comp_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (h : (g.comp f).FormallyEtale) :
    f.FormallyEtale := by
  let e := RingEquiv.ofBijective g hg
  have : f = (e.symm : T →+* S).comp (g.comp f) := by
    ext x
    exact (e.symm_apply_apply (f x)).symm
  rw [this]
  exact h.comp (formallyEtale_of_bijective _ e.symm.bijective)

theorem formallyEtale_stalkMap {M W : Scheme.{0}} (f : M ⟶ W) (U : M.Opens)
    [Etale (U.ι ≫ f)] (w : U.toScheme) : (f.stalkMap (U.ι w)).hom.FormallyEtale := by
  have hu := FormallyUnramified.stalkMap (U.ι ≫ f) w
  have hs : ((U.ι ≫ f).stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ w))
  have h : ((U.ι ≫ f).stalkMap w).hom.FormallyEtale := by
    algebraize [((U.ι ≫ f).stalkMap w).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have : IsIso (U.ι.stalkMap w) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h
  exact formallyEtale_of_comp_bijective (f.stalkMap (U.ι w)).hom (U.ι.stalkMap w).hom
    (ConcreteCategory.bijective_of_isIso _) h

theorem strictMono_ι {M : Scheme.{0}} (U : M.Opens) : StrictMono U.ι := by
  have hi := U.ι.isOpenEmbedding.isInducing
  intro a b h
  refine lt_of_le_not_ge ?_ ?_
  · exact hi.specializes_iff.2 h.le
  · exact fun h' => h.not_ge (hi.specializes_iff.1 h')

theorem map_maximalIdeal_stalk {M W : Scheme.{0}} (f : M ⟶ W) [LocallyOfFiniteType f] (z : M)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    (maximalIdeal (W.presheaf.stalk (f z))).map (f.stalkMap z).hom =
      maximalIdeal (M.presheaf.stalk z) := by
  have hft := LocallyOfFiniteType.stalkMap f z
  algebraize [(f.stalkMap z).hom]
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f z)) (M.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem log_ordFrac_map {K L : Type} [Field K] [Field L] (V : ValuationSubring K)
    (V' : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing V']
    (ρ : K →+* L) (ψ : V →+* V') (hψ : ∀ a, (ψ a : L) = ρ a) {t : V} (ht : Irreducible t)
    (ht' : Irreducible (ψ t)) {g : K} (hg : g ≠ 0) :
    WithZero.log (Ring.ordFrac V' (ρ g)) = WithZero.log (Ring.ordFrac V g) := by
  obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_zpow (F := K) ht hg
  have h1 := ordTop_vw_unit_mul_zpow (F := K) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := L) ht' (Units.map ψ.toMonoidHom u) m
  have e : ρ (algebraMap V K u * algebraMap V K t ^ m) =
      algebraMap V' L (Units.map ψ.toMonoidHom u) * algebraMap V' L (ψ t) ^ m := by
    rw [map_mul, map_zpow₀]
    simp [hψ]
  rw [← e] at h2
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_inj] at h1
  rw [ordTop_vw_of_ne_zero _ ((map_ne_zero ρ).2 hg), WithTop.coe_inj] at h2
  rw [h1, h2]

theorem isFreeGen_formMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {D : ℕ}
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem maximalIdeal_eq_bot {X : Scheme.{0}} [IsIntegral X] {x : X} (h : Order.coheight x = 0) :
    maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h.le
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime ⊥).symm

theorem coheight_apply_eq_one {M W : Scheme.{0}} [IsIntegral W] (f : M ⟶ W) [LocallyOfFiniteType f]
    (U : M.Opens) [Etale (U.ι ≫ f)] (w : U.toScheme) (h1 : Order.coheight (U.ι w) = 1)
    (hB : maximalIdeal (M.presheaf.stalk (U.ι w)) ≠ ⊥) : Order.coheight (f (U.ι w)) = 1 := by
  have hle : Order.coheight w ≤ 1 :=
    h1 ▸ Order.coheight_le_coheight_apply_of_strictMono _ (strictMono_ι U) w
  have hle' := GlobalTheory.GenExtendNormal.coheight_apply_le_one (U.ι ≫ f) (Flat.generalizingMap _) w hle
  refine le_antisymm hle' ?_
  rw [Order.one_le_iff_ne_zero]
  intro h0
  apply hB
  rw [← map_maximalIdeal_stalk f _ (formallyEtale_stalkMap f U w), maximalIdeal_eq_bot h0,
    Ideal.map_bot]

theorem exists_isAt_ord_formOrd : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f]
    (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z →
    ∃ E : DivOver p, E.IsAt (f z) ∧
      (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU z hz E' hE'
  haveI := hU
  obtain ⟨w, rfl⟩ : ∃ w : U.toScheme, U.ι w = z := ⟨⟨z, hz⟩, rfl⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := GlobalTheory.ModifSections.isNormalScheme_of_smooth p
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  haveI hB : IsDiscreteValuationRing (M.presheaf.stalk (U.ι w)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing hE'.equiv.symm
  have hφ := formallyEtale_stalkMap f U w
  have hmax := map_maximalIdeal_stalk f (U.ι w) hφ
  have hc := coheight_apply_eq_one f U w hE'.coheight_eq_one
    (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
  haveI hA : IsDiscreteValuationRing (W.presheaf.stalk (f (U.ι w))) :=
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hc
  let ψ : E.ring →+* E'.ring :=
    hE'.equiv.toRingHom.comp ((f.stalkMap (U.ι w)).hom.comp hE.equiv.symm.toRingHom)
  have hψ : ∀ a, (ψ a : M.functionField) = functionFieldMap f a := by
    intro a
    obtain ⟨b, rfl⟩ := hE.equiv.surjective a
    have e : ψ (hE.equiv b) = hE'.equiv (f.stalkMap (U.ι w) b) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact (functionFieldMap_algebraMap f (U.ι w) b).symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (W.presheaf.stalk (f (U.ι w)))
  have ht' : Irreducible (f.stalkMap (U.ι w) t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at ht ⊢
    rw [← hmax, ht, Ideal.map_span, Set.image_singleton]
  have htE : Irreducible (hE.equiv t) := ht.map hE.equiv
  have htE' : Irreducible (ψ (hE.equiv t)) := by
    have e : ψ (hE.equiv t) = hE'.equiv (f.stalkMap (U.ι w) t) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact ht'.map hE'.equiv
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    log_ordFrac_map E.ring E'.ring (functionFieldMap f) ψ hψ htE htE' g.ne_zero
  refine ⟨E, hE, hord, fun η hη => ?_⟩
  have hn : topologicalKrullDim W = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨c, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have hconst : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext
    ((hψ _).trans (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a))
  have hψFE : ψ.FormallyEtale :=
    RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp
      (formallyEtale_of_bijective _ hE.equiv.symm.bijective) hφ)
      (formallyEtale_of_bijective _ hE'.equiv.bijective)
  have h3 : ((functionFieldMap f).comp E.ring.subtype).comp E.const = Cartier.constFn (f ≫ p) := by
    ext a
    exact RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a
  have e1 : GlobalTheory.EtaleKlt.ratPull p f n (E.toRat n ω) =
      E'.toRat n (TopForm.formMap n ψ hconst ω) := by
    change TopForm.formMap n (functionFieldMap f) _ (TopForm.formMap n E.ring.subtype rfl ω) =
      TopForm.formMap n E'.ring.subtype rfl (TopForm.formMap n ψ hconst ω)
    exact (formMap_formMap E.ring.subtype (functionFieldMap f)
      ((functionFieldMap f).comp E.ring.subtype) rfl _ _ h3 ω).trans
      (formMap_formMap ψ E'.ring.subtype ((functionFieldMap f).comp E.ring.subtype)
        (RingHom.ext hψ) _ _ h3 ω).symm
  have h1 : E.formOrd (c • E.toRat n ω) = E.ord (Units.mk0 c hc0) :=
    DivOver.IsFormOrd.formOrd_eq hη ⟨ω, hω, Units.mk0 c hc0, rfl, rfl⟩
  have hη' : GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω) ≠ 0 := by
    have hfree := E'.isFreeGen_toRat (isFreeGen_formMap hψFE hconst hω)
    rw [map_smulₛₗ, e1]
    intro h0
    have := hfree.1 (a₁ := functionFieldMap f c) (a₂ := 0) (by simp only [h0, zero_smul])
    exact hc0 ((map_eq_zero _).1 this)
  have h2 : E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
      E'.ord (Units.map (functionFieldMap f).toMonoidHom (Units.mk0 c hc0)) :=
    DivOver.IsFormOrd.formOrd_eq hη' ⟨_, isFreeGen_formMap hψFE hconst hω, _,
      by rw [map_smulₛₗ, e1]; rfl, rfl⟩
  change E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
    E.formOrd (c • E.toRat n ω)
  rw [h1, h2, hord]

end GlobalTheory.EtaleDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | exact GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | (intros; apply GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd <;> assumption)
end
