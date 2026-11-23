module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle423
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle012
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
import Std.Tactic.BVDecide.Normalize.Prop
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle013

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord
section Loc
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hsm := h.isSmooth
  obtain ⟨c, x, rfl, hi, hc, e, hsub⟩ := h
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hci : ∀ a, (contra (x a).rep).IsIrreducible := fun a =>
    GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a)
  have hcu : ∀ a, IsCuspidal (contra (x a).rep) := fun a => by
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hc a).1, (hc a).2.2⟩).1
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA] at this
    exact (IrrGL.isCusp_of.1 this).2
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra e
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
  have H : IsCuspSupport (contra π) (fun a => (x a).1) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hi) hi,
      fun a => ⟨(hc a).1, hci a, hcu a⟩, e, ?_⟩
    exact (GlobalTheory.CompanionTheory.ContraSub.main k N _ _ _ _ hsm (isSmooth_parInd e _) hsub).trans
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective)
  have e2 : (Zc.dualCl ∘ x) = fun a => IrrGL.of (contra (x a).rep) (H.2.1 a).2.2.1 (H.2.1 a).2.1 :=
    funext fun a => GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA (x a)
  rw [Multiset.map_map, e2]
  exact hasSupport_of_isCuspSupport H
private theorem hasSupport_of_invT (c : k ≃+* k') (hc : Continuous c) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k') W)
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g v, τ (GlobalTheory.LFun.ConjPlace.invT c N g) (T v) = T (σ g v))
    {s : Multiset (IrrGL (k := k))} (h : HasSupport σ s) :
    HasSupport τ ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL c (GlobalTheory.LocalFieldIso.continuous_symm c hc))) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm c hc
  obtain ⟨E⟩ := GlobalTheory.GelfandKazhdan.equiv_contra k N V σ (hA k N V σ h.isSmooth h.isIrreducible) h.isIrreducible
  have h1 := (hasSupport_contra h).of_equiv E.symm
  have h2 := GlobalTheory.SuppIne.hasSupport_comp c hc hc' h1
  refine h2.of_equiv (GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩ T.bijective)
  have hg : GlobalTheory.LFun.ConjPlace.invT c N (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k
      (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) = g :=
    Units.ext (Matrix.ext fun i j => by
      rw [GlobalTheory.LFun.ConjPlace.invT_val]
      exact c.apply_symm_apply _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change T (σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) v) = τ g (T v)
  rw [← hT, hg]
private theorem dualCl_eq_of {x y : IrrGL (k := k)} (H : GlobalTheory.LocLanglands.DualCl x y) : Zc.dualCl x = y := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨n, π, π', rfl, rfl, ⟨E⟩⟩ := H
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  change IrrGL.of _ _ _ = IrrGL.of π'.ρ π'.smooth π'.irr
  exact IrrGL.of_eq_of.2 ⟨(GlobalTheory.ContraRefl.contraEquiv (equivRep π)).trans E.symm⟩
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem val_lt_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) < 1 ↔ valuation k x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x⁻¹
  have p1 : 0 < valuation k x := by
    rw [zero_lt_iff]; simpa using hx
  have p2 : 0 < valuation k' (i x) := by
    rw [zero_lt_iff]; simpa using hx
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ p1, inv_le_one₀ p2] at h
  rw [← not_le, ← not_le, h]
private theorem val_eq_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) = 1 ↔ valuation k x = 1 := by
  have a := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x
  have b := val_lt_one_iff i hi x
  exact ⟨fun h => le_antisymm (a.1 h.le) (not_lt.1 fun l => (b.2 l).ne h),
    fun h => le_antisymm (a.2 h.le) (not_lt.1 fun l => (b.1 l).ne h)⟩
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem unram_unif (i : k ≃+* k') (hi : Continuous i) (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    μ (Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k')) = μ (ImaginaryQuadraticEtaCharacter.unif k) := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  set a : kˣ := Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k') with ha
  have hav : (a : k) = i.symm (ImaginaryQuadraticEtaCharacter.unif k' : k') := rfl
  have S := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  have S' := (ImaginaryQuadraticEtaCharacter.polFacts k').1
  have ha1 : valuation k (a : k) < 1 := by
    rw [hav]; exact (val_lt_one_iff i.symm hi' _).2 S'.1
  have hb1 : valuation k' (i (ImaginaryQuadraticEtaCharacter.unif k : k)) < 1 := (val_lt_one_iff i hi _).2 S.1
  have le1 := S.2 _ ha1
  have le2 := S'.2 _ hb1
  have pa : 0 < valuation k (a : k) := by
    rw [zero_lt_iff]; simp
  have pb : 0 < valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := by
    rw [zero_lt_iff]; simp
  have pu : 0 < valuation k' (ImaginaryQuadraticEtaCharacter.unif k' : k') := by
    rw [zero_lt_iff]; simp
  have le3 : valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) ≤ valuation k (a : k) := by
    have h1 : valuation k' (i ((ImaginaryQuadraticEtaCharacter.unif k : k) * (a : k)⁻¹)) ≤ 1 := by
      have : i (a : k) = (ImaginaryQuadraticEtaCharacter.unif k' : k') := by rw [hav]; exact i.apply_symm_apply _
      rw [map_mul, map_inv₀, this, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ le2 zero_le'
    have h2 := (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi _).1 h1
    rw [map_mul, map_inv₀] at h2
    simpa using (mul_inv_le_iff₀ pa).1 h2
  have he : valuation k (a : k) = valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := le_antisymm le1 le3
  have hu : μ (a * (ImaginaryQuadraticEtaCharacter.unif k)⁻¹) = 1 := hμ _ (by
    rw [Units.val_mul, map_mul, he, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ pb.ne'])
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu
private theorem isUnram_comp (i : k ≃+* k') (hi : Continuous i) {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) :
    IsUnram (μ.comp (Units.map i.symm.toRingHom.toMonoidHom)) := fun x hx =>
  hμ _ ((val_eq_one_iff i.symm (GlobalTheory.LocalFieldIso.continuous_symm i hi) _).2 hx)
private theorem unl_of_map (i : k ≃+* k') (hi : Continuous i) (q : ℕ) (s : Multiset (IrrGL (k := k)))
    (h : ImaginaryQuadraticEtaCharacter.Unl q ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i (GlobalTheory.LocalFieldIso.continuous_symm i hi)))) :
    ImaginaryQuadraticEtaCharacter.Unl q s := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  intro ξ hξ ξ' hξ' hun
  obtain ⟨h1, m1⟩ := hξ
  obtain ⟨h2, m2⟩ := hξ'
  let U : k'ˣ →* kˣ := Units.map i.symm.toRingHom.toMonoidHom
  have sm : ∀ ζ : kˣ →* ℂˣ, IsSmoothChar ζ → IsSmoothChar ((ζ⁻¹).comp U) := fun ζ hζ =>
    IsOpen.preimage (Continuous.units_map _ hi') hζ.inv
  have mem : ∀ (ζ : kˣ →* ℂˣ) (hζ : IsSmoothChar ζ), IrrGL.ofChar ζ hζ ∈ s →
      IrrGL.ofChar ((ζ⁻¹).comp U) (sm ζ hζ) ∈ (s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i hi') := fun ζ hζ hm =>
    Multiset.mem_map.2 ⟨IrrGL.ofChar ζ⁻¹ hζ.inv, Multiset.mem_map.2 ⟨_, hm,
      dualCl_eq_of (GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ hζ hζ.inv rfl)⟩,
      GlobalTheory.DegOneChar.trGL_ofChar i hi' _ _ _⟩
  have e : ((ξ'⁻¹).comp U) * ((ξ⁻¹).comp U)⁻¹ = (ξ * ξ'⁻¹).comp U :=
    MonoidHom.ext fun x => by simp [mul_comm]
  have := h ((ξ'⁻¹).comp U) ⟨sm _ h2, mem _ _ m2⟩ ((ξ⁻¹).comp U) ⟨sm _ h1, mem _ _ m1⟩
    (by rw [e]; exact isUnram_comp i hi hun)
  rw [e, MonoidHom.comp_apply] at this
  rwa [unram_unif i hi _ hun] at this
end Loc
theorem conj_torsion_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → ConjTor := by
  intro _ E _ _ _ n hn π hd w w' hu hT
  by_cases e : w' = w
  · subst e
    exact hT
  obtain rfl : w' = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl ⟨hu, Or.inl e⟩
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc : Continuous (GlobalTheory.ThetaSatake.cloc w) := (conjLoc_spec _ w).1
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm _ hc
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have key : ∀ σ, π.IsLocComp (GlobalTheory.ThetaSatake.cw w) σ → ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v,
      τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n g) (T v) = T (σ.ρ g v) := fun σ hσ =>
    GlobalTheory.CompanionTheory.OneExDatum.exists_equiv_of_dualIsConj hd w σ τ hσ (hA _ _ _ _ σ.smooth σ.irred) hτ
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨T, hTT⟩ := key σ hσ
    obtain ⟨s, hs, h1⟩ := hT.1 τ hτ
    have hs' : HasSupport τ.ρ s := hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred).symm
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w).symm hc' τ.ρ σ.ρ T.symm (fun g v => by
      obtain ⟨u, rfl⟩ := T.surjective v
      have := hTT (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) u
      have e : GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) = g :=
        (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n).apply_symm_apply g
      rw [e] at this
      rw [this, T.symm_apply_apply, T.symm_apply_apply]) hs'
    refine ⟨_, h2.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), ?_⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨y'', hy'', rfl⟩ := Multiset.mem_map.1 hy'
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA y'' (hs'.isCusp hy'')).2
    exact this.trans (h1 _ hy'')
  · rintro s ⟨σ, hσ, hs⟩
    obtain ⟨T, hTT⟩ := key σ hσ
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w) hc σ.ρ τ.ρ T hTT hs
    have h3 := hT.2 _ ⟨τ, hτ, h2⟩
    rw [GlobalTheory.ThetaSatake.absNorm_cw]
    exact unl_of_map (GlobalTheory.ThetaSatake.cloc w) hc _ _ h3
end UpperTheory.V.Z.Ord
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)
end P_spSupp
open P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem step_spSupp_alt (G : Grp k n) : G.Step_spSupp_alt := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _
  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy
  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])
  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2
end UpperTheory.TNZ.Grp
end
end
end

section




section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spCount
section Abstract
variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}
variable (G : Grp k n)
end Local
end UpperTheory.TNZ.Grp.P_spCount
namespace UpperTheory.TNZ.Grp
open P_spCount
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open scoped Classical in

theorem step_spCount_alt {n : ℕ} (G : Grp k n) : G.Step_spCount_alt := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩
end UpperTheory.TNZ.Grp
end
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spPiSub
end UpperTheory.TNZ.Grp.P_spPiSub
namespace UpperTheory.TNZ.Grp
open P_spPiSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem step_spPiSub_alt {n : ℕ} (G : Grp k n) : G.Step_spPiSub_alt := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq
end UpperTheory.TNZ.Grp
end
end
end
