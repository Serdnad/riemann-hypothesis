module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteCharNontrivial

theorem trace_eq_tau (I : AutInst) (x : I.E) :
    Algebra.trace ℚ I.E x = Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  have h1 : Algebra.trace ℚ I.E (star x) = Algebra.trace ℚ I.E x :=
    Algebra.trace_eq_of_algEquiv ((starRingAut : I.E ≃+* I.E).equivRatAlgEquiv _ _) x
  have h2 : Algebra.trace ℚ I.E (algebraMap I.F I.E (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) =
      2 * Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    rw [← Algebra.trace_trace (S := I.F), Algebra.trace_algebraMap, I.cm.deg2, map_nsmul, nsmul_eq_mul]
    norm_num
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), h1] at h2
  linarith

theorem exists_away {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (hg : g ≠ 0)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ j : 𝓞 E, j ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), g ∈ Q'.asIdeal → Q' ≠ Q → j ∈ Q'.asIdeal := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {g}}.Finite :=
    Ideal.finite_factors (by simpa using hg)
  have hch : ∀ v : HeightOneSpectrum (𝓞 E), ∃ a : 𝓞 E, a ∉ Q.asIdeal ∧ (v ≠ Q → a ∈ v.asIdeal) := by
    intro v
    by_cases hv : v = Q
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, fun h => (h hv).elim⟩
    · have hn : ¬ v.asIdeal ≤ Q.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hn
      exact ⟨a, ha', fun _ => ha⟩
  choose a ha ha' using hch
  refine ⟨∏ v ∈ hfin.toFinset, a v, ?_, ?_⟩
  · have := Q.isPrime
    intro h
    obtain ⟨v, -, hv⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ha v hv
  · intro Q' hQ' hne
    have hm : Q' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hQ'
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hm) (ha' Q' hne)

theorem core (I : AutInst) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) (Q : HeightOneSpectrum (𝓞 I.E)) (hgQ : ((g : ℕ) : 𝓞 I.E) ∈ Q.asIdeal)
    (hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal) (j : 𝓞 I.E) (hj : j ∉ Q.asIdeal) :
    ∃ z : 𝓞 I.E, psiEf (divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (algebraMap (𝓞 I.E) I.E (j * z)))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hgE : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have htr : ∀ z : 𝓞 I.E, ∃ n : ℤ, Algebra.trace ℚ I.E
      ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) = n := by
    intro z
    have e : divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E (j * z))) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
          ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) := by
      have e1 : algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((g : I.F)⁻¹) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((g : I.E)⁻¹) := by
        rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
        rfl
      rw [divN, e1, ← RingHom.map_mul, RingHom.map_mul (algebraMap (𝓞 I.E) I.E), mul_assoc]
    have h1 := hcon z
    rw [e] at h1
    have h2 := hrat ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z)
    rw [h1, one_mul] at h2
    rw [trace_eq_tau]
    exact PsiCondAllPf.trace_of_psi I _ h2
  obtain ⟨d, hd, hdQ⟩ := PsiCondAllPf.exists_diff_not_mem Q hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int _ htr d hd
  have hcg : (g : 𝓞 I.E) * c = j * d := by
    apply RingOfIntegers.coe_injective
    rw [RingHom.map_mul, RingHom.map_mul, hc, map_natCast]
    field_simp
  have hm : j * d ∈ Q.asIdeal := hcg ▸ Ideal.mul_mem_right _ _ hgQ
  rcases Q.isPrime.mem_or_mem hm with h | h
  exacts [hj h, hdQ h]

theorem exists_psi_ne_one : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  intro D psiEf _ _ hrat Q hQ
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    have hQ' := hQ
    rw [Nat.cast_mul] at hQ'
    rcases Q.isPrime.mem_or_mem hQ' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) Q hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.E D.host.E (D.host.g_prime i) (D.nd.g_split i) Q hi).1
  obtain ⟨j, hj, hj'⟩ := exists_away ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.2 hg) Q
  obtain ⟨z, hz⟩ := core (instOf D) psiEf hrat _ hg Q hQ hun j hj
  let z' : 𝓞 D.host.E := z
  refine ⟨oToS D.host.F D.host.E (j * z'), fun Q' h1 h2 => ?_, hz⟩
  rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hj' Q' h1 h2)

end GlobalTheory.FiniteCharNontrivial
end

section

noncomputable section

namespace GlobalTheory.BridgeDict

open NumberField Matrix Formalism.MainNotions.S
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Ainf HA fstA sndA inclR)

theorem comp_eq_thetaV (I : AutInst) (v : InfinitePlace I.F) (θ : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ) :
    θ.comp (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)).toRingHom =
      Formalism.L2.SG.AdBridge.thetaV I v := by
  have key : (fun a : Ainf I.F => θ (a ⊗ₜ[I.F] (1 : I.E))) =
      fun a : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (a v) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hθ.2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)) ?_
    funext x
    have e : (algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E) =
        (1 : Ainf I.F) ⊗ₜ[I.F] (algebraMap I.F I.E x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    simp only [Function.comp_apply]
    rw [e, hθ.1, I.φ_over]
    exact (Formalism.L2.SG.AdBridge.evV_algebraMap I v x).symm
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul]
    have e : (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) (a ⊗ₜ[I.F] x) =
        (a.1 ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [e, map_mul, hθ.1, congrFun key a.1]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem tauF_apply (I : AutInst) (z : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I z =
      Algebra.TensorProduct.comm I.F _ _ (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fin_eq (I : AutInst) (h : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I h).map (Formalism.L2.SG.AdBridge.tauF I) =
      (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
  unfold Formalism.MainNotions.StandardLattice.finMat
  rw [Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  rw [tauF_apply]

theorem infMat_bridge (I : AutInst) (e : I.GA ≃ₜ* Formalism.L2.SG.AdBridge.HAd I) (he : Formalism.L2.SG.AdBridge.IsBridge I e)
    (v : InfinitePlace I.F) (θv : Ainf I.F ⊗[I.F] I.E →+* ℂ) (hθv : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θv) (x : I.GA) :
    Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θv (e x) = I.P v * uMat (x.1 v) * (I.P v)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [(he x).1 v, Formalism.L2.SG.AdBridge.ofHAInf, ← comp_eq_thetaV I v θv hθv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_map]
  rfl

end GlobalTheory.BridgeDict

namespace GlobalTheory.BridgeDict

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem bridge_dict : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  intro D θ hθ V fr
  have hb := Formalism.IndefR.Eqv.UI.brg_isBridge fr
  have hθv : ∀ v : InfinitePlace D.host.F,
      IsInfEmb (Formalism.IndefR.Eqv.UI.phiV D v) (θ ((Formalism.L2.Host.tauPl D).symm v)) := fun v => hθ _
  refine ⟨fun x => ?_, fun x τ A hA => ?_, fun W hW => ?_⟩
  · have h1 := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.Eqv.UI.instV fr)).2.1 (Formalism.IndefR.Eqv.UI.brg fr) hb
    have e : Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔
        Formalism.IndefR.Eqv.UI.brg fr x ∈ Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := Iff.rfl
    rw [e, ← h1]
    exact (Formalism.IndefR.Eqv.UI.brg fr).injective.mem_set_image
  · subst hA
    have h := infMat_bridge (Formalism.IndefR.Eqv.UI.instV fr) _ hb (Formalism.L2.Host.tauPl D τ) (θ τ)
      (by have h := hθv (Formalism.L2.Host.tauPl D τ); rwa [Equiv.symm_apply_apply] at h) x
    exact h
  · obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.CuspCompare.isIsot_iff (Formalism.IndefR.Eqv.UI.instV fr) W).1 hW
    refine ⟨r, C, hC, fun x hx => ?_⟩
    obtain ⟨L, R, hL, hR⟩ := GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E)
      (Formalism.IndefR.Eqv.UI.instV fr).J_det hC.2.1
    let T : GA D V ≃* (Formalism.IndefR.Eqv.UI.instV fr).GA := (Formalism.IndefR.Eqv.UI.brg fr).symm.toMulEquiv
    have hT : ∀ g, Formalism.IndefR.Eqv.UI.brg fr (T g) = g := fun g => (Formalism.IndefR.Eqv.UI.brg fr).apply_symm_apply g
    unfold NI at hx
    have := (GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical _ _ hW).1 (fun g => ?_) _).1 hx
    · exact ((Formalism.IndefR.Eqv.UI.brg fr).symm_apply_apply x) ▸ this
    · rw [GlobalTheory.CuspCompare.mem_NA_iff (Formalism.IndefR.Eqv.UI.instV fr) _ hθv g (T g) ?_ ?_ hL hR]
      · exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)
      · rw [(hb (T g)).2, Formalism.L2.SG.AdBridge.ofHAFin, fin_eq]
        exact congrArg (fun h => (finMat _ _ h).map _) (hT g)
      · intro v
        rw [← infMat_bridge _ _ hb v _ (hθv v) (T g)]
        exact congrArg (infMat _ _ _) (hT g)

end GlobalTheory.BridgeDict
end
end
