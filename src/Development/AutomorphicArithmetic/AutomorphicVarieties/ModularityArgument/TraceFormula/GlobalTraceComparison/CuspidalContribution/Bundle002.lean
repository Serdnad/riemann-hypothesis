module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle417
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

private theorem rt_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)}
    {K K' : Subgroup (GL (Fin a) (Af E))} {W W' : Submodule ℂ (Kinf E a → ℂ)} (hle : K' ≤ K)
    (hn : ∀ c : GL (Fin a) (Af E), (∀ w, GeneralLinearGroup.map (pLoc E w) c ∈ KGL w (n := a)) → ∀ u ∈ K', c⁻¹ * u * c ∈ K')
    (hT : ∀ f : Kinf E a → ℂ, (∀ a, (fun k => f (a * k)) ∈ W) → ∀ b, (fun k => f (k * b)) ∈ W') {φ m B} (h : EigT bad K W φ m B)
    {k : GA E a} (hk : k ∈ Reduction.maxCompact (K := E) (n := a)) : EigT bad K' W' (rt E a k φ) m B := by
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  set kf := GeneralLinearGroup.map (pFin E) k with hkf
  have hmem : ∀ w, GeneralLinearGroup.map (pLoc E w) kf ∈ KGL w (n := a) := fun w => by
    have hGL : GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a =
        KGL w (n := a) := by
      change GLint (Fin a) (ValuativeRel.valuation (w.adicCompletion E)).integer =
        GLint (Fin a) (w.adicCompletionIntegers E).toSubring
      exact congrArg (GLint (Fin a))
        (Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x)
    rw [← hGL]
    have e : GeneralLinearGroup.map (pLoc E w) kf = Reduction.finAt w k := by
      ext i j : 2
      rfl
    rw [e]
    exact hk.2 w
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Kinf E a, k = infGL E a (Unitary.toUnits k₀) * finGL E a kf := by
    obtain ⟨k₀, e⟩ := (UpperTheory.V.Cm.cptEq E a).surjective ⟨archPart k, archPart_mem_archCompact hk⟩
    refine ⟨k₀, ?_⟩
    rw [← UpperTheory.V.Cm.infEmb_cptEq, e, ← UpperTheory.V.Fb.finEmb_eq]
    exact (infEmb_archPart_mul_finEmb_finPart k).symm
  refine ⟨hne, (UpperTheory.V.Cm.isAutForm_iff _).2 (((UpperTheory.V.Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    ⟨fun u hu g => ?_, fun g => ?_⟩, fun t => ⟨(h.cap t).1, fun u => ?_⟩, fun w hw' => ?_⟩
  · change φ.1 (g * finGL E a u * k) = φ.1 (g * k)
    rw [← h.ty.1 _ (hle (hn kf hmem u hu)) (g * k)]
    congr 1
    conv_lhs => rw [hk₀]
    conv_rhs => rw [hk₀]
    rw [mul_assoc g, ← mul_assoc (finGL E a u), ← infGL_comm]
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  · have h1 := hT (fun k' => φ.1 (g * finGL E a kf * infGL E a (Unitary.toUnits k'))) (fun c => by
      simpa only [map_mul, mul_assoc] using h.ty.2 (g * finGL E a kf * infGL E a (Unitary.toUnits c))) k₀
    convert h1 using 2 with k'
    change φ.1 (g * _ * k) = _
    congr 1
    conv_lhs => rw [hk₀]
    rw [mul_assoc g (finGL E a kf), ← infGL_comm, map_mul, map_mul]
    simp only [mul_assoc]
  · have e := LinearMap.congr_fun ((capAct E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · have hw := h.sat w hw'
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw (hmem w)
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hloc : u * locGL E a w g = locGL E a w g * u := by
      have hproj (v : Pl E) :
          GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
            GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := by
        rw [map_mul (GeneralLinearGroup.map (pLoc E v)) u (locGL E a w g),
          map_mul (GeneralLinearGroup.map (pLoc E v)) (locGL E a w g) u]
        by_cases hv : v = w
        · subst hv
          rw [hu1, one_mul, mul_one]
        · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
      ext i j : 2
      exact FiniteAdeleRing.ext _ fun v =>
        congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (hproj v)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), hloc, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.iwaT :
    LevShrink → TypeSat → IwaT := by
  intro hL hT E _ _ _ r s bad K W hK hW
  obtain ⟨K', hle, hK', hn⟩ := hL E _ bad K hK.isOpen hK.loc
  obtain ⟨W', hW', hT⟩ := hT _ W hW
  refine ⟨K', W', hK', hW', fun φ m B h ⟨g, hg⟩ => ?_⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, rt_eig hle hn hT h hk, m₁, m₂, ?_⟩
  have hl : IsLeftInvariant φ.1 := h.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← constantTerm_rightTranslate] at hg
  exact hg
end

section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open GlobalTheory.Mem.Chr.CharModel
open scoped nonZeroDivisors

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem log_norm_coord (t : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    Real.log ‖(t : Af E) w‖ = -((GlobalTheory.Idele.ord_vw t w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℕ)) := by
  have hq : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [FinitePlace.norm_def, GlobalTheory.Idele.valued_idele, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp [Real.log_zpow]

private theorem logFin_eq (t : (Af E)ˣ) : logFin E t = -∑ᶠ w, Real.log ‖(t : Af E) w‖ := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero t)
  have h1 : GlobalTheory.Idele.idealOf t = ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw t v := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hv (by simp [h0])
  have h2 : ∑ᶠ w, Real.log ‖(t : Af E) w‖ = ∑ w ∈ hfin.toFinset, Real.log ‖(t : Af E) w‖ := by
    refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h0
    apply hv
    change Real.log ‖(t : Af E) v‖ = 0
    rw [log_norm_coord, h0]
    simp
  have hq : ∀ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := fun v => by
    simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
  rw [logFin, h1, map_prod, Rat.cast_prod, Real.log_prod, h2, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [log_norm_coord, neg_neg, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [Real.log_zpow]
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    exact zpow_ne_zero _ (hq v)

end SlopeTestRemainingChoices

section Aux2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem logAbs_eq_logNorm (u : (Ad E)ˣ) : PositivityTheory.Rg.BcB.logAbs (u : Ad E) = logNorm E u := by
  rw [logNorm, logFin_eq, PositivityTheory.Rg.BcB.logAbs, logInf, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, DiscreteGroups.T1.G.norm_cV_eq, DiscreteGroups.T1.G.mult_eq_two]
  rfl

end Aux2

section Aux3

open UpperTheory.V.Cj.S (Pl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

private theorem det_coord_le {bad : Set (Pl E)} {K : Subgroup (GL (Fin N) (Af E))} (hK : Lev bad K)
    {x : GL (Fin N) (Af E)} (hx : x ∈ K) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((GeneralLinearGroup.det x : (Af E)ˣ) : Af E) w) ≤ 1 := by
  obtain ⟨a, ha⟩ := hK.int x hx w
  have e1 : ((GeneralLinearGroup.det x : (Af E)ˣ) : Af E) w = (GeneralLinearGroup.map (pLoc E w) x).val.det :=
    RingHom.map_det (pLoc E w) x.val
  rw [e1, ← ha]
  have e2 : (bc (Ov E w).subtype a).val.det = (Ov E w).subtype a.val.det :=
    (RingHom.map_det (Ov E w).subtype a.val).symm
  rw [e2]
  exact a.val.det.2

private theorem chi_fin {bad : Set (Pl E)} {K : Subgroup (GL (Fin N) (Af E))} (hK : Lev bad K) (z : ℂ)
    {u : GL (Fin N) (Af E)} (hu : u ∈ K) : ((chiDet N (Model.absC E z) (finGL E N u) : ℂˣ) : ℂ) = 1 := by
  have h0 : logFin E (GeneralLinearGroup.det u) = 0 := by
    refine GlobalTheory.CompanionTheory.LimV.logFin_eq_zero_of_integral _ (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => det_coord_le hK hu w)
      (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_)
    rw [← map_inv]
    exact det_coord_le hK (inv_mem hu) w
  rw [PositivityTheory.Rg.Rs.ExponentTwist.chiDet_absC_val, det_finGL, GlobalTheory.CompanionTheory.LimV.logNorm_finId, h0]
  simp

private theorem chi_inf (z : ℂ) (k : Kinf E N) :
    ((chiDet N (Model.absC E z) (infGL E N (Unitary.toUnits k)) : ℂˣ) : ℂ) = 1 := by
  have h := GlobalTheory.CompanionTheory.LimV.chiDet_absC_cf (E := E) N z k (c := 1) (one_mem _)
  rw [PositivityTheory.Rg.Rs.InducedTensorMap.cf, map_one, mul_one] at h
  rw [h, Units.val_one]

end Aux3

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open GlobalTheory.Mem.Chr.CharModel in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.normTw :
    NormTw := by
  intro E _ _ _ N hN bad K W hK π φ m hφ hφ0 hT hm
  obtain ⟨s, hs⟩ := GlobalTheory.T.aux_statement_20 E N hN π fun τ => ⟨_, hm τ⟩
  have hψ : mulChi N (Model.absC E s) φ ∈ (π.twist (Model.absC E s)).V := ⟨φ, hφ, rfl⟩
  have hψ0 : mulChi N (Model.absC E s) φ ≠ 0 := fun e => hφ0 ((mulChi N (Model.absC E s)).map_eq_zero_iff.1 e)
  have htw : ∀ t, (π.twist (Model.absC E s)).HasInfChar t ((m t).map (· + s)) := fun t => by
    have h1 := (hm t).twist (Model.absC E s)
    rwa [Model.expo_absC] at h1
  refine ⟨π.twist (Model.absC E s), -s, hs, ?_, ⟨_, hψ, hψ0, ?_, ?_⟩, fun t => ?_, ?_, _, hψ, -s, fun g => ?_⟩
  · rw [← CuspSub.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel, PositivityTheory.Rg.Rs.StrStepB.absC_zero,
      CuspSub.twist_one]
  · intro u hu g
    rw [mulChi_apply, mulChi_apply, hT.1 u hu g, map_mul, Units.val_mul, chi_fin hK s hu, mul_one]
  · intro g
    have e : (fun k : Kinf E N => (mulChi N (Model.absC E s) φ).1 (g * infGL E N (Unitary.toUnits k))) =
        ((chiDet N (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext k
      rw [mulChi_apply, map_mul, Units.val_mul, chi_inf, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.smul_mem _ (hT.2 g)
  · simpa only [sub_neg_eq_add] using htw t
  · obtain ⟨g₀, hg₀⟩ : ∃ g, (mulChi N (Model.absC E s) φ).1 g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ0 (Subtype.ext (funext hcon))
    have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin N, Eop τ i i) (mulChi N (Model.absC E s) φ) =
        ((m τ).sum + N * s) • mulChi N (Model.absC E s) φ := fun τ => by
      rw [GlobalTheory.T.trace_operator_eigenvalue_sum E N _ τ _ (htw τ) _ hψ, Multiset.sum_map_add]
      simp [(hm τ).1]
    have hlie : lie E N (oneL E N) (mulChi N (Model.absC E s) φ) =
        (∑ τ : E →+* ℂ, ((m τ).sum + N * s)) • mulChi N (Model.absC E s) φ := by
      rw [GlobalTheory.T.lie_central_element_trace E N, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul]
    have hz : ∑ τ : E →+* ℂ, ((m τ).sum + N * s) = 0 := by
      refine GlobalTheory.CompanionTheory.TotalTrace.eq_zero_of_exp_mul_eq_one fun t => ?_
      have h1 := GlobalTheory.T.central_eigen_exponential E N _ _ hlie t g₀
      rw [hs _ hψ t g₀] at h1
      have h2 : Complex.exp ((∑ τ : E →+* ℂ, ((m τ).sum + N * s)) * t) * (mulChi N (Model.absC E s) φ).1 g₀ =
          1 * (mulChi N (Model.absC E s) φ).1 g₀ := by rw [one_mul]; exact h1.symm
      exact mul_right_cancel₀ hg₀ h2
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
    linear_combination hz
  · have e : PositivityTheory.Rg.BcB.logAbs g.val.det = logNorm E (GeneralLinearGroup.det g) :=
      logAbs_eq_logNorm (GeneralLinearGroup.det g)
    rw [mulChi_apply, PositivityTheory.Rg.Rs.ExponentTwist.chiDet_absC_val, e, mul_assoc, ← Complex.exp_add]
    simp
end
