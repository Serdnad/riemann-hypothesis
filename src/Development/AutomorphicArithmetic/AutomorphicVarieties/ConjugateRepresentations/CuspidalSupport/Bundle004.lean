module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem kgl_eq (w : Pl E) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = KGL w (n := a) := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = GLint (Fin a) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem loc_comm (w : Pl E) (g : GL (Fin a) (w.adicCompletion E)) {u : GL (Fin a) (Af E)}
    (hu : GeneralLinearGroup.map (pLoc E w) u = 1) : u * locGL E a w g = locGL E a w g * u := by
  have H : ∀ v, GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
      GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hu, mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.rtK :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.RtK := by
  intro hc E _ _ _ a φ m B h k hk
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  refine ⟨hne, (Cm.isAutForm_iff _).2 (((Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    fun t => ⟨(h.cap t).1, fun u => ?_⟩, h.sat.mono fun w hw => ?_⟩
  · have e := LinearMap.congr_fun ((hc E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · set kf := GeneralLinearGroup.map (pFin E) k with hkf
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    have hmem : kw ∈ KGL w (n := a) := by
      rw [← kgl_eq]
      have e : kw = GroundTheory.Automorphic.Reduction.finAt w k := by
        ext i j : 2
        rfl
      rw [e]
      exact hk.2 w
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw hmem
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

namespace UpperTheory.V.Cj.S

theorem satOfEig : SatOfEig := by
  intro E _ _ w n V _ _ π x hx0 hx hsc
  have hK : IsCommensurated (KGL w (n := n)) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  choose c hc using fun j => hsc _ (Tj_mem_hecke (n := n) hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w (n := n)) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hx0, hx, hB, fun ϖ' hu' j hj => ?_⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j, hBc j hj]

end UpperTheory.V.Cj.S
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

private theorem rank_le_aleph0_of_irred [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    {ρ : Representation ℂ G V} (hs : GlobalTheory.PRep.IsSmooth ρ) (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => stable_eq hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

end

private theorem biSimple {E : Type} [Field E] [NumberField E] {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin a) (Af E)) V} (hi : ρ.IsIrreducible) (w : Pl E) :
    GlobalTheory.CompanionTheory.SatAe.IsBiSimple (locOf ρ w) := by
  intro S h1 h2
  refine stable_eq hi S fun k x hx => ?_
  let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
  have h3 := h2 (ρ (k * (locGL E a w g)⁻¹)) (fun g' => by
    change ρ _ * ρ _ = ρ _ * ρ _
    rw [← map_mul, ← map_mul, LocSph.comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])])
    _ (h1 g x hx)
  have h4 : ρ (k * (locGL E a w g)⁻¹) (locOf ρ w g x) = ρ k x := by
    change ρ _ (ρ _ x) = ρ k x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rwa [h4] at h3

theorem UpperTheory.V.Cj.S.tauSat :
    UpperTheory.V.Cj.S.TauSat := by
  intro E _ _ _ a τ v hv
  haveI := GlobalTheory.CompanionTheory.SatAe.secondCountable_GL (E := E) (a := a)
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change V at v
  have hr := rank_le_aleph0_of_irred hs hi hv
  filter_upwards [LocSph.eventually_mem ((hs v).mem_nhds (by simp))] with w hw
  have hfix : v ∈ fixed (locOf ρ w) (KGL w (n := a)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hsl : GlobalTheory.PRep.IsSmooth (locOf ρ w) := fun x => (hs x).preimage (CuspSub.continuous_locGL w)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => GlobalTheory.CompanionTheory.SatAe.exists_scalar hsl
    (SatCompare.isOpen_isCompact_KGL w a).2 (Final.GLintComm E w a) (Final.HeckeCommGL E w a ℂ) (biSimple hi w) hr h hh)
    ((Submodule.ne_bot_iff _).2 ⟨v, hfix, hv⟩)
  exact ⟨B, hB, hB.2 v hfix hv⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem stable_twist (χ : HChar E) {U : Submodule ℂ (Sm E a)} (h : _root_.GlobalTheory.CuspRep.IsStable U) :
    _root_.GlobalTheory.CuspRep.IsStable (U.map (mulChi a χ).toLinearMap) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (h o φ hφ)) (U.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩

private theorem map_twist_inv (χ : HChar E) (U : Submodule ℂ (Sm E a)) :
    (U.map (mulChi a χ).toLinearMap).map (mulChi a χ⁻¹).toLinearMap = U := by
  rw [← Submodule.map_comp]
  have : (mulChi a χ⁻¹).toLinearMap ∘ₗ (mulChi a χ).toLinearMap = LinearMap.id := LinearMap.ext fun φ => by
    change mulChi a χ⁻¹ (mulChi a χ φ) = φ
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  rw [this, Submodule.map_id]

private theorem exists_twist (ha : 1 ≤ a) (c : ℂ) :
    ∃ χ : HChar E, dchi χ (Matrix.of (oneL E a)).trace = -c := by
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨Model.absC E (-c / (a * (2 * Fintype.card (InfinitePlace E)))), ?_⟩
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one, nsmul_eq_mul]
  push_cast
  field_simp

private theorem compl_zero {C : Submodule ℂ (Sm E a)} (hc : ∀ φ ∈ C, IsCuspForm φ)
    (h0 : ∀ φ ∈ C, lie E a (oneL E a) φ = 0) (hs : _root_.GlobalTheory.CuspRep.IsStable C) {U : Submodule ℂ (Sm E a)} (hU : U ≤ C)
    (hsU : _root_.GlobalTheory.CuspRep.IsStable U) : ∃ D ≤ C, _root_.GlobalTheory.CuspRep.IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C := by
  have hr : C ≤ LinearMap.range (UpperTheory.V.Cm.ofCusp E a) := fun φ h => UpperTheory.V.Cm.mem_range_ofCusp.2 (hc φ h)
  have hz : C.comap (UpperTheory.V.Cm.ofCusp E a) ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms E a :=
    fun ψ h => UpperTheory.V.Cm.mem_centralCuspForms_of (h0 _ h)
  have st := UpperTheory.V.Cm.stab_comap hsU
  obtain ⟨D, -, d2, d3, d4, d5, d6⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_compl_centralCuspForms
    (U.comap (UpperTheory.V.Cm.ofCusp E a)) ((Submodule.comap_mono hU).trans hz) st.ρ st.σ st.τ
  have hUe : (U.comap (UpperTheory.V.Cm.ofCusp E a)).map (UpperTheory.V.Cm.ofCusp E a) = U :=
    Submodule.map_comap_eq_self (hU.trans hr)
  have hD : _root_.GlobalTheory.CuspRep.IsStable (D.map (UpperTheory.V.Cm.ofCusp E a)) := UpperTheory.V.Cm.isStable_map ⟨d2, d3, d4⟩
  refine ⟨D.map (UpperTheory.V.Cm.ofCusp E a) ⊓ C, inf_le_right, fun o φ h => ⟨hD o φ h.1, hs o φ h.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, ← hUe, ← Submodule.map_inf _ UpperTheory.V.Cm.ofCusp_injective, d5, Submodule.map_bot, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, inf_eq_right, ← hUe, ← Submodule.map_sup, d6]
    exact (Submodule.map_comap_eq_self hr).ge.trans (Submodule.map_mono hz)

end

theorem UpperTheory.V.Cj.S.ciCompl :
    UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl := by
  intro hb E _ _ _ a ha m U hU hsU
  obtain ⟨hs, c, hc⟩ := hb E a m
  obtain ⟨χ, hχ⟩ := exists_twist (E := E) ha c
  obtain ⟨D, d1, d2, d3, d4⟩ := compl_zero (C := (CI a m).map (mulChi a χ).toLinearMap)
    (by rintro _ ⟨φ, h, rfl⟩; exact (mem_CI.1 h).1.mulChi χ)
    (by
      rintro _ ⟨φ, h, rfl⟩
      rw [LinearEquiv.coe_coe, lie_mulChi, hc φ h, hχ, neg_smul, add_neg_cancel, map_zero])
    (stable_twist χ hs) (Submodule.map_mono hU) (stable_twist χ hsU)
  refine ⟨D.map (mulChi a χ⁻¹).toLinearMap, (Submodule.map_mono d1).trans (map_twist_inv χ _).le,
    stable_twist _ d2, ?_, ?_⟩
  · rw [← map_twist_inv χ U, ← Submodule.map_inf _ (mulChi a χ⁻¹).injective, d3, Submodule.map_bot]
  · rw [← map_twist_inv χ U, ← Submodule.map_sup, d4, map_twist_inv]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem slice_cap (h : UpperTheory.V.Cj.S.Slice) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ}
    (e : Fin a ↪ Fin n) (g : GA E n) :
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t u ψ, cap t u (f ψ) = f (capB e t u ψ) := by
  obtain ⟨f, hf, hE⟩ := h E a n e g
  exact ⟨f, hf, fun t u ψ => (UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ (hE t) _ ψ).symm⟩

theorem UpperTheory.V.Cj.S.capRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.CapBlock → UpperTheory.V.Cj.S.CapRel := by
  intro hS hB E _ _ _ r s ψ hψ t u
  refine ⟨res (capB (e1 r s) t (u - (s : ℂ) / 2) ψ).1, fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e1 r s) (emb (e2 r s) y)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = fun x => res φ.1 x y := fun φ => funext fun x => by
      rw [hf, res, blk, UpperTheory.V.Af.Fin.emb_comm]
    exact ⟨f ψ, key ψ, by rw [hc, key]⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e2 r s) (emb (e1 r s) x)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = res φ.1 x := fun φ => funext fun y => hf φ y
    refine ⟨f _, key _, ?_⟩
    rw [hc, key]
    exact funext fun y => (hB E r s ψ hψ t u x y).symm
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

variable {R S : Type} [CommRing R] [CommRing S]

private theorem corner_sub_one {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, corner_sub_one]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

private theorem corner_blk {r t : ℕ} (s : R →ₙ+* S) (g : GL (Fin r) R) (h : GL (Fin t) R) :
    cornerGL (r + t) s (blk g h) = blk (cornerGL r s g) (cornerGL t s h) := by
  rw [blk, blk, map_mul, corner_emb, corner_emb]

private theorem corner_unip {n r : ℕ} (s : R →ₙ+* S) (X : UPos n r → R) :
    cornerGL n s (unipGL X) = unipGL fun p => s (X p) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one]
  change s ((1 + blockEntry X - 1) i j) = (1 + blockEntry (fun p => s (X p)) - 1) i j
  rw [add_sub_cancel_left, add_sub_cancel_left, blockEntry_apply, blockEntry_apply]
  split_ifs
  · rfl
  · exact map_zero s

private theorem emb_mem {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {k : GL (Fin a) L}
    (hk : k ∈ GLint (Fin a) O) : emb e k ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hk
  exact ⟨emb e k, emb_map e O.subtype k⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding :
    UpperTheory.V.Cj.S.HeckeLocalBlock := by
  intro E _ _ w r s
  refine ⟨fun b₁ b₂ => ?_, fun X => ?_, fun x y Y => ?_, fun k₁ h₁ k₂ h₂ => ?_⟩
  · simp only [finGL, locGL, corner_blk]
  · simp only [finGL, locGL, corner_unip]
    exact ⟨_, rfl⟩
  · obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (Ad E) r s x y
    exact ⟨_, hc (Ad E) (RingHom.id _) Y⟩
  · exact mul_mem (emb_mem _ _ h₁) (emb_mem _ _ h₂)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctCap :
    UpperTheory.V.Cj.S.CtCap := by
  intro E _ _ _ n r φ hφ
  have ha := (UpperTheory.V.Cm.isAutForm_iff φ).1 hφ
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r
  let φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n := ⟨φ.1, ha⟩
  refine ⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩
  · rw [UpperTheory.V.Cm.coe_smEq_symm, hf]
    exact UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g
  · obtain ⟨p, -, q, -, e⟩ := UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)
    have h := hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' +
      Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')
    rw [map_add (f := _), map_smul, hfu, hfu] at h
    rw [e]
    exact h
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

open UpperTheory.V UpperTheory.V.Af.Fin in
private theorem lie_eq_lam {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (i j : Fin a) (x : Cinf E)
    (φ : Sm E a) :
    Cm.smEq E a (lie E a (toL (Matrix.single i j x)) φ) =
      lam E a (Matrix.single i j (Cm.mixEq E x)) (Cm.smEq E a φ) := by
  rw [← Cm.uAction_ι_smEq, lam_apply]
  congr 3
  refine Subtype.ext (Matrix.ext fun k l => ?_)
  change Cm.mixEq E (Matrix.single i j x k l) = Matrix.single i j (Cm.mixEq E x) k l
  simp only [Matrix.single_apply, apply_ite (Cm.mixEq E), map_zero]

open UpperTheory.V UpperTheory.V.Af.Fin in
theorem UpperTheory.V.Cj.S.slice :
    UpperTheory.V.Cj.S.Slice := by
  intro E _ _ _ a n e g
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E a n e g
  have key : ∀ i j x ψ, (Cm.smEq E a).symm (f (Cm.smEq E n (lie E n (toL (Matrix.single (e i) (e j) x)) ψ))) =
      lie E a (toL (Matrix.single i j x)) ((Cm.smEq E a).symm (f (Cm.smEq E n ψ))) := fun i j x ψ => by
    rw [LinearEquiv.symm_apply_eq, lie_eq_lam, lie_eq_lam, LinearEquiv.apply_symm_apply, ← matrixExtendByZero_single, hl]
  refine ⟨(Cm.smEq E a).symm.toLinearMap ∘ₗ f ∘ₗ (Cm.smEq E n).toLinearMap, fun ψ x => hf _ x, fun t i j ψ => ?_⟩
  rw [← Cm.uC_genC, ← Cm.uC_genC]
  simp only [Cm.genC, AlgRepEndIrreducible.eL, map_smul, map_sub, Cm.uC_ιC, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
end
