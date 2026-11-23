module

public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EigBoxL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlaceBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.Desc.V0

section Abs

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem map_mem_isotypic_invariants {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W →ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x))
    {F : Fin m → W} (hF : F ∈ inv1 K₁ τ₀ ρ) : (fun i => e (F i)) ∈ inv1 K₁ τ₀ ρ' := by
  refine ⟨fun k i => ?_, fun k _ i => ?_⟩
  · have h := congrArg e (hF.1 k i)

    simp only [map_sum, map_smul, MonoidHom.comp_apply, MonoidHom.coe_fst, h₁ k.1 k.2] at h
    simpa only [MonoidHom.comp_apply, MonoidHom.coe_fst] using h
  · simp

private theorem rank_isotypic_invariants_eq {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W ≃ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x)) :
    Module.rank ℂ (inv1 K₁ τ₀ ρ) = Module.rank ℂ (inv1 K₁ τ₀ ρ') := by
  have s₁ : ∀ k ∈ K₁, ∀ x, e.symm (ρ' k x) = ρ k (e.symm x) := fun k hk x =>
    e.injective (by rw [h₁ k hk, e.apply_symm_apply, e.apply_symm_apply])
  let E : (Fin m → W) ≃ₗ[ℂ] (Fin m → W') := LinearEquiv.piCongrRight fun _ => e
  have hE : (inv1 K₁ τ₀ ρ).map (E : (Fin m → W) →ₗ[ℂ] (Fin m → W')) = inv1 K₁ τ₀ ρ' := by
    refine le_antisymm ?_ fun F hF => ?_
    · rintro _ ⟨F, hF, rfl⟩
      exact map_mem_isotypic_invariants K₁ τ₀ ρ ρ' e.toLinearMap h₁ hF
    · refine ⟨fun i => e.symm (F i), map_mem_isotypic_invariants K₁ τ₀ ρ' ρ e.symm.toLinearMap s₁ hF, ?_⟩
      funext i
      exact e.apply_symm_apply (F i)
  exact (LinearEquiv.ofSubmodules E _ _ hE).rank_eq

end Abs

section Fam

variable {I : Type} {Gi Wi Wi' : I → Type} [∀ i, Group (Gi i)]
  [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] [∀ i, AddCommGroup (Wi' i)] [∀ i, Module ℂ (Wi' i)]

private theorem congr_piRep (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (τ' : ∀ i, Representation ℂ (Gi i) (Wi' i))
    (a : ∀ i, Wi i ≃ₗ[ℂ] Wi' i) (g : ∀ i, Gi i) (h : ∀ i x, a i (τ i (g i) x) = τ' i (g i) (a i x))
    (x : ⨂[ℂ] i, Wi i) : PiTensorProduct.congr a (piRep τ g x) = piRep τ' g (PiTensorProduct.congr a x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [piRep, PiTensorProduct.congr, map_smul, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, LinearEquiv.ofLinear_apply, PiTensorProduct.map_tprod]
    exact congrArg (fun t => r • PiTensorProduct.tprod ℂ t) (funext fun i => h i (f i))
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Fam

theorem invEq1 : InvEq1 := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V _ c ι m τ₀ σ σ' C C' hu
  refine rank_isotypic_invariants_eq (KT n (wt s)) _ _ _ (PiTensorProduct.congr fun u => (hu u).some.toLinearEquiv) ?_
  intro g hg x
  refine congr_piRep _ _ _ g (fun u y => ?_) x
  exact LinearMap.congr_fun ((hu u).some.isIntertwining' ⟨g u, hg u (Set.mem_univ u)⟩) y

end UpperTheory.V.Z.Desc.V0
end
end

section

open UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.eigBoxE :
    EigBoxE := by
  intro L _ _ n V _ S G H W W' X _ _ _ _ _ _ _ _ ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
  exact eigBoxL ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

private theorem Kc_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g⁻¹ * x * g ∈ Kc k n 1 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a⁻¹ * b * a, ?_, by simp only [map_mul, map_inv]⟩
  have hb' := MonoidHom.mem_ker.1 hb
  exact MonoidHom.mem_ker.2 (by simp only [map_mul, map_inv, hb', mul_one, inv_mul_cancel])

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

variable (s : HidaSetting l L Ω)

private theorem sec_one (w w' : Plc L) (h : GLw n w) (hw : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n w' (sec n s w h : Ga l L n) = 1 := by
  unfold CaseU.sec
  split_ifs with hb
  · have hm := ((MulEquiv.ofBijective _ hb).symm h).2
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm w') hw)
  · exact map_one _

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dite_eq_left h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_GaS {x : Ga l L n} (hx : x ∈ GaS n s) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0) : cmp n w x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

end UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

open UpperTheory.V.Z.Desc.V0.InertiaSectionNorm in
theorem UpperTheory.V.Z.Desc.V0.normS :
    NormS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV Q c m τ₀
  obtain ⟨hb, hcomm, hdesc⟩ := secSp l L Ω s n hn V hV
  have spec := secS_spec (n := n) s hb
  have hq : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)⟩
  have hlev : ∀ K, (hset Q τ₀).lev K = (hset Q τ₀).UQ := fun K => by
    haveI : IsEmpty (hset Q τ₀).Q := hq
    unfold HSet.lev
    rw [iSup_of_empty]
    exact sup_bot_eq _
  have h0 : ∀ (g : GLw n (s.w s.v0)) (t : s.St), cmp n (s.w t) (sec0 n s g) = 1 := fun g t =>
    congrFun (congrArg Prod.fst (spec (1, g)).1) t
  have hτ : ∀ (u u' : Ub n s), (∀ t : s.St, cmp n (s.w t) (u : Ga l L n) = cmp n (s.w t) (u' : Ga l L n)) →
      (hset Q τ₀).τ u = (hset Q τ₀).τ u' := fun u u' h =>
    congrArg τ₀ (Subtype.ext (funext h))
  have huq : ∀ g : GLw n (s.w s.v0), g ∈ KO _ (Fin n) → ∀ u ∈ UQ n Q, ∃ u' ∈ UQ n Q,
      (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g ∧ (hset Q τ₀).τ u' = (hset Q τ₀).τ u := by
    intro g hg u hu
    obtain ⟨k, hk, p, hp, e⟩ := (hdesc Q (u : Ga l L n)).1 ⟨u, hu, rfl⟩
    have hp' : ((p.1, g⁻¹ * p.2 * g) : GS n s) ∈ (KT n (wt s)).prod (Kc _ n 1) :=
      Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hp).1, Kc_conj hg (Subgroup.mem_prod.1 hp).2⟩
    have hconj : ((p.1, g⁻¹ * p.2 * g) : GS n s) = ((1, g) : GS n s)⁻¹ * p * (1, g) :=
      Prod.ext (by simp) (by simp)
    have e' : (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g = secS n s (p.1, g⁻¹ * p.2 * g) * k := by
      have hc : k * sec0 n s g = sec0 n s g * k := (hcomm (1, g) k hk).eq.symm
      rw [hconj, map_mul, map_mul, map_inv, e]
      change (sec0 n s g)⁻¹ * (secS n s p * k) * sec0 n s g = (sec0 n s g)⁻¹ * secS n s p * sec0 n s g * k
      simp only [mul_assoc, hc]
    obtain ⟨u', hu', e''⟩ := (hdesc Q _).2 ⟨k, hk, _, hp', e'⟩
    have e3 : (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g := e''
    refine ⟨u', hu', e3, hτ _ _ fun t => ?_⟩
    rw [e3, map_mul, map_mul, map_inv, h0, inv_one, one_mul, mul_one]
  refine ⟨fun g hg => ⟨fun K u hu => ?_, fun u hu => huq g hg u hu, fun w hw h => ?_⟩, fun g hg => ?_⟩
  · rw [hlev] at hu
    obtain ⟨u', hu', h⟩ := huq g hg u hu
    exact ⟨u', by rw [hlev]; exact hu', h⟩
  · refine comm_of fun w' => ?_
    by_cases hu : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · refine Or.inl (mem_GaS s (spec (1, g)).2 (notS s ?_))
      rw [hu, ← hV]
      exact hw.1
    · exact Or.inr (sec_one s w w' h hu)
  · obtain ⟨u, hu, e⟩ := (hdesc Q (sec0 n s g)).2 ⟨1, one_mem _, (1, g),
      Subgroup.mem_prod.2 ⟨one_mem _, hg⟩, (mul_one _).symm⟩
    have e3 : (u : Ga l L n) = sec0 n s g := e
    refine ⟨u, hu, e3, ?_⟩
    exact (hτ u 1 fun t => by rw [e3, h0]; exact (map_one _).symm).trans (map_one (hset Q τ₀).τ)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open UpperTheory.V.Z.Desc.V0

section SlopeTestRemainingChoices

open Formalism.MainNotions.N

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}

private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩

private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩

private theorem irr_of_comp (φ : Γ' →* Γ) {r : Γ →* GL (Fin n) k} (h : Af.IsIrr (r.comp φ)) : Af.IsIrr r :=
  ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩

private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]

private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm

private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩

private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl

private theorem datEnd {O A B M : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] (j : A →ₐ[O] B) (φ : B →+* Module.End A M)
    (hj : ∀ a, φ (j a) = algebraMap A _ a) (J : Ideal B) (hJ : ∀ b, b ∈ J ↔ φ b = 0) (hr : J.IsRadical) :
    ∃ _ : Module B M, (∀ (b : B) (m : M), b • m = φ b m) ∧ UpperTheory.V.J.Dat j J M := by
  letI : Module B M := Module.compHom M φ
  have h0 : ∀ (b : B) (m : M), b • m = φ b m := fun _ _ => rfl
  have h1 : Module.annihilator B M = J := by
    ext b
    rw [Module.mem_annihilator, hJ, LinearMap.ext_iff]
    rfl
  refine ⟨inferInstance, h0, fun a m => ?_, inferInstance, inferInstance, hr, fun p _ => by rw [h1], fun c hc a ha => ?_⟩
  · rw [h0, hj]
    rfl
  · rw [hJ] at ha ⊢
    rw [map_mul, hj] at ha
    ext m
    have h2 : c • φ a m = 0 := LinearMap.congr_fun ha m
    refine (Module.Free.chooseBasis A M).repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun v => (Module.Free.chooseBasis A M).repr v i) h2
    simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h3
    rw [(mul_eq_zero.1 h3).resolve_left hc, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]

private theorem datHecke {O A B N κ : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup N] [Module A N] (Y : Submodule A N) (op : κ → Module.End A N) [Fact (CommOn Y op)] [Module.Free A Y]
    [Module.Finite A Y] (j : A →ₐ[O] B) (f : B →+* heckeAlg Y op) (hj : ∀ a, f (j a) = algebraMap A _ a)
    (hr : (RingHom.ker f).IsRadical) :
    ∃ _ : Module B Y, (∀ (b : B) (m : Y), b • m = (f b).1 m) ∧ UpperTheory.V.J.Dat j (RingHom.ker f) Y :=
  datEnd j ((heckeAlg Y op).val.toRingHom.comp f) (fun a => congrArg Subtype.val (hj a)) _
    (fun _ => RingHom.mem_ker.trans Subtype.ext_iff) hr

private theorem datTop {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (j : A →ₐ[O] B) :
    UpperTheory.V.J.Dat j ⊤ PUnit :=
  ⟨fun _ _ => rfl, Module.Free.of_subsingleton A PUnit, ⟨⟨∅, Subsingleton.elim _ _⟩⟩, le_top, fun p _ => by
    rw [Module.annihilator_eq_top_iff.2 ⟨fun _ _ => rfl⟩], fun _ _ _ _ => Submodule.mem_top⟩

end SlopeTestRemainingChoices

private theorem unitN {l : ℕ} [Fact l.Prime] {c : Coef l} {A : Type} [CommRing A] [Algebra c.O A] {N : ℕ} (h : ¬ l ∣ N) :
    IsUnit (N : A) := by
  have h0 : IsUnit (N : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)
  have h1 := (h0.map (algebraMap ℤ_[l] c.O)).map (algebraMap c.O A)
  simpa using h1

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
set_option maxHeartbeats 2000000 in
private theorem absDimE (hMu : MuZ) (hME : MuZE) (hSp : Spec2) (hU : UnitEv) (hP : PartRep) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) {A : Type} [CommRing A]
    [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ) (ι : Qbar l ≃+* ℂ)
    (a₀ : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a₀ K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a₀ K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a₀ K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a₀ K)ˣ} (out : H.Out θ a₀ K P I (D₀.map f.toRingHom) ψ)
    [Module R (H.MK θ a₀ K)] (hs : ∀ (b : A) (m : H.MK θ a₀ K), b • m = j b • m)
    (hact : ∀ (b : R) (m : H.MK θ a₀ K), b • m = (f b).1 m)
    {G : Type} [Group G] {K₀ K₁ : Subgroup G} (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ) (hNK : NormK H K₀ K₁ β) (hE : IsE K₀ K₁ a N)
    (hu : IsUnit (N : A)) (e : Module.End A (H.MK θ a₀ K)) (hep : IsProj H θ β a N e)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam)
    (hρ : ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ →
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) → Af.IsIrr ρ) :
    IsDimE H θ ι lam K β a N (muE j (H.MK θ a₀ K) hs e x) := by
  obtain ⟨-, hfi, hfr⟩ := (hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hss, -, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  have hi := hρ ρ hc hss ((map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD)
  obtain ⟨d, ξ, c0, sp, hsp, htr⟩ := hSp L Ω l n c H hA A θ hθ ι (x.comp j) lam har
  obtain ⟨hne, -⟩ := hMu L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ R j f hf hs hact y e1
  have hmu := hME L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp htr K a₀ R j f hf hs hact y e1 G K₀ K₁ β a N hNK hE hu e hep
  have e2 : y.comp f = x := AlgHom.ext hy
  rw [e2] at hmu
  refine ⟨x.comp j, d, ξ, c0, sp, _, hsp, fun v i => ?_, hne, fun Y hY => ?_, hmu⟩
  · rw [RingEquiv.symm_apply_apply]
    exact hU L Ω l n c H hA A θ hθ ι K a₀ I _ ψ out.univ y v i
  · obtain ⟨g, hg⟩ := hP L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ y e1 I _ ψ out.univ ρ hc hi hD Y hY
    exact irr_iso ⟨g, hg⟩ hi


private theorem irrOf {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {c : Coef l}
    {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r} (x : B.Pt) (hx : UpperTheory.V.J.IrrPt x)
    (ρ₀ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hs : Formalism.MainNotions.N.IsSSRep ρ₀)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = W.GDet.ofRep (W.mat ρ₀)) : Af.IsIrr ρ₀ := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨ρ, -, hρ, hi⟩ := hx
  have hr : x.IsRep (ρ₀.comp V.pr) := by
    replace hD : x.D = W.GDet.ofRep (W.mat ρ₀) := hD
    change x.D.comap V.pr = _
    rw [hD]
    exact (AlgebraTools.Det.repApi (W.mat ρ₀)).2.2.2.2.2.2.1 V.pr
  have e : Af.RepIso (ρ₀.comp V.pr) ρ := iso_of_det (ss_of_irr hi) (ss_comp hpr hs) (hρ.symm.trans hr)
  exact irr_of_comp V.pr (irr_iso e.symm' hi)

end
