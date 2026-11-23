module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle249
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaLoc

open GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem isLinAt_comp {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ) (hP : ∀ Φ, P (ι Φ))
    (h : IsLinAt ω₁ s μ η ι) : IsLinAt ω₂ s μ η (T ∘ₗ ι) := by
  obtain ⟨c, hc, hc', hι⟩ := h
  refine ⟨c, hc, hc', fun h g hh hg Φ Φ' hΦ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← hT _ _ (hP Φ), hι h g hh hg Φ Φ' hΦ, map_smul]

end GlobalTheory.ThetaLoc

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
namespace GlobalTheory.ThetaLocInv

theorem thetaRead_inv : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (_root_.GlobalTheory.SmGL.twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  intro D M i rep X μ η Θ s μw ηw ι c hι Wl Vl _ _ _ _ πl σl T' hT' T'' hT'' g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) = h := by rw [exh, back]
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg, back]
  have hω := hι xh xg hxh hxg Φ Φ' (by rw [eh, eg]; exact hΦ')
  have key := Θ.inv xh xg (ι Φ) (T' a) (T' (πl h a)) (T'' c') (T'' (σl g c'))
    (by rw [← hT' xh hxh a, eh]) (by rw [← hT'' xg hxg c', eg])
  rw [hω, eh] at key
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  simpa using key

end GlobalTheory.ThetaLocInv
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem apart_of_apart_not_apart {w w₀ u : HeightOneSpectrum (𝓞 E)} (hw : Apart w w₀) (hu : ¬ Apart u w₀) : Apart u w := by
  unfold Apart at *
  intro h
  exact hw (h.symm.trans (not_not.1 hu))

theorem mem_levelOf_iff_of_locU {w₀ w : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)}
    (hle : ∀ w, H w ≤ locU a w) (hfib : ∀ w u, ¬ Apart w u → H w = H u) (hw : Apart w w₀) {x : UA E a}
    (hx : x ∈ locU a w) : x ∈ levelOf a w₀ H ↔ x ∈ H w := by
  have hx' := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := (mem_levelOf.1 h).2.2 w hw
    rw [← eq_of_cLoc_eq (hle w hy) hx e]
    exact hy
  · intro h
    refine mem_levelOf.2 ⟨hx'.1, fun u hu => hx'.2 u (apart_of_apart_not_apart hw hu), fun w' hw' => ?_⟩
    by_cases hw'w : Apart w' w
    · exact ⟨1, one_mem _, by rw [map_one, hx'.2 w' hw'w]⟩
    · exact ⟨x, by rw [hfib w' w hw'w]; exact h, rfl⟩

theorem map_eq_image {w : HeightOneSpectrum (𝓞 E)} {L : Subgroup (UA E a)} (hL : L ≤ locU a w)
    (e : locU a w ≃ₜ* GL (Fin a) (w.adicCompletion E)) (he : ∀ x : locU a w, e x = cLoc w (x : UA E a)) :
    ((L.map (cLoc w) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) =
      e '' ((L.subgroupOf (locU a w) : Subgroup (locU a w)) : Set (locU a w)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hL hx⟩, Subgroup.mem_subgroupOf.2 hx, he _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.1 hy, (he y).symm⟩

theorem injective_of_compAlong {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (hirr : σ.IsIrreducible) (f : W →ₗ[ℂ] (UA E a → ℂ)) (hf0 : f ≠ 0)
    (hf : ∀ (x : locU a w) v, f (σ (((cLoc w).comp (locU a w).subtype) x) v) = RU E a x (f v)) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  rw [← LinearMap.ker_eq_bot]
  refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr).2 _ (fun g u hu => ?_)).resolve_right fun h => hf0 ?_
  · rw [LinearMap.mem_ker] at hu ⊢
    have := hf (e.symm g) u
    have hg : ((cLoc w).comp (locU a w).subtype) (e.symm g) = g := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]
    rw [hg] at this
    rw [this, hu, map_zero]
  · refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem fix_of_fixed {U : Submodule ℂ (UA E a → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (hJ : GlobalTheory.PRep.fixed σ.ρ J ≠ ⊥) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ J → RU E a x φ = φ := by
  obtain ⟨hirr, f, hf0, hfU, hf⟩ := hc
  have hinj := injective_of_compAlong hw hirr f hf0 hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hJ
  refine ⟨f v, hfU v, fun h => hv0 (hinj (by rw [h, map_zero])), fun x hx hxJ => ?_⟩
  have := hf ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GlobalTheory.LGrp.mem_fixed.1 hv _ hxJ] at this
  exact this.symm

theorem fixed_ne_bot_of_fix {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {L : Subgroup (UA E a)} (hL : L ≤ locU a w) {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0)
    (hφ : ∀ x ∈ L, RU E a x φ = φ) : GlobalTheory.PRep.fixed σ.ρ (L.map (cLoc w)) ≠ ⊥ := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hp : (cLoc w).comp (locU a w).subtype = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  have hirr : Representation.IsIrreducible (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) := by
    rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  have hsup := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hc φ hφU
  let ι := {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}
  have hf' : ∀ (i : ι) (g : locU a w) (u : σ.V), i.1 ((σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) g u) =
      ((RU E a).comp (locU a w).subtype) g (i.1 u) := fun i g u => i.2.2 g u
  have hK : ∀ k ∈ {x : locU a w | (x : UA E a) ∈ L}, ((RU E a).comp (locU a w).subtype) k φ = (1 : ℂ) • φ :=
    fun k hk => by rw [one_smul]; exact hφ k.1 hk
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.SplitEigen.exists_eigen_of_mem_iSup (ι := ι) ((RU E a).comp (locU a w).subtype)
    (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) hirr (fun i => i.1) hf'
    {x : locU a w | (x : UA E a) ∈ L} (fun _ => 1) φ hφ0 hK hsup
  refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 ?_, hv0⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hv ⟨x, hL hx⟩ hx
  rw [one_smul] at this
  exact this

theorem KGL_le_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    GlobalTheory.LFun.KGL w (n := a) ≤ (intU a w).map (cLoc w) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  intro g hg
  have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
  exact ⟨(e.symm g).1, mem_intU_of (e.symm g).2 (by rw [h1]; exact hg), h1⟩

end GlobalTheory.Cong.AdaptLev

end
end

section

noncomputable section

namespace GlobalTheory.HtCardProof

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.L2 Module

section Local

variable {l m : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {K LL : FinExt l}
  (r : ↥(GK K) →* GL (Fin m) ↥LL.1)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
include T in
theorem exists_count (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) [FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) (_root_.Formalism.L2.vrep r) τ)] :
    ∃ M : Multiset ℤ, Multiset.card M = finrank ↥LL.1 ↥(DdRE (P.PD K) (_root_.Formalism.L2.vrep r) τ) ∧
      ∀ a, (M.count a : ℤ) = multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a := by
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (_root_.Formalism.L2.vrep r) τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (_root_.Formalism.L2.vrep r) τ
  have anti := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (_root_.Formalism.L2.vrep r) τ
  haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ a ≤ DdRE (P.PD K) (_root_.Formalism.L2.vrep r) τ)
  have nn : ∀ a, 0 ≤ multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a := fun a => by
    have := Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))
    unfold multV
    omega
  obtain ⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi := ⟨min lo hi, min_le_left _ _, min_le_right _ _⟩
  have zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a = 0 := fun a ha => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    have e : FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ a = FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ (a + 1) := by
      rcases ha with ha | ha
      · exact (hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm
      · exact (hhi a ha).trans (hhi (a + 1) (by omega)).symm
    unfold multV
    rw [e, sub_self]
  refine ⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a).toNat a, ?_, fun b => ?_⟩
  · rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    have hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a =
        (finrank ↥LL.1 ↥(FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ hi) :=
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2
    have e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (_root_.Formalism.L2.vrep r) τ) := by
      rw [hlo lo₁ hl1]
    have e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (_root_.Formalism.L2.vrep r) τ hi) = 0 := Submodule.finrank_eq_zero.2 (hhi hi le_rfl)
    rw [e1, e2] at hs
    have : ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (_root_.Formalism.L2.vrep r) τ a).toNat : ℕ) : ℤ) =
        (finrank ↥LL.1 ↥(DdRE (P.PD K) (_root_.Formalism.L2.vrep r) τ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]
      simp
    exact_mod_cast this
  · rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    by_cases hb : b ∈ Finset.Ico lo₁ hi
    · rw [if_pos hb, Int.toNat_of_nonneg (nn b)]
    · rw [if_neg hb, zero b hb]
      rfl

end Local

theorem htCard : GlobalTheory.HeightCounting.HtCard := GlobalTheory.PhtCompare.phtCmp

end GlobalTheory.HtCardProof

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host UpperTheory.V.Published

theorem _root_.GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.QuadNormRam.not_unrAt_of_ramified | exact GlobalTheory.QuadNormRam.not_unrAt_of_ramified | (intros; apply GlobalTheory.QuadNormRam.not_unrAt_of_ramified <;> assumption)
end
