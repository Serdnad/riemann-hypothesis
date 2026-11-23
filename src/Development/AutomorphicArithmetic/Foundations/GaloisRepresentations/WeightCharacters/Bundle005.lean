module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem proj_of_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G → V →ₗ[ℂ] V)
    (A : Submodule ℂ V) (S : Set (Submodule ℂ V))
    (hSA : ∀ U ∈ S, U ≤ A) (hSs : ∀ U ∈ S, ∀ x, ∀ v ∈ U, ρ x v ∈ U)
    (hSi : ∀ U ∈ S, ∀ N ≤ U, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → N = ⊥ ∨ N = U)
    (hAS : A ≤ sSup S) (ψ : V) (hψA : ψ ∈ A) (hψ : ψ ≠ 0) :
    ∃ U ∈ S, ∃ pr : V →ₗ[ℂ] V, pr ψ ≠ 0 ∧ ∀ f ∈ A, pr f ∈ U ∧ ∀ x, pr (ρ x f) = ρ x (pr f) := by
  classical
  let P : Set (Submodule ℂ V) := {C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}
  have hbot : (⊥ : Submodule ℂ V) ∈ P :=
    ⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _,
      fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨C, -, hC⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hz ((hcP hz).2.1 x v hvz)
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcP hz).2.2 hvz) ⊥ hbot
  obtain ⟨hCA, hCs, hψC⟩ := hC.prop
  have hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N := by
    intro N hNA hNs hNC
    by_contra hn
    have hm : C ⊔ N ∈ P := ⟨sup_le hCA hNA, fun x v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩
    exact hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))
  obtain ⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by
    by_contra hn
    push Not at hn
    exact hψC (sSup_le hn (hAS hψA))
  have hUs := hSs U hUS
  have hdisj : C ⊓ U = ⊥ := by
    rcases hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_right.1 h) hUC
  have hψU := hsup U (hSA U hUS) hUs hUC
  have hAle : A ≤ C ⊔ U := by
    refine hAS.trans (sSup_le fun Y hY => ?_)
    by_cases hYC : Y ≤ C
    · exact hYC.trans le_sup_left
    have hYs := hSs Y hY
    rcases hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv.1
        rw [← e, map_add (f := _)]
        exact Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h
    · exfalso
      obtain ⟨c, hc, y, hy, e⟩ := Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)
      have hyCU : y ∈ C ⊔ U := by
        have : y = ψ - c := by rw [← e]; abel
        rw [this]
        exact sub_mem hψU (Submodule.mem_sup_left hc)
      have hy0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))
      rw [hy0, add_zero] at e
      exact hψC (e ▸ hc)
    · exact inf_eq_right.1 h
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C ⊔ U)
  have hc : IsCompl U (C ⊔ D) := by
    refine ⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩
    · obtain ⟨c, hc, d, hd, e⟩ := Submodule.mem_sup.1 hu'
      have hdCU : d ∈ C ⊔ U := by
        have : d = u - c := by rw [← e]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)
      have hd0 : d = 0 := Submodule.disjoint_def.1 hD.disjoint d hdCU hd
      rw [hd0, add_zero] at e
      have : u ∈ C ⊓ U := ⟨e ▸ hc, hu⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot ℂ).1 this
    · rw [codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]
      exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)
  let pr : V →ₗ[ℂ] V := U.subtype ∘ₗ Submodule.projectionOnto U (C ⊔ D) hc
  have hprU : ∀ u ∈ U, pr u = u := fun u hu =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hc ⟨u, hu⟩)
  have hprC : ∀ c ∈ C, pr c = 0 := fun c hc' => by
    have h0 : Submodule.projectionOnto U (C ⊔ D) hc c = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hc (Submodule.mem_sup_left hc')
    simp [pr, h0]
  have hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u := fun c hc' u hu => by
    rw [map_add (f := _), hprC c hc', hprU u hu, zero_add]
  refine ⟨U, hUS, pr, ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc', u, hu, e⟩ := Submodule.mem_sup.1 (hAle hψA)
    rw [← e, hform c hc' u hu]
    intro h0
    rw [h0, add_zero] at e
    exact hψC (e ▸ hc')
  · obtain ⟨c, hc', u, hu, rfl⟩ := Submodule.mem_sup.1 (hAle hf)
    refine ⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩
    rw [hform c hc' u hu, map_add (f := _), hform _ (hCs x c hc') _ (hUs x u hu)]

theorem embProj_holds : EmbProj := by
  intro E _ _ _ a τ U hU κ hκ u hu hu0
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E a τ
  let π : AutSub E a := ⟨U, hU⟩
  let s : Matrix.unitaryGroup (Fin a) ℂ →* UA E a := (embU a τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cEmb τ (s y) = unitaryIncl a y := fun y => by
    have h3 := he (e.symm y)
    rw [e.apply_symm_apply] at h3
    exact h3.symm
  have hirr := isIrreducible_smallRep_unitary a κ
  obtain ⟨-, hsimple⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr
  let S : Set (Submodule ℂ (UA E a → ℂ)) := {V | ∃ F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ), Function.Injective F ∧ (∀ w, F w ∈ U) ∧
    (∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w)) ∧ V = LinearMap.range F}
  have hc : ∀ g, ∃ y, ∀ y', Commute ((s y)⁻¹ * g) (s y') := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU a τ) : UA E a)⁻¹ * g) ((e.symm y : embU a τ) : UA E a)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨f, hf⟩ : ∃ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), f ≠ 0 := by
    obtain ⟨-, F, hF0, hFm, hFi⟩ := hκ
    refine ⟨⟨F.codRestrict U hFm, fun y => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ a κ (unitaryIncl a y) v) = RU E a (s y) (F v)
      rw [← hs y]
      exact hFi (e.symm y) v
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ π.rep s _ _ π.isIrreducible_rep hirr hirr hc f hf).1
  have hUS : U ≤ sSup S := by
    intro φ hφ
    have h1 : (⟨φ, hφ⟩ : U) ∈ (⨆ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), LinearMap.range f.toLinearMap) :=
      htop ▸ Submodule.mem_top
    refine (iSup_le (a := (sSup S).comap U.subtype) fun f' => ?_) h1
    rintro _ ⟨w, rfl⟩
    let F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ) := U.subtype ∘ₗ f'.toLinearMap
    have hF : ∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w) := fun y w =>
      congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f' y w)
    show F w ∈ sSup S
    rcases hsimple (LinearMap.ker F) (fun y x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      exact (hF y x).trans (by rw [hx, map_zero])) with h | h
    · exact le_sSup (show LinearMap.range F ∈ S from ⟨F, LinearMap.ker_eq_bot.1 h, fun w => (f' w).2, hF, rfl⟩) ⟨w, rfl⟩
    · have : w ∈ LinearMap.ker F := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker.1 this]
      exact zero_mem _
  obtain ⟨_, ⟨F, hinj, hFU, hF, rfl⟩, pr, h1, h2⟩ := proj_of_sum (fun y => RU E a (s y)) U S
    (by rintro _ ⟨F, -, hFU, -, rfl⟩ _ ⟨w, rfl⟩; exact hFU w)
    (by rintro _ ⟨F, -, -, hF, rfl⟩ y _ ⟨w, rfl⟩; exact ⟨_, hF y w⟩)
    (by
      rintro _ ⟨F, -, -, hF, rfl⟩ N hN hNs
      rcases hsimple (N.comap F) (fun y x hx => by
        show F _ ∈ N
        exact (hF y x).symm ▸ hNs y _ hx) with h | h
      · left
        rw [eq_bot_iff]
        intro φ hφ
        obtain ⟨w, rfl⟩ := hN hφ
        have : w ∈ N.comap F := hφ
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]
        exact zero_mem _
      · right
        refine le_antisymm hN ?_
        rintro _ ⟨w, rfl⟩
        exact (h ▸ Submodule.mem_top : w ∈ N.comap F))
    hUS u hu hu0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.2 hinj)
  have hGF : ∀ w, G (F w) = w := fun w => LinearMap.congr_fun hG w
  refine ⟨G ∘ₗ pr, fun h0 => h1 ?_, fun x hx y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (h2 u hu).1
    rw [LinearMap.comp_apply, ← hw, hGF] at h0
    rw [← hw, h0, map_zero]
  · obtain ⟨w, hw⟩ := (h2 y hy).1
    have hx' : s (e ⟨x, hx⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    have h3 := (h2 y hy).2 (e ⟨x, hx⟩)
    rw [← hw, ← hF, ← hs, hx'] at h3
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h3, ← hw, hGF, hGF]

end UpperTheory.Gal.Wt

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famSum_of : ExpBasic → EvLem → TorFacts → QR → WtBd → EmbProj → FamSum := by
  intro hEB hEv hTor hQR hBd hEP E _ _ _ a τ W K ν d B hB U hU hBU hne κ hκ k
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ
  have hx : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = unitaryIncl a u := fun u => by
    have h := he (e.symm u)
    rw [e.apply_symm_apply] at h
    exact ⟨⟨(e.symm u).1, (Subgroup.mem_inf.1 (e.symm u).2).1⟩, (e.symm u).2, h.symm⟩
  choose x hx using fun z : Circle => (show ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = tor a k z by
    obtain ⟨u, hu⟩ := (hTor a k z).2.1
    rw [← hu]
    exact hx u)
  rename_i hxu
  have hc : IsCirc τ k x := hx
  obtain ⟨S, hS, hBS⟩ := hB.fin
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ L : (UA E a → ℂ) →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T := fun T Φ h1 h2 L =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (L ∘ₗ S.subtype)
  obtain ⟨y₁, y₂, v, hv⟩ := hne
  constructor
  · obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU y₁ y₂ v) hv
    refine (hBd a k κ _).1 {w | ∃ y₁ y₂ v, w = p (B y₁ y₂ v)} ⟨_, ⟨y₁, y₂, v, rfl⟩, hp0⟩ ?_ ?_
    · rintro u _ ⟨y₁, y₂, v, rfl⟩
      obtain ⟨x', h1, h2⟩ := hxu u
      exact ⟨_, _, _, by rw [← h2, ← hp _ h1 _ (hBU _ _ _), hB.inf x']⟩
    · rintro _ ⟨y₁, y₂, v, rfl⟩ L
      have := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hc y₁ y₂ v g) (L ∘ₗ p)
      convert this using 2 with z
      rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z)]
      rfl
  · obtain ⟨y, v', hv'⟩ : ∃ y v', B 1 y v' ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨u, b, hb, rfl⟩ := hQR a y₁
      obtain ⟨x', -, h2⟩ := hxu u
      have e1 := hB.inf x' 1 ((cEmb τ x'.1)⁻¹ * y₂) (W.rep x'⁻¹ v)
      rw [h, map_zero, mul_one, mul_inv_cancel_left, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, h2] at e1
      rw [hB.up b hb, ← e1, smul_zero] at hv
      exact hv rfl
    obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU 1 y v') hv'
    refine (hBd a k κ _).2 _ hp0 fun L => ?_
    have h1 := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hc y v' g) (L ∘ₗ p)
    have h2 := hEB.2.1 _ _ _ _ (hEB.2.2.2.1 1 (psum ν k)).2 h1
    rw [sub_eq_add_neg]
    convert h2 using 2 with z
    rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z), (hx z).2, mul_one, ← one_mul (tor a k z),
      hB.up _ (hTor a k z).1, (hTor a k z).2.2.1, map_smul, map_smul, one_mul, one_mul]
    rfl

end UpperTheory.Gal.Wt

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famOff_holds : FamOff := by
  intro E _ _ _ a τ W K ν d B hB U hU hBU hne τ' hτ'
  classical
  obtain ⟨y₁, y₂, v₀, hv₀⟩ := hne
  set v := InfinitePlace.mk τ' with hv
  obtain ⟨e, he⟩ : ∃ e, B y₁ y₂ (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 : B y₁ y₂ = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hi : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hi]
      exact hc _
    exact hv₀ (by rw [h1]; rfl)
  have h : (AU.mk ⟨U, hU⟩).HasWt v.embedding (W v) := by
    refine ⟨isIrreducible_sqRep a (W v), B y₁ y₂ ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun x => hBU _ _ _,
      fun x u => ?_⟩
    · have := LinearMap.congr_fun h0 (e v)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E a := embU_le_infU _ x.2
      have h1 : cEmb τ x.1 = 1 :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 τ) (by rw [InfinitePlace.mk_embedding]; exact hτ'.symm)
      have h2 := hB.inf ⟨x.1, hx⟩ y₁ y₂ (GlobalTheory.CoefIrred.tenMul W (Function.update e v u))
      rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2, h1, one_mul, one_mul] at h2
      exact h2.symm
  rcases InfinitePlace.embedding_mk_eq τ' with e | e
  · have h' := h
    rw [← Wt.at_embedding W v, e] at h'
    exact h'
  · have h2 := h.conjugate
    rw [← Wt.at_embedding W v, ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ'] at h2
    exact h2

theorem psum_succ {a : ℕ} (κ : DomWeight a) (i : Fin a) : psum κ (i + 1) = psum κ i + κ.w i := by
  have e : (Finset.univ.filter fun j : Fin a => j.val < i + 1) = insert i (Finset.univ.filter fun j : Fin a => j.val < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [psum, e, Finset.sum_insert (by simp), add_comm, psum]

theorem famWt_of : FamOff → FamSum → FamWt := by
  intro hOff hSum E _ _ _ a τ W K ν d B hB U hU hBU hne
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU
  refine ⟨mu, ⟨hU, hmu, ?_⟩, fun τ' h => hasWeightAt_unique ⟨U, hU⟩ τ' (hmu τ') (hOff E a τ W K ν d B hB U hU hBU hne τ' h),
    fun i => ?_⟩
  · obtain ⟨y₁, y₂, v, hv⟩ := hne
    exact ⟨_, hBU y₁ y₂ v, hv, fun x hx => hB.fix x hx _ _ _⟩
  · have h1 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) i
    have h2 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) (i + 1)
    rw [psum_succ, psum_succ] at h2
    rw [abs_le]
    push_cast
    omega

end UpperTheory.Gal.Wt

end
end
