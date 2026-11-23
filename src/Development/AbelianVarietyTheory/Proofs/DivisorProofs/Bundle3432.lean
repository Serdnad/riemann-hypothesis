module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointCompCompactificationStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UCore

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ p _ z₁ Φ hΦ y₀ N₀
  choose ct hct using hΦ
  have hev : ∀ y a, Φ.ev y a = (ct y).val a := fun y => (hct y).1
  choose e he using fun y => (hct y).2
  obtain ⟨D, hD, hproj⟩ := GlobalTheory.UPoinc.UDeepP.exists_udeep_proj E H Dw hpq l Xo cf C X₁ N₀
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  obtain ⟨w₁⟩ := nonempty_uWit X₁
  obtain ⟨w₂, htie⟩ := GlobalTheory.UPoinc.UDeep.exists_tie E H Dw hpq l Xo cf C X₁ D w₁
  refine ⟨D.m, hD, D.dvd, D.X.Ω₁, inferInstance, D.alg, D.fd, D.gal, ?_⟩
  intro 𝔷 h𝔷 ev' hev' hle hlt
  obtain ⟨hB, hmax, -, hlift⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
    hN D.fin D.gen z₁
  obtain ⟨z₂, hz₂, h𝔷z⟩ := hmax 𝔷 h𝔷
  haveI := D.fd
  haveI := D.gal
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have hl : ∀ y, ∃ y₂ : Sp (OO p) ⟶ D.X.M.Z, y₂ ≫ D.q = (ct y).y ∧
      ∀ b, ev' y b = D.X.M.val (gPt p ≫ y₂) (b : D.X.Ω₁) :=
    fun y => hlift p (ct y).y (ct y).cen (ev' y) (fun a => by rw [hev', hev]; rfl)
  choose y₂ hq hval using hl
  have hcen : ∀ y, y₂ y (cPt p) = z₂ := by
    intro y
    refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p (y₂ y) ?_ ?_
    · rw [← Scheme.Hom.comp_apply, hq]; exact (ct y).cen
    · intro b hb; rw [← hval]; exact hlt y b hb
  let ct₂ : ∀ y, UCTrait D.X p z₂ := fun y => { D.lift (ct y) (y₂ y) (hq y) with cen := hcen y }
  choose yy₁ hyy₁ using fun y => GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ (ct y)
  choose yy hyy hcomp using fun y => GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y) (yy₁ y) (hyy₁ y) (y₂ y) (hq y)
  have hyy₂ : ∀ y, UIsLabW D.X w₂ (ct₂ y) (yy y) := fun y => hyy y
  choose d hd using fun y => GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) (ct₂ y) (yy y₀) (yy y) (hyy₂ y₀) (hyy₂ y)
  let k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y := fun y =>
    if h : y = y₀ then (by subst h; exact LinearEquiv.refl _ _) else (e y₀).trans ((d y).trans (e y).symm)
  have hk0 : k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) := by simp [k]
  have hk : ∀ y a x, yy y₀ a = QuotientAddGroup.mk (e y₀ x) → yy y a = QuotientAddGroup.mk (e y (k y x)) := by
    intro y a x hax
    by_cases h : y = y₀
    · subst h; simpa [hk0] using hax
    · simp only [k, dif_neg h, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact hd y a _ hax
  have hsurj := (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p z₂ (ct₂ y₀) (yy y₀) (hyy₂ y₀).uIsLab).1
  choose A hA using fun x : (ct y₀).T.P.D.toPre.X =>
    hsurj (QuotientAddGroup.mk x : ModN (D.X.S.r * D.X.S.N) (ct y₀).T.P.D.toPre.X)
  obtain ⟨f, t, hfO, hft⟩ := GlobalTheory.T.unitary_thetaFourier_classSums_deeper_integral E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂
  have hfapp : (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) := fun ct yy₁ h1 => (hft ct yy₁ h1).2.2
  let F : (Fin 1 → Φ.X y₀) → ↥(X₁.S.HH X₁.M z₁) → integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
    fun c κ => ⟨f (A (e y₀ (c 0))) κ, (hB _).2 fun z' hz' => hfO _ κ z' hz'⟩
  have hF : ∀ c κ, ((F c κ : integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁) : D.X.Ω₁) = f (A (e y₀ (c 0))) κ :=
    fun _ _ => rfl
  refine ⟨k, ↥(X₁.S.HH X₁.M z₁), F, hk0, ?_, ?_, ?_, ?_⟩
  ·
    intro c c' κ hcc
    apply Subtype.ext
    rw [hF, hF]
    obtain ⟨w, hw⟩ := hcc 0
    refine GlobalTheory.UPoinc.DeepSame.deep_eq_of_congMod E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _
      (hA _) (hA _) ⟨e y₀ w, ?_⟩ κ
    rw [hw, map_add (f := _), map_nsmul]
  ·
    intro y c κ μ hμ hmin
    rw [hval y, qW_one]
    obtain ⟨hle_t, -, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    have hyyA : yy y (A (e y₀ (c 0))) = QuotientAddGroup.mk (e y (k y (c 0))) := hk y _ _ (hA _)
    refine GlobalTheory.UPoinc.class_limit_norm_le p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => hle_t μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0) ?_ ?_
    · obtain ⟨w, hw⟩ := hμ 0
      exact ⟨e y w, by simp [hw, map_add (f := _), map_nsmul]⟩
    · intro x' hx'
      have := hmin (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      simpa [qW_one] using this
  ·
    intro y μ huniq
    obtain ⟨-, heq_t, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    obtain ⟨κ, hκ⟩ := heq_t (e y (μ 0))
    refine ⟨fun u => (k y).symm (μ u), κ, fun u => ⟨0, by simp⟩, ?_⟩
    rw [hval y, qW_one]
    have hyyA : yy y (A (e y₀ ((k y).symm (μ 0)))) = QuotientAddGroup.mk (e y (μ 0)) := by
      simpa using hk y _ _ (hA (e y₀ ((k y).symm (μ 0))))
    refine GlobalTheory.UPoinc.classSum_norm_eq_of_unique_least p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => (hft (ct y) (yy₁ y) (hyy₁ y).uIsLab).1 μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0)
      ⟨0, by simp⟩ hκ ?_
    intro x' hx' hne
    have := huniq (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      (fun h => hne (congrFun h 0))
    simpa [qW_one] using this
  ·
    intro σ hσ
    obtain ⟨σ', hσ'⟩ := GlobalTheory.UPoinc.intClosure_aut_extends X₁.o₁ X₁.Ω₁ D.X.Ω₁ X₁.M z₁ σ
    obtain ⟨s, hs_pt, hs_q, hs_val⟩ := GlobalTheory.Poinc.GalAut.autAct X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
      hN D.fin D.gen σ'
    have hcs : (y₂ y₀ ≫ s) (cPt p) = z₂ := by
      refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p _ ?_ ?_
      · rw [← Scheme.Hom.comp_apply, Category.assoc, hs_q, hq]; exact (ct y₀).cen
      · intro b hb
        rw [← Category.assoc, hs_val, hσ', ← hval]
        apply hlt y₀
        have h2 : b ∈ 𝔷.comap σ := by rw [hσ]; exact hb
        exact h2
    have hsz : s z₂ = z₂ := by
      have h3 := hcs
      rw [Scheme.Hom.comp_apply, hcen y₀] at h3
      exact h3
    obtain ⟨aσ, -, haσ⟩ := GlobalTheory.T.deeperUnitaryLevel_galois_acts_on_labels E H Dw hpq l Xo cf C X₁ D σ' s hs_pt
    have hqs : (y₂ y₀ ≫ s) ≫ D.q = (ct y₀).y := by rw [Category.assoc, hs_q, hq]
    obtain ⟨yy', hyy', hcomp'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀) (y₂ y₀ ≫ s) hqs
    let ct₂' : UCTrait D.X p z₂ := { D.lift (ct y₀) (y₂ y₀ ≫ s) hqs with cen := hcs }
    have hyy'₂ : UIsLabW D.X w₂ ct₂' yy' := hyy'
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) ct₂' (yy y₀) yy' (hyy₂ y₀) hyy'₂
    have hrel : ∀ x, yy' x = yy y₀ (aσ x) :=
      haσ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab (y₂ y₀) (hq y₀) hqs (yy y₀) yy' (hyy y₀).uIsLab (hcomp y₀) hyy'.uIsLab hcomp'
    let γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀ := (e y₀).trans (g.trans (e y₀).symm)
    have hL : 3 ≤ X₁.S.r * X₁.S.N := by
      have h6 := X₁.big.2.2
      have : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega)) (Nat.factorial_ne_zero _))
      omega
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]; exact D.dvd.trans ((dvd_pow_self _ two_ne_zero).trans (dvd_mul_left _ _))
    have hLpos : 0 < D.X.S.r * D.X.S.N :=
      Nat.mul_pos (by have := D.X.S.r_pos; omega) (by have := D.X.S.N_ge; omega)
    have htf : ∀ (n : ℕ) (x : (ct y₀).T.P.D.toPre.X), 0 < n → n • x = 0 → x = 0 := by
      intro n x hn hx
      have h1 : ((n : ℤ)) • (e y₀).symm x = 0 := by
        rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
      rcases smul_eq_zero.1 h1 with h | h
      · omega
      · simpa using congrArg (e y₀) h
    have hcongY := GlobalTheory.UPoinc.compat_forces_congMod X₁.S.Gam D.X.S.Gam (ct y₀).T.P.D.toPre.X (X₁.S.r * X₁.S.N) (D.X.S.r * D.X.S.N)
      (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) (Nat.div_mul_cancel hdvd) hLpos htf D.lab (yy₁ y₀)
      (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X₁ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab).1 (yy y₀) yy' (hcomp y₀) hcomp'
      g.toLinearMap.toAddMonoidHom (fun a μ h => hg a μ h)
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x := by
      intro x
      obtain ⟨w, hw⟩ := hcongY (e y₀ x)
      have hw' : g (e y₀ x) = e y₀ x + (X₁.S.r * X₁.S.N) • w := hw
      refine ⟨(e y₀).symm w, ?_⟩
      simp only [γ, LinearEquiv.trans_apply]
      rw [hw', map_add (f := _), map_nsmul, LinearEquiv.symm_apply_apply]
    refine ⟨γ, GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (Φ.X y₀) (X₁.S.r * X₁.S.N) D.m hL (γ.restrictScalars ℤ) hcong, hcong, ?_⟩
    · intro c κ
      apply Subtype.ext
      rw [← hσ']
      show σ' (f (A (e y₀ (c 0))) κ) = f (A (e y₀ (γ (c 0)))) κ
      refine GlobalTheory.UPoinc.GalLab.main E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj σ' s hs_q hs_val hsz aσ
        (fun ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5 => haσ p z₁ ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5)
        (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _ (by rw [← hrel]; exact hg _ _ (hA _)) (hA _) ⟨0, ?_⟩ κ
      simp [γ]

end GlobalTheory.UPoinc.UCore
end
end

section

set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSConst

theorem isConstAlong_of_ks_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hb D q hq Θ hKS hΘ ρ hρ
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', v', dd, hdd⟩ := GlobalTheory.T.exists_basis_raynaudTangent_invariantFields (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  obtain ⟨h, hB, hD⟩ : ∃ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
    generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq ⊢
    letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
    let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
      { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
    exact GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd m (bdParam k m d) gam hmon hne D'
      (fun i => by
        show f (bdParam k m d i) ∈ _
        rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  exact GlobalTheory.T.degenerationData_constant_of_flat_heatOperators E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hD
    (GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero E H k m d t P gam hmon hli hab n v hv hb Y n' v' dd hdd D q hq h hB hD Θ hKS hΘ) ρ hρ
end GlobalTheory.KSConst
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  first | (exact @GlobalTheory.HTNecessary.main) | (exact GlobalTheory.HTNecessary.main) | (intros; apply GlobalTheory.HTNecessary.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  first | (exact @GlobalTheory.UPel.HT.realise_isKS) | (exact GlobalTheory.UPel.HT.realise_isKS) | (intros; apply GlobalTheory.UPel.HT.realise_isKS <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.potentialGoodReduction_of_order_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.potModel_of_intDivOrder_leftAction | exact GlobalTheory.potModel_of_intDivOrder_leftAction | (intros; apply GlobalTheory.potModel_of_intDivOrder_leftAction <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_lift_principal_symmetric_bundle_complete : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  first | exact @GlobalTheory.PolLiftComplete.exists_lift | exact GlobalTheory.PolLiftComplete.exists_lift | (intros; apply GlobalTheory.PolLiftComplete.exists_lift; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_open_locus_kernel_killed_symmetric_bundle : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G), (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen, s.IsGen) → x ^ d = 1) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus) | (exact GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus) | (intros; apply GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus  <;> assumption)
end
