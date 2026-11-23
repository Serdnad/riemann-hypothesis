module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle106
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConjugateComponentAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle118
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle112

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_iotaAll (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) := by
  by_cases hj : InR D j
  · obtain ⟨⟨ι, hι⟩, -⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι,
      fun _ hr => ?_⟩
    have e : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι) = ι := by
      ext x i
      rfl
    rw [e]
    exact hι
  · exact ⟨0, fun h => absurd h hj⟩

theorem exists_pkgAll (Q : Par D) (hQ : Q.Pins) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (j : ℕ)
    (σ : Q.c.F →+* ℂ) (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (hι : InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (Kf : Subgroup (GA D (D.sp.W j))) (hK : IsLevelK (D.sp.W j) Q.l.M Kf) (χ : (AE D)ˣ →* Circle)
    (hχ : InR D j → GoodEmb Q.c σ → IsHeckeChar D χ ∧ ∀ a, χ (idF D a) = 1) :
    ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (mu : GA D (D.sp.W j) → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → (∀ k, (U.X k).p0 = (Q.Dw j).q) ∧
        PkgLaws (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀) Kf χ U dict mu x₀ := by
  by_cases h : InR D j ∧ GoodEmb Q.c σ
  · obtain ⟨hj, hσ⟩ := h
    obtain ⟨⟨C, hC, hCι⟩, -⟩ := GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r
      (D.sp.W_rank j hj.1 hj.2) _ (hι hj (D.sp.W_rank j hj.1 hj.2)) (hpq j) hQ.2.1.2 hσ
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.T.exists_uniformisation_dictionary_character_laws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r C hC Kf hK χ
      (hχ hj hσ).1 (hχ hj hσ).2
    rw [hCι] at hP
    exact ⟨C.unf un, dict, mu, C.x₀, fun _ _ => ⟨fun k => (hC.base.type k).1, hP⟩⟩
  · obtain ⟨U, ⟨k⟩⟩ := GlobalTheory.T.exists_uniformisation_with_component_at_every_embedding D Q hQ hpq j σ
    exact ⟨U, fun _ => ⟨k, fun _ _ _ => 0⟩, fun _ => 1, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩

end GlobalTheory.Member
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.AnyLevel

theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ)
    (hτσ : (τ : ℂ →+* ℂ).comp σ = σ)
    (hfix : FixesCurve H τ l.M') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlevA, hlev⟩ := GlobalTheory.T.marking_at_conjugate_splitPoint_transported_twisted E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hmem : ∀ v, F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := fun v => by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  have hA' : ∀ v, ∃ x, Φ (F.t i v) = F.t i' v + l.A • x := fun v => by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
    obtain ⟨e, he⟩ := hlevA v a ha b hb hab.symm
    rw [hw, map_one, one_smul, one_smul, hab] at he
    exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → FixesCurve H τ l.M' → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hσx hsig τ hτ hC
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_periodSpace_perm_of_complexAut E H D l Xo σ g ty F hpq hσ hty hσx τ hτ
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hσx, hτ]
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := GlobalTheory.T.exists_split_period_any_level E H D l Xo σ g ty F hpq hσ hty hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty τ hτσ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat.AnyLevel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hA hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces E H D l Xo _ g ty F hD rfl hty hA c fun τ hτ => ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  exact GlobalTheory.T.permutes_periodSpaces_id_of_fixes_cm_curve_torsion E H D l Xo _ g ty F hD rfl hty hA hsig τ (hτ _ (c.le h1)) (hC τ hτ)

end GlobalTheory.CompRat
end
