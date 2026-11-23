module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorsDifferenceGlobal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GoodRedU

theorem subsingleton_lattice_of_range_subset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out _ T ξ hξ ⟨ξ₀, hξ₀, hlies⟩
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1

  have hr : Set.range ξ ⊆ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hξ
  let ξ' : Sp T.V ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι ξ hr
  have hξ' : ξ' ≫ U₀.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hK : jK T.V ≫ ξ' = ξ₀ := by
    rw [← cancel_mono U₀.ι, Category.assoc, hξ', hξ₀]
  let q : Sp T.V ⟶ Sp X₁.S.R := ξ' ≫ out.u₀
  have hB := GlobalTheory.isAbelianScheme_pullback_obj q X₁.ρ.P.A X₁.ρ.P.isAb

  obtain ⟨g, hg⟩ := Spec.map_surjective (ξ₀ ≫ out.u₀)
  have hf : X₁.Lies (spMap g.hom) T.y := by
    show X₁.Lies (Spec.map (CommRingCat.ofHom g.hom)) T.y
    rw [CommRingCat.ofHom_hom, hg]; exact hlies
  obtain ⟨G, _, α, β, hα, hβ, -⟩ := hf.uOver
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₂.cart hβ
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (isGrpPullback_pullback T.t.G (jK T.V)) m₁.cart
  haveI := he₁
  haveI := he₂
  have hq : spMap g.hom = jK T.V ≫ q := by
    show Spec.map (CommRingCat.ofHom g.hom) = _
    rw [CommRingCat.ofHom_hom, hg, ← hK, Category.assoc]
  have h₁ := ((isGrpPullback_of_iso e₂).comp ((isGrpPullback_of_iso e₁).comp hα)).congr
    (by rw [Category.id_comp, Category.id_comp, hq]) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback q).obj X₁.ρ.P.A) (jK T.V)).comp
    (isGrpPullback_pullback X₁.ρ.P.A q)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨Eiso, -, -⟩ := TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso Eiso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map Eiso.hom))
    rw [← Over.w Eiso.hom]
    infer_instance
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus T.t.G := fun _ _ _ _ _ => inferInstance
  exact ChartNotAb.subsingleton_of_closed_mem_abLocus T.P hc

end GlobalTheory.UPoinc.GoodRedU
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDefect

theorem exists_gauge_translate : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])), e.IsGen → ∀ (k : ℕ) (τ : SecM Y.q.left Q.P.L k), ∃ ρ : SecM Y.q.left Q.P.L k, (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) := by
  intro R _ _ Q O _ _ _ oa Y x e he k τ
  obtain ⟨ρ, hρ⟩ := exists_sec (L := Q.P.L) Q.P.isLB
    (φ' := fun _ : Fin 1 => Y.q.left) (ε' := fun _ => (k : ℤ))
    (by
      intro U _ g
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [zpow_mul, zpow_mul, zpow_one, zpow_neg_one, _root_.mul_comm]
      exact inv_mul_cancel_right _ _)
    (pullMulSec τ (𝟙 Y.H * (toUnit Y.H ≫ x)).left (GeneratorPullback.powGen Q.P.L _ _ e k) (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ e he k))
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [hρ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ]
  congr 1
  exact congrArg Units.val (map_pow _ _ _)

theorem exists_conj_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb mu
  obtain ⟨x, e, β, w, π, π', he, hwe, hTR⟩ := GlobalTheory.T.thetaShift_fourierTerm_translation_gauge R Dd O oa Y m t gam hm ht D hD mu
  obtain ⟨h', hb', hΘ, hu, hint⟩ :=
    GlobalTheory.T.heatOperator_conj_translation_gauge R Dd.toPre O oa Y n (fun a => v a) dd hv D h hb x e β he hwe
  refine ⟨h', w, π, π', hb', hΘ, hu, ?_⟩
  intro k α σ σ₁ σ₁' hk hs hA
  obtain ⟨τ₁, τ₁', hτ₁, hτ₁', hA₁⟩ := hA
  obtain ⟨σ'', τ, τ'', hτ, hτ'', hA'⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h' hb' k α σ
  obtain ⟨ρ, hρ⟩ := exists_gauge_translate Y x e he k τ₁
  obtain ⟨ρ', hρ'⟩ := exists_gauge_translate Y x e he k τ₁'
  have hAρ := hint k τ₁ τ₁' ρ ρ' hρ hρ' hA₁
  obtain ⟨a, b, -, hab⟩ := hTR k α hk
  obtain ⟨h1, h2⟩ := hab σ σ₁ τ τ₁ ρ hs hτ hτ₁ hρ
  exact ⟨σ'', ⟨τ, τ'', hτ, hτ'', hA'⟩, h2 σ'' σ₁' τ'' τ₁' ρ' hτ'' hτ₁' hρ'
    (GlobalTheory.T.leibniz_along_baseConstants_at_points Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB (fun a => v a) dd hv D h' k a b ρ τ ρ' τ'' h1 hAρ hA')⟩

end GlobalTheory.HeatDefect
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_connection_matrix_invariant_basis : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_symmKS | exact GlobalTheory.HeatInvLift.exists_invLift_symmKS | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_symmKS <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusInvariant_heatOperators_difference_global : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (e : Fin n → R) (π π' : R), (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) ∧ ∀ (i : h.J) (i' : h'.J) (Wo : Y.H.left.Opens), Wo ≤ h.W i ⊓ h'.W i' → (∀ f, h.d i Wo f - h'.d i' Wo f = ∑ a, constFn Y.H.hom Wo (e a) * dd a Wo f + ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo * dd a Wo f) ∧ 2 * (rsT (h.p i) Wo - rsT (h'.p i') Wo) + 2 * dlg Y.H Y.q.left Q.P.L (h.d i) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo = 2 * constFn Y.H.hom Wo π ∧ 2 * (rsT (h.p' i) Wo - rsT (h'.p' i') Wo) + 2 * ∑ a, constFn Y.H.hom Wo (h.u a) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dd a Wo (dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo) = 2 * constFn Y.H.hom Wo π' := by
  first | exact @GlobalTheory.HeatUniqGlob.main | exact GlobalTheory.HeatUniqGlob.main | (intros; apply GlobalTheory.HeatUniqGlob.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DivInt

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem t_mem (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {mu : X} (h : mu ≠ 0) : t mu ∈ maximalIdeal V := by
  haveI := 𝔪.cn.2.2.2
  obtain ⟨u, hu⟩ := 𝔪.psi mu
  obtain ⟨r, hr, -, hm, -⟩ := (PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hr hu
  have : (u : V) * t mu ∈ maximalIdeal V := hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this

theorem ratio (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} (ha : X₁.M.Div X₁.S.th a z₁) (b : X₁.S.Gam) :
    ∃ v : V, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ = algebraMap V (FractionRing V) v * 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC
  have hC : yC (closedPoint V) ⤳ z₁ := sp _
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hξz : ξ ⤳ z₁ := sp _
  have hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁ := ha.2 b
  have hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz hr
  have haξ : X₁.S.th a ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem a)
  refine ⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩
  have e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a := (div_mul_cancel₀ _ ha.1).symm
  have e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩) :=
    RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)
  rw [← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]

theorem label_zero_of_mem_supI : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 a ha
  have ha' : X₁.M.Div X₁.S.th a z₁ := ha
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.exists_thetaConstant_ne_zero_uniformisedMember I X₁ z₁ act V ev X t δ 𝔪
  have hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b₀
    rw [h0, mul_zero] at hv
    exact hb₀ hv
  obtain ⟨ν, hν1, hνm⟩ := GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn
  have hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun b => by
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b
    rw [hv, map_mul]
    exact mul_le_of_le_one_left' (hν1 v)
  obtain ⟨w, hw, hle⟩ := GlobalTheory.T.thetaConstant_valuation_le_common_bound_mul_monomial I X₁ z₁ act V ev X t δ 𝔪 ν hν1 hνm _ hmax a
  have h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)
  have h1 : 1 ≤ ν (algebraMap V (FractionRing V) (t w)) := by
    have := mul_le_mul_of_nonneg_left hle
      (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul] at this
  by_cases hw0 : w = 0
  · exact hw0 ▸ hw
  · exact absurd h1 (not_le.2 (hνm _ (t_mem 𝔪 hw0)))

end GlobalTheory.GSep.DivInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.GSep

theorem exists_uLink_regAt_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (r : Fin Cm.m → V₁), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ GlobalTheory.GSep.ULink C X₁ act u π ∧ IsCov C π z₁ ζ ∧ IsCN V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ GlobalTheory.GSep.RegAt X₁ z₁ ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ ∀ k, r k ^ 2 = ρ₁ (Cm.s k) := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn ho j₀
  classical
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_finite_cover_linked_thetaSystems E H Dw hpq l Xo c C n hn ho j₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.FinLift.lift_point_finite_surjective (FractionRing V) _ _ Cm.y q hqf hqs
  obtain ⟨X₁, act, u, π, yM, hlink, hrN, ⟨U, g', hg', hgU, hrange⟩, hyM, hreg⟩ := hB L yL
  let G : Polynomial V := ∏ k, (Polynomial.X ^ 2 - Polynomial.C (Cm.s k))
  have hG : G.Monic := Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_pow_sub_C _ two_ne_zero
  obtain ⟨V₁, _, _, _, ρ₁, σ, hV₁, hinj, hfin, hσ, hR⟩ := GlobalTheory.USep.Setup.exists_ext V hV L G hG
  choose r hr₂ using fun k => hR.exists_sq
    (Finset.dvd_prod_of_mem (fun k => Polynomial.X ^ 2 - Polynomial.C (Cm.s k)) (Finset.mem_univ k))
  have hr : Set.range (ξ ≫ pullback.fst _ _ :) ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hrange ⟨ξ p, rfl⟩
  let f : Sp V ⟶ U.toScheme := IsOpenImmersion.lift U.ι _ hr
  have hf : f ≫ U.ι = ξ ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
  have hkey : spMap σ ≫ spMap (algebraMap (FractionRing V) L) ≫ jK V = jK V₁ ≫ spMap ρ₁ := by
    simp only [← Spec.map_comp]
    exact congrArg (fun χ => spMap χ) hσ
  have hcomp : (spMap σ ≫ yM) ≫ g' = jK V₁ ≫ spMap ρ₁ ≫ f := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [hgU, hyM, hf, ← Category.assoc yL, hyL]
    simp only [Category.assoc, UCompact.i]
    rw [← Category.assoc Cm.y, hξ]
    simp only [Category.assoc]
    rw [reassoc_of% hkey]
  obtain ⟨z₁, ev, hloc, hev, hev2⟩ := GlobalTheory.FiniteLift.exists_stalk_lift V₁ hV₁.1.2.2.1 X₁.M.Z U.toScheme g' hg'
    (spMap ρ₁ ≫ f) (spMap σ ≫ yM) hcomp
  have hev' : spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = (spMap ρ₁ ≫ ξ) ≫ pullback.fst _ _ := by
    rw [← hgU, reassoc_of% hev, hf, Category.assoc]
  haveI := hloc
  obtain ⟨ζ, hζ⟩ := GlobalTheory.USep.Setup.exists_lift_genericFibre C ev _ _ hev'
  haveI : IsPreimmersion (spMap C.b) := by
    letI : Algebra C.o c.F := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hgen : ∀ p : Sp (X₁.M.Z.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF := by
    intro p hp
    have hpt := hlink.2.2.2
    have h1 : π (genericPoint X₁.M.Z) =
        (pullback.fst C.z (spMap C.b)) (C.iF (u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)))) := by
      rw [← X₁.M.pt_apply (closedPoint X₁.Ω₁)]
      exact congrArg (fun χ : Sp X₁.Ω₁ ⟶ C.Z => χ (closedPoint X₁.Ω₁)) hpt
    refine ⟨u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)),
      (pullback.fst C.z (spMap C.b)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply ζ, hζ, Scheme.Hom.comp_apply, GlobalTheory.USep.Setup.fromSpecStalk_bot z₁ p hp, h1]
  refine ⟨j, X₁, act, u, π, z₁, ζ, V₁, inferInstance, inferInstance, inferInstance, ρ₁, ev, r, hj, hrN, hlink,
    ⟨X₁.normal, ⟨U, g', hg', hgU, hrange⟩, hζ, hgen⟩, ⟨hV₁.1.1, hV₁.1.2.2.1, hV₁.1.2.2.2, hV₁.2⟩, hinj, hfin, hloc, ?_, ?_, hr₂⟩
  · intro a ha
    rw [hev2]
    convert hreg a ha using 2
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg yM (Subsingleton.elim (α := PrimeSpectrum L) _ _))
  · rw [← cancel_mono (pullback.fst C.z (spMap C.b)), Category.assoc, hζ, hev']

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem zhAbove_surjective {X₁ : GSet} {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} (h : ZHAbove X₁ Y πY) :
    Function.Surjective πY := by
  obtain ⟨-, -, -, -, -, hH, hP⟩ := h
  haveI := hP
  have hc : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
  have hg : genericPoint X₁.M.Z ∈ Set.range πY := by
    refine ⟨Y.pt (IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    have e := congrArg (fun f : Sp X₁.Ω₁ ⟶ X₁.M.Z => f (IsLocalRing.closedPoint X₁.Ω₁)) hH
    simp only [Scheme.Hom.comp_apply] at e
    exact e.trans (X₁.M.pt_apply _)
  intro z
  have : z ∈ closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) := by
    rw [genericPoint_spec X₁.M.Z |>.def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.2 hg) hc) this

theorem exists_gMem_injective : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem X₁
  obtain ⟨y, hy⟩ := zhAbove_surjective hY z₁
  obtain ⟨V, i1, i2, i3, -, ev, X, i4, t, δ, 𝔫, -, -, -, hinj⟩ := GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY y hy
  exact ⟨V, i1, i2, i3, ev, X, i4, t, δ, hinj, ⟨𝔫⟩⟩

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.galoisTower_thetaMember_terms_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  first | exact @GlobalTheory.GSep.BaseTerms.terms_baseChange | exact GlobalTheory.GSep.BaseTerms.terms_baseChange | (intros; apply GlobalTheory.GSep.BaseTerms.terms_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.thetaMember_terms_coefficients_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
  (x x₂ : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (fr₂ : ∀ a, FrAt (x₂ a))
  (th th₂ : SecA 𝔪.A (FractionRing V) 1) (w₀ w₀₂ : W0 𝔪.U.toUnifPre) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) 1)
  (g' g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x b) (fr b) →
  (∀ a, (x₂ a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀₂.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀₂ th₂ s₂ →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀₂ g₂ w₂ (x₂ b) (fr₂ b) →
  ∀ χ, coef s g' w χ = coef s₂ g₂ w₂ χ := by
  first | exact @GlobalTheory.GSep.TermsUniq.coef_eq | exact GlobalTheory.GSep.TermsUniq.coef_eq | (intros; apply GlobalTheory.GSep.TermsUniq.coef_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaLabel_class_zero_of_divides_all_thetaConstants : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  first | exact @GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI | exact GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI | (intros; apply GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.toroidal_boundary_local_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @GlobalTheory.BdEquation.exists_reduced_equation | exact GlobalTheory.BdEquation.exists_reduced_equation | (intros; apply GlobalTheory.BdEquation.exists_reduced_equation <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_uniform_lift_sections_thickeningTower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))), (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  first | exact @GlobalTheory.FormalAlg.exists_lift_sections_tower | exact GlobalTheory.FormalAlg.exists_lift_sections_tower | (intros; apply GlobalTheory.FormalAlg.exists_lift_sections_tower <;> assumption)
end
