module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem valR_of_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  intro X L hL Ω _ _ x g k σ ω hv i hi
  set z := IsLocalRing.closedPoint Ω
  have hxz : x z ∈ L.U i := hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hxz)
  have h := hv (Sp Ω) (𝟙 _) z J hJ
  have e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  have e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  rw [sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2),
    Category.id_comp] at h
  have m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have a1 : valR x _ (σ.f fun _ => i) =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i)) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _
  have mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i) := Set.mem_iInter.2 fun _ => hxz
  have a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _
  have a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val :=
    gs_unit _ _ _ mG _
  have hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω := by
    rw [← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]
    simp [GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]
  rw [a1, a2, a3]
  have h' := congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h
  rw [map_mul, hω, Units.val_pow_eq_pow_val, map_pow] at h'
  exact h'

end GlobalTheory.HeatV
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GermVal

theorem valR_linComb_germ : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w k σ' s H F _ _ ξ i j h2 h1
  have m2 : f₂ (ξ (IsLocalRing.closedPoint F)) ∈ L₂.U i := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₂) _).1 h2
  have m1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ L₁.U j := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₁) _).1 h1
  have hy := H (ξ (IsLocalRing.closedPoint F)) i j m2 m1
  have a2 : ξ (IsLocalRing.closedPoint F) ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => m2
  have aw : ξ (IsLocalRing.closedPoint F) ∈
      ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => m2, Set.mem_iInter.2 fun _ => m1⟩
  have a1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ (LB.LinComb L₁ (K := Fin 1) (fun _ => 𝟙 X₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => m1
  rw [GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ a2, GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ aw,
    GlobalTheory.ZH.ThetaData.valR_eq_gs (ξ ≫ f₁) _ a1, gs_stalkMap ξ _ _ a2, gs_stalkMap ξ _ _ aw,
    gs_comp ξ f₁ _ _ a1, hy]
  simp only [map_mul, map_pow]

end GlobalTheory.GermVal
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

theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_of_isWeight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  first | exact @GlobalTheory.Heat.isTerm_of_isWt | exact GlobalTheory.Heat.isTerm_of_isWt | (intros; apply GlobalTheory.Heat.isTerm_of_isWt <;> assumption)
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

namespace GlobalTheory.HeatUniq.FourierChart

open GlobalTheory.KS GlobalTheory.Heat.Glue

theorem images_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  intro R _ _ Q Oa _ _ _ oa Y n dd D hdd h h' hb hb' k α C hloc τ₁ τ₁' τ₂ τ₂'' hgerm hwt hA hA'
  have hL : Q.P.L.IsLB := Q.P.isLB

  have e1 : ∀ c : Fin 1 → Q.P.L.ι, τ₁.f c = τ₂.f c := by
    intro c
    refine fn_ext fun x hx => ?_
    obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L hL x (fun _ : Fin 1 => 𝟙 Y.H.left ≫ Y.q.left) c
      (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => by
        simpa using Set.mem_iInter.1 hx k)
    have := hgerm x J hJ
    rwa [sval_of τ₁ (𝟙 _) x J c hJc, sval_of τ₂ (𝟙 _) x J c hJc] at this

  have loc : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (i : hh.J) (O : Y.H.left.Opens) (hO : O ≤ hh.W i)
      (f : Γ(Y.H.left, hh.W i)),
      rsT (op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k (hh.W i) f) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT f O) := by
    intro hh i O hO f
    have hd : ∀ g, resG Y.H.left hO (hh.d i (hh.W i) g) = hh.d i O (resG Y.H.left hO g) :=
      fun g => ((hh.lift i).1.2.2 (hh.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG Y.H.left hO (dd a (hh.W i) g) = dd a O (resG Y.H.left hO g) :=
      fun a g => ((hdd a).2.2 (hh.W i) O hO le_top g).symm
    have hc : ∀ r, resG Y.H.left hO (constFn Y.H.hom (hh.W i) r) = constFn Y.H.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn Y.H.hom hO r)
    have hp : ∀ p : Γ(Y.H.left, hh.W i), resG Y.H.left hO (rsT p (hh.W i)) = rsT p O := fun p => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]

    simp only [GlobalTheory.Heat.op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

  have actO : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (τ τ' : SecM Y.q.left Q.P.L k), hh.Acts k τ τ' →
      ∀ (i : hh.J) (O : Y.H.left.Opens), O ≤ hh.W i →
      rsT (τ'.f fun _ => hh.j i) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT (τ.f fun _ => hh.j i) O) := by
    intro hh τ τ' hAc i O hO
    have hW : hh.W i ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => hh.j i) := le_wchart _ (hh.le i)
    rw [← rsT_rsT hW hO (τ'.f _), hAc i, loc hh i O hO, rsT_rsT hW hO]

  have chart : ∀ (i : h.J) (i' : h'.J), ∃ O : Y.H.left.Opens, O = h.W i ⊓ h'.W i' ∧
      rsT (τ₁'.f fun _ => h'.j i') O =
        rsT (τ₂''.f fun _ => h'.j i') O + constFn Y.H.hom O C * rsT (τ₂.f fun _ => h'.j i') O := by
    intro i i'
    obtain ⟨V, hV⟩ := (hb i).1
    obtain ⟨V', hV'⟩ := (hb' i').1
    have hO : Y.q.left ⁻¹ᵁ (V ⊓ V') = h.W i ⊓ h'.W i' := by rw [hV, hV']; rfl
    refine ⟨Y.q.left ⁻¹ᵁ (V ⊓ V'), hO, ?_⟩
    have hO1 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h.W i := hO.le.trans inf_le_left
    have hO2 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h'.W i' := hO.le.trans inf_le_right
    have hOc : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) ⊓
        LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
      le_inf (hO1.trans (le_wchart _ (h.le i))) (hO2.trans (le_wchart _ (h'.le i')))
    have hOU : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) :=
      fun y hy => ⟨h.le i (hO1 hy), h'.le i' (hO2 hy)⟩
    have hunit : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) *
        pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ (V ⊓ V')) = 1 := by
      rw [← pbT_mul, Units.mul_inv, pbT_one _ hOU]
    have hw := hwt (h'.j i') (V ⊓ V') (hO2.trans (h'.le i'))
    have key := hloc i i' (V ⊓ V') hO.le _ hw
    have s1 := sec_rel Y.q.left k τ₁ (fun _ => h.j i) (fun _ => h'.j i') hOc
    have s1' := sec_rel Y.q.left k τ₁' (fun _ => h.j i) (fun _ => h'.j i') hOc
    have a1 := actO h τ₁ τ₁' hA i _ hO1
    have a2 := actO h' τ₂ τ₂'' hA' i' _ hO2
    beta_reduce at s1 s1'
    rw [e1, e1] at s1
    rw [e1, s1, key, ← a2, s1'] at a1
    have hu : IsUnit (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) ^ k) :=
      (show IsUnit _ from ⟨⟨_, _, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩).pow k
    exact hu.mul_left_cancel a1

  intro y J hJ
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h.W i by rw [h.cover]; trivial)
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h'.W i by rw [h'.cover]; trivial)
  obtain ⟨O, hOeq, hid⟩ := chart i i'
  have hyO : y ∈ O := hOeq ▸ ⟨hi, hi'⟩
  have hOc : O ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
    hOeq ▸ (inf_le_right.trans (le_wchart _ (h'.le i')))
  have hyJ := hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)
  have hyj' : (𝟙 Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') := hOc hyO
  have tr : ∀ τ : SecM Y.q.left Q.P.L k, sval τ (𝟙 Y.H.left) y J =
      (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) (𝟙 Y.H.left) y
        (fun _ => J (𝟙 Y.H.left ≫ Y.q.left)) (fun _ => h'.j i')).val *
        gs (𝟙 Y.H.left) y O (rsT (τ.f fun _ => h'.j i') O) := by
    intro τ
    refine (sec_trans τ (𝟙 Y.H.left) y hyJ hyj').trans (congrArg _ ?_)
    rw [rsT_of_le (show O ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => h'.j i') from hOc)]
    exact (gs_res (𝟙 Y.H.left) y hOc hyO _).symm
  have hc : gs (𝟙 Y.H.left) y O (constFn Y.H.hom O C) = gs (𝟙 _) y ⊤ (scal Y.H.hom C) := by
    rw [gs_constFn Y.H.hom O (𝟙 Y.H.left) y hyO C, Category.id_comp, cst, gs_eq Y.H.hom y ⊤ trivial]
    exact (gs_eq (𝟙 _) y ⊤ trivial _).symm
  rw [tr τ₁', tr τ₂'', tr τ₂, hid, gs_add _ _ _ hyO, gs_mul _ _ _ hyO, hc]
  ring

end GlobalTheory.HeatUniq.FourierChart
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

theorem _root_.GlobalTheory.T.exists_heatOperator_glued_pullbackBundlePower : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) → ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  first | exact @GlobalTheory.Heat.Glue.exists_acts | exact GlobalTheory.Heat.Glue.exists_acts | (intros; apply GlobalTheory.Heat.Glue.exists_acts <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_basis_raynaudTangent_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayBasis.exists_basis_isInv | exact GlobalTheory.RayBasis.exists_basis_isInv | (intros; apply GlobalTheory.RayBasis.exists_basis_isInv <;> assumption)
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

theorem _root_.GlobalTheory.T.logDerivatives_coboundary_coeffs_mem_maximalIdeal : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := by
  first | exact @GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob | exact GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob | (intros; apply GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob <;> assumption)
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
open GlobalTheory.TangentOrigin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeffRing

theorem spMap_fstHom_surjective (B : Type) [CommRing B] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
  intro p
  haveI := p.isPrime
  refine ⟨(⟨p.asIdeal.comap (algebraMap B (DualNumber B)), Ideal.IsPrime.comap _⟩ : PrimeSpectrum B), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change (algebraMap B (DualNumber B)) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hx : x = algebraMap B (DualNumber B) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hn : (TrivSqZeroExt.inr x.snd : DualNumber B) ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 2
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    exact zero_mem _
  constructor
  · intro h
    rw [hx]
    exact add_mem h hn
  · intro h
    have h2 := sub_mem h hn
    rwa [show x - TrivSqZeroExt.inr x.snd = algebraMap B (DualNumber B) x.fst by
      rw [sub_eq_iff_eq_add]; exact hx] at h2

theorem evalPt_tvE_mul : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  intro R _ G _ _ u dd hinv B _ _ e he z O h
  set φ : R →+* B := algebraMap R B with hφ
  have hz : z.left ≫ G.hom = spMap φ := Over.w z
  have eφ : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap B (DualNumber B)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hv : (tv u).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
    (Over.w (tv u)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv u).left) ≫ G.hom = (tEpsG (z.left ≫ G.hom)).hom := by
    show _ = spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom
    refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
    rw [hz, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eφ]
  let g' : tEpsG (z.left ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap B (DualNumber B)) ≫ z.left) (Category.assoc _ _ _)
  let v' : tEpsG (z.left ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv u).left) h2
  have htr : IsTr G φ z.left u (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩

  have hk : ∀ (t : B) (ht : t * t = 0), ∃ kt : Chart.sp (R₀ := R) B ⟶ tEpsG (z.left ≫ G.hom),
      kt.left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ∧ kt ≫ g' = z ∧
        kt ≫ v' = Chart.spMap (GlobalTheory.SqZero.epsTo R t ht) ≫ tvE u := by
    intro t ht
    have hτa : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom.comp (algebraMap B (DualNumber B)) =
        RingHom.id B := by
      ext b
      simp [GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl]
    have hsp : spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ≫ spMap (algebraMap B (DualNumber B)) =
        𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτa, CommRingCat.ofHom_id, Spec.map_id]
    refine ⟨Over.homMk (spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom) ?_, rfl, ?_, ?_⟩
    · show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom = _
      rw [← Category.assoc, hsp, Category.id_comp]
      exact hz
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left = z.left
      rw [← Category.assoc, hsp, Category.id_comp]
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (dualMap φ) ≫ (tv u).left = (Chart.spMap (GlobalTheory.SqZero.epsTo R t ht)).left ≫ (tv u).left
      rw [Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.dualTo_apply, GlobalTheory.SqZero.epsTo, dualMap, hφ, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]
  obtain ⟨k, hkl, hkg, hkv⟩ := hk e he
  obtain ⟨k0, hk0l, hk0g, hk0v⟩ := hk 0 (mul_zero 0)

  have hone : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = 1 := by
    let K : Chart.sp (R₀ := R) B ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)).toRingHom) (by
        show _ ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ = spMap φ
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun a => ?_
        simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, hφ])
    have e1 : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u =
        K ≫ smT (𝟙 (Sp R)) 0 (tv u) := by
      apply Over.OverMorphism.ext
      show (Chart.spMap _).left ≫ (tv u).left = spMap _ ≫ (smT (𝟙 (Sp R)) 0 (tv u)).left
      rw [smT_left, Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, epsMul]
    rw [e1, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.comp_one]
  have hp : (Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z = k ≫ (g' * v') := by
    rw [MonObj.comp_mul, hkg, hkv, mul_comm]
  have hp0 : k0 ≫ (g' * v') = z := by
    rw [MonObj.comp_mul, hk0g, hk0v, hone, _root_.mul_one]
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = z.left := by
    have := congrArg (fun q => q.left) hp0
    simp only [Over.comp_left, hk0l] at this
    have hfh : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) (0 : B) (mul_zero 0)).toRingHom =
        (TrivSqZeroExt.fstHom B B B).toRingHom := RingHom.ext fun a => by
      simp [GlobalTheory.SqZero.dualTo_apply]
    rw [← hfh]
    exact this
  have hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O := by
    intro p _
    obtain ⟨q, rfl⟩ := spMap_fstHom_surjective B p
    rw [← hfst] at h
    exact h (Set.mem_univ q)
  have hpl : ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left =
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left := by
    rw [hp, Over.comp_left, hkl]
  have h' : ⊤ ≤ ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left ⁻¹ᵁ O := by
    rw [hpl]
    intro q _
    exact hw (Set.mem_univ _)
  refine ⟨h', fun f => ?_⟩
  have hval : valR (g' * v').left O f = evalPt (g' * v').left O hw f := by
    unfold valR; rw [dite_eq_left hw]; rfl
  have hvalz : valR z.left O (dd O f) = evalPt z.left O h (dd O f) := by
    unfold valR; rw [dite_eq_left h]; rfl
  have hsnd := hinv.2 B φ z.left (g' * v').left O f hz h htr
  rw [hval, hvalz] at hsnd
  have key : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst + (evalPt (g' * v').left O hw f).snd * e := by
    rintro y hy rfl
    rw [evalPt_spMap_comp _ _ O hw hy f]
    exact GlobalTheory.SqZero.dualTo_apply _ _ _ _
  have key0 : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst := by
    rintro y hy rfl
    exact evalPt_spMap_comp _ _ O hw hy f
  rw [key _ h' hpl.symm, key0 _ h hfst, hsnd]
  ring

end GlobalTheory.VertCoeffRing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  first | exact @GlobalTheory.Poinc.psd_of_min | exact GlobalTheory.Poinc.psd_of_min | (intros; apply GlobalTheory.Poinc.psd_of_min <;> assumption)
end
