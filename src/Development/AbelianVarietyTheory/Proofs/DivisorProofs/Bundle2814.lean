module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorField
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

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

theorem _root_.GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  first | exact @GlobalTheory.FormalOrigin.exists_formalPoint | exact GlobalTheory.FormalOrigin.exists_formalPoint | (intros; apply GlobalTheory.FormalOrigin.exists_formalPoint <;> assumption)
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

theorem _root_.GlobalTheory.T.pointValue_fractionField_comm_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenericVal.valR_generic | exact GlobalTheory.GenericVal.valR_generic | (intros; apply GlobalTheory.GenericVal.valR_generic <;> assumption)
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


theorem _root_.GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  first | exact @GlobalTheory.SecScalVal.val_of_secScal | exact GlobalTheory.SecScalVal.val_of_secScal | (intros; apply GlobalTheory.SecScalVal.val_of_secScal <;> assumption)
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


theorem _root_.GlobalTheory.T.pointValue_relation_sections_through_generating_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  first | exact @GlobalTheory.GermVal.valR_linComb_germ | exact GlobalTheory.GermVal.valR_linComb_germ | (intros; apply GlobalTheory.GermVal.valR_linComb_germ <;> assumption)
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


theorem _root_.GlobalTheory.T.pointValue_section_in_chart_of_frame_value : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  first | exact @GlobalTheory.HeatV.valR_of_isValue | exact GlobalTheory.HeatV.valR_of_isValue | (intros; apply GlobalTheory.HeatV.valR_of_isValue <;> assumption)
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

namespace GlobalTheory.Heat

theorem heat_acts_on_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D), IsBasic Y h → ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α), ∃ σ', TActs Y h k α σ σ' := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h hb k α σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.RayEv.exists_sec_fourierTerm R Dd.toPre O oa Y k α σ
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_heatOperator_glued_pullbackBundlePower Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB dd (fun a => (hv a).1) (⇑D) h k τ
  have hE : ∀ a (β : Dd.toPre.X) (V : Y.H.left.Opens) f, IsWt Y β V f → IsWt Y β V (dd a V f) :=
    fun a => GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField Y (v a) (dd a) (hv a)
  choose V hV using fun i => (hb i).1
  have hle : ∀ i, h.W i ≤ LB.wchart Dd.toPre.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => h.le i hx
  have hw : ∀ i, IsWt Y α (h.W i) (rsT (τ'.f fun _ => h.j i) (h.W i)) := by
    intro i
    rw [hτ' i]
    exact GlobalTheory.T.torusInvariant_heatOperator_preserves_weight Y dd _ h hE hb i k α _ (GlobalTheory.T.raynaudFourierTerm_chartFunctions_isWeight Y k α σ τ hτ _ _ (hle i))
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.isRaynaudFourierTerm_of_isWeight Y k α τ' h.J V (fun i _ => h.j i) (by simp only [← hV]; exact h.cover)
    (fun i => by rw [← hV i]; exact hle i) (fun i => by rw [← hV i]; exact hw i)
  exact ⟨σ', τ, τ', hτ, hσ', hτ'⟩

end GlobalTheory.Heat
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
namespace GlobalTheory.DlogBasis

section Coch

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kap (r : A) : C1 U := fun i j => constFn q (U i ⊓ U j) r

theorem rsT_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := by simp [rsT, h]

theorem resG_constFn' {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) : resG Y h (constFn q O₀ r) = constFn q O r := by
  simp only [constFn, resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  first
    | (erw [Scheme.Hom.appLE_map])
    | (simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]; rfl)

theorem rsT_add' {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg' {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mulc {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) (s : Γ(Y, O₀)) :
    rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  rw [rsT_le h, rsT_le h, map_mul, resG_constFn' q h]

theorem kap_add (r s : A) : kap q U (r + s) = kap q U r + kap q U s := by funext i j; simp [kap, constFn]

theorem kap_mul (r s : A) : kap q U (r * s) = kap q U r * kap q U s := by funext i j; simp [kap, constFn]

theorem kap_zero : kap q U 0 = 0 := by funext i j; simp [kap, constFn]

variable {q U}

theorem isCob_zero : IsCob U 0 := ⟨0, fun i j => by simp only [Pi.zero_apply]; unfold rsT; split_ifs <;> simp⟩

theorem isCob_add {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c + d) := by
  obtain ⟨b, hb⟩ := hc
  obtain ⟨b', hb'⟩ := hd
  refine ⟨b + b', fun i j => ?_⟩
  simp only [Pi.add_apply, hb, hb', rsT_add']
  ring

theorem isCob_neg {c : C1 U} (hc : IsCob U c) : IsCob U (-c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨-b, fun i j => ?_⟩
  simp only [Pi.neg_apply, hb, rsT_neg']
  ring

theorem isCob_sub {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c - d) := by simpa [sub_eq_add_neg] using isCob_add hc (isCob_neg hd)

theorem isCob_kap_mul (r : A) {c : C1 U} (hc : IsCob U c) : IsCob U (kap q U r * c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun i => constFn q (U i) r * b i, fun i j => ?_⟩
  simp only [Pi.mul_apply, hb, kap, rsT_mulc q inf_le_right, rsT_mulc q inf_le_left]
  ring

theorem isCob_sum {n : ℕ} (c : Fin n → C1 U) (hc : ∀ a, IsCob U (c a)) : IsCob U (∑ a, c a) := Finset.sum_induction _ (fun x => IsCob U x) (fun _ _ => isCob_add) isCob_zero (fun a _ => hc a)

theorem isCob_congr {c d : C1 U} (h : c = d) (hc : IsCob U c) : IsCob U d := h ▸ hc

end Coch

section Coc

theorem pbT_id {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ 𝟙 X ⁻¹ᵁ O₀ from h)]
  simp [resG, Scheme.Hom.appLE]
  (erw [Category.id_comp]) <;> rfl

theorem dlg_res {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  have e : ∀ s : Γ(B.left, L.U i ⊓ L.U j), pbT (𝟙 _) s (L.U i ⊓ L.U j) = s := fun s => by
    rw [pbT_id s le_rfl]; simp [resG]
  simp only [dlg, e]
  rw [rsT_le hT, map_mul, ← hδ.2.2 _ _ hT le_top]
  rfl

theorem s1 : ∀ (A : Type) [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left), L.IsLB → ∀ δ : Fld B.left, IsField ⊤ δ → IsCoc L.U (fun i j => dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) := by
  intro A _ B _ _ L hL δ hδ i j k
  have h1 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j := inf_le_left
  have h2 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h3 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  dsimp only
  rw [dlg_res B L δ hδ i j h1, dlg_res B L δ hδ j k h2, dlg_res B L δ hδ i k h3, ← hL.cocycle i j k]
  generalize res h1 (L.g i j) = a
  generalize res h2 (L.g j k) = b
  simp only [Units.val_mul, mul_inv_rev, hδ.2.1 _ le_top]
  linear_combination (-(δ _ ↑b * ↑b⁻¹)) * a.mul_inv + (-(δ _ ↑a * ↑a⁻¹)) * b.mul_inv

end Coc

theorem s2 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := GlobalTheory.T.abelian_cech_h1_basis_cocycles

theorem s3 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := GlobalTheory.T.logDerivatives_coboundary_coeffs_mem_maximalIdeal

section Main

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kapH : A →+* C1 U where
  toFun := kap q U
  map_one' := by funext i j; simp [kap, constFn]
  map_mul' := kap_mul q U
  map_zero' := kap_zero q U
  map_add' := kap_add q U

theorem kapH_apply (r : A) (i j : I) : kapH q U r i j = constFn q (U i ⊓ U j) r := rfl

theorem lin_eq {n : ℕ} (c : C1 U) (cc : Fin n → A) (b : Fin n → C1 U) :
    (fun i j => c i j - ∑ a, constFn q (U i ⊓ U j) (cc a) * b a i j) = c - ∑ a, kapH q U (cc a) * b a := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem cechCochain_sum_sub_sum_constFn_eq_ringHom {n N : ℕ} (c : Fin n → A) (φ : Fin n → C1 U) (t : Fin N → A) (z : Fin N → C1 U) :
    (fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j - ∑ k, constFn q (U i ⊓ U j) (t k) * z k i j) =
      ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U (t k) * z k := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem comb_eq {n : ℕ} (φ b : Fin n → C1 U) (P : Matrix (Fin n) (Fin n) A) (c : Fin n → A) :
    ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U ((c ᵥ* P) k) * b k =
      ∑ a, kapH q U (c a) * (φ a - ∑ k, kapH q U (P a k) * b k) := by

  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib,
  Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

end Main


open Classical in
theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  intro A _ _ _ B _ _ g L hab hsm hL hamp hK haff hfin v dd hinv hbasis c hc
  haveI := hfin
  let φ : Fin g → C1 L.U := fun a i j => dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)
  obtain ⟨b, -, hb⟩ := s2 A B g L.ι L.U hab hsm hL.cover haff
  have hφ : ∀ a, IsCoc L.U (φ a) := fun a => s1 A B L hL (dd a) (hinv a).1
  choose P hP using fun a => (hb (φ a) (hφ a)).exists
  have key : ∀ y : Fin g → A, IsCob L.U
      (∑ a, kapH B.hom L.U (y a) * φ a - ∑ k, kapH B.hom L.U ((y ᵥ* Matrix.of P) k) * b k) := by
    intro y
    rw [comb_eq]
    exact isCob_sum _ fun a => isCob_kap_mul _ (isCob_congr (lin_eq B.hom L.U (φ a) (P a) b) (hP a))
  have hmem : ∀ y : Fin g → A, (∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A) → ∀ a, y a ∈ maximalIdeal A := by
    intro y hy
    exact s3 A B g L hab hsm hL hamp hK haff hfin v dd hinv hbasis y g (y ᵥ* Matrix.of P) b hy
      (isCob_congr (cechCochain_sum_sub_sum_constFn_eq_ringHom B.hom L.U y φ (y ᵥ* Matrix.of P) b).symm (key y))
  have hdet : IsUnit (Matrix.of P).det := by
    by_contra hnd
    have h0 : IsLocalRing.residue A (Matrix.of P).det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnd))
    rw [RingHom.map_det] at h0
    obtain ⟨ybar, hy0, hyP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨y, rfl⟩ : ∃ y : Fin g → A, (fun a => IsLocalRing.residue A (y a)) = ybar :=
      ⟨fun a => (IsLocalRing.residue_surjective (ybar a)).choose,
        funext fun a => (IsLocalRing.residue_surjective (ybar a)).choose_spec⟩
    apply hy0
    funext a
    have hk : ∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A := by
      intro k
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrFun hyP k

      simpa [Matrix.vecMul, dotProduct, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    simpa [IsLocalRing.residue_eq_zero_iff] using hmem y hk a
  obtain ⟨e, he, heu⟩ := hb c hc
  refine ⟨e ᵥ* (Matrix.of P)⁻¹, ?_, ?_⟩
  · have h1 := key (e ᵥ* (Matrix.of P)⁻¹)
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one] at h1
    have h2 := isCob_sub (isCob_congr (lin_eq B.hom L.U c e b) he) h1
    exact isCob_congr (lin_eq B.hom L.U c _ φ).symm (isCob_congr (sub_sub_sub_cancel_right _ _ _) h2)
  · intro cc' hcc'
    have h3 := isCob_add (isCob_congr (lin_eq B.hom L.U c cc' φ) hcc') (key cc')
    have h4 : IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom (L.U i ⊓ L.U j) ((cc' ᵥ* Matrix.of P) a) * b a i j) :=
      isCob_congr (lin_eq B.hom L.U c _ b).symm (isCob_congr (sub_add_sub_cancel _ _ _) h3)
    have h5 := heu _ h4
    rw [← h5, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end GlobalTheory.DlogBasis
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

theorem _root_.GlobalTheory.T.sectionValueInFrame_linearCombination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  first | exact @GlobalTheory.Heat.exists_isValue_lin | exact GlobalTheory.Heat.exists_isValue_lin | (intros; apply GlobalTheory.Heat.exists_isValue_lin <;> assumption)
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


theorem _root_.GlobalTheory.T.exists_section_power_through_generating_lineBundleIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  first | exact @GlobalTheory.SecThroughIso.exists_sec_of_iso | exact GlobalTheory.SecThroughIso.exists_sec_of_iso | (intros; apply GlobalTheory.SecThroughIso.exists_sec_of_iso <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_derivation_fractionRing_of_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenDer.exists_derivation_fractionRing | exact GlobalTheory.GenDer.exists_derivation_fractionRing | (intros; apply GlobalTheory.GenDer.exists_derivation_fractionRing <;> assumption)
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


theorem _root_.GlobalTheory.T.value_at_invariantField_translate_sqZero : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  first | exact @GlobalTheory.VertCoeffRing.evalPt_tvE_mul | exact GlobalTheory.VertCoeffRing.evalPt_tvE_mul | (intros; apply GlobalTheory.VertCoeffRing.evalPt_tvE_mul <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.finite_minimiser_systems_smooth_cone : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  first | exact @GlobalTheory.Poinc.MinSys.finite_minimiser_systems | exact GlobalTheory.Poinc.MinSys.finite_minimiser_systems | (intros; apply GlobalTheory.Poinc.MinSys.finite_minimiser_systems <;> assumption)
end
