module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
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
import Mathlib.Tactic.Polynomial.Basic
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullbackWeightZero

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)), IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y V f S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero

theorem h1cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := GlobalTheory.T.invariant_fields_cech_h1_relation

theorem liepush : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := GlobalTheory.T.exists_logDeriv_polarization_raynaud_eq_pullback

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (c' : Fin g → R) (N : Fin g → Fin n → R)
    (M : Fin n → Fin g → R) (hNM : ∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) (X : Fin g → Γ₀) :
    ∑ a, κ (c' a) * X a = ∑ b, κ (∑ a, c' a * N a b) * ∑ a', κ (M b a') * X a' := by
  have e : ∀ a', ∑ b, (∑ a, c' a * N a b) * M b a' = c' a' := by
    intro a'
    simp_rw [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hNM]
    simp
  simp_rw [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
  rw [Finset.sum_comm]

  simp_rw [← Finset.sum_mul, ← map_sum, e]

theorem h1_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin n → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', pbT Y.q.left (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') + (pbT Y.q.left (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - pbT Y.q.left (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz
  obtain ⟨g, w, dd', M, N, hw, hsp, hNM, hdl⟩ := liepush R Dd O oa Y n v dd hdd
  obtain ⟨c', y, hc'⟩ := h1cover R Dd g w dd' hw hsp J V j hcov hle z hz
  refine ⟨fun b => ∑ a, c' a * N a b, y, fun i i' => ?_⟩
  have hW : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
      Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
    Y.q.left.preimage_mono (inf_le_inf (hle i) (hle i'))
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  rw [hc' i i', GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_right le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_left le_rfl]
  congr 1
  simp only [hdl _ _ _ _ hW, GlobalTheory.KS.pbT_sum, GlobalTheory.KS.pbT_mul]
  simp only [GlobalTheory.KS.pbT_constFn _ _ hW, GlobalTheory.KS.pbT_constFn _ Y.q.left (O₀ := V i ⊓ V i') (O := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (inf_le_inf (hle i) (hle i')) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) c' N M hNM _

theorem exists_comb_dlg_add_cob : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz hw
  have hA := descend R Dd.toPre O oa Y
  have hB := isWt_pbT R Dd.toPre O oa Y
  choose z' hz' using fun i i' => (hA (V i ⊓ V i') (z i i') (hw i i')).exists
  have hcoc : IsCoc V z' := by
    intro i i' i''
    apply (hA (V i ⊓ V i' ⊓ V i'') _ (hB _ (rsT (z' i i'') (V i ⊓ V i' ⊓ V i'')))).unique _ rfl
    rw [GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl, GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) le_rfl,
      GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) le_rfl]
    have e1 : rsT (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i']; exact GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left _
    have e2 : rsT (z i' i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i' i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i' i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_right) inf_le_right) _
    have e3 : rsT (z i i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_left) inf_le_right) _
    rw [← e1, ← e2, ← e3]
    exact hz i i' i''
  obtain ⟨c, y', hc⟩ := h1_pull R Dd O oa Y n v dd hdd J V j hcov hle z' hcoc
  refine ⟨c, fun i => pbT Y.q.left (y' i) (Y.q.left ⁻¹ᵁ V i), fun i => hB _ _, fun i i' => ?_⟩
  rw [GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left, GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_right, ← hc i i']
  exact (hz' i i').symm

end GlobalTheory.PullbackWeightZero
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
namespace GlobalTheory.Heat.SymReg

theorem sum_sum_bilin_regroup {I₁ I₂ J₁ J₂ R : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂] [CommRing R]
    (x : I₁ → R) (y : I₂ → R) (L : J₁ → J₂ → R) (u : J₁ → I₁ → R) (w : J₂ → I₂ → R) :
    ∑ i, ∑ j, x i * y j * ∑ a, ∑ e, L a e * u a i * w e j
      = ∑ a, ∑ e, L a e * (∑ i, x i * u a i) * (∑ j, y j * w e j) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ a, ∑ e, x i * y j * (L a e * u a i * w e j)
      = ∑ i, ∑ a, ∑ e, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ i, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ j, ∑ i, L a e * (x i * u a i) * (y j * w e j) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (Λ : Matrix (Fin n) (Fin n) F) (W : P₀.A.left.Opens), IsAffineOpen W → ⊤ ≤ ξ ⁻¹ᵁ W → (∀ f f' : Γ(P₀.A.left, W), ∃ h : Γ(P₀.A.left, W), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) → ∀ a e, ∃ h : Γ(P₀.A.left, W), valR ξ W h = Λ a e := by
  intro K _ _ P₀ n v dd hinv F _ ψ ξ _ _ δ hδ Λ W hW hξW hΛ a e
  let φ : Γ(P₀.A.left, W) →+* F :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (ξ.appLE W ⊤ hξW).hom
  have hφ : ∀ f, valR ξ W f = φ f := fun f => by
    unfold valR; rw [dite_eq_left hξW]; rfl
  have hδ' : ∀ b x, φ (dd b W x) = δ b (φ x) := fun b x => by
    rw [← hφ, ← hφ]; exact hδ b W x hξW
  obtain ⟨N, g, f, hgf⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW a
  obtain ⟨N', g', f', hgf'⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW e
  choose h hh using fun (i : Fin N) (j : Fin N') => hΛ (f i) (f' j)
  have hh' : ∀ i j, φ (h i j) = ∑ a', ∑ e', Λ a' e' * δ a' (φ (f i)) * δ e' (φ (f' j)) := by
    intro i j; rw [← hφ, hh]; simp only [hφ]
  have key : ∀ b, ∑ i, φ (g i) * δ b (φ (f i)) = if a = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf b)

    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  have key' : ∀ b, ∑ j, φ (g' j) * δ b (φ (f' j)) = if e = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf' b)

    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  refine ⟨∑ i, ∑ j, g i * g' j * h i j, ?_⟩
  rw [hφ]

  simp only [map_sum, map_mul, hh']
  rw [sum_sum_bilin_regroup (fun i => φ (g i)) (fun j => φ (g' j)) Λ (fun a' i => δ a' (φ (f i)))
    (fun e' j => δ e' (φ (f' j)))]
  simp only [key, key', mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.Heat.SymReg
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

theorem _root_.GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  first | exact @GlobalTheory.LieRigid.lie_inj | exact GlobalTheory.LieRigid.lie_inj | (intros; apply GlobalTheory.LieRigid.lie_inj <;> assumption)
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

theorem _root_.GlobalTheory.T.torusInvariant_lifts_sub_eq_sum_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (V : Q.P.A.left.Opens) (D : Derivation ℤ R R) (d d' : Fld Y.H.left), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d' → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f)) → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d' _ f)) → ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ a, IsWt Y 0 _ (h a)) ∧ ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, d O' f - d' O' f = ∑ a, rsT (h a) O' * dd a O' f := by
  first | exact @GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields | exact GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields | (intros; apply GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_addHom_invariantField_kills_weightZero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  first | exact @GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | exact GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero | (intros; apply GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero <;> assumption)
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
open ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.raynaud_section_identity_of_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  first | exact @GlobalTheory.RayFlatDesc.main | exact GlobalTheory.RayFlatDesc.main | (intros; apply GlobalTheory.RayFlatDesc.main <;> assumption)
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

theorem _root_.GlobalTheory.T.fourierTerm_identity_descends_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  first | exact @GlobalTheory.TermDescend.main | exact GlobalTheory.TermDescend.main | (intros; apply GlobalTheory.TermDescend.main <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_basis_pullback_matrix_invariantFields_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R) (Qm : Matrix (Fin n) (Fin g) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) ∧ P * Qm = 1 ∧ ∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W := by
  first | exact @GlobalTheory.InvFactor.exists_basis_pull_matrix | exact GlobalTheory.InvFactor.exists_basis_pull_matrix | (intros; apply GlobalTheory.InvFactor.exists_basis_pull_matrix <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

namespace GlobalTheory.Poinc.Sep

theorem pullback_map_left_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (F : G ⟶ G) :
    ((Over.pullback f).map F).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ F.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_left_snd {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (F : G ⟶ G) :
    ((Over.pullback f).map F).left ≫ pullback.snd G.hom f = pullback.snd G.hom f :=
  pullback.lift_snd _ _ _



set_option backward.isDefEq.respectTransparency false in
theorem exists_unif_trait : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), jK V ≫ ξ = spMap e ≫ Y.pt → (ξ ⁻¹' abLocus O.G).Nonempty → ∃ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback ξ).obj O.G)) (β : A.A.left ⟶ ((Over.pullback Y.pt).obj O.G).left), IsGrpPullback A.A ((Over.pullback Y.pt).obj O.G) (spMap e) β ∧ LBIso A.L ((O.L.L.pull (pullback.fst O.G.hom Y.pt)).pull β) ∧ ∀ F : O.G ⟶ O.G, IsMonHom F → ∃ E : EndU U.toUnifPre, E.aA.left ≫ β = β ≫ ((Over.pullback Y.pt).map F).left := by
  intro X₁ Y U₀ EE O V _ _ _ hc hch ξ e he hab
  obtain ⟨D, A, U, hl, -⟩ := O.unif V inferInstance inferInstance hc ξ hab
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  let κ : A.A.left ⟶ ((Over.pullback ξ).obj O.G).left :=
    U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V)
  have hκ : IsGrpPullback A.A ((Over.pullback ξ).obj O.G) (jK V) κ :=
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso U.gen.symm).comp
      (isGrpPullback_pullback ((Over.pullback ξ).obj O.G) (jK V))).congr (Category.id_comp _) rfl
  have hm : IsGrpPullback A.A O.G (spMap e ≫ Y.pt) (κ ≫ pullback.fst O.G.hom ξ) :=
    (hκ.comp (isGrpPullback_pullback O.G ξ)).congr he rfl
  have hp := isGrpPullback_pullback O.G Y.pt
  have w : (κ ≫ pullback.fst O.G.hom ξ) ≫ O.G.hom = (A.A.hom ≫ spMap e) ≫ Y.pt :=
    hm.1.w.trans (Category.assoc _ _ _).symm
  let β : A.A.left ⟶ pullback O.G.hom Y.pt := pullback.lift _ _ w
  have hβf : β ≫ pullback.fst O.G.hom Y.pt = κ ≫ pullback.fst O.G.hom ξ := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd O.G.hom Y.pt = A.A.hom ≫ spMap e := pullback.lift_snd _ _ _
  have hio : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 A.A.left := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hoi : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨D, A, U, β, hp.cancel (hm.congr rfl hβf.symm) hβs, ?_, fun F hF => ?_⟩
  · have h₁ : LBIso A.L (A.L.pull (𝟙 A.A.left)) :=
      (GlobalTheory.PolBaseChange.lbIso_refl A.isLB).chartPull (chartPullId A.L)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A.L _ _ rfl)
    have h₂ : LBIso (A.L.pull (𝟙 A.A.left)) (U.LG.L.pull κ) :=
      GlobalTheory.GenSpread.lbIso_pull_comp U.gen.inv.left hio.symm rfl U.ext
    have h₃ : LBIso (U.LG.L.pull κ) (O.L.L.pull (κ ≫ pullback.fst O.G.hom ξ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso hl κ rfl
    have h₄ : LBIso (O.L.L.pull (κ ≫ pullback.fst O.G.hom ξ)) ((O.L.L.pull (pullback.fst O.G.hom Y.pt)).pull β) :=
      GlobalTheory.GenSpread.lbIso_pull_pull O.L.isLB β hβf.symm
    exact LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₁
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₂
        (LBIso.trans (pull_isLB U.LG.isLB _) (pull_isLB O.L.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₃ h₄))
  · have hFξ : IsMonHom ((Over.pullback ξ).map F) :=
      Functor.map.instIsMonHom (F := Over.pullback ξ) (f := F)
    have hFj : IsMonHom ((Over.pullback (jK V)).map ((Over.pullback ξ).map F)) :=
      Functor.map.instIsMonHom (F := Over.pullback (jK V)) (f := (Over.pullback ξ).map F)
    have hright : IsMonHom ((Over.pullback (jK V)).map ((Over.pullback ξ).map F) ≫ U.gen.hom) :=
      CategoryTheory.instIsMonHomComp _ _
    have hconj : IsMonHom (U.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback ξ).map F) ≫ U.gen.hom) :=
      CategoryTheory.instIsMonHomComp _ _
    obtain ⟨E, -, hE⟩ := exists_degenerationEndomorphism_of_admissibleBase V _ ⟨inferInstance, inferInstance, inferInstance, hc⟩ D A _
      (IsSemiAbelian.pullback _ _ O.semi) U ((Over.pullback ξ).map F)
      (U.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback ξ).map F) ≫ U.gen.hom) hFξ hconj
      (by rw [Iso.hom_inv_id_assoc])
    refine ⟨E, ?_⟩
    have n₁ := pullback_map_left_fst (jK V) ((Over.pullback ξ).obj O.G) ((Over.pullback ξ).map F)
    have n₂ := pullback_map_left_fst ξ O.G F
    have n₃ := pullback_map_left_fst Y.pt O.G F
    have n₄ := pullback_map_left_snd Y.pt O.G F
    have a₁ : E.aA.left ≫ κ = κ ≫ ((Over.pullback ξ).map F).left := by
      rw [hE]
      show (U.gen.inv.left ≫ ((Over.pullback (jK V)).map ((Over.pullback ξ).map F)).left ≫ U.gen.hom.left) ≫
        U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V) =
        (U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V)) ≫ _
      rw [Category.assoc, Category.assoc, ← Category.assoc U.gen.hom.left, hoi, Category.id_comp, n₁, Category.assoc]
    apply pullback.hom_ext
    · calc (E.aA.left ≫ β) ≫ pullback.fst O.G.hom Y.pt = (E.aA.left ≫ κ) ≫ pullback.fst O.G.hom ξ := by
            exact (Category.assoc _ _ _).trans ((congrArg (E.aA.left ≫ ·) hβf).trans (Category.assoc _ _ _).symm)
        _ = (κ ≫ pullback.fst O.G.hom ξ) ≫ F.left := by
            rw [a₁]; exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) n₂).trans (Category.assoc _ _ _).symm)
        _ = (β ≫ ((Over.pullback Y.pt).map F).left) ≫ pullback.fst O.G.hom Y.pt := by
            rw [← hβf]; exact (Category.assoc _ _ _).trans ((congrArg (β ≫ ·) n₃.symm).trans (Category.assoc _ _ _).symm)
    · calc (E.aA.left ≫ β) ≫ pullback.snd O.G.hom Y.pt = A.A.hom ≫ spMap e := by
            rw [Category.assoc, hβs, ← Category.assoc, Over.w]
        _ = (β ≫ ((Over.pullback Y.pt).map F).left) ≫ pullback.snd O.G.hom Y.pt := by
            exact hβs.symm.trans ((congrArg (β ≫ ·) n₄.symm).trans (Category.assoc _ _ _).symm)

end GlobalTheory.Poinc.Sep
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

namespace GlobalTheory.GSep

theorem unit_ne_zero_dvd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.GSep
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem GMem.exists_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.GSep

end
end
