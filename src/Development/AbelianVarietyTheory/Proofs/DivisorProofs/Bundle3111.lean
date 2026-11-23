module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

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

namespace GlobalTheory.VertCoeff

theorem isWt_sub {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (V : Y.H.left.Opens) (f g : Γ(Y.H.left, V)) (hf : IsWt Y α V f)
    (hg : IsWt Y α V g) : IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' h h' hq hc
  have e : ∀ (b : Sp S ⟶ Y.H.left), valR b V (f - g) = valR b V f - valR b V g := fun b => by
    unfold valR; split_ifs <;> simp
  rw [e, e, hf S φ x x' c a a' ha ha' h h' hq hc, hg S φ x x' c a a' ha ha' h h' hq hc, mul_sub]

theorem lifts_sub_eq_sum_invFields : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (V : Q.P.A.left.Opens) (D : Derivation ℤ R R) (d d' : Fld Y.H.left), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d' → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f)) → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d' _ f)) → ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ a, IsWt Y 0 _ (h a)) ∧ ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, d O' f - d' O' f = ∑ a, rsT (h a) O' * dd a O' f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hdd V D d d' hd hd' hw hw'
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  let δ : Fld Y.H.left := fun O f => d O f - d' O f
  have hF : IsField (Y.q.left ⁻¹ᵁ V) δ := by
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
    · simp only [δ, hd.1.1 W hW, hd'.1.1 W hW]; ring
    · simp only [δ, hd.1.2.1 W hW, hd'.1.2.1 W hW]; ring
    · simp only [δ, hd.1.2.2 W W' h hW, hd'.1.2.2 W W' h hW, map_sub]
  have hC : ∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0 := fun O hO r => by
    simp only [δ, hd.2 O hO r, hd'.2 O hO r, sub_self]
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_invariant_field_coefficients_of_linear_vectorField R Y.H hsm n v dd hdd _ δ hF hC
  refine ⟨c, GlobalTheory.T.raynaudTorusWeight_zero_invariantField_coeffs R Q O oa Y n v dd hdd V δ hF hC
    (fun α V' hV' f hf => isWt_sub Y α _ _ _ (hw α V' hV' f hf) (hw' α V' hV' f hf)) c hc, fun O' hO' f => hc O' hO' f⟩

end GlobalTheory.VertCoeff
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
namespace GlobalTheory.LieRigid

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)

theorem dlg_sub {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {O T : B.left.Opens} (hO : O ≤ L.U i ⊓ L.U j) (hT : T ≤ O) :
    rsT (dlg B (𝟙 _) L δ i j O) T = rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T := by
  rw [GlobalTheory.CoverRefinementPullback.dlg_res' B L δ hδ i j (hT.trans hO)]
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, ← hδ.2.2 _ _ hT le_top,
    GlobalTheory.CoverRefinementPullback.resG_resG', GlobalTheory.CoverRefinementPullback.resG_resG']
  rfl

theorem lie_inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  intro R _ _ P w δ hδ K V jk hV hVj b hb
  have hδ1 : IsField ⊤ δ := hδ.1
  have hcob : IsCob P.L.U (fun j j' => dlg P.A (𝟙 _) P.L δ j j' (P.L.U j ⊓ P.L.U j')) := by
    refine GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps P.A.left P.L.ι K P.L.U V hV _
      (fun k k' => dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k'))
      (fun j k => rsT (dlg P.A (𝟙 _) P.L δ j (jk k) (P.L.U j ⊓ P.L.U (jk k))) (P.L.U j ⊓ V k))
      (fun j j' k => ?_) (fun j k k' => ?_) ⟨b, fun k k' => (hb k k').symm⟩
    · have t1 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ P.L.U j' := inf_le_left
      have t2 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ V k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have t3 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j' ⊓ V k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      rw [GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j j' (jk k) t1 (t3.trans (inf_le_inf le_rfl (hVj k)))
          (t2.trans (inf_le_inf le_rfl (hVj k)))]
      abel
    · have t1 : P.L.U j ⊓ V k ⊓ V k' ≤ V k ⊓ V k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have t2 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k := inf_le_left
      have t3 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      rw [dlg_sub _ _ δ hδ1 (jk k) (jk k') (inf_le_inf (hVj k) (hVj k')) t1,
        GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k')) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j (jk k) (jk k')
          (t2.trans (inf_le_inf le_rfl (hVj k))) (t1.trans (inf_le_inf (hVj k) (hVj k')))
          (t3.trans (inf_le_inf le_rfl (hVj k')))]
      abel
  obtain ⟨H, hH⟩ := hcob

  have hgp := GlobalTheory.Heat.DlogIndep.isGrpPullback_self P.A
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hgp (tv w)
  have hul : u.left = (tv w).left := (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hu)
  have hut : IsTangent u :=
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hgp _).2 (by rw [hu]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem _)
  have hee : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      φ DualNumber.eps * φ DualNumber.eps = 0 := fun S _ _ φ => by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφ : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      (algOverHom φ ≫ u : algOver R S ⟶ P.A) = (Chart.spMap (SqZero.epsTo R (φ DualNumber.eps) (hee S φ)) ≫ u) := by
    intro S _ _ φ
    have e : φ = SqZero.epsTo R (φ DualNumber.eps) (hee S φ) := DualNumber.algHom_ext (by simp [SqZero.epsTo, SqZero.dualTo_apply])
    conv_lhs => rw [e]
    rfl
  have h1 : u = 1 := GlobalTheory.Heat.DlogIndep.eq_one_of_coboundary P.isLB P.ktriv (DualNumber.eps : DualNumber R)
    DualNumber.eps_mul_eps u (fun j => -H j)
    (fun S _ _ φ y U hU => by
      rw [hφ S φ]; exact (GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y U hU).1)
    (fun S _ _ φ y j j' hj hj' => by
      rw [hφ S φ]
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (P.L.U j ⊓ P.L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hH j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (H j) _) = valHom (R := S) y.left _ hj (H j) := by
        rw [rsT, dite_eq_left inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (H j') _) = valHom (R := S) y.left _ hj' (H j') := by
        rw [rsT, dite_eq_left inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, GlobalTheory.Heat.DlogIndep.pbT_id, map_sub, map_mul, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (P.L.g j j').val * valHom (R := S) y.left _ hU (P.L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine ((GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg]
      linear_combination (φ DualNumber.eps * valHom (R := S) y.left _ hU (P.L.g j j').val) * e₁ +
        (-(φ DualNumber.eps * valHom (R := S) y.left _ hU (δ _ (P.L.g j j').val))) * e₂)
  have h2 : tv w = tv (0 : TanM (𝟙 (Sp R)) P.A) := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_zero, ← hu, h1, map_one]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext h2

end GlobalTheory.LieRigid
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
namespace GlobalTheory.HeatMod.TorUniq
open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)
open GlobalTheory.HeatMod.TorField

theorem exists_addHom_of_kills_wt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd e he
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  have hc : IsLieComb e u (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) := (GlobalTheory.SqZero.isLieComb_iff_lieExp e _).2 rfl
  have ht := GlobalTheory.Reg.isTangent_of_isLieComb hb.1 hc
  have hq : GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q = 1 :=
    Over.OverMorphism.ext (GlobalTheory.T.spec_hom_ext_of_localization_at_primes _ _ _ _ fun P _ => GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit R Q O oa Y n (fun a => v a) u hb.1 hu dd hd e he _ _)
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit R Q O oa Y _ ht hq
  refine ⟨ℓ, fun α V f hf => ?_⟩
  show combF Y.H.hom dd e _ f = _
  refine sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := GlobalTheory.SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => GlobalTheory.SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g _ hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (e i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) _ a₁ Finset.univ
  have E0 := congrArg (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ ·) hℓ.symm
  simp only [GlobalTheory.SqZero.comp_lieExp, ← Category.assoc] at E0
  rw [GlobalTheory.SqZero.lieExp] at E0
  rw [← E0] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left (Y.q.left ⁻¹ᵁ V) s = inl (valR g _ s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add (f := _)]; rfl
  simp only [a₃, hψ, hu'] at k'

  rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg, combF,
  GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

end GlobalTheory.HeatMod.TorUniq
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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TermDescend

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ₀ σ₁ σ₂ τ₀ τ₁ τ₂ a b h₀ h₁ h₂ H z J hJ
  obtain ⟨Z, p, w, y, hw, hp, hinj, hy⟩ := GlobalTheory.RayLift.exists_flat_lift R Q O oa Y z
  subst hw
  obtain ⟨J', hJ', hJJ⟩ := exists_good Q.P.L Q.P.isLB w (K := (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left)
    (fun ψ => p ≫ ψ) J (fun ψ ψ' e => by rw [(cancel_epi p).1 e]) (fun ψ => by
      rw [Scheme.Hom.comp_apply]; exact hJ ψ)
  have hfun : (fun ψ => J' (p ≫ ψ)) = J := funext hJJ
  let T : Over (Sp R) := Over.mk (y ≫ Y.H.hom)
  let x : T ⟶ Y.H := Over.homMk y rfl
  let v : (Z.presheaf.stalk w)ˣ := val ((Y.Φ T x).s α) (𝟙 _) w J'
  have e₀ : sval τ₀ y w J' = sval σ₀ (y ≫ Y.q.left) w J' * v.val := h₀ T x w J' hJ'
  have e₁ : sval τ₁ y w J' = sval σ₁ (y ≫ Y.q.left) w J' * v.val := h₁ T x w J' hJ'
  have e₂ : sval τ₂ y w J' = sval σ₂ (y ≫ Y.q.left) w J' * v.val := h₂ T x w J' hJ'
  have E := H Z y w J' hJ'
  have hH : y ≫ Y.H.hom = p ≫ ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) := by
    rw [← Category.assoc, ← hy, Category.assoc, Over.w Y.q]
  rw [e₀, e₁, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul] at E
  have E' := (Units.mul_left_inj _).1 E
  rw [hH, hy, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ',
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial,
    GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial, hfun, ← map_mul, ← map_mul, ← map_add] at E'
  exact hinj E'

end GlobalTheory.TermDescend
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

theorem _root_.GlobalTheory.T.kodairaSpencer_descent_of_torus_invariant_lifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) → (∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → KSRel Dd.toPre.P.A (𝟙 Dd.toPre.P.A.left) Dd.toPre.P.L e ⇑D (P * C * Pᵀ) := by
  first | exact @GlobalTheory.HeatDescend.ksRel_of_invLifts | exact GlobalTheory.HeatDescend.ksRel_of_invLifts | (intros; apply GlobalTheory.HeatDescend.ksRel_of_invLifts <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_invariant_tangent_basis_raynaudExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayTan.exists_basis_isInv | exact GlobalTheory.RayTan.exists_basis_isInv | (intros; apply GlobalTheory.RayTan.exists_basis_isInv <;> assumption)
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

theorem _root_.GlobalTheory.T.heatOperator_period_defect_isCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_cocycle | exact GlobalTheory.HeatDefect.defect_cocycle | (intros; apply GlobalTheory.HeatDefect.defect_cocycle <;> assumption)
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

noncomputable section

namespace GlobalTheory.RayFlatDesc

theorem gs_sub_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

theorem gs_zero_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  intro R _ _ Q O _ _ _ oa Y k ρ τ a b H Z r z J hJ
  have := GlobalTheory.RayTan.smooth_H R Q O oa Y
  have hL : Q.P.L.IsLB := Q.P.isLB
  have key : ∀ j : Fin 1 → Q.P.L.ι,
      (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom a) * ρ.f j -
        (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom b) * τ.f j = 0 := by
    intro j
    apply GlobalTheory.Mum.fst_generic_app_injective Y.H.hom _
    rw [map_zero]
    apply fn_ext
    intro y hy
    have hy' : pullback.fst Y.H.hom (jK R) y ∈
        (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U j := hy
    have hw : pullback.fst Y.H.hom (jK R) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j := hy
    obtain ⟨J', hJ', e⟩ := exists_good Q.P.L hL y (fun _ : Unit => pullback.fst Y.H.hom (jK R) ≫ Y.q.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hw 0)
    have ej : ∀ i : Fin 1, J' (pullback.fst Y.H.hom (jK R) ≫ Y.q.left) = j i := fun i => by
      rw [Subsingleton.elim i 0]; exact e ()
    have h1 := H _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition y J' hJ'
    rw [sval_of ρ _ y J' j ej, sval_of τ _ y J' j ej] at h1
    rw [gs_pull (𝟙 _) (pullback.fst Y.H.hom (jK R)) y _ hy', Category.id_comp, gs_zero_of _ _ _,
      gs_sub_of _ _ _ hy', gs_mul _ _ _ hy', gs_mul _ _ _ hy', gs_res _ _ _ hy', gs_res _ _ _ hy']
    exact sub_eq_zero.2 h1
  have hm : r z ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U
      (fun _ => J (r ≫ Y.q.left)) :=
    Set.mem_iInter.2 fun _ => hJ (r ≫ Y.q.left)
  have e := congrArg (gs r z _) (key fun _ => J (r ≫ Y.q.left))
  rw [gs_sub_of _ _ _ hm, gs_mul _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_zero_of _ _ _,
    sub_eq_zero] at e
  rw [sval_of ρ r z J _ (fun _ => rfl), sval_of τ r z J _ (fun _ => rfl)]
  exact e

end GlobalTheory.RayFlatDesc
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

theorem _root_.GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.GcDual.exists_dual_forms | exact GlobalTheory.GcDual.exists_dual_forms | (intros; apply GlobalTheory.GcDual.exists_dual_forms <;> assumption)
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

theorem _root_.GlobalTheory.T.stalkDerivation_mem_span_invariant_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  first | exact @GlobalTheory.StalkDerSpan.stalk_derivation_span | exact GlobalTheory.StalkDerSpan.stalk_derivation_span | (intros; apply GlobalTheory.StalkDerSpan.stalk_derivation_span <;> assumption)
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

theorem _root_.GlobalTheory.T.invariant_fields_cech_h1_relation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  first | exact @GlobalTheory.CoverRefinementPullback.main | exact GlobalTheory.CoverRefinementPullback.main | (intros; apply GlobalTheory.CoverRefinementPullback.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.Sep.exists_isAct : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  intro g n F W Z i X₁
  obtain ⟨c, hc, pr, h1, h2, h3⟩ := X₁.sharp
  choose act hact using fun a : Matrix (Fin 8) (Fin 8) ℤ =>
    (h2 X₁.ρ.P.A fun u => (List.ofFn fun v => pr v ^ a u v).prod).exists
  exact ⟨act, c, hc, pr, h1, h2, h3, hact⟩
end
