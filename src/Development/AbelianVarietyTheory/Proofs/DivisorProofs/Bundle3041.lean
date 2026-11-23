module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
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

namespace GlobalTheory.RayTan

theorem smooth_H : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Smooth Y.H.hom := by
  intro R _ _ Q O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  obtain ⟨n, ⟨v⟩⟩ := GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme R Y.H (smooth_H R Q O oa Y)
  choose dd hdd using fun a => GlobalTheory.T.exists_invariantVectorField_of_tangentVector_origin R Y.H (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayTan
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

namespace GlobalTheory.HeatDescend

open GlobalTheory.KS

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (P : Matrix (Fin g) (Fin n) R)
    (C : Matrix (Fin n) (Fin n) R) (X Z : Fin g → Γ₀) :
    ∑ a, ∑ b, κ (C a b) * (∑ c', κ (P c' b) * X c') * ∑ c, κ (P c a) * Z c =
      ∑ c, ∑ c', κ ((P * C * Pᵀ) c c') * X c' * Z c := by

  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c)
      = ∑ b, ∑ a, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ c', ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = ∑ c, ∑ c', ∑ b, ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => ?_
        ring

theorem pbT_id' {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U)) {O : X.Opens} (h : O ≤ U) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT_of_le (𝟙 X) (show O ≤ (𝟙 X) ⁻¹ᵁ U from h), rsT_of_le h]
  rfl

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)) :
    IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

section General

variable {R : Type} [CommRing R] {G B : Over (Sp R)} (q : G ⟶ B)

theorem exists_lift (hinj : ∀ (O : B.left.Opens) (f f' : Γ(B.left, O)),
      pbT q.left f (q.left ⁻¹ᵁ O) = pbT q.left f' (q.left ⁻¹ᵁ O) → f = f')
    (D : R → R) (V : B.left.Opens) (d : Fld G.left) (hd : IsLift G D (q.left ⁻¹ᵁ V) d)
    (hdesc : ∀ O, O ≤ V → ∀ f : Γ(B.left, O), ∃ f' : Γ(B.left, O),
      pbT q.left f' (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O))) :
    ∃ dB : Fld B.left, IsLift B D V dB ∧ ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
  classical
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  let dB : Fld B.left := fun O f => if h : O ≤ V then (hdesc O h f).choose else 0
  have hB : ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
    intro O h f
    simp only [dB, dif_pos h]
    exact (hdesc O h f).choose_spec
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hd
  refine ⟨dB, ⟨⟨fun O h f f' => hinj O _ _ ?_, fun O h f f' => hinj O _ _ ?_, fun O O' h' h f => hinj O' _ _ ?_⟩,
    fun O h r => hinj O _ _ ?_⟩, hB⟩
  · rw [pbT_add, hB O h, hB O h, hB O h, pbT_add, h1 _ (q.left.preimage_mono h)]
  · rw [pbT_add, pbT_mul, pbT_mul, hB O h, hB O h, hB O h, pbT_mul, h2 _ (q.left.preimage_mono h)]
  · have hp : q.left ⁻¹ᵁ O' ≤ q.left ⁻¹ᵁ O := q.left.preimage_mono h'
    rw [hB O' (h'.trans h), ← rsT_of_le h', ← rsT_of_le h', pbT_rsT _ h' le_rfl, pbT_rsT _ h' le_rfl,
      ← rsT_pbT q.left le_rfl hp, ← rsT_pbT q.left le_rfl hp (dB O f), hB O h, rsT_of_le hp, rsT_of_le hp]
    exact h3 _ _ hp (q.left.preimage_mono h) _
  · rw [hB O h, pbT_constFn _ _ le_rfl, pbT_constFn _ _ le_rfl, hq, h4 _ (q.left.preimage_mono h)]

theorem dlg_pull {g : ℕ} (L : LB B.left) (δ : Fld G.left) (e : Fin g → Fld B.left) (he : ∀ c, IsField ⊤ (e c))
    (p : Fin g → R) (hδ : ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V),
      δ W (pbT q.left f W) = ∑ c, constFn G.hom W (p c) * pbT q.left (e c V f) W)
    (i i' : L.ι) (O : B.left.Opens) (h : O ≤ L.U i ⊓ L.U i') :
    dlg G q.left L δ i i' (q.left ⁻¹ᵁ O) =
      ∑ c, constFn G.hom _ (p c) * pbT q.left (dlg B (𝟙 _) L (e c) i i' O) (q.left ⁻¹ᵁ O) := by
  unfold dlg
  rw [← pbT_rsT q.left h le_rfl, hδ O _ le_rfl, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pbT_mul, pbT_id' _ h, pbT_id' _ h, pbT_rsT q.left h le_rfl, _root_.mul_assoc]

end General

theorem ksRel_of_invLifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) → (∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → KSRel Dd.toPre.P.A (𝟙 Dd.toPre.P.A.left) Dd.toPre.P.L e ⇑D (P * C * Pᵀ) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd _ g w e P he hP D J V j d hcov hle hlift hwt C hC
  have hA := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero R Dd.toPre O oa Y
  have hinj : ∀ (U : Dd.toPre.P.A.left.Opens) (f f' : Γ(Dd.toPre.P.A.left, U)),
      pbT Y.q.left f (Y.q.left ⁻¹ᵁ U) = pbT Y.q.left f' (Y.q.left ⁻¹ᵁ U) → f = f' := fun U f f' h =>
    (hA U _ (isWt_pbT Y U f')).unique h rfl
  choose dB hB hB' using fun i => exists_lift Y.q hinj D (V i) (d i) (hlift i) fun U hU f =>
    (hA U _ (hwt i 0 U (Y.q.left.preimage_mono hU) _ (isWt_pbT Y U f))).exists
  refine ⟨J, V, j, dB, hcov, hle, hB, fun i i' U hU f => hinj U _ _ ?_⟩
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  have hL : U ≤ Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i') := hU.trans (inf_le_inf (hle i) (hle i'))
  rw [pbT_sub, hB' i U (hU.trans inf_le_left), hB' i' U (hU.trans inf_le_right),
    hC i i' _ (Y.q.left.preimage_mono hU)]
  simp only [fun b => dlg_pull Y.q Dd.toPre.P.L (dd b) e (fun c => (he c).1) (fun c => P c b) (hP b) _ _ U hL,
    fun a => hP a U _ le_rfl f, pbT_sum, pbT_mul, pbT_constFn _ Y.q.left (O₀ := U) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) P C _ _

end GlobalTheory.HeatDescend
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

theorem _root_.GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  first | exact @GlobalTheory.InvCoefUniq.coef_eq_zero | exact GlobalTheory.InvCoefUniq.coef_eq_zero | (intros; apply GlobalTheory.InvCoefUniq.coef_eq_zero <;> assumption)
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

theorem _root_.GlobalTheory.T.invariant_vectorField_of_tangent_vector_linear_combination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) → ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  first | exact @GlobalTheory.Heat.InvComb.isInv_comb | exact GlobalTheory.Heat.InvComb.isInv_comb | (intros; apply GlobalTheory.Heat.InvComb.isInv_comb <;> assumption)
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

theorem _root_.GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  first | exact @GlobalTheory.Heat.FormalDer.main | exact GlobalTheory.Heat.FormalDer.main | (intros; apply GlobalTheory.Heat.FormalDer.main <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  first | exact @GlobalTheory.WtLift.exists_isWt_lift | exact GlobalTheory.WtLift.exists_isWt_lift | (intros; apply GlobalTheory.WtLift.exists_isWt_lift <;> assumption)
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

theorem _root_.GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  first | exact @GlobalTheory.Heat.sval_eq_of_localIdentity | exact GlobalTheory.Heat.sval_eq_of_localIdentity | (intros; apply GlobalTheory.Heat.sval_eq_of_localIdentity <;> assumption)
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
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatDefect

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem val_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem good_comp {X Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Z) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem gs_scal (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (c : R) : (m.left.stalkMap z).hom (gs (𝟙 _) (m.left z) ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) := by
  rw [← gs_comp_stalk m.left (𝟙 _) z ⊤ trivial, Category.comp_id]
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  have e₁ := gs_pull m.left (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  have e₂ := gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  rw [Over.w m] at e₁
  rw [Category.id_comp] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem shiftEq_at {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α} {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R}
    (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (m ≫ DegPre.prB Q (FractionRing R)).left z J =
      (val u m.left z J).val *
          sval σ (m ≫ DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom c) *
          sval σ₂ (m ≫ DegPre.prB Q (FractionRing R)).left z J := by
  have e := congrArg (m.left.stalkMap z).hom (H u hu hc (m.left z) _ (good_comp m.left z hJ))
  rw [Over.comp_left, Over.comp_left, Over.comp_left, sval_comp_stalk _ _ _ _ hJ, sval_comp_stalk _ _ _ _ hJ,
    sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul, gs_scal]
  congr 2
  have := val_comp_stalk u (𝟙 _) m.left z hJ
  rw [Category.comp_id] at this
  exact this.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem scal_injective (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    Function.Injective (fun r : R => gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom r)) := by
  let F := FractionRing R
  let χ : F →+* (DegPre.BF Q F).left.presheaf.stalk z :=
    ((DegPre.BF Q F).left.presheaf.germ ⊤ z trivial).hom.comp
      ((fst (TF (R := R) F) Q.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have hT : (DegPre.BF Q F).hom = (fst (TF (R := R) F) Q.P.A).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Over.w (fst (TF (R := R) F) Q.P.A)]
    show _ ≫ (jFK (R := R) F ≫ jK R) = _
    rw [jFK, jK, ← Spec.map_comp]
    rfl
  have key : ∀ r : R, gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q F).hom r) = χ (algebraMap R F r) := by
    intro r
    unfold ReciprocityTheory.ChartRestriction.G.Out.scal
    rw [hT, gs_eq _ z ⊤ trivial]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R F))
    have n' := congrArg (fun f => f.hom r) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
    simp only [χ, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, n']
    rfl
  intro a b hab
  have : χ (algebraMap R F a) = χ (algebraMap R F b) := (key a).symm.trans (hab.trans (key b))
  exact IsFractionRing.injective R F (χ.injective this)
end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem sval_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {x y : Q.X} (e : x = y)
    (he : Q.SecB k x = Q.SecB k y) (σ : Q.SecB k x) {Z : Scheme.{0}} (r : Z ⟶ Q.P.A.left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) : sval (cast he σ) r z J = sval σ r z J := by
  subst e; rfl

theorem tActs_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R}
    {h : Heat Y.H Y.q.left Q.P.L dd D} {k : ℕ} {x y : Q.X} (e : x = y) (he : Q.SecB k x = Q.SecB k y)
    {σ σ' : Q.SecB k x} (H : TActs Y h k x σ σ') : TActs Y h k y (cast he σ) (cast he σ') := by
  subst e; exact H

theorem scal_add {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) (a b : R) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom (a + b)) =
      gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom a) +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom b) := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  rw [map_add (f := _), map_add (f := _)]
  exact gs_add (𝟙 _) z ⊤ trivial _ _

theorem scal_zero {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom 0) = 0 := by
  have := scal_add Q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem defect_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h c hB hD k hk mu mu' α
  obtain ⟨σ, σ₁, σ₂, he, h1, h2, h3, z, J, hJ, hs⟩ := GlobalTheory.T.exists_integral_sections_thetaShift_triple R Dd k hk mu mu' α
  have e : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  obtain ⟨σ', a1⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k α σ
  obtain ⟨σ₁', a2⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₁
  obtain ⟨σ₂', a3⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₂
  have d1 := hD k mu α σ σ' σ₁ σ₁' hk h1 a1 a2
  have d2 := hD k mu' (α + k • mu) σ₁ σ₁' σ₂ σ₂' hk h2 a2 a3
  have d3 := hD k (mu + mu') α σ σ' _ _ hk h3 a1 (tActs_cast e he a3)
  obtain ⟨⟨u1, hu1, hc1⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  obtain ⟨⟨u2, hu2, hc2⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu' (α + k • mu)
  obtain ⟨⟨u3, hu3, hc3⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k (mu + mu') α
  have E1 := shiftEq_at d1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E10 := shiftEq_at h1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E2 := shiftEq_at d2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E20 := shiftEq_at h2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E3 := shiftEq_at d3 u3 hu3 hc3 (𝟙 _) z J hJ
  have E30 := shiftEq_at h3 u3 hu3 hc3 (𝟙 _) z J hJ
  simp only [Category.id_comp, scal_zero, zero_mul, add_zero] at E1 E10 E2 E20 E3 E30
  rw [sval_cast e he, sval_cast e he] at E3
  rw [sval_cast e he] at E30
  rw [← Category.assoc, UUA.trF_add, add_comm mu' mu] at E1 E10
  set s := sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set s' := sval σ' (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set v1 := (val u1 (DegPre.trF Dd.toPre (FractionRing R) mu').left z J).val
  set v2 := (val u2 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set v3 := (val u3 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set p1 := sval σ₁ (DegPre.trF Dd.toPre (FractionRing R) mu' ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set q := sval σ₂ (DegPre.prB Dd.toPre (FractionRing R)).left z J
  set C1 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu α))
  set C2 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu' (α + k • mu)))
  set C3 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k (mu + mu') α))
  have k1 : (v2 * v1 - v3) * s = 0 := by linear_combination (-v2) * E10 - E20 + E30
  have hv' : v2 * v1 - v3 = 0 := hs.mul_left_eq_zero.mp k1
  have k2 : (C3 - (C1 + C2)) * q = 0 := by linear_combination E2 - E3 + v2 * E1 + s' * hv' - C1 * E20
  have hq : IsUnit q := by
    rw [E30]; exact (Units.isUnit _).mul hs
  have hC : C3 = C1 + C2 := sub_eq_zero.mp (hq.mul_left_eq_zero.mp k2)
  rw [← scal_add] at hC
  exact scal_injective R Dd.toPre z hC

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

theorem _root_.GlobalTheory.T.exists_invariant_field_coefficients_of_linear_vectorField : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  first | exact @GlobalTheory.VertCoeffRing.exists_coeff | exact GlobalTheory.VertCoeffRing.exists_coeff | (intros; apply GlobalTheory.VertCoeffRing.exists_coeff <;> assumption)
end
