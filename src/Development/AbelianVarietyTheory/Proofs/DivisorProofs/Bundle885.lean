module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle869
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisation_preimage_value_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  first | exact @GlobalTheory.CechPer.pre_val_rules | exact GlobalTheory.CechPer.pre_val_rules | (intros; apply GlobalTheory.CechPer.pre_val_rules <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  first | exact @GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | exact GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift | (intros; apply GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harris_taylor_object_maps_compose_cancel : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (o₃ : GlobalTheory.UPel.HT.Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g))) ∧ (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_cancel | exact GlobalTheory.UPel.HT.objMap_comp_cancel | (intros; apply GlobalTheory.UPel.HT.objMap_comp_cancel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (exact GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (intros; apply GlobalTheory.UPel.HT.Datum.charP_tensor_matrix  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (exact GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (intros; apply GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

def TateIsoO.transport {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := Φ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n b x := by rw [I.lin, hact]
  ker n hn hc x := by rw [map_eq_one_iff Φ Φ.injective]; exact I.ker n hn hc x
  onto n hn hc q := by
    obtain ⟨q, rfl⟩ := Φ.surjective q
    rw [← map_pow, map_eq_one_iff Φ Φ.injective, I.onto n hn hc]
    exact exists_congr fun x => Φ.injective.eq_iff.symm
  tower n m hn hm hc x := by rw [← map_pow, I.tower n m hn hm hc]
  isom n hn hc x y := he _ _ _ _ (I.isom n hn hc x y)

@[simp] theorem TateIsoO.transport_ev {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type}
    [Group Q] [Group Q'] {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x))
    (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z) (I : TateIsoO D k Q act e) (n : ℕ) (y : D.La) :
    (I.transport Φ hact he).ev n y = Φ (I.ev n y) := rfl

theorem tateIsoO_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  intro p _ D R _ b N N' S S' s s' o o' f φ φ₂ hp hsq hact hpol k _ _ x
  have e : φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (fst o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (fst o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, Category.assoc, hsq.1,
        ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (snd o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (snd o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, Category.assoc, hsq.2,
        ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hL' : (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left).IsLB := pull_isLB o'.isLB _
  have H1 : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    LBIso.chartPull (chartPullPull o'.P _ _ rfl) (chartPullSame o.P _ (fun _ => φ₂) _ _ fun _ => e) hpol
  have hw : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullId _) (chartPullOut o.P (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1) φ
      (fun _ => φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => rfl) H1
  let Φ := GlobalTheory.ObjPull.pushEquiv hp (Over.mk x)
  have hW : ∀ (n : ℕ) (g g' : Over.mk x ⟶ o'.A) (z : kˣ),
      Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z) ↔
        Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (Φ g) (Φ g') (unitOn z) :=
    fun n g g' z => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f φ _ _ hL hL' hp hw (Over.mk x) n g g' (Φ g) (Φ g')
      _ rfl rfl
  have hA : ∀ c (g : Over.mk x ⟶ o'.A), Φ (g ≫ o'.act.act c) = Φ g ≫ o.act.act c := fun c g =>
    Over.OverMorphism.ext (by
      show (g ≫ o'.act.act c).left ≫ φ = (Φ g ≫ o.act.act c).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc])
  refine ⟨fun I' => ⟨I'.transport Φ hA fun n g g' z h => (hW n g g' z).1 h, fun n y => rfl⟩,
    fun I => ⟨I.transport Φ.symm (fun c g => Φ.injective ?_) (fun n g g' z h => (hW n _ _ z).2 ?_), fun n y => ?_⟩⟩
  · rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  · rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
  · rw [TateIsoO.transport_ev]
    exact (GlobalTheory.ObjPull.pushEquiv_symm_left hp (Over.mk x) (I.ev n y)).symm

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.uniformisationAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  first | exact @GlobalTheory.unifAt_correspond_of_cartesian | exact GlobalTheory.unifAt_correspond_of_cartesian | (intros; apply GlobalTheory.unifAt_correspond_of_cartesian <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Kunneth

section Pairs

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
  {C : Type} [Category.{0} C] (A : C ⥤ AffOp X') (B : C ⥤ AffOp X)
  (hle : ∀ T, (A.obj T).unop.1 ≤ φ ⁻¹ᵁ (B.obj T).unop.1)

def toPair : C ⥤ (Pair φ)ᵒᵖ where
  obj T := Opposite.op ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩
  map {T T'} a := (homOfLE (Subtype.coe_le_coe.1
    (Prod.mk_le_mk.2 ⟨leOfHom (A.map a).unop, leOfHom (B.map a).unop⟩) :
      (⟨((A.obj T').unop, (B.obj T').unop), hle T'⟩ : Pair φ) ≤ ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem restrict_pullHO1 (h : φ ≫ s = s' ≫ spMap σ) (c : HO1 s) :
    (CoefMap.restrict (OAff s') A).pull1 (pullHO1 h c) =
      ((pairPull h).comp (CoefMap.restrict (OPair φ s') (toPair A B hle))).pull1 c := by
  rw [CoefMap.pullCohomologyOne_comp, (isPullO_pullHO1 h c : (pairPull h).pull1 c = (pairRes φ s').pull1 (pullHO1 h c))]
  exact CoefMap.pullCohomologyOne_comp (pairRes φ s') (CoefMap.restrict (OPair φ s') (toPair A B hle)) (pullHO1 h c)

end Pairs

end GlobalTheory.Kunneth

namespace GlobalTheory.Kunneth

def prodFun {J J' : Type} [Preorder J] [Preorder J'] {Z : Scheme.{0}} (W : J × J' → Z.affineOpens)
    (hW : Monotone W) : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Z where
  obj T := Opposite.op (W (T.1.unop, T.2.unop))
  map a := (homOfLE (hW (Prod.mk_le_mk.2 ⟨leOfHom a.1.unop, leOfHom a.2.unop⟩))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem cup_tmul_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom →
    IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom),
    ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 →
    ∑ i, x i ⊗ₜ[K] y i = 0 := by
  intro K _ X Y hXs hXq hYs hYq n x y hsum
  obtain ⟨J, _, _, U, hU, hUi, hUc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K X.left X.hom hXs hXq
  obtain ⟨J', _, _, V, hV, hVi, hVc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K Y.left Y.hom hYs hYq
  choose Wf h1 h2 i1 i2 hWe hi1 hi2 hbij using fun p : J × J' ↦ GlobalTheory.T.exists_affine_open_product_sections_iso K X Y (U p.1) (V p.2)
  have hWm : Monotone Wf := fun p q hpq ↦ by
    show (Wf p).1 ≤ (Wf q).1
    rw [hWe p, hWe q]
    exact inf_le_inf (Scheme.Hom.preimage_mono _ (hU hpq.1)) (Scheme.Hom.preimage_mono _ (hV hpq.2))
  haveI : Finite J'ᵒᵖ := Finite.of_equiv J' Opposite.equivToOpposite
  let Ψ := prodFun Wf hWm
  let F := hU.functor.op ⋙ OAff X.hom
  let G := hV.functor.op ⋙ OAff Y.hom
  let E := Ψ ⋙ OAff (X ⊗ Y).hom
  let B₁ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp X.left := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ ⋙ hU.functor.op
  let B₂ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Y.left := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ ⋙ hV.functor.op
  have hle₁ : ∀ T, (Ψ.obj T).unop.1 ≤ (fst X Y).left ⁻¹ᵁ (B₁.obj T).unop.1 := fun T ↦ h1 (T.1.unop, T.2.unop)
  have hle₂ : ∀ T, (Ψ.obj T).unop.1 ≤ (snd X Y).left ⁻¹ᵁ (B₂.obj T).unop.1 := fun T ↦ h2 (T.1.unop, T.2.unop)
  let m₁ := (pairPull (ovw (fst X Y))).comp (CoefMap.restrict (OPair (fst X Y).left (X ⊗ Y).hom) (toPair Ψ B₁ hle₁))
  let m₂ := (pairPull (ovw (snd X Y))).comp (CoefMap.restrict (OPair (snd X Y).left (X ⊗ Y).hom) (toPair Ψ B₂ hle₂))
  let j₁ : ∀ T : Jᵒᵖ × J'ᵒᵖ, F.obj T.1 →ₐ[K] E.obj T := fun T ↦ i1 (T.1.unop, T.2.unop)
  let j₂ : ∀ T : Jᵒᵖ × J'ᵒᵖ, G.obj T.2 →ₐ[K] E.obj T := fun T ↦ i2 (T.1.unop, T.2.unop)
  have nat₁ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : F.obj T.1), j₁ T' (mp F a.1 b) = mp E a (j₁ T b) := by
    intro T T' a b
    refine (hi1 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi1 (T.1.unop, T.2.unop) b).symm))
    exact m₁.naturality a b
  have nat₂ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : G.obj T.2), j₂ T' (mp G a.2 b) = mp E a (j₂ T b) := by
    intro T T' a b
    refine (hi2 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi2 (T.1.unop, T.2.unop) b).symm))
    exact m₂.naturality a b
  let n₁ : CoefMap (RingHom.id K) F E :=
    { G := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₁ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₁ T T' a b
      smul := fun T r b ↦ map_smul (j₁ T) r b }
  let n₂ : CoefMap (RingHom.id K) G E :=
    { G := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₂ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₂ T T' a b
      smul := fun T r b ↦ map_smul (j₂ T) r b }
  let rU := CoefMap.restrict (OAff X.hom) hU.functor.op
  let rV := CoefMap.restrict (OAff Y.hom) hV.functor.op
  let rE := CoefMap.restrict (OAff (X ⊗ Y).hom) Ψ
  have key₁ : ∀ a, rE.pull1 (pO1 (fst X Y) a) = n₁.pull1 (rU.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₁ hle₁ (ovw (fst X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₁ (rU.comp n₁) (𝟙 B₁) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rU n₁ a)
    refine (congrArg ((rU.comp n₁).α T) (mp_id (OAff X.hom) _ b)).trans ?_
    exact hi1 (T.1.unop, T.2.unop) b
  have key₂ : ∀ a, rE.pull1 (pO1 (snd X Y) a) = n₂.pull1 (rV.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₂ hle₂ (ovw (snd X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₂ (rV.comp n₂) (𝟙 B₂) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rV n₂ a)
    refine (congrArg ((rV.comp n₂).α T) (mp_id (OAff Y.hom) _ b)).trans ?_
    exact hi2 (T.1.unop, T.2.unop) b
  have hbU : Function.Bijective rU.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K X.left X.hom J U hU hUi hUc
  have hbV : Function.Bijective rV.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K Y.left Y.hom J' V hV hVi hVc
  choose x' hx' using fun i ↦ H1.mk_surjective F (rU.pull1 (x i))
  choose y' hy' using fun i ↦ H1.mk_surjective G (rV.pull1 (y i))
  have hz : H2.mk E (∑ i, cupZ E (n₁.pullbackOneCocycle (x' i)) (n₂.pullbackOneCocycle (y' i))) = 0 := by
    have h0 := congrArg rE.pull2 hsum

    rw [map_zero, map_sum] at h0

    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
    rw [CoefMap.pullCohomologyTwo_cup, key₁, key₂, ← hx', ← hy']
    rfl
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hz
  have e := GlobalTheory.T.tensor_algebra_product_diagram_compat K Jᵒᵖ J'ᵒᵖ F G E j₁ j₂ nat₁ nat₂ (fun T ↦ hbij (T.1.unop, T.2.unop)) n x' y' f
    (fun T T' T'' a b ↦ by
      rw [hf]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rfl)
  simp only [hx', hy'] at e
  let eU := LinearEquiv.ofBijective rU.pull1 hbU
  let eV := LinearEquiv.ofBijective rV.pull1 hbV
  apply (TensorProduct.congr eU eV).injective

  rw [map_sum, map_zero]
  exact e

end GlobalTheory.Kunneth
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  first | exact @GlobalTheory.AbCoh.tmul_of_pull_eq_zero | exact GlobalTheory.AbCoh.tmul_of_pull_eq_zero | (intros; apply GlobalTheory.AbCoh.tmul_of_pull_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_flat_lifting_obstruction_class : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  first | exact @GlobalTheory.AbCoh.exists_bock | exact GlobalTheory.AbCoh.exists_bock | (intros; apply GlobalTheory.AbCoh.exists_bock <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  first | exact @GlobalTheory.AbCoh.exists_lift_of_bock_zero | exact GlobalTheory.AbCoh.exists_lift_of_bock_zero | (intros; apply GlobalTheory.AbCoh.exists_lift_of_bock_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hyper_h2_generated_by_cups : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  first | exact @GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | exact GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | (intros; apply GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp <;> assumption)
end
