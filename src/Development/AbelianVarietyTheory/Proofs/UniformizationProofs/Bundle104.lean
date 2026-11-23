module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_iso_agrees_on_complete_points_alt : Laws → Laws2 → ∀ (R
    : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I
    : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A'
    : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of
    R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj
    G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD
    : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j
    : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j
    e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt
    e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG
    x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j
    e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK
    : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst
    G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e
    : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM'
    : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt
    e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r
    z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j
    e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e
    G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f
    (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z
    jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r
    : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫
    ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK
    R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L
    (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL
    (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (B : Type) [CommRing
    B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of
    B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → (g'
    ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map
    (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e
    : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e
    G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e
    G).left = ρ ≫ g) → ∃ v : Γ(Spec (CommRingCat.of B), ⊤)ˣ, (∀ (Z : Scheme.{0}) (ρ
    : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj
    G').left), r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK
    R) = ρ ≫ g ∧ ∀ z : Z, Geo.Tor.gw wK r z jL (fun _ => jL') = gm ρ z ⊤ v) ∧ ∀ (e : ℕ) (Z
    : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM
    : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), r ≫ (fstG I e G').left = ρ ≫ g' → (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j
    e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r
    ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w
    e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * gm ρ z ⊤ v := by
  first | exact @GlobalTheory.generic_iso_agrees_on_complete_points | exact GlobalTheory.generic_iso_agrees_on_complete_points | (intros; apply GlobalTheory.generic_iso_agrees_on_complete_points <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDimension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem nonempty_linearEquiv_of_rel {F M N : Type*} [Semiring F] [AddCommMonoid M] [AddCommMonoid N] [Module F M]
    [Module F N] (P : M → N → Prop) (h₁ : ∀ m, ∃! n, P m n) (h₂ : ∀ n, ∃! m, P m n)
    (ha : ∀ m n m' n', P m n → P m' n' → P (m + m') (n + n')) (hs : ∀ (c : F) m n, P m n → P (c • m) (c • n)) :
    Nonempty (M ≃ₗ[F] N) := by
  choose f hf hf' using h₁
  let g : M →ₗ[F] N :=
    { toFun := f
      map_add' := fun m m' => (hf' _ _ (ha _ _ _ _ (hf m) (hf m'))).symm
      map_smul' := fun c m => (hf' _ _ (hs c _ _ (hf m))).symm }
  refine ⟨LinearEquiv.ofBijective g ⟨fun m m' e => ?_, fun n => ?_⟩⟩
  · have e' : f m = f m' := e
    exact (h₂ (f m')).unique (e' ▸ hf m) (hf m')
  · obtain ⟨m, hm, -⟩ := h₂ n
    exact ⟨m, (hf' _ _ hm).symm⟩

section Comb

variable {X Y : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j

theorem exists_isComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) : ∃ s, IsComb b a s :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by

    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isComb_iff_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) :
    IsComb b a s ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (a i) * sval (b i) (𝟙 Y) y J := by
  refine ⟨fun h y J hJ => SectionScalarValuation.sval_lin a b h _ y hJ, fun h j => ?_⟩
  obtain ⟨t, ht⟩ := exists_isComb b a
  rw [← ht j]
  exact sec_ext_val hL (fun y J hJ => (h y J hJ).trans (SectionScalarValuation.sval_lin a b ht _ y hJ).symm) j

theorem exists_basis_of_gen (hL : L.IsLB) {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => g (c i)) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ' k) φ₃) (Sum.elim ε' fun k => -ε₃ k) φ ε := fun U _ w => by
    have := h U w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
    rw [← this]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL h (pullMulSec (b i) (𝟙 Y) u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := invGen_isGen L _ _ u hu
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
  refine (existsUnique_congr fun c => ?_).1 (hb t)
  rw [isComb_iff_sval hL, isComb_iff_sval hL]
  refine forall₃_congr fun y J hJ => ?_
  rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_inv, Category.id_comp, Units.mul_inv_eq_iff_eq_mul,
    Finset.sum_mul]
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]

end Comb

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_basis_famSec (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → FamFree.FamSec D F k α,
      ∀ s, ∃! c : Fin (k ^ D.P.g) → F, IsComb b (fun i => gF D F (c i)) s := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  refine exists_basis_of_gen D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) u hu (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc]) (gF D F) b (fun s => ?_)
  exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).2 (hb s)

theorem nonempty_fam_equiv (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Nonempty (Fam D F k ≃ₗ[F] (D.X ⧸ FamFree.multiples D k → Fin (k ^ D.P.g) → F)) := by
  let rep : D.X ⧸ FamFree.multiples D k → D.X := Quotient.out
  have hrep : ∀ c, QuotientAddGroup.mk (rep c) = c := fun c => Quotient.out_eq c
  choose b hb using fun c => exists_basis_famSec (D := D) (F := F) hT hk (rep c)
  refine nonempty_linearEquiv_of_rel
    (fun s z => ∀ c, IsComb (b c) (fun i => gF D F (z c i)) (s.s (rep c))) (fun s => ?_) (fun z => ?_) ?_ ?_
  · choose z hz hz' using fun c => hb c (s.s (rep c))
    exact ⟨z, hz, fun z' h => funext fun c => hz' c _ (h c)⟩
  · choose σ hσ using fun c => exists_isComb (b c) (fun i => gF D F (z c i))
    refine (existsUnique_congr fun s => forall_congr' fun c => ?_).1
      (FamFree.existsUnique_fam hG hB hk rep hrep σ)
    exact ⟨fun h => h ▸ hσ c, fun h => SecOps.sec_ext fun j => (h j).trans (hσ c j).symm⟩
  · intro s z s' z' h h' c j
    rw [add_f, h c j, h' c j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, map_add (f := _), resTop, add_mul]
  · intro a s z h c j
    rw [smul_f, h c j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, resTop, _root_.mul_assoc]

theorem finrank_fam (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  obtain ⟨e⟩ := nonempty_fam_equiv (D := D) (F := F) hG hT hB hk
  have hc : Nat.card (D.X ⧸ FamFree.multiples D k) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  have : Finite (D.X ⧸ FamFree.multiples D k) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite (D.X ⧸ FamFree.multiples D k)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_fin_fun, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc, smul_eq_mul, pow_add]

theorem main : GlobalFnsSt → CubeSt → SquareSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D.toPre F k) ∧ Module.finrank F (Fam D.toPre F k) = k ^ (D.toPre.rank + D.toPre.P.g) :=
  fun hG _ _ hT _ _ _ _ D _ _ _ _ hk => finrank_fam hG hT D.tau_bimult hk

end GlobalTheory.FamDimension
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem point_ext {X : Scheme.{0}} [X.IsSeparated] (x₁ x₂ : (TWM.TO hϖ hv).left ⟶ X)
    (h : (TWM.ιS hϖ hv).left ≫ x₁ = (TWM.ιS hϖ hv).left ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness (terminal.from X) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (terminal.from X) :=
    { R := TWO.Ov v, K := F, i₁ := (TWM.ιS hϖ hv).left ≫ x₁, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

theorem exists_ratio_nonneg {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, 0 ≤ v x ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL h (Geo.Tor.genSec t ht)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.TwistUnit.exists_ratio_local (R := TWO.Ov v) hL s t' ht'
  refine ⟨TWM.ιr (v := v) x₀, TWM.v_ιr x₀, fun z J hJ => ?_⟩
  have e := gs_pull (𝟙 _) (TWM.ιS hϖ hv).left z ⊤ trivial x₀
  rw [Category.id_comp] at e
  have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤)
    (TWM.appTop_specMap (CommRingCat.ofHom (algebraMap (TWO.Ov v) F)) x₀))
  exact (sval_genSec t ht _ z hJ).symm.trans ((hs _ _ z J hJ).symm.trans
    ((hx₀ _ _ z J hJ).trans (congrArg (· * _) e')))

theorem exists_ratio_zero {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, v x = 0 ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨x, hx, e⟩ := exists_ratio_nonneg hϖ hv hL h t ht t' ht'
  obtain ⟨y, hy, e'⟩ := exists_ratio_nonneg hϖ hv hL (fun U _ g => (h U g).symm) t' ht' t ht
  refine ⟨x, le_antisymm (TWO.le_zero_of_add_eq_zero_nonneg ?_ hy) hx, e⟩
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := e z J hJ
  rw [e' z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, ← map_mul] at a
  have b : cstH z (x * y) = 1 := by
    rw [← Units.mul_left_inj (val t (TWM.ιS hϖ hv).left z J), _root_.one_mul]; exact a.symm
  rw [← AddValuation.map_mul, cstH_inj z (b.trans (map_one _).symm), AddValuation.map_one]

theorem v_of_isCoef {D : DegData V (maximalIdeal V)} {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b}
    {χ : D.toPre.X} {l ω : ℚ} (hg : GenV hϖ hv (g.s χ) l) (hw : GenV hϖ hv w ω)
    (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (hm : TWM.ιS hϖ hv ≫ m = g.b)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)))
    (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)))
    (hG₀ : G₀.IsGen) (x : F)
    (hs : ∀ z J, Good D.toPre.P.L z J → sval s (lift (𝟙 (TF (R := V) F)) g.b).left z J =
      cst (R := V) F z x * (val G₀ (TWM.ιS hϖ hv).left z J).val) :
    ∃ c, IsCoef k g w χ s c ∧ v c = v x + ((l + ω : ℚ) : WithTop ℚ) := by
  have hL := D.toPre.P.isLB
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨φ₁, h₁, t₁, ht₁, x₁, v₁, e₁⟩ := hg
  obtain ⟨φ₂, h₂, t₂, ht₂, x₂, v₂, e₂⟩ := hw
  have c₁ : TWM.ιS hϖ hv ≫ cP D.toPre _ χ = cP D.toPre _ χ := comp_cP D.toPre _ χ
  have c₂ : TWM.ιS hϖ hv ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have c₃ : TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * m) = cP D.toPre _ χ * g.b := by
    rw [MonObj.comp_mul, c₁, hm]
  obtain rfl : φ₁ = TWM.gtφO hϖ hv m χ := funext fun i => point_ext hϖ hv _ _ ((h₁ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₃.symm, congrArg (·.left) c₁.symm, congrArg (·.left) hm.symm,
      congrArg (·.left) c₂.symm]))
  obtain rfl : φ₂ = TWM.lineφO hϖ hv m := funext fun i => point_ext hϖ hv _ _ ((h₂ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₂.symm, congrArg (·.left) hm.symm]))
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D.toPre m χ k h
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have r : m * SectionScalarValuation.cQ D.toPre _ χ = cP D.toPre _ χ * m := mul_comm _ _
      have r' : SectionScalarValuation.cQ D.toPre (TWM.TO hϖ hv) χ = cP D.toPre _ χ := rfl
      rw [r, r'] at p
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p, Fintype.prod_unique (_ : PUnit → U), q]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, TWM.gtφO, TWM.lineφO, DegPre.gtε, DegPre.lineε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ G₀ t₁) t₂)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hG₀ ht₁) ht₂)
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TWM.TO hϖ hv).hom)
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ D.toPre.rig_gen k) _)
  refine ⟨x * x₁ * x₂ * u, fun z J hJ => ?_, ?_⟩
  · have a := eu z J hJ
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Over.w (TWM.ιS hϖ hv)] at a
    have b : val (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TF (R := V) F).hom z J = rigV D.toPre (TF (R := V) F).hom z J ^ k := map_pow _ _ _
    rw [b, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at a
    rw [hs z J hJ, e₁ z J hJ, e₂ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination (-(cstH z x * cstH z x₁ * cstH z x₂)) * a
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hu, v₁, v₂, add_zero, add_assoc,
      WithTop.coe_add]

end

theorem exists_fam_coef_val : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 4 ≤ k → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) l ω, w.IsGen → GtV hϖ hv g l → GenV hϖ hv w ω → ∀ a₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, (s.s β).f j = 0) ∧ v (coef s g w a₀) = (((Q a₀ : ℚ) / k + l a₀ + ω : ℚ) : WithTop ℚ) := by
  intro hLL hT _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk g w l ω hw hg hω a₀
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hs⟩ :=
    GlobalTheory.exists_integral_section_unit_at hLL.1 hT V ϖ hϖ D Q hQ F v hv k hk a₀ m
  rw [hm] at hs
  obtain ⟨c, hc, vc⟩ := v_of_isCoef hϖ hv (hg a₀) hω m hm σ G₀ hG₀ x hs
  obtain ⟨s₀, rfl, h₀⟩ := GlobalTheory.FamFree.exists_fam_single hLL.1.globalFns D.tau_bimult (by omega : 1 ≤ k) a₀ σ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, v ζ = (((Q a₀ : ℚ) / k : ℚ) : WithTop ℚ) := by
    by_cases h : a₀ = 0
    · exact ⟨1, by rw [h, QForm.Q_zero hϖ D hQ, AddValuation.map_one]; simp⟩
    · have h1 := QForm.Q_pos hϖ D hQ h
      obtain ⟨ζ, -, e⟩ := exists_val_eq hv (r := (Q a₀ : ℚ) / k)
        (div_pos (by exact_mod_cast (by omega : (0 : ℤ) < Q a₀)) (by exact_mod_cast (by omega : 0 < k)))
      exact ⟨ζ, e⟩
  have hsm : Fam.IsSmul D.toPre F ζ s₀ (ζ • s₀) := (isSmul_iff _ _ _).2 rfl
  have hz : ∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, ((ζ • s₀).s β).f j = 0 := fun β hβ j => by
    rw [hsm β j, h₀ β (fun mu e => hβ mu e.symm) j]; exact mul_zero _
  refine ⟨ζ • s₀, fun χ => ?_, hz, ?_⟩
  · by_cases h : ∃ z : D.toPre.X, χ = a₀ + k • z
    · obtain ⟨z, rfl⟩ := h
      have H := SectionScalarValuation.fe_move hϖ hQ hv k z a₀ (ζ • s₀) (hσ.smul hζ.ge (hsm a₀))
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have e : 0 + (Q a₀ : ℚ) / k + ((k * Q z + QForm.bOf D.toPre Q z a₀ : ℤ) : ℚ) =
          0 + (Q (a₀ + k • z) : ℚ) / k := by
        rw [q_shift hϖ hQ a₀ z k]; push_cast; field_simp; ring
      rwa [e] at H
    · exact vge_of_zero (hz χ fun z e => h ⟨z, e⟩) _
  · have e : ζ • s₀ = (ζ - 1) • s₀ + s₀ := by rw [sub_smul, one_smul, sub_add_cancel]
    rw [e, ((coef_basic V D.toPre F k g).2.2 w hw).2.1, coef_eq hc, show (ζ - 1) * c + c = ζ * c by ring,
      AddValuation.map_mul, hζ, vc, hx, ← WithTop.coe_add, ← WithTop.coe_add, zero_add, add_assoc]

end GlobalTheory.UT.CoefUnit
end
end
