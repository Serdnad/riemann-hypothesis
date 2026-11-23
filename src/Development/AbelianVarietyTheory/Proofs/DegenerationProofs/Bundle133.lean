module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.RigCmpPf

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    eSec G' ≫ F = f ≫ eSec G := (cubeMapOf h).e_comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def upt (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {e : ℕ} {Z : Scheme.{0}}
    (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) : Z ⟶ (thickObj R I e G).left :=
  a ≫ eSec (thickObj R I e G)

omit [IsDomain R] [IsCommMonObj G] in
theorem eSec_fst (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ (fstG I e G).left = (a ≫ thick R I e) ≫ eSec G :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (UnitValue.eSec_pullback_fst (thick R I e) G)).trans
    (Category.assoc _ _ _).symm)

theorem eSec_pG {e : ℕ} (g : GtCoord I D e G) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ g.pG.left = (a ≫ thick R I e) ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (η[thickObj R I e G] ≫ g.q) = η[thickObj R I e D.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) := congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_fst (G := D.P.A) e a)
  unfold upt
  rw [← h2]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)

theorem rig_val (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (z : Z) {JG : (Z ⟶ G.left) → U.P.L.L.ι} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJG : Good U.P.L.L z JG)
    (hJ : Good D.P.L z J) :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw (U.w e) (upt G a) z (J ((upt G a) ≫ (U.gt e).pG.left))
          (fun _ => JG ((upt G a) ≫ (fstG I e G).left)) *
        val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z JG := by
  have h := (U.w_vals e (Over.mk a) z JG J hJG hJ _ (fun _ => rfl)).1
  rw [one_left] at h
  exact h

theorem rig_level {V : Type} [CommRing V] [IsDomain V] {I' : Ideal V} {D' : DegPre V}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (a' : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (ha : a ≫ thick R I e = (a' ≫ thick V I' e) ≫ spMap φ) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw C.v (upt G' a' ≫ (U'.gt e).pG.left) z (J (upt G a ≫ (U.gt e).pG.left))
          (J' (upt G' a' ≫ (U'.gt e).pG.left)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (a' ≫ thick V I' e) z J' := by
  have hG := eSec_comm C.pb
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨K', hK'⟩ := exists_good_pt U'.P.L.isLB z
  have e₁ := rig_val U e a z hK hJ
  have e₂ := rig_val U' e a' z hK' hJ'
  have e₃ := (C.wL_map.vals (Over.mk (a' ≫ thick V I' e)) z K' K hK' hK _ (fun _ => rfl)).1
  rw [one_left] at e₃
  have hx : upt G a ≫ (fstG I e G).left = (upt G' a' ≫ (fstG I' e G').left) ≫ F := by
    rw [eSec_fst e a, eSec_fst e a', ha]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hG.symm).trans (Category.assoc _ _ _).symm)
  have e₄ := ((C.lev e _ _ _ (hx.trans (Category.assoc _ _ _))).2 z J J' hJ hJ').2 _ _
    (hK (upt G a ≫ (fstG I e G).left)) (hK' (upt G' a' ≫ (fstG I' e G').left))
  have f₃ : val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z K =
      gw C.wL (upt G' a' ≫ (fstG I' e G').left) z (K (upt G a ≫ (fstG I e G).left))
        (K' (upt G' a' ≫ (fstG I' e G').left)) *
      val (L := U'.P.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) U'.P.L.rig
        (a' ≫ thick V I' e) z K' := by
    rw [ha, hx, eSec_fst e a']
    exact e₃
  exact e₁.trans ((congrArg _ f₃).trans ((_root_.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄.symm).trans ((_root_.mul_assoc _ _ _).trans (congrArg _ e₂.symm)))))

end GlobalTheory.RigCmpPf

namespace GlobalTheory


open RigCmpPf in
theorem rigCmp_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  intro R V _ _ _ _ _ _ I I' φ hI' hφ D D' A G _ _ A' G' _ _ U U' F C
  have hB := eSec_comm C.pbB
  have key := AbelianPartIso.pmaps_of_thickenings hI' D.P.isLB D'.P.isLB C.v C.v_gen (eSec D'.P.A)
    (spMap φ ≫ eSec D.P.A) hB D'.rig D'.rig_gen
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (spMap φ))
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) fun e z p q hp hq => by
      have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono hφ _
      let a : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
        spMap (Ideal.quotientMap _ φ hle)
      have ha : a ≫ thick R I e = (𝟙 _ ≫ thick V I' e) ≫ spMap φ := by
        rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : Unit => thick V I' e ≫ spMap φ ≫ eSec D.P.A)
        (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (fun _ : Unit => thick V I' e ≫ eSec D'.P.A)
        (fun _ => q) (fun _ _ _ => rfl) (fun _ => hq)
      have E := rig_level C e a (𝟙 _) ha z hJ hJ'
      have hp' : (a ≫ thick R I e) ≫ eSec D.P.A = thick V I' e ≫ spMap φ ≫ eSec D.P.A := by
        rw [ha, Category.id_comp]
        exact Category.assoc _ _ _
      rw [eSec_pG (U.gt e) a, eSec_pG (U'.gt e) (𝟙 _), hp', ha, Category.id_comp, eJ (), eJ' (),
        val_of _ _ z J (fun _ => p) (fun _ => (congrArg J (Category.assoc _ _ _)).trans (eJ ())),
        val_of _ _ z J' (fun _ => q) (fun _ => eJ' ())] at E
      refine Eq.trans ?_ E
      have m₁ : thick V I' e z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      have m₂ : spMap φ (thick V I' e z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      exact (gm_res _ z _ m₁ _).trans (gm_pull _ (spMap φ) z _ m₂ _)
  intro Z r z p q hp hq
  have hm : (spMap φ ≫ eSec D.P.A) (r z) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun g => g (r z) ∈ D.P.L.U (p PUnit.unit)) hB).mp (hp PUnit.unit)
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have m₁ : r z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  have m₂ : spMap φ (r z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  exact ((gm_res r z _ m₁ _).trans (gm_pull r (spMap φ) z _ m₂ _)).symm

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Defs
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

def ThG (m : ℕ) {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (x : T ⟶ G) (c : Γ(T.left, ⊤)) : Prop :=
  x ^ (m ^ 2) = 1 ∧ ∃ (t : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T))
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, (snd T G ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T)) (θ : ThetaGrp G L ((m ^ 2 : ℕ) : ℤ) T),
    α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT G 1).left) (rigT G L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull G L (mulT G _ m) (snd _ G ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift G L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf G L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good L z J → VVRank.sv G t (ptSecT G 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (rigT G L ρ T ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val

def NZ {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) : Prop :=
  ∃ g : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left g = closedPoint V ∧ g ∈ nonzeroLocus σ

def UnivBasis {K : Type} [CommRing K] (x : Sp K ⟶ S) (e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [CommRing K'] (i : K →+* K') (x' : Sp K' ⟶ S) (h : spMap i ≫ x = x') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')),
    ∃! c : Γ((Over.mk x').left, ⊤),
      s = c • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)


variable {G L} in
def IsRigidificationPullbackCompatibleIso {S' : Scheme.{0}} {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left} {L' : LB A.left} (w : LB.Iso L' (L.pull φ))
    (f : S' ⟶ S) (ρ' : LB.Gen (L'.pull (eSec A))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (J) (J'), Good L z J → Good L' z J' →
    val (L := L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ (r ≫ f) z J =
      wVal w z J J' (r ≫ eSec A) * val (L := L') (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ' r z J'
end Defs

theorem thG_iff {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : GlobalTheory.UT.SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (c : F) :
    ThG A.A A.L ρ m th x (fnOf c) ↔ x ^ (m ^ 2) = 1 ∧ ∃ t, GlobalTheory.UT.ThC A ρ m th x t c := Iff.rfl

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}

theorem val_rigT (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T₀.left) (z : Z) {J} (hJ : Good L₀ z J) :
    val (rigT G L₀ ρ₀ T₀ k) r z J =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T₀.hom ≫ eSec G) r
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J
    (fun _ => J (r ≫ T₀.hom ≫ eSec G)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hz _).trans (gm_pull r T₀.hom z _ (rigT_le G L₀ _ hz) _)


include hτ in
theorem IsRigidificationPullbackCompatibleIso.rigT (h : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'}
    (hJ : Good L₀ z J) (hJ' : Good L₁ z J') : val (rigT G L₀ ρ₀ T₀ k) (r ≫ τ) z J =
      wVal w z J J' (r ≫ T.hom ≫ eSec A) ^ k * val (rigT A L₁ ρ₁ T k) r z J' := by
  rw [val_rigT k _ z hJ, val_rigT k _ z hJ', Category.assoc, hτ, ← Category.assoc, h _ _ z J J' hJ hJ', mul_zpow,
    Category.assoc]

theorem norm_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ} {a : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
      val α₀ (r ≫ psi hp τ hτ) z J = (wVal w z J J' (r ≫ (snd T A).left) ^ a *
        wVal w z J J' (r ≫ (snd T A ^ m).left) ^ (-((1 : ℕ) : ℤ))) * val α r z J')
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J') :
    val α₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = val (Out.rigT G L₀ ρ₀ T₀ (a - 1)) (r ≫ τ) z J ↔
      val α (r ≫ (ptSecT A 1).left) z J' = val (Out.rigT A L₁ ρ₁ T (a - 1)) r z J' := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    H _ _ _ _ _ hJ hJ', Category.assoc, Category.assoc, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, ← zpow_add,
    show a + -((1 : ℕ) : ℤ) = a - 1 from rfl, mul_right_inj]

theorem value_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {a : ℤ} {t₀ : LB.Sec (LPow G L₀ a T₀)} {t : LB.Sec (LPow A L₁ a T)}
    (ht : SecRel hp τ hτ w t t₀) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J')
    (c : Z.presheaf.stalk z) :
    VVRank.sv G t₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = c * (val (Out.rigT G L₀ ρ₀ T₀ a) (r ≫ τ) z J).val ↔
      VVRank.sv A t (r ≫ (ptSecT A 1).left) z J' = c * (val (Out.rigT A L₁ ρ₁ T a) r z J').val := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    ht _ _ _ _ _ hJ hJ', Category.assoc, NormTheta.ptSec_snd, Units.val_mul, mul_left_comm, Units.mul_right_inj]

theorem value_at {a : ℤ} {t : LB.Sec (LPow A L₁ a T)} {c : Γ(T.left, ⊤)} (hL₁ : L₁.IsLB)
    (h : ∀ z J, Good L₁ z J → VVRank.sv A t (ptSecT A 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) (𝟙 _) z J).val)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L₁ z J) :
    VVRank.sv A t (r ≫ (ptSecT A 1).left) z J = gs r z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) r z J).val :=
  sv_of_isValueAt (x := (1 : T ⟶ A)) (ρ := Out.rigT A L₁ ρ₁ T a) (isValueAt_of_sv hL₁ fun y J hJ => by
    rw [Category.id_comp]; exact h y J hJ) r z hJ

theorem ThG.move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T₀.left, ⊤)} (H : ThG G L₀ ρ₀ m th₀ x₀ c) : ThG A L₁ ρ₁ m th x (τ.appTop.hom c) := by
  obtain ⟨-, t₀, α₀, s₀, θ₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨t, ht⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ t₀
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α₀ h₁
  obtain ⟨θ, hθ, hθ'⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn h₄
  refine ⟨hn, t, α, s, θ, hα, corr_of_val hL₁ fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅, fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    rw [val_pull hJ']
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').1 ((val_pull hJ _ _ _).symm.trans (val_corr hJ h₂ _))
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := (value_iff hp τ hτ hr ht (𝟙 _) y hJ hJ' _).1 (value_at hL₀ h₆ (𝟙 _ ≫ τ) y hJ)
    rw [Category.id_comp (ptSecT A 1).left] at q
    exact q.trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem ThG.up [IsIso τ] [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x₀ ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T.left, ⊤)} (H : ThG A L₁ ρ₁ m th x c) : ThG G L₀ ρ₀ m th₀ x₀ ((inv τ).appTop.hom c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s
  obtain ⟨t₀, ht⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ t
  obtain ⟨α₀, hα, vα⟩ := ThetaPtUp.exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α h₁
  obtain ⟨θ₀, hθ, hθ'⟩ := ThetaPtUp.symLift_up hp τ hτ hw hL₀ hL₁ hx h₀ h₄
  refine ⟨hn, t₀, α₀, s₀, θ₀, hα, corr_of_val hL₀ fun y J hJ => ?_,
    ThetaPtUp.isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅,
    fun y J hJ => ?_⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    rw [val_pull hJ, ← IsIso.inv_hom_id τ]
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').2 ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' h₂ _))
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := (value_iff hp τ hτ hr ht (inv τ) y hJ hJ' _).2 (value_at hL₁ h₆ (inv τ) y hJ')
    rw [IsIso.inv_hom_id, Category.id_comp] at q
    exact q.trans (congrArg (· * _) ((gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])).symm)

theorem ThG.smul (hL₁ : L₁.IsLB) {m : ℕ} {x : T ⟶ A} {th th' : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {a c : Γ(T.left, ⊤)}
    (h : SecM.ofSec A th' = a • SecM.ofSec A th) (H : ThG A L₁ ρ₁ m th x c) : ThG A L₁ ρ₁ m th' x (a * c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  have tw : ∀ {p q : ℤ} {κ : T ⊗ A ⟶ A} {β} (_ : β.IsGen) {u u' : LB.Sec (LPow A L₁ q T)} {v : LB.Sec (LPow A L₁ p T)},
      SecM.ofSec A u' = a • SecM.ofSec A u → IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u v →
      IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u' (SecM.toSec A (a • SecM.ofSec A v)) := by
    intro p q κ β hβ u u' v hu hv
    refine VVRank.isTwistPull_of_sv A hL₁ hβ fun y J hJ => ?_
    have e₁ := sv_of_eq_mul (s := u') (t := u) (c := a) (fun j => congrArg (fun q => q.1 j) hu)
      (𝟙 _ ≫ (lift (fst T A) κ).left) y hJ
    have e₂ := sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A v)) (t := v) (c := a) (fun j => rfl) (𝟙 _) y hJ
    rw [e₁, e₂, VVRank.sv_of_isTwistPull A hv (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, lift_fst, mul_left_comm]
  refine ⟨h₀, SecM.toSec A (a • SecM.ofSec A t), α, SecM.toSec A (a • SecM.ofSec A s), θ, h₁, h₂, tw h₁ h h₃, h₄,
    tw θ.isGen rfl h₅, fun y J hJ => ?_⟩
  rw [sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A t)) (t := t) (c := a) (fun j => rfl) _ y hJ, h₆ y J hJ,
    ptSecT_fst, ← _root_.mul_assoc, gs_mul _ y ⊤ trivial]


include hp in
theorem exists_rigidificationPullbackCompatibleIso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hρ : ρ₀.IsGen) :
    ∃ ρ₁ : LB.Gen (L₁.pull (eSec A)), ρ₁.IsGen ∧ IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀ := by
  have e : eSec A ≫ φ = f ≫ eSec G := by
    have := over_one hp (T := baseOver S') (T₀ := baseOver S) f ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (f ≫ ·) (Category.id_comp _)))
  obtain ⟨ρ₁, h₁, h₂⟩ := exists_gen_through (φ' := fun _ : PUnit => eSec A) (φ := fun _ : PUnit => eSec G)
    (ε := fun _ => 1) (h := f) hw hL₀ hL₁ (fun _ => e) ρ₀ hρ
  exact ⟨ρ₁, h₁, fun Z r z J J' hJ hJ' => (h₂ Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])⟩

end Move

theorem ThG.unique (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} {m : ℕ} (hm : Odd m) (hu : IsUnit ((m ^ 2 : ℕ) : Γ(S, ⊤))) {T : Over S}
    {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {x : T ⟶ P.A} {c c' : Γ(T.left, ⊤)} (H : ThG P.A P.L ρ m th x c)
    (H' : ThG P.A P.L ρ m th x c') : c = c' := by
  obtain ⟨hx, t, α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ := H
  obtain ⟨-, t', α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩ := H'
  have hL := P.isLB
  obtain ⟨-, huniq⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns P.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  obtain rfl : s₁ = s₁' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A hs₁ _ y hJ).trans
      (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull P.A hs₁' _ y hJ).symm))
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  obtain rfl : t = t' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A ht _ y hJ).trans
      (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull P.A ht' _ y hJ).symm))
  refine fn_ext (V := ⊤) fun y _ => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory.Ex.OneGen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.hasSum_of_adicSum_unitBallExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C], CExt R I C → ∀ (Ix : Type) (x : Ix → C) (s : C), GlobalTheory.UT.SumF I C x s → HasSum x s := by
  first | exact @GlobalTheory.Ex.AdicNormSum.main | exact GlobalTheory.Ex.AdicNormSum.main | (intros; apply GlobalTheory.Ex.AdicNormSum.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ValuesSubfield
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_numOf_th {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) :
    ∃ (N₁ : NumD F) (ν₁ : NumOf D F N₁), ν₁.J = ν.J ∧ ν₁.th = th :=
  ⟨{ N with th := fun x => sF th (ν.eA x).left ν.J / rigVal ν },
    { ν with th := th, th_gen := hth, th_eq := fun _ => div_mul_cancel₀ _ (vF_ne_zero ν.good _ _) }, rfl, rfl⟩

theorem exists_values_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  intro hG R _ _ D he hb F F' _ _ _ _ f hf N' ν'
  obtain ⟨N₀, ν₀, h₀⟩ := ValuesExist.exists_numOf D F hG he hb ν'.th ν'.th_gen (fun ψ => ν'.J (spMap f ≫ ψ))
    fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F) (spMap f (IsLocalRing.closedPoint F')) z) ▸
      ν'.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F'))
  obtain ⟨N, ν, h₁, h₂⟩ := exists_numOf_th ν₀ ν'.th ν'.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := fun ψ => by rw [h₁, h₀]
  refine ⟨N, ν, numHom f hf ν ν' hJ h₂.symm, eX_numHom f hf ν ν' hJ h₂.symm, fun k p p' c c' h hc hc' => ?_⟩
  have hg : p'.g = gtExt D f hf p.g := (eq_gtExt_iff f hf _ _).2 h.2
  rw [hg] at hc'
  exact numHom_rel f hf ν ν' hJ h₂.symm hc hc'

end GlobalTheory.ValuesSubfield
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_integral_degeneration_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  first | exact @GlobalTheory.ValuesExist.exists_integral_values | exact GlobalTheory.ValuesExist.exists_integral_values | (intros; apply GlobalTheory.ValuesExist.exists_integral_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.RescaleValues

theorem vF_psi_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (q : D.X → (FractionRing R)ˣ) (χ : D.X) {J : (Sp F ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : ∀ ψ : Sp F ⟶ D.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    vF ((TauTwist.rescale D q).psi χ) (jFK (R := R) F) J =
      algebraMap (FractionRing R) F (q χ) * vF (D.psi χ) (jFK (R := R) F) J := by
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have e := TauTwist.val_psi_rescale q χ (jFK (R := R) F) (z := z) (J := J) (fun ψ => hJ ψ trivial)
  have e₁ : TauTwist.unitAt (jFK (R := R) F) z (q χ) =
      TorusExt.stalkUnits z (Units.map (algebraMap (FractionRing R) F).toMonoidHom (q χ)) := by
    have h := TauTwist.unitAt_spMap (𝟙 (Sp F)) (algebraMap (FractionRing R) F) z (q χ)
    rw [Category.id_comp] at h
    exact h.trans (TorusExt.gm_unitOn z _)
  refine (GaugeValues.vF_eq hJ z _ _).symm.trans ?_
  refine (congrArg (fun x => (((TorusExt.stalkUnits z).symm x : Fˣ) : F)) (e.trans (congrArg (· * _) e₁))).trans ?_
  refine Eq.trans ?_ (congrArg (_ * ·) (GaugeValues.vF_eq hJ z _ _))
  simp only [map_mul, MulEquiv.symm_apply_apply, Units.val_mul]
  rfl

theorem exists_numOf_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (k : ℕ) (β : N.Form k) (u : Fˣ) (q : D.X → (FractionRing R)ˣ), (∀ y, algebraMap (FractionRing R) F (q (ν.eX y)) = ((u ^ (β.be y y / 2) : Fˣ) : F)) → ∃ ν' : NumOf (TauTwist.rescale D q) F (N.twist β u), (∀ y : N.X, ν'.eX y = ν.eX y) ∧ ∀ x : N.A, ν'.eA x = ν.eA x := by
  intro R _ _ D F _ _ N ν k β u q hq
  refine ⟨{ J := ν.J, good := ν.good, th := ν.th, th_gen := ν.th_gen, eA := ν.eA, eX := ν.eX, c_eq := ν.c_eq,
            θ_eq := ν.θ_eq, σ_eq := ν.σ_eq, th_eq := ν.th_eq, ψ_eq := fun (χ : N.X) => ?_ }, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans ?_ (congrArg (· * _) (vF_psi_rescale D q (ν.eX χ) ν.good).symm)
  show ((N.ψ χ * u ^ (β.be χ χ / 2) : Fˣ) : F) = _
  rw [Units.val_mul, ν.ψ_eq, hq]
  exact (mul_comm _ _).trans (_root_.mul_assoc _ _ _).symm

end GlobalTheory.RescaleValues
end
