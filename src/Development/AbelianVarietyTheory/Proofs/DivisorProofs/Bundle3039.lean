module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionEndomorphismGraphOfTorsionAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautUniq

theorem lamVal_eq_of_rig : ∀ {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}, M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (w₁ w₂ : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), w₁.IsGen → w₂.IsGen → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₁ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B').left) (z : Z) J J', Good M z J → Good M' z J' → lamVal w₁ p z J J' = lamVal w₂ p z J J' := by
  intro S S' B B' _ _ _ _ M M' β₂ hM hM' hB' w₁ w₂ h₁ h₂ n₁ n₂ Z p z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have hp := surj_comp (surj_snd hG hB' _) (hG _ _ hB').2
  have mem : ∀ {Y : Scheme.{0}} (q : Y ⟶ (G2 B').left) (y : Y) {J₀ : (Y ⟶ B.left) → M.ι}
      {J₀' : (Y ⟶ B'.left) → M'.ι}, Good M y J₀ → Good M' y J₀' →
      q y ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
        (fun _ I => J₀ (q ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₀' (q ≫ (psum B' (x2 B') I.down).left)) :=
    fun q y J₀ J₀' h h' => TopologicalSpace.Opens.mem_inf.2
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => h (q ≫ β₂ ≫ (psum B (x2 B) I.down).left),
       h'.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) q⟩
  have hw : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) _ _ he2 hp h₁ h₂ (fun s a ha => ?_)
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y
      exact ⟨_, mem (𝟙 _) y hJ₁ hJ₁'⟩
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM s
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' s
      have hb := mem (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s hJ₁ hJ₁'
      have tr : ∀ {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)}, w.IsGen → lamVal w (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s J₁ J₁' = 1 →
          gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a) (w.s a) =
            gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a ⊓ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).g a
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left))) := by
        intro w hw hv
        have := congrArg (gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s _) (hw a
          (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
           fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
        rw [map_mul, gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩),
          gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩)] at this
        rw [this]
        unfold lamVal at hv
        rw [hv, _root_.mul_one]
      rw [tr h₁ (n₁ _ s J₁ J₁' hJ₁ hJ₁'), tr h₂ (n₂ _ s J₁ J₁' hJ₁ hJ₁')]
  rw [hw]

end GlobalTheory.TautUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.LamComp


open GlobalTheory.HalfBC GlobalTheory.PrimCocycle in
theorem lam_comp : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁)), w₁.IsGen → ∃ w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  intro SA SB SC A _ _ B _ _ C _ _ MA MB MC hA hB hC m₁ m₂ m hm w₂ h₂ w₁ h₁
  subst hm
  have lA : (abelian₂ A MA).IsLB := DVR.linComb_isLB _ hA _ _
  have lB : (abelian₂ B MB).IsLB := DVR.linComb_isLB _ hB _ _
  have lC : (abelian₂ C MC).IsLB := DVR.linComb_isLB _ hC _ _
  have p₂ := (isGen_iff _).1 h₂
  have p₁ := (isGen_iff _).1 h₁
  obtain ⟨w, T⟩ := exists_comp lB w₂ w₁ p₂ p₁ lC lA
  refine ⟨w, (isGen_iff _).2 (T.pgen_comp lB p₂ p₁), fun Z p z JA JB JC gA gB gC => ?_⟩
  have t := T Z p z (fun k => JC ((p ≫ m₁ ≫ m₂) ≫ lamφ C k))
    (fun k => JB ((p ≫ m₁) ≫ lamφ B k)) (fun k => JA (p ≫ lamφ A k))
    (Set.mem_iInter.2 fun k => gC ((p ≫ m₁ ≫ m₂) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => gB ((p ≫ m₁) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => gA (p ≫ lamφ A k))
  rw [mul_comm]
  show Geo.Tor.gw w p z (fun k => JC (p ≫ (m₁ ≫ m₂) ≫ lamφ C k)) (fun k => JA (p ≫ lamφ A k)) =
    Geo.Tor.gw w₂ (p ≫ m₁) z (fun k => JC ((p ≫ m₁) ≫ m₂ ≫ lamφ C k)) (fun k => JB ((p ≫ m₁) ≫ lamφ B k)) *
    Geo.Tor.gw w₁ p z (fun k => JB (p ≫ m₁ ≫ lamφ B k)) (fun k => JA (p ≫ lamφ A k))
  simp only [Category.assoc] at t ⊢
  exact t

end GlobalTheory.LamComp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauOnOpen

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens}

theorem tauW_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tauW_generic (ψW : PsiOn D W) (a b : D.X) (lam : (TK R).left ⟶ W.toScheme) (h : lam ≫ W.ι = jK R)
    (z : (TK R).left) (J) (hJ : Good D.P.L z J) : val (ψW.tau a b) lam z J = val (D.tau a b) (𝟙 _) z J := by
  have hW : lam ≫ W.ι = 𝟙 _ ≫ jK R := h.trans (Category.id_comp _).symm
  obtain ⟨mu, l₁, l₂⟩ : ∃ mu : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, mu ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      mu ≫ (jK R ∣_ W) = lam :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have vψ : ∀ χ, val (ψW.psi χ) lam z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
    have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) mu).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at e
    exact e
  have vρ : val (D.rigW W) lam z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun q => val D.rig q z J) hW
  refine (TauPull.val_tauW ψW lam hJ a b).trans (Eq.trans ?_ (TauPull.val_tau (𝟙 _) hJ a b).symm)
  rw [← vψ, ← vψ, ← vψ, ← vρ]

end GlobalTheory.TauOnOpen

namespace GlobalTheory

theorem exists_tau_onOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  intro R _ _ D W ψW a b
  obtain ⟨t, ht, hv⟩ : ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TW W).left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (ψW.tau a b) r z J := by
    refine exists_gen D.P.isLB (fun U _ h => ?_) (ψW.tau a b) (TauOnOpen.tauW_isGen ψW a b)
    have e₁ : (toUnit (TW W) ≫ D.c (a + b)).left = ((toUnit (TW W) ≫ D.c a) * (toUnit (TW W) ≫ D.c b)).left := by
      rw [D.c_add]; exact congrArg (fun q : TW W ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TW W)) (D.c a) (D.c b))
    have e₂ : (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
    simp [lamPts, negε]
  exact ⟨t, ht, hv, fun lam h z J hJ => (hv _ lam z J hJ).trans (TauOnOpen.val_tauW_generic ψW a b lam h z J hJ)⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.LamCancel

theorem lam_cancel : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m)), w.IsGen → ∃ w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁), w₁.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  intro SA SB SC A _ _ B _ _ C _ _ MA MB MC hA hB hC m₁ m₂ m hm w₂ h₂ w hw
  subst hm
  have lA : (abelian₂ A MA).IsLB := DVR.linComb_isLB _ hA _ _
  have lB : (abelian₂ B MB).IsLB := DVR.linComb_isLB _ hB _ _
  have lC : (abelian₂ C MC).IsLB := DVR.linComb_isLB _ hC _ _
  have p₂ := (isGen_iff _).1 h₂
  have pw := (isGen_iff _).1 hw
  obtain ⟨w₁, T⟩ := Geo.Tor.exists_cancel lC w₂ w p₂ pw lB lA
  refine ⟨w₁, (isGen_iff _).2 (T.pgen_cancel lC p₂ pw), fun Z p z JA JB JC gA gB gC => ?_⟩
  have t := T Z p z (fun k => JC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left)) (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    (Set.mem_iInter.2 fun k => gC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (Set.mem_iInter.2 fun k => gB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    (Set.mem_iInter.2 fun k => gA (p ≫ (psum A (x2 A) k.down).left))
  refine Eq.trans ?_ (t.trans ((mul_comm _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · show Geo.Tor.gw w p z (fun k => JC (p ≫ (m₁ ≫ m₂) ≫ (psum C (x2 C) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₁ p z (fun k => JB (p ≫ m₁ ≫ (psum B (x2 B) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₂ (p ≫ m₁) z (fun k => JC ((p ≫ m₁) ≫ m₂ ≫ (psum C (x2 C) k.down).left))
      (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    simp only [Category.assoc]

end GlobalTheory.LamCancel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DataPos

variable {V : Type} [CommRing V] [IsDomain V]

theorem lamPts_generic (D : DegPre V) (a b : D.X) (k : Fin 4) :
    lamPts (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b) k = jK V ≫ lamPts (D.c a) (D.c b) k := by
  have e : (toUnit (TK V)).left = jK V := GlobalTheory.Mum.UnitValuedLeadingSection.toUnit_TK_left V
  fin_cases k
  · show ((toUnit (TK V) ≫ D.c a) * (toUnit (TK V) ≫ D.c b)).left = jK V ≫ (D.c a * D.c b).left
    rw [← MonObj.comp_mul, Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c a).left = jK V ≫ (D.c a).left
    rw [Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c b).left = jK V ≫ (D.c b).left
    rw [Over.comp_left, e]
  · show (1 : TK V ⟶ D.P.A).left = jK V ≫ (1 : 𝟙_ _ ⟶ D.P.A).left
    rw [← e, ← Over.comp_left, MonObj.comp_one]

theorem lamPts_sec (D : DegPre V) (a b : D.X) (k : Fin 4) : lamPts (D.c a) (D.c b) k ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k <;> exact GlobalTheory.Mum.UnitValuedLeadingSection.left_comp_hom_unit _

theorem tau_diag_pos : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V))
    (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧
      ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε),
        ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
          Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  intro V _ _ _ D y hy
  obtain ⟨z₀⟩ : Nonempty (TK V).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.Mum.UnitValuedLeadingSection.exists_topGood V D.toPre.P z₀
  obtain ⟨u₁, hu₁⟩ :=
    GlobalTheory.Mum.UnitValuedLeadingSection.tau_diag_eq_unit_mul_psi_sq V D.toPre D.tau_bimult D.psi_even z₀ J₀ hJ₀ y
  obtain ⟨r₀, hr₀, e₀⟩ :=
    (GlobalTheory.Mum.UnitValuedLeadingSection.psiIn_iff_val V D.toPre z₀ J₀ hJ₀ y (maximalIdeal V)).1 (D.psi_pos y hy)
  have hr : (u₁ : V) * r₀ ^ 2 ∈ maximalIdeal V :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr₀ 2 two_pos)
  have eT : ((val (D.toPre.tau y y) (𝟙 _) z₀ J₀ : ((TK V).left.presheaf.stalk z₀)ˣ) : (TK V).left.presheaf.stalk z₀) =
      GlobalTheory.Mum.UnitValuedLeadingSection.thK V z₀ (algebraMap V _ ((u₁ : V) * r₀ ^ 2)) := by
    rw [hu₁, Units.val_mul, Units.val_pow_eq_pow_val, e₀, map_mul, map_mul, map_pow, map_pow]
    rfl
  have hr0 : algebraMap V (FractionRing V) ((u₁ : V) * r₀ ^ 2) ≠ 0 := by
    intro h
    have := (val (D.toPre.tau y y) (𝟙 _) z₀ J₀).ne_zero
    rw [eT, h, map_zero] at this
    exact this rfl
  refine ⟨_, hr, Units.mk0 _ hr0, rfl, ?_⟩

  set k : (FractionRing V)ˣ := Units.mk0 _ hr0 with hk
  set φV := lamPts (D.toPre.c y) (D.toPre.c y) with hφVdef
  set φK := lamPts (toUnit (TK V) ≫ D.toPre.c y) (toUnit (TK V) ≫ D.toPre.c y) with hφKdef
  have hφ : ∀ k, φK k = jK V ≫ φV k := lamPts_generic D.toPre y y
  let jst : Fin 4 → D.toPre.P.L.ι := fun k => J₀ (jK V ≫ φV k)
  have hint : ∀ k, φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) = ⊤ := fun k => hJ₀.2 (φV k) (lamPts_sec D.toPre y y k)
  have htop : LB.wchart D.toPre.P.L φV jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    exact this
  have htopK : LB.wchart D.toPre.P.L φK jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : jK V p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    show p ∈ (φK k).base ⁻¹' (D.toPre.P.L.U (jst k) : Set _)
    rw [hφ k]
    exact this
  have hle : ∀ j, LB.wchart D.toPre.P.L φV j ≤ LB.wchart D.toPre.P.L φV j ⊓ LB.wchart D.toPre.P.L φV jst :=
    fun j => le_inf le_rfl (by rw [htop]; exact le_top)
  let u : LB.Gen (LB.LinComb D.toPre.P.L φV negε) := ⟨fun j => res (hle j) ((LB.LinComb D.toPre.P.L φV negε).g j jst)⟩
  obtain ⟨t, htg, ht⟩ := GlobalTheory.PolDeg.Wit.exists_tau D.toPre y y

  have hkey : t.s jst = res le_top (unitOn k) := by
    refine unit_ext fun x hx => ?_
    obtain rfl : x = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) x z₀
    refine Units.ext ?_
    rw [gm_res _ x _ hx]
    have e1 : gm (𝟙 _) x ((LB.LinComb D.toPre.P.L φK negε).U jst) (t.s jst) = val t (𝟙 _) x J₀ :=
      (val_of t (𝟙 _) x J₀ jst (fun k => by show J₀ (𝟙 _ ≫ φK k) = J₀ (jK V ≫ φV k); rw [Category.id_comp, hφ k])).symm
    rw [e1, ht _ _ x J₀ hJ₀.1, eT]
    have e2 := GlobalTheory.RefTauCoord.gm_unitOn (R := V) (RingHom.id (FractionRing V)) x k
    have e3 : spMap (RingHom.id (FractionRing V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e3] at e2
    exact e2.symm
  refine ⟨u, fun Z ρ z J hJ => ?_⟩
  have hmK : ρ z ∈ LB.wchart D.toPre.P.L φK jst := by rw [htopK]; trivial
  have hmV : (ρ ≫ jK V) z ∈ LB.wchart D.toPre.P.L φV jst := by rw [htop]; trivial
  have L1 : val (D.toPre.tau y y) ρ z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst * gm ρ z ⊤ (unitOn k) := by
    rw [← ht Z ρ z J hJ]
    refine (gen_trans htg ρ z (hJ.mem φK ρ) hmK).trans ?_
    rw [hkey]
    exact congrArg (_ * ·) (gm_res _ z _ hmK _)
  have L2 : val u (ρ ≫ jK V) z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    have hm := hJ.mem φV (ρ ≫ jK V)
    exact (gm_res _ z (hle _) hm _).trans (gm_linComb _ _ _ _ z _ _ hm hmV)
  have L3 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF
    refine Finset.prod_congr rfl fun k _ => ?_
    have e : ρ ≫ φK k = (ρ ≫ jK V) ≫ φV k := by rw [hφ k, Category.assoc]
    have h : ∀ a b : Z ⟶ D.toPre.P.A.left, a = b →
        gm a z (D.toPre.P.L.U (J a) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J a) (jst k)) =
          gm b z (D.toPre.P.L.U (J b) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J b) (jst k)) := by
      rintro a b rfl; rfl
    exact congrArg (· ^ negε k) (h _ _ e)
  rw [L1, L2, L3, mul_comm]

end GlobalTheory.DataPos
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.refinesPolarised_pullback_injective : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  first | exact @GlobalTheory.RefPull.refines_pull | exact GlobalTheory.RefPull.refines_pull | (intros; apply GlobalTheory.RefPull.refines_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  first | exact @GlobalTheory.PairPts.lamPts_fst_eq_psum | exact GlobalTheory.PairPts.lamPts_fst_eq_psum | (intros; apply GlobalTheory.PairPts.lamPts_fst_eq_psum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

def siegLamData (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := Q.B
  ab := Q.isAb
  P := abelian₂ Q.B Q.M.L
  isLB := LB.isLB_linComb Q.M.isLB _ _
  rig₁ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull Q.M.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG Q.isAb (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) _

theorem lbIso_diag_data {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    LBIso ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left)
      (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
  have hL := Q.M.isLB
  have hT : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have hc := fun x y z => diff₃_ptCls (T := Q.B) hL hT x y z
  have hrM : Out.Rigidified Q.B Q.M.L := ⟨Q.M.rig, Q.M.rigGen⟩
  have p1 : ptCls Q.M.L Q.B 1 = 1 := ptCls_one hL hrM Q.B
  have einv : GrpObj.inv (X := Q.B) = (𝟙 Q.B)⁻¹ := by simp [Hom.inv_def]
  have key : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B) =
      ptCls Q.M.L Q.B (𝟙 Q.B) * ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹ := by
    have a := diff₂_mul_right hc (𝟙 Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹
    rw [mul_inv_cancel] at a
    have b : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) 1 = 1 := by
      simp only [diff₂, _root_.mul_one, p1, inv_one, mul_inv_cancel]
    have c : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹ =
        1 * (ptCls Q.M.L Q.B (𝟙 Q.B))⁻¹ * (ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹)⁻¹ * 1 := by
      rw [diff₂, mul_inv_cancel, p1]
    rw [b, c] at a
    exact GlobalTheory.AdjPolLocal.le_val_one_add_pow_sub a
  refine lbIso_nested hL _ _ _ _ _ _ ?_
  rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_two]
  refine (prod_lam _ _ (cls Q.M.L)).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one]
  refine key.trans ?_
  rw [einv]
  rfl

theorem relAmple_diag {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : Data R)
    (hD : ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left).IsLB) :
    RelAmple Q.B ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left) := by
  have := Q.isAb.proper
  have hMa : IsAmpleLB Q.M.L := isAmpleLB_of_relAmple_of_isAffine Q.B Q.M.isLB Q.ample
  have hN : IsAmpleLB (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
    have := GlobalTheory.GraphVolume.isAmpleLB_graph hMa (GrpObj.inv (X := Q.B)).left (N := 1) le_rfl
    rwa [Nat.cast_one] at this
  have hDa := hN.of_lbIso hD (lbIso_diag_data Q)
  refine relAmple_of_isAmpleLB Q.B hD fun U hU => ?_
  have : CompactSpace (Q.B.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := Q.B.hom) _ U.isOpen hU.isCompact)
  exact hDa.pull_of_isOpenImmersion _

end GlobalTheory.MumFam.TensPol

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

end GlobalTheory.MumFam.TensPol
end
end
