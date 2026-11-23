module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015

@[expose] public section

section

noncomputable section

namespace GlobalTheory

namespace KerPerp

variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}

theorem exists_isotropic_section [Module.Projective O Y] {w : O} (hw : w + star w = 1) (halt : EF.IsAlt)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ s : Y →ₗ[O] L, (∀ x, y (s x) = x) ∧ ∀ x x', EF (s x) (s x') = 0 := by
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property y LinearMap.id hy
  have hs0' : ∀ x, y (s0 x) = x := fun x => LinearMap.congr_fun hs0 x
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : kerPerp hadj y ≤ LinearMap.ker y := fun t ht => hle t (mem_kerPerp.1 ht)
  obtain ⟨be, hbe_apply⟩ : ∃ be : LinearMap.BilinForm ℤ Y,
      ∀ x x', be x x' = EF (s0 x) (s0 (w • x')) :=
    ⟨EF.compl₁₂ s0.toAddMonoidHom.toIntLinearMap
      (s0.toAddMonoidHom.toIntLinearMap ∘ₗ (LinearMap.lsmul O Y w).toAddMonoidHom.toIntLinearMap),
      fun _ _ => rfl⟩
  have hbe : ∀ (a : O) x x', be (a • x) x' = be x (star a • x') := by
    intro a x x'
    rw [hbe_apply, hbe_apply, map_smul s0 a x, hadj, map_smul s0 w (star a • x'), map_smul s0 w x',
      map_smul s0 (star a) x', smul_comm]
  have hn := neg_apply_nilTo hadj hb hy hbe
  refine ⟨s0 + (kerPerp hadj y).subtype ∘ₗ nilTo hadj hb hy hbe ∘ₗ s0, fun x => ?_, fun x x' => ?_⟩
  · have h0 : y ((nilTo hadj hb hy hbe (s0 x) : L)) = 0 :=
      LinearMap.mem_ker.1 (hle' (nilTo hadj hb hy hbe (s0 x)).2)
    simp [hs0', h0]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _)]
    have h1 := hn (s0 x) (s0 x')
    have h2 := hn (s0 x') (s0 x)
    rw [hs0', hs0', hbe_apply] at h1 h2
    have h3 := isotropic hle' (nilTo hadj hb hy hbe (s0 x)).2 (nilTo hadj hb hy hbe (s0 x')).2
    have h4 := skew (s0 x) (nilTo hadj hb hy hbe (s0 x'))
    have k1 : EF (s0 x') (s0 (w • x)) = -EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x, skew, hadj]
    have k2 : EF (s0 x) (s0 x') = EF (s0 x) (s0 (w • x')) + EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x', ← map_add (EF (s0 x)), ← add_smul, hw, one_smul]
    linarith

end KerPerp

theorem exists_split_of_coisotropic_ker (O L Y : Type) [CommRing O] [StarRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module.Projective O Y] (w : O)
    (EF : LinearMap.BilinForm ℤ L) (y : L →ₗ[O] Y) (hw : w + star w = 1) (halt : ∀ x, EF x x = 0)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module O M) (EM : LinearMap.BilinForm ℤ M) (e : L ≃+ Y × (Y →+ ℤ) × M),
      Function.Bijective EM ∧ (∀ v, (e v).1 = y v) ∧
      (∀ (a : O) v x, (e (a • v)).2.1 x = (e v).2.1 (star a • x)) ∧
      (∀ (a : O) v, (e (a • v)).2.2 = a • (e v).2.2) ∧
      ∀ v v', EF v v' = (e v').2.1 (e v).1 - (e v).2.1 (e v').1 + EM (e v).2.2 (e v').2.2 := by
  obtain ⟨s, hsy, hsiso⟩ := KerPerp.exists_isotropic_section (EF := EF) (y := y) hw halt hb hadj hy hle
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : KerPerp.kerPerp hadj y ≤ LinearMap.ker y := fun t ht =>
    hle t (KerPerp.mem_kerPerp.1 ht)
  obtain ⟨E, hE⟩ : ∃ E : KerPerp.kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y,
      ∀ (t : KerPerp.kerPerp hadj y) (v : L), E t (y v) = -EF t v :=
    ⟨KerPerp.equivDual hadj hb hy, KerPerp.equivDual_apply hadj hb hy⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L →ₗ[ℤ] Module.Dual ℤ Y, ∀ v x, Φ v x = -EF v (s x) :=
    ⟨-(EF.compl₂ s.toAddMonoidHom.toIntLinearMap), fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : L →ₗ[ℤ] L, ∀ v, T v = ((E.symm (Φ v) : KerPerp.kerPerp hadj y) : L) :=
    ⟨(KerPerp.kerPerp hadj y).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ Φ,
      fun _ => rfl⟩
  have hTK : ∀ v, T v ∈ KerPerp.kerPerp hadj y := fun v => by rw [hTdef]; exact (E.symm (Φ v)).2
  have hEF : ∀ (t : KerPerp.kerPerp hadj y) w, EF t w = -E t (y w) := fun t w => by rw [hE]; ring
  have hT : ∀ v w, EF (T v) w = EF v (s (y w)) := fun v w => by
    rw [hTdef, hEF, LinearEquiv.apply_symm_apply, hΦ, neg_neg]
  have hTy : ∀ v, y (T v) = 0 := fun v => LinearMap.mem_ker.1 (hle' (hTK v))
  obtain ⟨P, hP⟩ : ∃ P : L →ₗ[ℤ] L, ∀ v, P v = v - s (y v) - T v :=
    ⟨LinearMap.id - s.toAddMonoidHom.toIntLinearMap ∘ₗ y.toAddMonoidHom.toIntLinearMap - T,
      fun _ => rfl⟩
  have hPy : ∀ v, y (P v) = 0 := fun v => by
    rw [hP, map_sub, map_sub, hsy, hTy, sub_self, sub_zero]
  have hPs : ∀ v x, EF (P v) (s x) = 0 := fun v x => by
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsiso, hT, hsy]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule O L, ∀ v, v ∈ N ↔ y v = 0 ∧ ∀ x, EF v (s x) = 0 :=
    ⟨{ carrier := {v | y v = 0 ∧ ∀ x, EF v (s x) = 0}
       add_mem' := fun {a b} ha hb => ⟨by rw [map_add (f := _), ha.1, hb.1, add_zero],
         fun x => by rw [map_add (f := _), LinearMap.add_apply, ha.2, hb.2, add_zero]⟩
       zero_mem' := ⟨map_zero y, fun x => by rw [map_zero, LinearMap.zero_apply]⟩
       smul_mem' := fun c v hv => ⟨by rw [map_smul, hv.1, smul_zero],
         fun x => by rw [hadj, ← map_smul s, hv.2]⟩ }, fun _ => Iff.rfl⟩
  have hPN : ∀ v, P v ∈ N := fun v => (hN _).2 ⟨hPy v, hPs v⟩
  have hΦN : ∀ m ∈ N, Φ m = 0 := fun m hm => LinearMap.ext fun x => by
    rw [hΦ, ((hN m).1 hm).2, neg_zero, LinearMap.zero_apply]
  have hPfix : ∀ m ∈ N, P m = m := fun m hm => by
    simp [hP, ((hN m).1 hm).1, hTdef, hΦN m hm]
  have hTsmul : ∀ (a : O) v, T (a • v) = a • T v := fun a v => hb.1 (LinearMap.ext fun w => by
    rw [hT, hadj, hadj, hT, map_smul y, map_smul s])
  have hdec : ∀ v, v = s (y v) + T v + P v := fun v => by rw [hP]; abel
  have hback : ∀ φ : Module.Dual ℤ Y, φ.toAddMonoidHom.toIntLinearMap = φ :=
    fun φ => LinearMap.ext fun _ => rfl
  let e : L ≃+ Y × (Y →+ ℤ) × N :=
    { toFun := fun v => (y v, (Φ v).toAddMonoidHom, ⟨P v, hPN v⟩)
      invFun := fun p => s p.1 + ((E.symm p.2.1.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
        (p.2.2 : L)
      left_inv := fun v => by
        show s (y v) + ((E.symm (Φ v).toAddMonoidHom.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
          P v = v
        rw [hback, ← hTdef]
        exact (hdec v).symm
      right_inv := fun p => by
        obtain ⟨a, φ, m⟩ := p
        have hyt : y ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) = 0 :=
          LinearMap.mem_ker.1 (hle' (E.symm _).2)
        have hym : y (m : L) = 0 := ((hN m).1 m.2).1
        have hyv : y (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) = a := by
          rw [map_add (f := _), map_add (f := _), hsy, hyt, hym, add_zero, add_zero]
        have hΦv : Φ (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) =
            φ.toIntLinearMap := by
          refine LinearMap.ext fun x => ?_
          rw [hΦ, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hsiso, hEF, hsy,
            LinearEquiv.apply_symm_apply, ((hN m).1 m.2).2]
          simp
        refine Prod.ext hyv (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ _ x = φ x
          rw [hΦv]
          rfl
        · show P _ = m
          rw [hP, hyv, hTdef, hΦv]
          exact (fun p q r : L => show p + q + r - p - q = r by abel) _ _ _
      map_add' := fun a b => by
        refine Prod.ext (map_add y a b) (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ (a + b) x = Φ a x + Φ b x
          rw [map_add (f := _), LinearMap.add_apply]
        · show P (a + b) = P a + P b
          exact map_add P a b }
  refine ⟨N, inferInstance, inferInstance,
    EF.compl₁₂ N.subtype.toAddMonoidHom.toIntLinearMap N.subtype.toAddMonoidHom.toIntLinearMap, e,
    ⟨?_, ?_⟩, fun v => rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    apply hb.1
    refine LinearMap.ext fun w => ?_
    have hm' : EF (m : L) (P w) = 0 := by
      simpa using LinearMap.congr_fun hm ⟨P w, hPN w⟩
    have hmN := (hN m).1 m.2
    rw [Submodule.coe_zero, map_zero, LinearMap.zero_apply, hdec w, map_add (f := _), map_add (f := _), hmN.2, hm',
      skew, hT, hmN.1, map_zero, map_zero]
    simp
  · intro g
    obtain ⟨v, hv⟩ := hb.2 (g ∘ₗ (AddMonoidHom.mk' (fun v => (⟨P v, hPN v⟩ : N))
      (fun a b => Subtype.ext (map_add P a b))).toIntLinearMap)
    refine ⟨⟨P v, hPN v⟩, LinearMap.ext fun m => ?_⟩
    have h1 : EF v m = g ⟨P m, hPN m⟩ := LinearMap.congr_fun hv m
    have h2 : (⟨P m, hPN m⟩ : N) = m := Subtype.ext (hPfix m m.2)
    have hmN := (hN m).1 m.2
    show EF (P v) m = g m
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, skew (s (y v)), hmN.2, hT, hmN.1, map_zero, map_zero]
    simp
  · intro a v x
    show Φ (a • v) x = Φ v (star a • x)
    rw [hΦ, hΦ, hadj, map_smul s]
  · intro a v
    refine Subtype.ext ?_
    show P (a • v) = a • P v
    rw [hP, hP, map_smul y, map_smul s, hTsmul, smul_sub, smul_sub]
  · intro v v'
    show EF v v' = Φ v' (y v) - Φ v (y v') + EF (P v) (P v')
    rw [hΦ, hΦ, hP, hP]
    simp only [map_sub, LinearMap.sub_apply]
    have f1 := hT v v'
    have f2 := hT v (s (y v'))
    rw [hsy] at f2
    have f3 : EF v (T v') = -EF v' (s (y v)) := by rw [skew, hT]
    have f4 : EF (s (y v)) (T v') = -EF v' (s (y (s (y v)))) := by rw [skew, hT]
    rw [hsy] at f4
    have f5 := hsiso (y v) (y v')
    have f6 : EF (T v) (T v') = 0 := KerPerp.isotropic hle' (hTK v) (hTK v')
    have f7 := skew (s (y v)) v'
    linarith

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.torusExtension_complexPoints_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  first | exact @GlobalTheory.TorusExtChar.points_eq_characters | exact GlobalTheory.TorusExtChar.points_eq_characters | (intros; apply GlobalTheory.TorusExtChar.points_eq_characters <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

section Val

variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

variable {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valR_of_corr (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (e : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (h : LB.Gen.Corr L φ ε φ' ε t t')
    (x : Sp A ⟶ Y) (j : K → L.ι) :
    valR x (LB.wchart L φ j) (t.s j).val = valR x (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  rw [TorusCoord.gen_eq_of_corr hL ht ht' h]

theorem top_le_wchart_iff {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    ⊤ ≤ LB.wchart L (fun k => h ≫ φ k) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j :=
  ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
    fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩

theorem valR_pullGen (φ : K → (Y ⟶ X)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Sp A ⟶ Y) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valR h (LB.wchart L φ j) (t.s j).val := by
  by_cases H : ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j
  · have H' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := (top_le_wchart_iff φ h j).2 H
    refine (HolHom.valR_res (𝟙 (Sp A)) _ _ H').trans ?_
    exact (HolHom.valR_comp (𝟙 (Sp A)) h _ _).symm.trans (by rw [Category.id_comp]; rfl)
  · have H' : ¬ ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun H' => H ((top_le_wchart_iff φ h j).1 H')
    exact (dif_neg H').trans (Eq.symm (show valR h (LB.wchart L φ j) (t.s j).val = 0 from dif_neg H))

end Val

section Pull

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

theorem gtφT_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) :
    Out.DegPre.gtφT D T' b' χ = fun k => h ≫ Out.DegPre.gtφT D T b χ k := by
  funext k
  rw [TorusCoord.gtφT_eq, ← Category.id_comp (D.Oφ b' χ k)]
  exact ((TorusCoord.comp_eq_of_left b b' h (𝟙 _) (by rw [Category.id_comp, e])).1 χ k).symm

theorem top_le_wchart_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D T' b' χ) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D T b χ) j := by
  rw [gtφT_pull e, top_le_wchart_iff]

theorem valR_of_isPull {A : Type} [CommRing A] {p : Sp A ⟶ Sp R} {T : Over (Sp R)} {g : Out.GtPt D T}
    {g' : Out.GtPt D (Over.mk p)} {h : Sp A ⟶ T.left} (H : Out.GtPt.IsPull (T' := Over.mk p) h g g') (χ : D.X)
    (j : Fin 4 → D.P.L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart D.P.L (Out.DegPre.gtφT D (Over.mk p) g'.b χ) j) ((g'.s χ).s j).val =
      valR h (LB.wchart D.P.L (Out.DegPre.gtφT D T g.b χ) j) ((g.s χ).s j).val :=
  (valR_of_corr D.P.isLB (gtφT_pull H.1 χ) (g'.isGen χ) (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) (H.2 χ) _ j).trans
    (valR_pullGen _ _ h j)

end Pull

section Ex

variable [Algebra (FractionRing ℂ) ℂ] {D : Out.DegPre ℂ} {g : ℕ} {ex : (Fin g → ℂ) → Out.GtPtF D ℂ}

theorem b_add (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (z z' : Fin g → ℂ) :
    (ex (z + z')).b = (ex z).b * (ex z').b := (h z z').1

theorem b_zero (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) : (ex 0).b = 1 := by
  have := b_add h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem b_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (n : ℕ) (z : Fin g → ℂ) :
    (ex ((n : ℂ) • z)).b = (ex z).b ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, b_zero h]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, b_add h, ih, pow_succ]

theorem top_le_wchart_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) {n : ℕ} {b₀ : D.P.A ⟶ D.P.A}
    (hb : b₀ = 𝟙 D.P.A ^ n) (z : Fin g → ℂ) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b χ) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A b₀ χ) j :=
  top_le_wchart_pull (T' := Out.TF (R := ℂ) ℂ) (h := (ex z).b.left) (by
    rw [b_nsmul h, hb, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]) χ j

theorem tf_hom [IsScalarTower ℂ (FractionRing ℂ) ℂ] : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

def IsRatio (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (n : ℕ) (s₀ : Out.GtPt D D.P.A) (u : D.X → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ x z j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j →
    chiVal (ex ((n : ℂ) • z)) x j = u x z * valAt' (show Sp ℂ ⟶ _ from (ex z).b.left)
      (LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A s₀.b x) j) ((s₀.s x).s j).val

end Ex

end GlobalTheory.AbelianLetters
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  first | exact @GlobalTheory.RigIso.main | exact GlobalTheory.RigIso.main | (intros; apply GlobalTheory.RigIso.main <;> assumption)
end
