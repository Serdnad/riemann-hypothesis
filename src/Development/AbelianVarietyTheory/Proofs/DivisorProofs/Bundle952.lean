module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle928
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UPel.HT.LevPull

theorem exists_pull_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  intro p _ D N H AH _ _ actH Y u hadd hlin htor
  let AE : Over Y.left := (Over.pullback Y.hom).obj AH
  letI iG : GrpObj AE := Functor.grpObjObj
  letI iC : IsCommMonObj AE := Functor.isCommMonObj_obj
  let φE : AE.left ⟶ AH.left := pullback.fst AH.hom Y.hom
  have hg : IsGrpPullback AE AH Y.hom φE := isGrpPullback_pullback AH Y.hom
  have inj : ∀ {T : Over Y.left} {x y : T ⟶ AE}, x.left ≫ φE = y.left ≫ φE → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext h (by rw [Over.w, Over.w]))
  have pm : ∀ {T : Over Y.left} (x y : T ⟶ AE), (x * y).left ≫ φE = (pushPt hg.1.w x * pushPt hg.1.w y).left :=
    fun x y => (hg.2 _ x y _ _ rfl rfl).symm

  let act' : D.O → (AE ⟶ AE) := fun a => Over.homMk (hg.1.lift (φE ≫ (actH.act a).left) AE.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φE = φE ≫ (actH.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over Y.left} (x : T ⟶ AE) a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ actH.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have injP : ∀ {T : Over Y.left} {x y : T ⟶ AE}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun h =>
    inj (congrArg (fun q => q.left) h)
  have pm' : ∀ {T : Over Y.left} (x y : T ⟶ AE), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
    fun x y => map_mul (pushHom hg _) x y
  let actE : OActN D.O AE :=
    { act := act'
      hom := fun a => isMonHom_of_mul _ fun T x y => injP (by
        have := actH.hom a
        rw [pa, pm', pm', pa, pa, MonObj.mul_comp])
      one := injP (by rw [← Category.id_comp (act' 1), pa, actH.one, Category.comp_id])
      mul := fun a b => injP (by
        rw [← Category.id_comp (act' (a * b)), pa, pa, actH.mul, ← Category.id_comp (act' b), pa, Category.assoc])
      add := fun a b => injP (by
        refine Eq.trans ?_ (pm' (act' a) (act' b)).symm
        rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa,
          actH.add]
        exact MonObj.comp_mul _ _ _) }

  let ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE) := fun y =>
    Over.homMk (hg.1.lift (u y).left (𝟙_ (Over Y.left)).hom (by rw [Over.w (u y)]; simp)) (hg.1.lift_snd _ _ _)
  have hη : ∀ y, (ηE y).left ≫ φE = (u y).left := fun y => hg.1.lift_fst _ _ _
  have hT : (𝟙_ (Over Y.left)).hom ≫ Y.hom = Y.hom := by simp
  have one_congr : ∀ {a b : Y.left ⟶ H}, a = b → (1 : Over.mk a ⟶ AH).left = (1 : Over.mk b ⟶ AH).left := by
    intro a b h; subst h; rfl
  refine ⟨AE, inferInstance, inferInstance, φE, actE, ηE, hg, ha, ⟨fun x y => inj ?_, fun c x => inj ?_,
    fun x => inj ?_⟩, hη⟩
  · rw [hη, pm, hadd]
    exact (mul_left_congr hT (pushPt hg.1.w (ηE x)) (pushPt hg.1.w (ηE y)) (u x : Over.mk Y.hom ⟶ AH) (u y) (hη x) (hη y)).symm
  · show (ηE (c • x)).left ≫ φE = ((ηE x).left ≫ (act' c).left) ≫ φE
    rw [hη, hlin, Category.assoc, ha, ← Category.assoc, hη]; rfl
  · rw [hη, htor]
    have e := congrArg (fun q => q.left) (map_one (pushHom hg (𝟙_ (Over Y.left))))
    refine Eq.trans ?_ e.symm
    exact (one_congr hT).symm

end GlobalTheory.UPel.HT.LevPull
end
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem isRayL_mul_prime_wideInd {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥)
    (hpm : 𝔭 ⊔ 𝔪 = ⊤) (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z)
    (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  have hN : ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hp)
  refine ⟨?_, ?_⟩
  · refine hZ.1.sub (DifferentiableOn.mul (fun s _ => ?_) hZ'.1)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hN)).differentiableWithinAt
  intro s hs
  classical
  set S : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I} with hSdef
  set A : Set (Ideal (𝓞 F)) := {I | CoprimeTo F (𝔪 * 𝔭) I} with hAdef
  set B : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I ∧ ¬ CoprimeTo F (𝔪 * 𝔭) I} with hBdef
  let g : ClassGroup (𝓞 F) → Ideal (𝓞 F) → ℂ := fun D I => (wideInd D I : ℂ) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)
  have h1 : HasSum (S.indicator (g C)) (Z s) := (hasSum_subtype_iff_indicator (s := S)).mp (hZ.2 s hs)
  have h2 : HasSum (S.indicator (g (C * (cls 𝔭)⁻¹))) (Z' s) :=
    (hasSum_subtype_iff_indicator (s := S)).mp (hZ'.2 s hs)
  have hAS : ∀ I, CoprimeTo F (𝔪 * 𝔭) I → CoprimeTo F 𝔪 I := fun I h =>
    ⟨h.1, eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_left _))⟩
  have hsplit : S.indicator (g C) = A.indicator (g C) + B.indicator (g C) := by
    funext I
    simp only [Pi.add_apply, Set.indicator, hSdef, hAdef, hBdef, Set.mem_setOf_eq]
    by_cases hA : CoprimeTo F (𝔪 * 𝔭) I
    · simp [hA, hAS I hA]
    · by_cases hS : CoprimeTo F 𝔪 I <;> simp [hA, hS]

  have hmulS : ∀ J, CoprimeTo F 𝔪 J → 𝔭 * J ∈ B := by
    intro J hJ
    refine ⟨⟨mul_ne_zero hp hJ.1, ?_⟩, fun h => ?_⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rwa [sup_comm]), sup_comm]; exact hJ.2
    · have : 𝔭 * J ⊔ 𝔭 = 𝔭 := sup_eq_right.mpr Ideal.mul_le_left
      have htop : 𝔭 * J ⊔ 𝔭 = ⊤ := eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))
      exact hmax.ne_top (this.symm.trans htop)
  have hnot : ∀ J, ¬ CoprimeTo F 𝔪 J → 𝔭 * J ∉ B := by
    intro J hJ hB
    apply hJ
    refine ⟨fun h0 => hB.1.1 (by simp [h0]), eq_top_iff.mpr (hB.1.2.symm.le.trans (sup_le_sup_right Ideal.mul_le_right _))⟩
  have hB_range : ∀ I ∈ B, ∃ J, 𝔭 * J = I := by
    intro I hI
    have hItop : I ⊔ 𝔭 ≠ ⊤ := by
      intro h
      apply hI.2
      refine ⟨hI.1.1, ?_⟩
      rw [Ideal.sup_mul_eq_of_coprime_right h]; exact hI.1.2
    have hle : I ≤ 𝔭 := le_sup_left.trans (hmax.eq_of_le hItop le_sup_right).ge
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    exact ⟨J, hJ.symm⟩
  have hinj : Function.Injective (fun J : Ideal (𝓞 F) => 𝔭 * J) := fun J J' h => mul_left_cancel₀ hp h
  have hcomp : (B.indicator (g C)) ∘ (fun J => 𝔭 * J) =
      fun J => ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * S.indicator (g (C * (cls 𝔭)⁻¹)) J := by
    funext J
    simp only [Function.comp_apply]
    by_cases hJ : CoprimeTo F 𝔪 J
    · rw [Set.indicator_of_mem (hmulS J hJ), Set.indicator_of_mem (show J ∈ S from hJ)]
      simp only [g, wideInd]
      rw [cls_mul hp hJ.1, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      have : (cls 𝔭 * cls J = C) ↔ (cls J = C * (cls 𝔭)⁻¹) := by
        rw [eq_mul_inv_iff_mul_eq, mul_comm]
      by_cases hc : cls J = C * (cls 𝔭)⁻¹
      · simp [hc, this.mpr hc]
      · simp [hc, mt this.mp hc]
    · rw [Set.indicator_of_notMem (hnot J hJ), Set.indicator_of_notMem (show J ∉ S from hJ), mul_zero]
  have h3 : HasSum (B.indicator (g C)) (((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    rw [← hinj.hasSum_iff (fun I hI => ?_), hcomp]
    · exact h2.mul_left _
    · by_contra hne
      obtain ⟨J, rfl⟩ := hB_range I (Set.mem_of_indicator_ne_zero hne)
      exact hI ⟨J, rfl⟩
  have h4 : HasSum (A.indicator (g C)) (Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    have := h1.sub h3
    rw [hsplit] at this
    have e : (fun b => (A.indicator (g C) + B.indicator (g C)) b - B.indicator (g C) b) = A.indicator (g C) := by
      funext I; simp
    rwa [e] at this
  exact (hasSum_subtype_iff_indicator (s := A)).mpr h4

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem f_eq_of_pt_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z Y : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (p : Y ⟶ pullback A.hom x.t)
    (q : Y ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst h
  rw [pullback.hom_ext h1 h2]

theorem exists_glue_data : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), ∀ i, 𝒰.f i ≫ t = (x i).t ∧ ∀ e : pullback A.hom (x i).t ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ → e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒰.f i → e ≫ f = (x i).f := by
  intro S A B _ _ L M hL hM Z 𝒰 x hx
  have hxt : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).t = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).t :=
    fun i j => congrArg Pt.t (hx i j _ _ _ pullback.condition)
  obtain ⟨t, ht⟩ : ∃ t : Z ⟶ S, ∀ i, 𝒰.f i ≫ t = (x i).t :=
    ⟨_, fun i => 𝒰.ι_glueMorphisms _ hxt i⟩
  have c1 : ∀ i, pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.snd A.hom t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i := fun i => pullback.condition
  have hw : ∀ i, (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ (x i).t := by
    intro i
    rw [Category.assoc, pullback.condition, ← Category.assoc, c1, Category.assoc, ht]
  have hu1 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.fst A.hom (x i).t = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t :=
    fun i => pullback.lift_fst _ _ _
  have hu2 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.snd A.hom (x i).t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) := fun i => pullback.lift_snd _ _ _
  have hc : ∀ i j, pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw i) ≫ (x i).f) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw j) ≫ (x j).f) := by
    intro i j
    have c3 : pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f j) := pullback.condition
    have hbc : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ 𝒰.f i = (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← c1, ← c1, ← Category.assoc, ← Category.assoc, c3]
    have H := hx i j _ _ _ hbc
    have e1 : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw i)),
        hu2, Category.assoc]
    have e2 : (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw j)),
        hu2, Category.assoc]
    obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t),
        p ≫ pullback.fst _ _ = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _ ∧ p ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨q, hq1, hq2⟩ : ∃ q : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t),
        q ≫ pullback.fst _ _ = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _ := by
      rw [hp1, hq1, hu1, hu1, ← Category.assoc, ← Category.assoc, c3]
    have h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _ := by rw [hp2, hq2]
    have K : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).f = q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).f :=
      f_eq_of_pt_eq H p q h1 h2
    have p1 : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hp1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hp2, Category.id_comp, Category.assoc, hu2]
    have p2 : q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hq1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hq2, Category.id_comp, Category.assoc, hu2]
    rw [← Category.assoc, ← Category.assoc, ← p1, ← p2]
    exact (Category.assoc _ _ _).trans (K.trans (Category.assoc _ _ _).symm)
  let 𝒱 := 𝒰.pullback₁ (pullback.snd A.hom t)
  refine ⟨t, Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc, fun i => ⟨ht i, fun e he1 he2 => ?_⟩⟩
  have hι : pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc = pullback.lift _ _ (hw i) ≫ (x i).f :=
    Scheme.Cover.ι_glueMorphisms 𝒱 _ hc i
  have hv : e ≫ pullback.snd A.hom t = pullback.snd A.hom (x i).t ≫ 𝒰.f i := he2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : pullback A.hom (x i).t ⟶ pullback (pullback.snd A.hom t) (𝒰.f i),
      v ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = e ∧ v ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i) = pullback.snd A.hom (x i).t :=
    ⟨pullback.lift e _ hv, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hvu : v ≫ pullback.lift _ _ (hw i) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hv1, he1, Category.id_comp]
    · rw [Category.assoc, hu2, hv2, Category.id_comp]
  rw [← hv1, Category.assoc, hι, ← Category.assoc, hvu, Category.id_comp]

end GlobalTheory.EndLoc.HomGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EndLoc.HomGlue

theorem pmap_hom_ext {S Z Y : Scheme.{0}} (A : Over S) (𝒰 : Z.OpenCover) (t : Z ⟶ S)
    {g₁ g₂ : pullback A.hom t ⟶ Y} (h : ∀ i, pmap A t (𝒰.f i) ≫ g₁ = pmap A t (𝒰.f i) ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd A.hom t)) _ _ fun (i : 𝒰.I₀) => ?_
  have w : (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom =
      pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  have e : pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.lift _ _ w ≫ pmap A t (𝒰.f i) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  show pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₁ = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₂
  rw [e, Category.assoc, Category.assoc, h]

theorem over_hom_ext_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {X Y : Over Z} {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, (Over.pullback (𝒰.f i)).map g₁ = (Over.pullback (𝒰.f i)).map g₂) : g₁ = g₂ := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun (i : 𝒰.I₀) => ?_
  have e1 : ((Over.pullback (𝒰.f i)).map g₁).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₁.left := pullback.lift_fst _ _ _
  have e2 : ((Over.pullback (𝒰.f i)).map g₂).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₂.left := pullback.lift_fst _ _ _
  show pullback.fst X.hom (𝒰.f i) ≫ g₁.left = pullback.fst X.hom (𝒰.f i) ≫ g₂.left
  rw [← e1, ← e2, h i]

theorem isMonHom_of_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {G H : Over Z} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : ∀ i, IsMonHom ((Over.pullback (𝒰.f i)).map f)) : IsMonHom f := by
  constructor
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

theorem lbIso_pull_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Y' ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hL _))

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem wit_w {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) :
    pmap A t g ≫ f ≫ B.hom = pmap A t g ≫ pullback.snd A.hom t ≫ t := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, -, -, e, e1, e2, e3⟩ := h
  haveI : IsIso e := by
    have : e = hA.1.isoPullback.hom :=
      pullback.hom_ext (by rw [e1, IsPullback.isoPullback_hom_fst]) (by rw [e2, IsPullback.isoPullback_hom_snd])
    rw [this]
    infer_instance
  rw [← cancel_epi e]
  calc e ≫ pmap A t g ≫ f ≫ B.hom = (e ≫ pmap A t g ≫ f) ≫ B.hom := by simp only [Category.assoc]
    _ = A'.hom ≫ g ≫ t := by rw [e3, Category.assoc, hB.1.w, Over.w_assoc]
    _ = e ≫ pmap A t g ≫ pullback.snd A.hom t ≫ t := by
        rw [pullback.lift_snd_assoc, Category.assoc, reassoc_of% e2]

theorem isMonHom_pull_of_wit {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B)
    (hΦ : Φ.left ≫ pullback.fst B.hom t = f) : IsMonHom ((Over.pullback g).map Φ) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, hΦ', -, e, e1, e2, e3⟩ := h
  have hPA := (isGrpPullback_pullback ((Over.pullback t).obj A) g).comp (isGrpPullback_pullback A t)
  have hPB := (isGrpPullback_pullback ((Over.pullback t).obj B) g).comp (isGrpPullback_pullback B t)
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hPA hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB hPB
  have key : a.hom.left ≫ e ≫ pmap A t g = pullback.fst _ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, e1, ha']
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% e2, Over.w_assoc a.hom]
      exact pullback.condition.symm
  have hmap : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g = pullback.fst _ g ≫ Φ.left :=
    pullback.lift_fst _ _ _
  have eq : (Over.pullback g).map Φ = a.hom ≫ Φ' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply hPB.1.hom_ext
    · have lhs : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        rw [← Category.assoc, hmap, Category.assoc, hΦ]
      have rhs : (a.hom ≫ Φ' ≫ b.hom).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        simp only [Over.comp_left, Category.assoc]
        rw [hb', ← e3, ← key]
        simp only [Category.assoc]
      exact lhs.trans rhs.symm
    · exact (Over.w _).trans (Over.w _).symm
  rw [eq]
  infer_instance

theorem local_iso (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (g : Z' ⟶ Z) [IsOpenImmersion g] (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f))
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) (hΦ : Φ.left ≫ pullback.fst B.hom t = f) :
    LBIso ((L.pull (pullback.fst A.hom t)).pull (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι)
      (((M.pull (pullback.fst B.hom t)).pull Φ.left).pull
        (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, -, hI, e, e1, e2, e3⟩ := h
  set U := ((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange with hU
  have hr : Set.range ⇑(U.ι ≫ pullback.snd A.hom t) ⊆ Set.range ⇑g := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set _) := Scheme.Opens.range_ι U ▸ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 hx
  have hl : IsOpenImmersion.lift g _ hr ≫ g = U.ι ≫ pullback.snd A.hom t := IsOpenImmersion.lift_fac _ _ _
  have wl : (U.ι ≫ pullback.fst A.hom t) ≫ A.hom = IsOpenImmersion.lift g _ hr ≫ g ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ t) hl.symm).trans (Category.assoc _ _ _)
  have he' : pullback.lift _ _ wl ≫ pmap A t g = U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hl]
  have he : hA.1.isoPullback.inv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, e1, IsPullback.isoPullback_inv_fst, Category.id_comp]
    · rw [Category.assoc, e2, IsPullback.isoPullback_inv_snd, Category.id_comp]
  obtain ⟨E, hE⟩ : ∃ E, E ≫ e = pullback.lift _ _ wl :=
    ⟨pullback.lift _ _ wl ≫ hA.1.isoPullback.inv, by rw [Category.assoc, he, Category.comp_id]⟩
  have h2 : LBIso (L.pull (U.ι ≫ pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull (U.ι ≫ Φ.left)) := by
    refine lbIso_pull hL hM E ?_ ?_ hI
    · rw [← e1, ← Category.assoc, hE, pullback.lift_fst]
    · rw [Category.assoc, hΦ, ← e3, ← Category.assoc, hE, ← Category.assoc, he']
  exact LBIso.trans (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hM _) _) _)
    (lbIso_pull_pull hL _ _) (LBIso.trans (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hM _) _) _) h2 (lbIso_pull_pull (LB.isLB_pull hM _) _ _).symm)

theorem glue_wit : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), (∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)) → HomGlue.Wit A B L M t f := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 t f hw
  have w : f ≫ B.hom = pullback.snd A.hom t ≫ t :=
    pmap_hom_ext A 𝒰 t fun i => wit_w (𝒰.f i) (hw i)
  let Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B :=
    Over.homMk (pullback.lift f (pullback.snd A.hom t) w) (pullback.lift_snd _ _ _)
  have hΦf : Φ.left ≫ pullback.fst B.hom t = f := pullback.lift_fst _ _ _
  have hΦ : IsMonHom Φ := isMonHom_of_cover 𝒰 Φ fun i => isMonHom_pull_of_wit (𝒰.f i) (hw i) Φ hΦf
  have ab_pull (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
      IsAbelianScheme ((Over.pullback t).obj G) := by
    letI := hG.comm
    letI := hG.smooth
    letI := hG.proper
    letI := hG.geomConnected
    constructor
    case comm => infer_instance
    case smooth =>
      show Smooth (pullback.snd G.hom t)
      infer_instance
    case proper =>
      show IsProper (pullback.snd G.hom t)
      infer_instance
    case geomConnected =>
      show GeometricallyConnected (pullback.snd G.hom t)
      infer_instance
  have hA' := ab_pull A hA
  have hB' := ab_pull B hB
  haveI : IsCommMonObj ((Over.pullback t).obj A) := hA'.comm
  haveI : IsCommMonObj ((Over.pullback t).obj B) := hB'.comm
  have hI : LBIso (L.pull (pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull Φ.left) :=
    hiso Z _ _ _ _ Φ hΦ hA' hB' (LB.isLB_pull hL _) (LB.isLB_pull hM _)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback A t) hrA)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback B t) hrB)
      fun z => ⟨(𝒰.f (𝒰.idx z)).opensRange, Scheme.Hom.mem_opensRange.2 (𝒰.covers z),
        local_iso hL hM (𝒰.f (𝒰.idx z)) (hw _) Φ hΦf⟩
  exact ⟨_, _, inferInstance, inferInstance, _, _, Φ, isGrpPullback_pullback A t, isGrpPullback_pullback B t, hΦ,
    hI, 𝟙 _, Category.id_comp _, Category.id_comp _, (Category.id_comp _).trans hΦf.symm⟩

end GlobalTheory.EndLoc.HomGlue
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.wachRingFacts_unramified_levelOne : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL), RingFacts (H.W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachPlace.ringFacts_of_caseA | exact GlobalTheory.WachPlace.ringFacts_of_caseA | (intros; apply GlobalTheory.WachPlace.ringFacts_of_caseA <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylor_add_square_zero_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  first | exact @GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | exact GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero <;> assumption)
end
