module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) (l : ℕ), l.Prime → (l : K) ≠ 0 → M.IsLB → Out.RelAmple P.A M → SymB M → FormIs P M s → ∃ δ : ℕ, Vol P.A.hom M P.g δ ∧ (∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g)) ∧ ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A)) (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))), TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → (δ : ZMod (l ^ j)) ^ 2 = Mat.det := by
  first | exact @GlobalTheory.SectionCount.sq_vol_eq_det | exact GlobalTheory.SectionCount.sq_vol_eq_det | (intros; apply GlobalTheory.SectionCount.sq_vol_eq_det <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_laws : Out.Laws → N1c := by
  intro hL
  have hU : ThetaUnifAV :=
    thetaUnifAV_of_laws (by cases hL; assumption) (by cases hL; assumption) (by cases hL; assumption)
      (by cases hL; assumption) (by cases hL; assumption)
  exact GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation hU hL

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_base_model_semiAbelian : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  first | exact @GlobalTheory.BaseModelEx.exists_baseModel | exact GlobalTheory.BaseModelEx.exists_baseModel | (intros; apply GlobalTheory.BaseModelEx.exists_baseModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.RaisedTransition

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.BaseRing.isDedFrac_RZ E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem div_mul_div {a b c : ℕ} (h : a ∣ b) (h' : b ∣ c) : c / b * (b / a) = c / a := by
  exact Nat.div_mul_div h' h

theorem levComp_trans {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← div_mul_div hd.1 hd'.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc, h.1,
      Category.assoc]
  · rw [← div_mul_div hd.2.2 hd'.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a), Category.assoc,
      h.2, Category.assoc]

theorem exists_isTransition : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀') (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₂ : Level H) (c₂ : Coeff l₂) (O₂ : Type) [CommRing O₂] (β₂ : O₂ →+* c₂.F) (Y₂ : Model (Xo l₂) c₂ β₂) (b : O →+* O₂), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → l₀.Dvd l → l₀'.Dvd l₂ → l.Dvd l₂ → c.F ≤ c₂.F → IsDedFrac β → IsDedFrac β₂ → IsInc (c.F.val.toRingHom.comp β) (c₂.F.val.toRingHom.comp β₂) b → Raises B Y → Raises B' Y₂ → ∃ π : Y₂.X ⟶ Y.X, IsTransition Y Y₂ b π := by
  intro hext L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ l₀' B B' l c O _ β Y l₂ c₂ O₂ _ β₂ Y₂ b hn hNe d₀ d₁ d₂ d hc hβ hβ₂ hb
    hR hR₂
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  obtain ⟨b₂, r₂, ν₂, hb₂, hl₂, ⟨a₂⟩⟩ := hR₂
  obtain ⟨b₀, r₀, ν₀, hb₀, hl₀, ⟨a₀⟩⟩ := GlobalTheory.T.deeper_level_base_model_finite_over_shallower hext L₁ L₂ L₃ E H D Xo n N T hN l₀ l₀' B B' hn hNe d₀
  obtain ⟨k, r, ν, hr, hk, hl, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l₂ c₂ Y₂.oF Y₂.m0 d

  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l₂).XF c₂ ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp Y₂.oF Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩

  have hbβ : β₂.comp b = (IntermediateField.inclusion hc).toRingHom.comp β :=
    RingHom.ext fun x => Subtype.ext (hb x)
  have hinj : Function.Injective β₂ := by
    letI := β₂.toAlgebra
    have := hβ₂.2.2
    exact IsFractionRing.injective O₂ c₂.F
  have hbb : b₂.comp b₀ = b.comp b₁ := RingHom.ext fun x => hinj (Subtype.ext
    ((hb₂ (b₀ x)).trans ((hb₀ x).trans ((hb (b₁ x)).trans (hb₁ x)).symm)))

  obtain ⟨ν₃, hν₃⟩ := LevelCover.sab_comp ν₂ ν₀ rfl
  obtain ⟨ν₄, hν₄⟩ := LevelCover.sab_comp ν' ν₁ rfl
  obtain ⟨a⟩ : Nonempty ((ofModel Y₂).Above B.C (b.comp b₁) (r₂ ≫ r₀) ν₃) := by
    rw [← hbb]
    exact ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C B'.C (ofModel Y₂) b₀ b₂ r₀ ν₀ r₂ ν₂ ν₃
      a₀ a₂ hν₃).choose⟩

  have hred : IsReduced ((Xo l₂).XF c₂) := by
    have := (Xo l₂).smooth
    have : Smooth (Xo l₂).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c₂.F _ (pullback.snd _ _)
      inferInstance).1
  have hover : (r₂ ≫ r₀) ≫ (Xo l₀).s = (r' ≫ r₁) ≫ (Xo l₀).s := by
    have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
    have := mono_spMap_of_isDedFrac (isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc)
    have q₁ : (r₂ ≫ r₀) ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β₂ ≫ spMap (b.comp b₁) := by
      rw [← Category.assoc, ← a.j_comm, Category.assoc, a.π_over, ← Category.assoc, j_over, Category.assoc]
    have q₂ : r₁ ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap β ≫ spMap b₁ := by
      rw [← Category.assoc, ← a₁.j_comm, Category.assoc, a₁.π_over, ← Category.assoc, j_over, Category.assoc]
    rw [← cancel_mono (spMap B.β), Category.assoc, ← j_over B.C, q₁, Category.assoc, ← j_over B.C, Category.assoc, q₂,
      reassoc_of% hr₂, spMap_comp, ← Category.assoc (spMap β₂), ← spMap_comp, hbβ, spMap_comp, Category.assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l₂ (Xo l₀) _ _ _ _ Y₂.oF _ _ ν₃ ν₄ hred hover
    (levComp_trans d₀ d₂ hl₂ hl₀ ν₃ hν₃) (levComp_trans d₁ d hl' hl₁ ν₄ hν₄)
  obtain ⟨h, mu, hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C (ofModel Y) (ofModel Y₂) b₁ b (IntermediateField.inclusion hc).toRingHom r₁ ν₁ a₁ r' ν' a.π a.mu a.π_over
    hβ₂ hbβ hr₂ (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₄, Category.assoc])
  have hφ' : Y₂.m.φ ≫ mu.φ = ν'.φ ≫ Y.m.φ := hφ
  refine ⟨h, pullback.lift h Y₂.s hh, mu, r', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, hf a.fin, hj,
    fun x => ?_, fun x => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.1 x)).trans (Category.assoc _ _ _)))
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.m.φ) (hl'.2 x)).trans (Category.assoc _ _ _)))

end GlobalTheory.RaisedTransition
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact GlobalTheory.T.relAmple_of_cube_div_generated_field K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
end
end
