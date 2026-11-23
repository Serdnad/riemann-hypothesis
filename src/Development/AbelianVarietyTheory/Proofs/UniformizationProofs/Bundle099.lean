module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TwistCompare

section Abstract

variable {X N Y V S₀ Z : Scheme.{0}} {L : LB X} {M : LB N} {c₀ : Y ⟶ X} {q : Y ⟶ N}

def wv (w : LB.Iso (L.pull c₀) (M.pull q)) (f : Z ⟶ Y) (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ N) → M.ι) :
    (Z.presheaf.stalk z)ˣ := GlobalTheory.FieldBaseChange.isoVal w f z (JM (f ≫ q)) (JL (f ≫ c₀))

theorem val_through_iso (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen)
    (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X) (s m : V ⟶ X) (a : N ⟶ N) (hc : m ≫ n ≫ q = (s ≫ n ≫ q) ≫ a) (k' k : ℤ)
    (b : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 N, a] ![k', -k])) (hb : b.IsGen)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![s, m] ![k', -k])) (hα : α.IsGen)
    (p : V ⟶ S₀) (e : S₀ ⟶ V) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ y JL JM, Good L y JL → Good M y JM → val b (e ≫ s ≫ n ≫ q) y JM =
      wv w (e ≫ s ≫ n) y JL JM ^ k' * wv w (e ≫ m ≫ n) y JL JM ^ (-k) * val α e y JL)
    (r : Z ⟶ V) (z : Z) (JL) (JM) (hJL : Good L z JL) (hJM : Good M z JM) :
    val b (r ≫ s ≫ n ≫ q) z JM =
      wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α r z JL := by
  obtain ⟨u, hu, hv⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw n hn rfl
  have hc' : ∀ κ, (![s, m] : Fin 2 → _) κ ≫ n ≫ q = (s ≫ n ≫ q) ≫ (![𝟙 N, a] : Fin 2 → _) κ := fun κ => by
    fin_cases κ
    exacts [(Category.comp_id _).symm, hc]
  obtain ⟨α', hα', hm⟩ := H1.exists_gen_move hM hL u hu ![𝟙 N, a] ![s, m] ![k', -k] (s ≫ n ≫ q) hc' b hb
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V) (z : Z) (JL) (JM), Good L z JL → Good M z JM →
      val b (r ≫ s ≫ n ≫ q) z JM =
        wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α' r z JL := by
    intro Z r z JL JM hJL hJM
    have g : ∀ f : V ⟶ X, gw u (r ≫ f) z (JM (r ≫ f ≫ n ≫ q)) (JL (r ≫ f)) = wv w (r ≫ f ≫ n) z JL JM := fun f => by
      rw [hv Z (r ≫ f) z _ _ (hJM (r ≫ f ≫ n ≫ q)) (hJL (r ≫ f)), wv]
      simp only [Category.assoc, hn, Category.comp_id]
    have := hm Z r z (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => JL (r ≫ (![s, m] : Fin 2 → _) κ))
      (fun κ => hJM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => hJL (r ≫ (![s, m] : Fin 2 → _) κ))
    rw [Fin.prod_univ_two, g, g] at this
    rw [val_of b _ z JM (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q))
      (fun κ => by rw [hc', Category.assoc])]
    exact this
  rw [key Z r z JL JM hJL hJM]
  refine congrArg _ (gen_unique hL p e he hp hα' hα (fun y J hJ => ?_) Z r z JL hJL)
  choose J' hJ' using fun ψ : S₀ ⟶ N => exists_chart hM (ψ y)
  exact mul_left_cancel ((key _ e y J J' hJ hJ').symm.trans (h₀ y J J' hJ hJ'))

end Abstract

section Rig

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT {T : Over S} (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem exists_two (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) (a : A.left ⟶ A.left) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a, (1 : A ⟶ A).left] ![k', -k, k - k'])) (hβ : β.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a] ![k', -k]), b.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val b r z J = val β r z J * rval rig (r ≫ A.hom) z J ^ (k' - k) := by
  obtain ⟨b, hb, hv⟩ := exists_gen hL (φ' := ![𝟙 _, a]) (ε' := ![k', -k]) (fun U _ h => by
      have e : (1 : A ⟶ A).left = A.hom ≫ eSec A := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val, e]
      rw [_root_.mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (rigT A L rig A (k' - k)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (GlobalTheory.NormTheta.rigT_isGen hr _))
  exact ⟨b, hb, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg _ (val_rigT rig _ r hJ)))⟩

end Rig

theorem alg_origin {M : Type} [CommGroup M] {w r g : M} (k' k : ℤ) (h : w * r = g) :
    1 * g ^ (k' - k) = w ^ k' * w ^ (-k) * r ^ (k' - k) := by
  rw [← h, _root_.one_mul, mul_zpow, ← zpow_add, sub_eq_add_neg]

theorem dualNumber_unit_mul_decomposition {M : Type} [CommRing M] {w w' α b : Mˣ} {v v' t t' : M} {k' k : ℕ}
    (h₁ : v' = (w ^ k').val * t') (h₂ : v = (w' ^ k).val * t) (h₃ : t' = α.val * t)
    (h₄ : b = w ^ (k' : ℤ) * w' ^ (-(k : ℤ)) * α) : v' = v * b.val := by
  have e : w ^ k' * α = w' ^ k * b := by
    rw [h₄, zpow_neg, zpow_natCast, zpow_natCast, mul_comm (w ^ k') _⁻¹, _root_.mul_assoc, mul_inv_cancel_left]
  rw [h₁, h₂, h₃, ← _root_.mul_assoc, ← Units.val_mul, e, Units.val_mul, mul_right_comm]

theorem twist_through_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  intro hG R _ _ I D A G _ _ U E F _ _ k' k β hβ nβ w₀ ρ hw ψ m hm hψ hm' α hα nα t t' v v' H H' HT y J hJ
  have := U.gen_hom
  have := E.homA
  have := E.homG
  obtain ⟨b, hb, vb⟩ := exists_two U.LG.isLB U.LG.rigGen E.aG.left (k' : ℤ) (k : ℤ) β hβ
  have hn : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hn' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have f₁ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ E.aG.left := pullback.lift_fst _ _ _
  have f₂ : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have f₃ : m.left ≫ U.gen.inv.left =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left) ≫ ((Over.pullback (jK R)).map E.aG).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, Category.assoc]
  have hc : m.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ E.aG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) f₃).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) f₁).trans (by simp only [Category.assoc]))))
  let f := jK R
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj (F := Over.pullback f)
  have o₀ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) := by
    rw [← EvalZero.eK_gen U, Category.assoc, hn', Category.comp_id]
  have o₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd, ← o₀]; rfl
  have o₂ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ m.left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, hm', ptSecT, lift_snd_assoc, MonObj.one_comp, ← o₀]; rfl
  have o₃ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (EvalZero.eK_gen U))
  have o₄ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ EvalZero.eK_fst).trans (Category.assoc _ _ _).symm)
  have o₅ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
      pullback.fst G.hom (jK R) = (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    Eq.trans (Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) o₁)) o₄
  have o₆ : ((jFK (R := R) F ≫ jK R) ≫ eSec G) ≫ G.hom = jFK (R := R) F ≫ jK R :=
    (Category.assoc _ _ _).trans ((congrArg _ (Over.w η[G])).trans (Category.comp_id _))
  obtain ⟨JA, hA⟩ : ∃ JA, Good A.L y JA := by
    choose J' hJ' using fun χ : (UnifPre.GF (G := G) F).left ⟶ A.A.left => exists_chart A.isLB (χ y)
    exact ⟨J', hJ'⟩
  have key := val_through_iso A.isLB U.LG.isLB hw.1 U.gen.inv.left hn (snd (TFK (R := R) F) A.A).left m.left
    E.aG.left hc k' k b hb α hα (fst (TFK (R := R) F) A.A).left (ptSecT A.A 1).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG A.isAb _) (fun z JL JM hL hM => by
      have a₁ := (val_pull hM β (eSec G) (jFK (R := R) F ≫ jK R)).symm.trans
        ((val_corr hM nβ (jFK (R := R) F ≫ jK R)).trans (val_one _))
      have a₂ := (val_pull hL α _ (𝟙 _)).symm.trans ((val_corr hL nα (𝟙 _)).trans (val_rigT ρ _ _ hL))
      rw [Category.id_comp, Category.id_comp] at a₂
      have a₃ : wv w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z JL JM * rval ρ (jFK (R := R) F) z JL =
          rval U.LG.rig (jFK (R := R) F ≫ jK R) z JM := by
        refine Units.ext (Eq.trans ?_ (EvalZero.normW_ext U F hw z hL hM))
        rw [← o₃, ← o₄]
        rfl
      rw [o₅, o₁, o₂, vb _ _ z JM hM]
      refine (congrArg₂ (· * ·) a₁ (congrArg (fun x => rval U.LG.rig x z JM ^ ((k' : ℤ) - k)) o₆)).trans ?_
      exact (alg_origin _ _ a₃).trans (congrArg _ a₂.symm)) (U.genF F).left y JA J hA hJ
  have g₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have g₂ : (U.genF F).left ≫ m.left ≫ U.gen.inv.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_snd]
  have g₃ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      UnifPre.gFK (G := G) F := Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) g₁)
  have g₄ : (U.genF F).left ≫ ψ.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫ (U.genF F).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hψ, Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, hm, hm', Category.assoc, lift_snd, lift_snd_assoc, whiskerLeft_snd_assoc, E.ext,
        Category.assoc]
  rw [g₃, g₁, g₂, vb _ _ y J hJ] at key
  have b₁ := GlobalTheory.BoxExpansion.isoRel_val H' (𝟙 _) y hA hJ
  have b₂ := GlobalTheory.BoxExpansion.isoRel_val H (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y hA hJ
  have b₃ := twist_val HT (U.genF F).left y hA
  rw [Category.comp_id, Category.id_comp, Category.id_comp] at b₁
  rw [Category.comp_id, ← g₄] at b₂
  exact dualNumber_unit_mul_decomposition b₁ b₂ b₃ key

end GlobalTheory.UT.TwistCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SecAdicSum

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem sumI_of_ker {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) R) {E Ix : Type} [AddCommGroup E] [Module R E] (ev : (Fin a → R) →ₗ[R] E)
    (v : Ix → Fin a → R) (v₀ : Fin a → R) (hv : ∀ i, A.mulVec (v i) = 0) (hv₀ : A.mulVec v₀ = 0)
    (h : ∀ e : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ∀ k, (v₀ - ∑ i ∈ T, v i) k ∈ I ^ (e + 1)) :
    SumI I (fun i => ev (v i)) (ev v₀) := by
  let N : Submodule R (Fin a → R) := LinearMap.ker A.mulVecLin
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨N.map ev, (IsNoetherian.noetherian N).map ev, ⟨v₀, hv₀, rfl⟩, fun i => ⟨v i, hv i, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h (n + c)
  refine ⟨S, fun T hT => ?_⟩
  have m₁ : v₀ - ∑ i ∈ T, v i ∈ N := N.sub_mem hv₀ (N.sum_mem fun i _ => hv i)
  have m₂ : v₀ - ∑ i ∈ T, v i ∈ I ^ (n + c) • (⊤ : Submodule R (Fin a → R)) := by
    rw [pi_eq_sum_univ (v₀ - ∑ i ∈ T, v i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hS T hT k)) Submodule.mem_top
  have m₃ := (hc (n + c) (Nat.le_add_left _ _)).le ⟨m₂, m₁⟩
  rw [Nat.add_sub_cancel] at m₃

  rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  exact ⟨_, Submodule.smul_mono le_rfl inf_le_right m₃, rfl⟩

section
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X}
  (P : Perf f M)

theorem exists_vec (s : LB.Sec M) :
    ∃ v : Fin P.a → R, P.D₀.mulVec v = 0 ∧ ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i := by
  have h : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) X (𝟙 X) f h
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy =>
    Set.mem_iInter.1 hy PUnit.unit
  let t : LB.Sec (M.pull (𝟙 X)) := ⟨fun j => AbLaw.rs X (le j) (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    have hm : y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 X) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    rw [Fintype.prod_unique, zpow_one]
    exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat _ _)).trans
      ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))⟩
  obtain ⟨v, hv⟩ := E.surjective t
  refine ⟨v.1, v.2, fun i => ?_⟩
  have e := hE v i
  rw [hv] at e
  exact (AbLaw.rs_rs _ _ _).symm.trans e

theorem comp_eq_zero {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0)
    (h0 : ∀ i y, π y ∈ P.W i → gs π y _ (loc₀ P v i) = 0) : g ∘ v = 0 := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have k₁ : (P.D₀.map g).mulVec (g ∘ v) = 0 := funext fun j =>
    (RingHom.map_mulVec g _ _ j).symm.trans ((congrArg g (congrFun hv j)).trans (map_zero g))
  refine congrArg Subtype.val (E.injective (a₁ := ⟨_, k₁⟩) (a₂ := ⟨0, Matrix.mulVec_zero _⟩) ?_)
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ (hE _ i).symm)
  refine (loc_comp P h v i).trans (Eq.trans (fn_ext (b := 0) fun y hy => ?_) (by simp))
  refine (gs_pull (𝟙 X') π y _ hy _).trans ?_
  rw [Category.id_comp, h0 i y hy, gs_eq (𝟙 X') y (π ⁻¹ᵁ P.W i) hy, map_zero, map_zero]

theorem loc₀_sub_sum {Ix : Type} (v₀ : Fin P.a → R) (v : Ix → Fin P.a → R) (T : Finset Ix) (i : P.I) :
    loc₀ P (v₀ - ∑ j ∈ T, v j) i = loc₀ P v₀ i - ∑ j ∈ T, loc₀ P (v j) i := by

  simp only [loc₀, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum, sub_mul, Finset.sum_mul,
  Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end

section
variable {X Y Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (LB.LinComb L φ ε))

theorem gs_loc₀ {s : LB.Sec (LB.LinComb L φ ε)} {v : Fin P.a → R}
    (h : ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i) (r : Z ⟶ X) (z : Z) {i : P.I} (hi : r z ∈ P.W i)
    {J : (Z ⟶ Y) → L.ι} (hJ : Good L z J) :
    gs r z _ (loc₀ P v i) = (trF φ ε r z (P.ch i) fun k => J (r ≫ φ k)).val * sval s r z J := by
  rw [← h i]
  exact (gs_res r z (P.le i) hi _).trans (sec_trans s r z (P.le i hi) (hJ.mem φ r))

end

theorem gs_cst_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {B : Over (Spec (CommRingCat.of R))} (b : TF (R := R) F ⟶ B) (z : (TF (R := R) F).left) (W : B.left.Opens)
    (hz : b.left z ∈ W) (c : R) : gs b.left z W (AbLaw.cst B.hom W c) =
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) c)) := by
  have w : b.left ≫ B.hom = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    rw [Over.w b, Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  rw [gs_eq b.left z W hz, app_cst w W c]
  exact TopCat.Presheaf.germ_res_apply (TF (R := R) F).left.presheaf _ z hz _

theorem sumF_of_sum_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁

    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
    ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSum
end
end
