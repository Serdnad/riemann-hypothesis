module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClosedFibreTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem vanish_of_terms_vanish {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  have hz : ∀ α, sval (f α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    have m := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ pGl U e)
    exact (gs_pull (𝟙 _) _ y _ m _).symm.trans ((congrArg (gs (𝟙 _) y _) (h0 α _)).trans (gs_zero (𝟙 _) y _ m))
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul]] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (((Units.mul_right_eq_zero _).1 H).trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by
  intro V _ _ _ ϖ hϖ D A G _ _ U σ g hE hχ
  have Q : ∀ α : D.toPre.X, (∀ j, ((U.gt 0).pG.left.app _).hom ((g α).f j) = 0) ↔
      ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom ϖ (g α) g' := fun α => by
    have := GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 1 α (g α)
    have hp : ϖ ^ (0 + 1) = ϖ := pow_one ϖ
    rwa [hp] at this
  rw [← not_forall]
  refine not_congr ⟨fun h => (Q 0).1 (WeightPf.weightIndep V _ D A G U 0 1 σ g h hE 0), fun h => ?_⟩
  refine vanish_of_terms_vanish U 0 1 σ g hE fun α => (Q α).2 ?_
  by_cases hα : α = 0
  · subst hα; exact h
  · exact hχ α hα

end GlobalTheory.ClosedFibreTerm
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.RosatiPower

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]

private theorem padd_comp_eq_padd_comp_of_isMonHom {T H K : Over S} [GrpObj H] [GrpObj K] (q : H ⟶ K) [IsMonHom q]
    (a b : T ⟶ H) : padd H a b ≫ q = padd K (a ≫ q) (b ≫ q) := by
  unfold padd
  simp [IsMonHom.mul_hom]

private theorem comp_padd_eq_padd_comp {T T' H : Over S} [GrpObj H] (x : T ⟶ T') (a b : T' ⟶ H) :
    x ≫ padd H a b = padd H (x ≫ a) (x ≫ b) := by
  unfold padd
  first
  | simp
  | simp [Hom.mul_def]
  | simp [comp_lift_assoc]

theorem rosatiφ_comp (q : G' ⟶ G) [IsMonHom q] {f g : G ⟶ G} {f' g' : G' ⟶ G'}
    (hf : f' ≫ q = q ≫ f) (hg : g' ≫ q = q ≫ g) (k : Fin 6) :
    rosatiφ G' f' g' k ≫ q.left = (q ⊗ₘ q).left ≫ rosatiφ G f g k := by
  have e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q := by simp
  have e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q := by simp
  have key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b →
      a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left := by
    intro a b h
    rw [← Over.comp_left, h, Over.comp_left]
  fin_cases k <;> refine key _ _ ?_ <;>
    simp only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]

theorem exists_restrict {A B : Over S} (q : A ⟶ B) (U : S.Opens) :
    ∃ n : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      n ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ q.left := by
  refine ⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  intro x hx
  rw [← Over.w q] at hx
  exact hx

private theorem exists_isGen_of_isGen_iso_of_isGen {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (u : LB.Iso A B) (hu : u.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ t' : LB.Gen A, t'.IsGen := by
  classical
  let tS : LB.Sec B := ⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by
    have e := congrArg Units.val (ht i j)
    simpa [res] using e⟩
  have hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a) := by
    intro a
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro x hx
    have hc := cover_inf hB a hx
    rw [TopologicalSpace.Opens.mem_iSup] at hc
    obtain ⟨b, hb⟩ := hc
    have hsp := secOfIso_spec tS hu hA hB a b
    have e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) =
        X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a)) := by
      simp only [rs, TopCat.Presheaf.germ_res_apply]
    change IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))
    rw [e1, hsp, isoCand, map_mul]
    refine IsUnit.mul ((Units.isUnit _).map _) ?_
    simp only [rs, TopCat.Presheaf.germ_res_apply]
    exact (Units.isUnit (t.s b)).map _
  refine ⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩
  apply Units.ext
  have e := (secOfIso tS hu hA hB).compat i j
  simpa [res] using e

end GlobalTheory.RosatiPower


open GlobalTheory.RosatiPower in
theorem GlobalTheory.rosatiAdj_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → RosatiAdj G L f g → RosatiAdj G' L' f' g' := by
  intro S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr
  have hm : ∀ i, IsMonHom (p.pr i) := p.hom
  unfold RosatiAdj at hr ⊢
  unfold boxLB at hiso
  intro s
  obtain ⟨U, hsU, t, ht⟩ := hr s
  refine ⟨U, hsU, ?_⟩
  obtain ⟨w, hw⟩ := hiso
  have hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left :=
    fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U
  choose n hn using hn
  have hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left =
      n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k := by
    intro i k
    rw [Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]
  let t' : ∀ i, ((L.pull (p.pr i).left).LinComb
      (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen :=
    fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t
  have ht' : ∀ i, (t' i).IsGen := by
    intro i
    exact LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht
  have hb := GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'
  have hwi := linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε
  exact exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb

end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem secIsMul_gs {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {a : R}
    {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) (hz : q z ∈ L.U j) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  rw [h j, gs_mul q z _ hz]
  congr 1
  exact gs_constFn p (L.U j) q z hz a

private theorem gs_eq_cst_mul_gs_of_secIsMul {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)}
    {L : LB Y} {a : R} {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  by_cases hz : q z ∈ L.U j
  · exact secIsMul_gs h q z j hz
  · simp only [gs, dif_neg hz, mul_zero]

theorem expandsAt_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (a : R) (σ σ' : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom a σ' σ → (∀ α, SecIsMul D.toPre.P.A.hom a (f' α) (f α)) → U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  intro R _ _ I D A G _ _ U e k a σ σ' f f' hσ hf hE
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  have hsf : ∀ α (y : (thickObj R I e G).left) J, sval (f' α) (pGl U e) y J =
      cst (pGl U e ≫ D.toPre.P.A.hom) y a * sval (f α) (pGl U e) y J := by
    intro α y J
    unfold sval
    exact gs_eq_cst_mul_gs_of_secIsMul (hf α) _ _ _
  have hsσ : ∀ (y : (thickObj R I e G).left) jL, sv U k σ' (fGl I G e) y jL =
      cst (fGl I G e ≫ G.hom) y a * sv U k σ (fGl I G e) y jL := by
    intro y jL
    unfold sv
    exact gs_eq_cst_mul_gs_of_secIsMul hσ _ _ _
  have hmap : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := by
    simp only [fGl, pGl, Over.w]
  refine expandsAt_of_val U e k σ' f' S ?_
  intro y J hJ
  obtain ⟨h0, h1⟩ := hS _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at h0 h1
  refine ⟨fun α hα => ?_, fun jL hmem => ?_⟩
  · rw [hsf, h0 α hα, mul_zero]
  · have h1' := h1 jL hmem
    rw [hsσ, hmap]
    have hsum : ∑ α ∈ S, sval (f' α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        cst (pGl U e ≫ D.toPre.P.A.hom) y a *
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hsf, _root_.mul_assoc]
    rw [hsum, ← h1']
    ring

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section

variable (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem jFK_self : jFK (R := V) (FractionRing V) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  exact Spec.map_id _

def specFrac : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing V)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F))

theorem specFrac_jFK : specFrac V F ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  (congrArg (fun q => specFrac V F ≫ q) (jFK_self V)).trans (Category.comp_id _)

def toFrac : TF (R := V) F ⟶ TF (R := V) (FractionRing V) :=
  Over.homMk (specFrac V F) ((Category.assoc (specFrac V F) (jFK (R := V) (FractionRing V)) (jK V)).symm.trans
    (congrArg (fun q => q ≫ jK V) (specFrac_jFK V F)))

theorem toFrac_jFK : (toFrac V F).left ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  specFrac_jFK V F

variable {V} (D : DegPre V)

def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing V) := toFrac V F ▷ D.P.A

theorem bc_prB : bc F D ≫ DegPre.prB D (FractionRing V) = DegPre.prB D F := whiskerRight_snd _ _

theorem bc_prB_left : (bc F D).left ≫ (DegPre.prB D (FractionRing V)).left = (DegPre.prB D F).left :=
  congrArg (fun q => q.left) (bc_prB F D)

theorem zF_bc : DegPre.zF D F ≫ bc F D = toFrac V F ≫ DegPre.zF D (FractionRing V) := by
  unfold DegPre.zF bc
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, whiskerRight_snd, lift_snd]
    rw [← Category.assoc, comp_toUnit]

theorem bc_famφ (α : D.X) (i : Fin 4) :
    (bc F D).left ≫ DegPre.famφ D (FractionRing V) α i = DegPre.famφ D F α i := by
  rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, bc_prB_left]

end

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (F : Type) [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_bc (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ bc F D.toPre = bc F D.toPre ≫ aF D (FractionRing V) oa a := by
  unfold aF
  apply CartesianMonoidalCategory.hom_ext
  · simp [bc]
  · simp only [Category.assoc, lift_snd]
    rw [← Category.assoc (bc F D.toPre), bc_prB]
    exact lift_snd _ _

theorem aF_bc_left (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (bc F D.toPre).left = (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left :=
  congrArg (fun q => q.left) (aF_bc D F oa a)

theorem bc_pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) (i : Fin 4 ⊕ Fin 4) :
    (bc F D.toPre).left ≫ pullφ D (FractionRing V) oa a χ i = pullφ D F oa a χ i := by
  rcases i with i | i
  · exact bc_famφ F D.toPre _ i
  · show (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left ≫ _ = (aF D F oa a).left ≫ _
    rw [← Category.assoc, ← aF_bc_left, Category.assoc, bc_famφ]

theorem sval_bc {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {g : D.toPre.SecB k α}
    (hs : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1)
    (ht : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) t (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval t r z J = sval s (r ≫ (bc F D.toPre).left) z J := by
  rw [← SectionScalarValuation.secScal_sval ht r z hJ, ← SectionScalarValuation.secScal_sval hs _ z hJ, Category.assoc, bc_prB_left]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (E : Fam D.toPre (FractionRing V) k) (E' : Fam D.toPre (FractionRing V) (k * N)) (g : ∀ α, D.toPre.SecB k α) (g' : ∀ α, D.toPre.SecB (k * N) α) (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (E'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (θ'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre F).left 1) → PullAl D (FractionRing V) oa a k N E E' → PullAl D F oa a k N θ θ' := by
  intro V _ _ _ D F _ _ O _ _ _ oa a k N E E' g g' θ θ' hE hE' hθ hθ' hP
  have hL := D.toPre.P.isLB
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    obtain ⟨u', hu', vu⟩ := exists_gen hL (φ' := pullφ D F oa a χ) (ε' := pullε k N)
      (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [bc_pullφ])
      (LB.pullGen D.toPre.P.L _ _ u (bc F D.toPre).left) (pullGen_isGen _ _ _ _ hu _)
    refine ⟨u', hu', corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_⟩
    · have e := val_corr hJ hc (toFrac V F).left
      rw [val_pull hJ, val_pull hJ, toFrac_jFK] at e
      have z₁ : (DegPre.zF D.toPre F).left ≫ (bc F D.toPre).left =
          (toFrac V F).left ≫ (DegPre.zF D.toPre (FractionRing V)).left :=
        congrArg (fun q => q.left) (zF_bc F D.toPre)
      rw [val_pull hJ, val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, Category.id_comp, z₁]
      exact e
    · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (bc F D.toPre).left y J hJ
      rw [sval_bc D F (hE' _) (hθ' _) _ y hJ, sval_bc D F (hE _) (hθ _) _ y hJ, vu _ _ y J hJ, val_pull hJ,
        Category.id_comp, Category.id_comp, aF_bc_left]
      exact e
  · refine fn_ext (V := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F β) j) fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart hL (ψ y)
    have hI' : Good D.toPre.P.L y I := hI
    have e : sval (θ'.s β) (𝟙 _) y I = 0 := by
      rw [sval_bc D F (hE' β) (hθ' β) _ y hI']
      exact (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (hI'.mem _ _))
    refine (sec_trans (θ'.s β) (𝟙 _) y hy (hI'.mem _ _)).trans ?_
    exact (congrArg _ e).trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullBaseChange
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.pullAl_linear_combination : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N n : ℕ), 0 < n → ∀ (c : Fin n → F) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D.toPre F (k * N)), (∀ l, PullAl D F oa a k N (s l) (s' l)) → PullAl D F oa a k N (∑ l, c l • s l) (∑ l, c l • s' l) := by
  first | exact @GlobalTheory.PullComb.main | exact GlobalTheory.PullComb.main | (intros; apply GlobalTheory.PullComb.main <;> assumption)
end
