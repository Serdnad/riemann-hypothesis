module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Mum.TraitValue

theorem value_of_expands {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK W))))
    (t : SecK A.L (snd (TFK (R := W) F) A.A).left k) (s : Fam D.toPre F k) (h : U.ExpandsF F k w t s)
    (σ : H0 U.LG.L k) (f : ∀ x, D.toPre.SecB k x) (hσ : ∀ e, U.ExpandsAt e k σ f)
    (hs : ∀ x, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F x) (DegPre.famε k) (s.s x) (D.toPre.famφB x)
      (DegPre.famε k) (f x) (DegPre.prB D.toPre F).left 1)
    (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ A.A).left) (z : Z) JG Jt (hG : Good U.LG.L z JG) (ht : Good A.L z Jt) :
    sval σ (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)) z JG =
      (gw w (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left) z
        (JG (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)))
        (fun _ => Jt (q ≫ (snd (TFK (R := W) F) A.A).left)) ^ k).val * sval t q z Jt := by
  obtain ⟨σ', h₁, h₂⟩ := h
  have h₃ : U.ExpandsG F k (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) s := by
    refine (expandsG_iff U.toUnifPre F k _ s).2 ⟨1, fun _ => 1, fun _ => (σ, f), fun _ => hσ, ?_, fun α => ?_⟩
    · rw [Fin.sum_univ_one, one_smul]
    · rw [Fin.sum_univ_one, one_smul]
      refine sec_ext' D.toPre.P.isLB fun y J hJ => ?_
      have a := (secScal_iff_val D.toPre.P.isLB _ _ _ _).1 (hs α) y J hJ
      rw [gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at a
      exact a.symm.trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing W) F))))))).symm
  obtain rfl : σ' = _ :=
    ((expandsG_bijective U.toUnifPre F GlobalTheory.allSixLaws.1.globalFns hk (U.expand k hk)).2 s).unique h₂ h₃
  let n : TFK (R := W) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have e₁ : (q ≫ n.left) ≫ (U.genF F).left = q := by
    rw [Category.assoc, ← Over.comp_left, hn, Over.id_left, Category.comp_id]
  have e₂ : (q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left]
  have e₃ : (q ≫ n.left) ≫ UnifPre.gFK (G := G) F =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) := by
    rw [← Category.assoc, e₂, Category.assoc, Category.assoc]
  have e₄ : ((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left =
      q ≫ (snd (TFK (R := W) F) A.A).left := by
    rw [e₂, Category.assoc, Category.assoc, ← Over.comp_left _ _ _ U.gen.inv, Iso.inv_hom_id, Over.id_left,
      Category.comp_id]
  have key := (isoRelM_iff w _ k _ h₁.1 _ h₁.2.1 _ _).1 h₁ Z (q ≫ n.left) z
    (JG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (Jt (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
    (hG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (ht (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
  rw [Category.comp_id, e₁, e₄, zpow_natCast] at key
  have v : sval (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) (q ≫ n.left) z JG =
      sval σ (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫
        pullback.fst G.hom (jK W)) z JG :=
    (sval_pullOver _ _ _ _ hG).trans (sval_pullOver _ _ _ _ hG)
  have key' := v.symm.trans key
  rw [e₂, e₃, Category.assoc, Category.assoc] at key'
  exact key'

theorem value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ w₀ _ E' hE F₀ s' σ hs ⟨σ'', f'', hc, hp, he⟩ Z p q h₁ h₂ z JP JG Jt gP gG gt
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have ep : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by rw [h₁]; simp only [Category.assoc]) ?_
    have a₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have a₂ : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom =
        (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have a₃ : spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) = jFK (R := W) F ≫ jK W :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap W (FractionRing W))) (CommRingCat.ofHom (algebraMap (FractionRing W) F))
    rw [h₂, a₃, Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% a₁, reassoc_of% a₂]
  have c := hc Z p z JP JG gP gG
  have h1 : Out.scal T.G.hom (1 : W) = 1 := by unfold Out.scal; rw [map_one, map_one]
  rw [h1, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul] at c
  have v := value_of_expands T.U F hk w₀ (E' s') s' (hE s') σ'' f'' he (hs f'' hp) Z q z JG Jt gG gt
  rw [c, _root_.mul_assoc, ← v, ← ep]

end GlobalTheory.Mum.TraitValue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem Trait.exp_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  intro R _ _ _ hB D C W _ _ _ T k hk F s₁ s₂ a₁ b₁ a₂ b₂ h₁ h₂ Z p p' hpp' z J hJ
  obtain ⟨σ₁, ⟨τ₁, f₁, hc₁, hp₁, he₁⟩, hg₁⟩ := h₁
  obtain ⟨σ₂, ⟨τ₂, f₂, hc₂, hp₂, he₂⟩, hg₂⟩ := h₂
  have hf : f₁ = f₂ := funext fun x =>
    (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB T.D'.toPre.P.isLB T.hD.w T.hD.w_gen (Fin 4)
      (T.D'.toPre.famφB x) (D.toPre.famφB (T.hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull T.hD x)
      (F.f (T.hD.xe x))).unique (hp₁ x) (hp₂ x)
  subst hf
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  have hGc := hGs.geomConnected
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero W _ bW T.D' T.A T.G T.U.toUnifPre k 2 ![1, -1] ![τ₁, τ₂]
    ![f₁, f₁] (fun i => by fin_cases i; exacts [he₁, he₂])).2 hGc (fun α j => by simp [Fin.sum_univ_two, Out.scal])
  have hτ : τ₁ = τ₂ := SecOps.sec_ext fun j => by
    have := H j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  subst hτ
  choose J' hJ' using fun ψ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (ψ z)
  have c₁ := hc₁ Z p z J J' hJ hJ'
  have c₂ := hc₂ Z p z J J' hJ hJ'
  have g₁ := hg₁ Z p p' hpp' z J hJ
  have g₂ := hg₂ Z p p' hpp' z J hJ
  have m : ∀ a b : W, gs p z ⊤ (scal T.G.hom (a * b)) = gs p z ⊤ (scal T.G.hom a) * gs p z ⊤ (scal T.G.hom b) :=
    fun a b => by
      rw [show scal T.G.hom (a * b) = scal T.G.hom a * scal T.G.hom b by simp only [scal, map_mul]]
      exact gs_mul p z ⊤ (show p z ∈ (⊤ : T.G.left.Opens) from trivial) _ _
  have key : gs p z ⊤ (scal T.G.hom b₂) * sval σ₁ p z J = gs p z ⊤ (scal T.G.hom b₁) * sval σ₂ p z J := by
    rw [c₁, c₂]; ring
  rw [g₁, g₂] at key
  rw [m, m]
  linear_combination key

end GlobalTheory.Mum
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem negT_fibre_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2
  have gB : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((GlobalTheory.ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart).congr rfl (by simp only [Category.assoc])
  have gA := C.α_cart
  have nfA : negT C.A.A (TFK (R := R) F) ≫ fst (TFK (R := R) F) C.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsA : negT C.A.A (TFK (R := R) F) ≫ snd (TFK (R := R) F) C.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have nfB : negT T.A.A (TFK (R := W) F) ≫ fst (TFK (R := W) F) T.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsB : negT T.A.A (TFK (R := W) F) ≫ snd (TFK (R := W) F) T.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have hw : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have e := congrArg (· ≫ C.G.hom) hf2
    have wB := gB.1.w
    simp only [Category.assoc] at e wB
    rw [gA.1.w, wB, ← Category.assoc (snd (TFK (R := R) F) C.A.A).left, ← Category.assoc (snd (TFK (R := W) F) T.A.A).left,
      Over.w, Over.w] at e
    exact e
  let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
    Over.homMk f hw
  have key : ρ ≫ pushHom gA _ (snd _ _) = pushHom gB _ (snd _ _) :=
    Over.OverMorphism.ext (by
      show f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ _
      exact hf2)
  have keyi : ρ ≫ pushHom gA _ (snd _ _ ≫ GrpObj.inv) = pushHom gB _ (snd _ _ ≫ GrpObj.inv) := by
    have i1 : (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    have i2 : (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    rw [i1, i2, map_inv, map_inv, GrpObj.comp_inv, key]
  apply pullback.hom_ext
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (fst (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (fst (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nfA, hf1, ← Over.comp_left, nfB]
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (snd (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nsA]
    apply gA.1.hom_ext
    · have k : f ≫ (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv).left ≫ C.α =
          (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
        congrArg Over.Hom.left keyi
      rw [Category.assoc, k]
      simp only [Category.assoc]
      rw [hf2, ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nsB]
    · rw [Category.assoc, Over.w, Category.assoc, Category.assoc, Over.w]
      rw [← Over.w (fst (TFK (R := R) F) C.A.A), ← Category.assoc, hf1,
        ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nfB]

end GlobalTheory.ThetaMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.Mum

theorem tensorLeft_hom_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} {a b : Z ⟶ (X ⊗ Y).left}
    (h1 : a ≫ (fst X Y).left = b ≫ (fst X Y).left) (h2 : a ≫ (snd X Y).left = b ≫ (snd X Y).left) : a = b :=
  pullback.hom_ext h1 h2

theorem trait_transl_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2 x' x hx
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) := by
    have := (ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart
    simpa only [Category.assoc] using this
  have gC := C.α_cart
  have hxx : x.left ≫ C.α = x'.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    have e1 : x.left = (ptSecT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    have e2 : x'.left = (ptSecT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [e1, ← hx, Category.assoc, Category.assoc, hf2, ← Category.assoc, ← Category.assoc, ← e2]
    simp only [Category.assoc]
  have hbase : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have a1 : (TFK (R := R) F ⊗ C.A.A).hom = (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom := (Over.w _).symm
    have a2 : (TFK (R := W) F ⊗ T.A.A).hom = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom := (Over.w _).symm
    have w := gT.1.w
    simp only [Category.assoc] at w
    rw [a1, a2, Category.assoc, Category.assoc, ← gC.1.w, reassoc_of% hf2, w]
  apply tensorLeft_hom_ext
  · simp only [Category.assoc, ← Over.comp_left, translT, lift_fst, hf1]
  · rw [Category.assoc, Category.assoc]
    apply gC.1.hom_ext
    · have eL : (translT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
          ((pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x)) * (pushPt gC.1.w (snd (TFK (R := R) F) C.A.A))).left := by
        rw [gC.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      have eR : (translT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫
          pullback.fst T.G.hom (jK W) ≫ T.β =
          ((pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x')) * (pushPt gT.1.w (snd (TFK (R := W) F) T.A.A))).left := by
        rw [gT.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
        Over.homMk f hbase
      have e0 : ρ ≫ pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x) = pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x') := by
        ext
        show f ≫ (fst (TFK (R := R) F) C.A.A ≫ x).left ≫ C.α = (fst (TFK (R := W) F) T.A.A ≫ x').left ≫ _
        simp only [Over.comp_left, Category.assoc]
        rw [hxx, reassoc_of% hf1]
      have e1 : ρ ≫ pushPt gC.1.w (snd (TFK (R := R) F) C.A.A) = pushPt gT.1.w (snd (TFK (R := W) F) T.A.A) := by
        ext
        exact hf2
      simp only [Category.assoc]
      rw [eL, hf2, eR, ← e0, ← e1, ← MonObj.comp_mul]
      rfl
    · simp only [Category.assoc]
      rw [Over.w (snd (TFK (R := R) F) C.A.A), Over.w (translT C.A.A x), ← Over.w (fst (TFK (R := R) F) C.A.A),
        reassoc_of% hf1, ← Category.assoc, ← Over.comp_left, translT, lift_fst]

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem PullB.vanMod {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b' : D'.SecB k x} (H : PullB hD x b b') {I : Ideal R} {I' : Ideal R'} (hI : I ≤ I'.comap φ) {e : ℕ}
    (hb : VanMod I b e) : VanMod I' b' e := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ :=
    (pull_grp hD).1.w
  have hc := ExpGTrans.famφB_pull hD x
  unfold PullB at H
  have ht : thick R' I' e ≫ specOf φ =
      spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle) ≫ thick R I e := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  obtain ⟨h, hh⟩ : ∃ h : pullback D'.P.A.hom (thick R' I' e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D'.P.A.hom (thick R' I' e) ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) :=
    ⟨pullback.lift _ (pullback.snd D'.P.A.hom (thick R' I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]),
      pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (D'.famφB x κ (pullback.fst D'.P.A.hom (thick R' I' e) y)))
  have e₁ := H _ (pullback.fst D'.P.A.hom (thick R' I' e)) y p q hp (Set.mem_iInter.1 hy)
  have hm : pullback.fst D.P.A.hom (thick R I e) (h y) ∈ LB.wchart D.P.L (D.famφB (hD.xe x)) p :=
    Set.mem_iInter.2 fun κ => by
      have a : h ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.famφB (hD.xe x) κ =
          pullback.fst D'.P.A.hom (thick R' I' e) ≫ D'.famφB x κ ≫
            hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := by
        rw [← Category.assoc, hh, Category.assoc, ← hc κ]
      exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) a).mpr (hp κ)
  have z₀ : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), f y ∈ U → gs f y U 0 = 0 := fun f y U h => by
    rw [gs_eq f y U h, map_zero, map_zero]
  rw [← hh] at e₁
  have e₂ := (Units.mul_right_eq_zero _).1 (e₁.symm.trans ((gs_pull h _ y _ hm _).symm.trans
    ((congrArg (gs h y _) (hb p)).trans (z₀ h y _ hm))))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (z₀ _ y _ hy).symm

theorem exists_intFam_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre), Function.Injective φ → IsLocalHom φ → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k), ∃ F' : IntFam (maximalIdeal W) D'.toPre k, ∀ x, PullB hD x (F.f (hD.xe x)) (F'.f x) := by
  intro R _ _ _ _ D W _ _ _ φ D' hD _ hl k F
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (F.f (hD.xe x))).exists
  have s₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have s₂ : scal (DegPre.BF D'.toPre (FractionRing W)).hom 1 = 1 := by rw [scal, map_one, map_one]
  obtain ⟨E, hE⟩ := exists_fam_of_isPullDeg GlobalTheory.allSixLaws.1.globalFns R W φ D.toPre D'.toPre hD k F.F F.f f'
    (fun α => s₁ ▸ F.ext α) hf'
  have hI : maximalIdeal R ≤ (maximalIdeal W).comap φ := fun a ha => map_nonunit φ a ha
  refine ⟨{ F := E, f := f', ext := fun α => s₂.symm ▸ hE α, small := fun e => ?_ }, hf'⟩
  exact ((F.small e).preimage hD.xe.injective.injOn).subset fun x hx hv => hx (PullB.vanMod (hf' x) hI hv)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.VPre

theorem four_rescale : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  intro O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀
  obtain ⟨N, hN0, hN1, k, hk0, hku, hmain⟩ := hF y₀ N₀
  refine ⟨N, hN0, hN1, k, hk0, hku, ?_⟩
  intro l a c e
  obtain ⟨f, hf⟩ := hmain l a c e
  obtain ⟨b, hb⟩ := hw (e + 1)

  have hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y) := by
    intro y x hx
    haveI := Φ.ev_loc y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)
  have hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y) := by
    intro y
    rw [Ideal.map_le_iff_le_comap]
    exact le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)
  have hbu : IsUnit b := by
    by_contra hn
    have hbm : b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀) := hmax y₀ b hbm
    have h2 := hle y₀ (hb y₀)
    have h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀) := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)
  refine ⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := hf y j
  refine ⟨S, hS1, hS2, ?_⟩
  set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ
  have hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J :=
    le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right
  set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz
  set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww
  have hzb : z * Φ.ev y b = 1 := by
    rw [hz, ← map_mul]
    simp
  have hzw : z - ww ∈ J := by
    apply hIe
    have h := (hb y)
    have hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y))) := by
      have : ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1 := by simp [hww]
      linear_combination ww * hzb - z * this
    rw [hx]
    exact neg_mem (Ideal.mul_mem_left _ _ h)
  have hprod : ∀ mu : Fin l × Fin s → Φ.X y,
      (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l := by
    intro mu
    rw [show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from
        funext fun i => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J
  simp_rw [hprod]
  rw [← Finset.sum_mul, map_mul, map_pow, ← hz]
  set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))
  have hd : z ^ l - ww ^ l ∈ J := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow z ww l
    rw [hr]
    exact Ideal.mul_mem_right _ _ hzw
  have : Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)

end GlobalTheory.Poinc.VPre
end
