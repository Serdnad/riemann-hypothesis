module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem RatModel.exists_eq_spMap_pt (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z)
    (hy : ∀ w, y w = genericPoint M.Z) : ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 : ⊤ ≤ y ⁻¹ᵁ U := fun w _ => by
    change y w ∈ U
    rw [hy]; exact hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ⟨β, ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_⟩
  rw [valR_spMap_comp β M.pt U h2]
  exact (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f).symm

variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

instance ZHPre.isIntegral : IsIntegral Q.G.left :=
  have := Q.semi
  isIntegral_left_of_isSemiAbelian Q.G

theorem ZHPre.hom_genericPoint : Q.G.hom (genericPoint Q.G.left) = genericPoint M.Z := by
  have hw : η[Q.G].left ≫ Q.G.hom = 𝟙 _ := Over.w η[Q.G]
  have h1 : Q.G.hom (η[Q.G].left (genericPoint M.Z)) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : M.Z ⟶ M.Z => f (genericPoint M.Z)) hw)
  have h2 := (genericPoint_specializes (η[Q.G].left (genericPoint M.Z))).map Q.G.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem ZHPre.exists_generic (hU : (U₀ : Set M.Z).Nonempty) :
    ∃ (K : Type) (_ : Field K) (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP ∧
      ∀ w, (g ≫ Q.φ) w = genericPoint Q.G.left := by
  let K : Type := Q.G.left.residueField (genericPoint Q.G.left)
  let x : Sp K ⟶ Q.G.left := Q.G.left.fromSpecResidueField (genericPoint Q.G.left)
  have hx : ∀ w, x w = genericPoint Q.G.left := fun w => Scheme.fromSpecResidueField_apply _ _
  have hx' : ∀ w, (x ≫ Q.G.hom) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hx, Q.hom_genericPoint]
  obtain ⟨β, hβ⟩ := M.exists_eq_spMap_pt (x ≫ Q.G.hom) hx'
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hr : Set.range (x ≫ Q.G.hom) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [hx', Scheme.Opens.range_ι]
    exact hg
  let y : Sp K ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (x ≫ Q.G.hom) hr
  have hy : y ≫ U₀.ι = x ≫ Q.G.hom := IsOpenImmersion.lift_fac _ _ _
  let g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y hy.symm
  have hg1 : g ≫ Q.φ = x := Q.cart.1.lift_fst x y hy.symm
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y hy.symm
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  refine ⟨K, inferInstance, β, g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), jP, ?_, pullback.lift_snd _ _ _, (top_le_preimage_iff _ _).1 hj, fun w => hg1 ▸ hx w⟩
  rw [← Category.assoc, hg2, hy, hβ]

theorem eq_of_valF_generic {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : ∀ w, x w = genericPoint X) {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valF x U f = valF x U f') : f = f' := by
  by_contra h0
  have hne : ((X.basicOpen (f - f') : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => h0 (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h)))
  have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (f - f') := fun w _ => by
    change x w ∈ X.basicOpen (f - f')
    rw [hx]
    exact (genericPoint_specializes hne.some).mem_open (X.basicOpen _).isOpen hne.some_mem
  have h2 : ⊤ ≤ x ⁻¹ᵁ U := le_preimage_mono x (X.basicOpen_le _) h1
  have hu := (le_preimage_basicOpen_iff x h2 _).1 h1
  have h3 := h h2
  rw [valF_eq_valR, valF_eq_valR, valR_eq x U h2, valR_eq x U h2] at h3
  rw [valR_eq x U h2, map_sub, h3, sub_self] at hu
  exact not_isUnit_zero hu

theorem ZHPre.eq_of_genVal (hU : (U₀ : Set M.Z).Nonempty) (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) (V : Q.G.left.Opens)
    (σ σ' : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) (h' : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ') :
    σ = σ' := by
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hU
  funext j
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ V := fun y hy => (hm' hy).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (hm' hy).2 0
  have e := (h K β g r jP jL h1 h2 h3 hL hV).symm.trans (h' K β g r jP jL h1 h2 h3 hL hV)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IotaShift
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (y : D.X) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen)
    (b : TF (R := R) F ⟶ D.P.A) (hb : b = g.b * cP D _ y) :
    ∃ ω : Frm D F k b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J =
      val w (𝟙 _) z J * val (g.s y) (𝟙 _) z J ^ k *
        (val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J *
          val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J) := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : jFK (R := R) F ≫ D.xK y = (cP D (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      have a₃ : ∏ i, h (DegPre.gtφ D F g.b y i) ^ ((k : ℤ) * DegPre.gtε i) =
          (∏ i, h (DegPre.gtφ D F g.b y i) ^ DegPre.gtε i) ^ (k : ℤ) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [a₃, prod_gt, prod_line, prod_line, hb, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (GeneratorPullback.powGen D.P.L _ _ (g.s y) k))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (powGen_isGen _ _ _ _ (g.isGen y) k))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen y) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _))
  refine ⟨u, hu, fun z J hJ => ?_⟩
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (map_pow _ _ _))) ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _))))

theorem coef_shift_frame (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) :
    ∃ ω : Frm D F k g'.b, ω.IsGen ∧ ∀ (s : Fam D F k) α, coef s g w (α + k • y) = coef s g' ω α := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  rw [ιb] at hb
  obtain ⟨ω, hω, vω⟩ := exists_frame y g w hw g'.b hb
  refine ⟨ω, hω, fun s α => coef_eq fun z J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k y α
  have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _
    (lift (𝟙 (TF (R := R) F)) g.b).left z J hJ
  have t : lift (𝟙 (TF (R := R) F)) g.b ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) g'.b := by
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
  rw [hv u hu hc _ _ z J hJ, ← Over.comp_left, t, val_famMult _ hJ, uVal, lift_fst_assoc, lift_fst, lift_snd,
    Category.id_comp, Over.id_left] at e₁
  have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g α y k
  rw [Category.id_comp, Over.id_left] at e₂
  have e₃ := hs α z J hJ
  have e₄ : th D z J (cP D _ α) g.b h.b = th D z J (cP D _ α) g.b (cP D _ y) := by rw [ιb]
  have e₅ : val (h.s α) (𝟙 _) z J = val (D.tau y α) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J := ιv α z J hJ
  rw [e₅, e₄] at e₃
  rw [isCoef_coef g' hω α s z J hJ, e₁, vω z J hJ]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
  linear_combination (norm := module) a₃ - a₂

theorem coef_shift (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) (w' : Frm D F k g'.b) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (s : Fam D F k) α, coef s g' w' α = c * coef s g w (α + k • y) := by
  obtain ⟨ω, hω, e⟩ := coef_shift_frame hG hι hadd w hw
  obtain ⟨c, hc, -, e'⟩ := ((coef_basic R D F k g').2.2 ω hω).2.2.1 w' hw'
  exact ⟨c, hc, fun s α => by rw [e', e]⟩

end

theorem parAt_add_iota : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k a g h g' y _ hι hadd
  constructor
  · intro H w' hw' l hl
    obtain ⟨w, hw⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g).1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w hw l hl
    refine ⟨c * κ, mul_ne_zero hc hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc, funext (e s)]
    exact ((Equiv.addRight (k • y)).hasSum_iff.2 (hs σ s hσ)).mul_left c
  · intro H w hw l hl
    obtain ⟨w', hw'⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g').1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w' hw' l hl
    refine ⟨c⁻¹ * κ, mul_ne_zero (inv_ne_zero hc) hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc]
    refine (Equiv.addRight (k • y)).hasSum_iff.1 ?_
    have := (hs σ s hσ).mul_left c⁻¹
    simp only [e s, inv_mul_cancel_left₀ hc] at this
    exact this

end GlobalTheory.ZH.IotaShift
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem exists_projBundle_closure : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  intro o Ω _ _ _ _ M Ω' _ _ φ J _ EE s hM ⟨j₀, hj₀⟩ hs
  obtain ⟨n, t, e, m, v, ht, hv⟩ := GlobalTheory.T.exists_projective_lattice_twist_generated o Ω M hM J EE
  obtain ⟨i₀, hi₀⟩ := ht.1 (genericPoint M.Z)
  obtain ⟨k₀, hk₀⟩ : ∃ k, pairing φ s (v k) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨c, hc⟩ := EE.exists_eq_sum_pairing (φ := φ) s (hv _ i₀ hi₀) j₀
    exact hj₀ (by simp [hc, pairing_div, h])
  let τ : Fin (n + 1) × Fin m → Ω' := fun q => φ (t q.1) * pairing φ s (v q.2)
  have hφ0 : φ (t i₀) ≠ 0 := (map_ne_zero φ).2 hi₀.1
  have hτ0 : τ (i₀, k₀) ≠ 0 := mul_ne_zero hφ0 hk₀
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Fin (n + 1) × Fin m) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨(i₀, k₀)⟩).ne'
  let ε : Fin (N + 1) ≃ Fin (n + 1) × Fin m := (Fintype.equivFinOfCardEq hN).symm
  obtain ⟨M', hcl, hproj⟩ := exists_isCl_isProjOver o Ω' N (fun l => τ (ε l)) ⟨ε.symm (i₀, k₀), by simpa using hτ0⟩ (by
    set K := Subfield.closure (Set.range (algebraMap o Ω') ∪ {x | ∃ i j, x = τ (ε j) / τ (ε i)})
    have hK : ∀ q, τ q / τ (i₀, k₀) ∈ K := fun q =>
      Subfield.subset_closure (Or.inr ⟨ε.symm (i₀, k₀), ε.symm q, by simp⟩)
    obtain ⟨V, hV, hD, hR⟩ := ht.2 i₀ hi₀.1
    have h1 : ∀ x, φ x ∈ K := map_mem_of_ringOn hV ⟨genericPoint M.Z, hD ▸ hi₀⟩ fun x hx => by
      rw [hR] at hx
      induction hx using Algebra.adjoin_induction with
      | mem _ h =>
        obtain ⟨i, rfl⟩ := h
        simpa [τ, mul_div_mul_right _ _ hk₀] using hK (i, k₀)
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, (φ.commutes r).symm⟩)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    refine EE.eq_top_of_pairing_mem hs (hv _ i₀ hi₀) hk₀ h1 fun k => ?_
    rw [pairing_div, mul_div_assoc]
    exact mul_mem (inv_mem (h1 _)) (by simpa [τ, mul_div_mul_left _ _ hφ0] using hK (i₀, k)))
  have hd : ∀ z, ∃ i k, M'.Div (fun i => φ (t i)) i z ∧ M'.Div (fun k => pairing φ s (v k)) k z := fun z => by
    obtain ⟨l, hl⟩ := hcl.1 z
    exact ⟨(ε l).1, (ε l).2, div_mul_prod_iff.1 ((div_comp_iff ε.surjective).1 hl)⟩
  obtain ⟨f, hf⟩ := ht.exists_isHom (M' := M') (φ := φ) fun z => (hd z).imp fun _ h => h.choose_spec.1
  refine ⟨M', f, hf, hproj, fun W B hW hne hB => ?_⟩
  exact charts_of_universal EE hs ht.1 hv hf (fun z => (hd z).choose_spec.imp fun _ h => h.2)
    (fun N' hN' => hcl.exists_isHom fun z => by
      obtain ⟨q, hq⟩ := hN' z
      obtain ⟨l, rfl⟩ := ε.surjective q
      exact ⟨l, (div_comp_iff (t := τ) ε.surjective).2 hq⟩) W B hW hne hB

end GlobalTheory.ZH.RatModel
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem vt_mul_io_shift (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by
  have e : N.c χ * (g * N.io w).b = N.c (χ + w) * g.b := by
    rw [Gt.mul_b, io_b, N.c_add, mul_assoc, mul_comm g.b]
  rw [vt, vt, e, ← mul_assoc, ← Units.val_mul]
  congr 2
  have a := congrArg Additive.ofMul (g.mult χ w)
  rw [Gt.mul_s, io_s, io_b, N.ψ_add, N.τ_symm w χ, N.cub.s12 (N.c χ) g.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) -a

theorem vt_mul_tor_shift (g : N.Gt) (t : Multiplicative N.X →* Oˣ) (χ : N.X) :
    N.vt (g * N.tor t) χ = (t (Multiplicative.ofAdd χ) : Oˣ) * N.vt g χ := by
  rw [vt, vt, mul_comm g, N.tor_mul_s_apply, Gt.mul_b, tor_b, one_mul, mul_left_comm (N.ψ χ), Units.val_mul, mul_assoc]

theorem tk_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.tk p (N.qTriv k z) = p.1.2.s z ^ k :=
  ((GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z).2.2 p.1.2).1

theorem tk_qTriv_left {k : ℕ} (p : N.QT k) (z : N.X) : N.tk (N.qTriv k z) p = p.1.2.s z ^ k := by
  rw [← Gt.pow_s, N.mem_QT.1 p.2, io_s, N.τ_symm]
  rfl

theorem wQ_qTriv_odd {k : ℕ} (hk : Odd k) (z : N.X) : N.wQ (N.qTriv k z) = N.ψ z ^ k := by
  symm
  rw [(GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk (N.qTriv k z) (N.qTriv k z)).1, tk_qTriv_right]
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z
  constructor
  · change _ * dbl N.θ N.σ (N.c z) ^ k = N.τ z z ^ k
    rw [h₁, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  · change _ = N.ψ (k • z) * mulq N.θ N.σ k (N.c z)
    rw [h₂, ← pow_mul, sq]

theorem wQ_mul_qTriv_odd {k : ℕ} (hk : Odd k) (p : N.QT k) (z : N.X) :
    N.wQ (p * N.qTriv k z) = N.wQ p * N.ψ z ^ k * p.1.2.s z ^ k := by
  have h := (GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk p (N.qTriv k z)).2.1
  rw [wp, tk_qTriv_right, tk_qTriv_left, div_self', one_pow, one_mul, N.wQ_qTriv_odd hk] at h
  exact h.symm

theorem txT_mul_qTriv {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (z χ : N.X) :
    N.txT m (p * N.qTriv (m ^ 2) z) χ = N.txT m p (χ + m • z) := by
  have e : (p * N.qTriv (m ^ 2) z).1.2 = p.1.2 * N.io z := rfl
  rw [txT, txT, N.wQ_mul_qTriv_odd hm.pow, e, mul_pow, ← N.io_nsmul, ← N.vt_mul_io_shift, ← mul_assoc,
    ← Units.val_mul]
  congr 2
  have h₁ := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m 0 p.1.2.b (N.c z)).2.1
  obtain ⟨-, h₂, h₃⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N m z
  have h₄ := congrArg (· ^ m) (h₃ p.1.2).1
  have h₅ := Gt.pow_s p.1.2 m (m • z)
  rw [N.c_nsmul] at h₅
  simp only [mul_pow, ← pow_mul, ← sq] at h₄
  rw [Gt.mul_b, io_b, h₁, ← h₂, ← h₄, ← h₅]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem txT_mul_tor {m : ℕ} (hm : Odd m) (p p' : N.QT (m ^ 2)) (χ : N.X) (t : Multiplicative N.X →* Oˣ)
    (h : p'.1.1 = p.1.1) (h' : p'.1.2 = p.1.2 * N.tor t) :
    N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) *
      N.txT m p χ := by
  have ht : t ^ (m ^ 2) = 1 := by
    apply N.tor_injective
    have a := N.mem_QT.1 p'.2
    rw [h, h', mul_pow, N.mem_QT.1 p.2, mul_eq_left] at a
    rw [N.tor_pow, a, N.tor_one]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hd : (m ^ 2 - 1) / 2 = j := by omega
  have hy : t p.1.1 ^ j * t p.1.1 ^ j * t p.1.1 = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hj, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
  have hb : p'.1.2.b = p.1.2.b := by rw [h', Gt.mul_b, tor_b, mul_one]
  have hs : p'.1.2.s p.1.1.toAdd = t p.1.1 * p.1.2.s p.1.1.toAdd := by
    rw [h', mul_comm p.1.2, N.tor_mul_s_apply]
    rfl
  rw [txT, txT, wQ, wQ, NumB.wS, NumB.wS, hb, h, hs, h', mul_pow, ← N.tor_pow, vt_mul_tor_shift, hd,
    ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_nsmul, map_mul, map_pow, MonoidHom.pow_apply]
  have a := congrArg Additive.ofMul hy
  apply Additive.ofMul.injective
  simp only [div_pow, mul_pow, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
  linear_combination (norm := abel) -a

end GlobalTheory.Ex.NumD

namespace GlobalTheory.Ex

theorem txT_shift : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  intro O _ N m hm p p' χ
  refine ⟨fun z h h' => ?_, fun t h h' => N.txT_mul_tor hm p p' χ t h h'⟩
  have e : p' = p * N.qTriv (m ^ 2) z := Subtype.ext (Prod.ext h h')
  rw [e, N.txT_mul_qTriv hm]

end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem pure_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ α hw b φ hr
  rintro χ ⟨l, hl⟩
  by_contra hne
  refine hl ((GlobalTheory.T.hasTorusWeight_iff_torusEquivariant k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).1 ?_ χ hne)
  intro Z τ g z hz
  have := Φ.D.q_hom
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
    (fun _ _ _ => rfl) (fun _ => c.le l hz)
  have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
    congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
  have h₁ := hr _ g.left z J hJ l hz (e ())
  have h₂ := hr _ ((τ ≫ Φ.D.i) * g).left z J hJ l
    (GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz)
    (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
  rw [hq, hw Z τ g z J hJ, Units.val_mul, mul_left_comm, ← h₁] at h₂
  exact h₂

end GlobalTheory.ZH.UFib
end
