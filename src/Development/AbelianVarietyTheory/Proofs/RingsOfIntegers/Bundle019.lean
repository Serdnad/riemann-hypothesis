module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioVal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

def germConst (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem gs_specMap {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F))
    (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ a = germConst F z (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a)) := by
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom (appTop_specMap (CommRingCat.ofHom f) a)

theorem gs_id_const {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c : F) :
    gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = germConst F z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_scal {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F)) (c : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ (scal (𝟙 (Spec (CommRingCat.of A))) c) = germConst F z (f c) := by
  rw [gs_specMap]
  congr 2
  simp [scal]

theorem unit_calc {S : Type} [CommRing S] {s G τ C P R E Eψ Er fam u : Sˣ} {T c₀ cψ cr A : S} {k : ℕ}
    (h1 : s.val = T * G.val) (h2 : τ * C = s ^ k) (h3 : fam = τ * (P * R)) (h4 : fam.val = c₀ * E.val)
    (h5 : P.val = cψ * Eψ.val) (h6 : R.val = cr * Er.val) (h8 : u.val = A)
    (hu : u = E * Eψ⁻¹ * Er⁻¹ * C * (G ^ k)⁻¹) : c₀ * A = T ^ k * cψ * cr := by
  have e1 : u * (Eψ * Er * G ^ k) = E * C := by
    rw [hu]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have e2 : fam * C = s ^ k * (P * R) := by rw [h3, ← h2]; ac_rfl
  have e1' := congrArg Units.val e1
  have e2' := congrArg Units.val e2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, h1, h4, h5, h6, h8, mul_pow] at e1' e2'
  apply (Eψ * Er * G ^ k).isUnit.mul_right_cancel
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination c₀ * e1' + e2'

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem v_ratio_gt (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)) (hG₀ : G₀.IsGen) (t : F)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) :
    ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = QForm.bOf D.toPre Q p.y α := by
  have hL := D.toPre.P.isLB
  have hmk : m ^ k = cP D.toPre (TO hϖ hv) p.y := by
    apply liftO_unique hϖ hv
    rw [comp_cP, cPoint_y, ← hm]
    exact map_pow (preHom (ιS hϖ hv)) m k
  obtain ⟨Ix, _, φV, εV, e', he', hfe', c₀, hc₀, hve'⟩ := famMult_data D hϖ hQ k p.y α
  obtain ⟨eψ, heψ, cψ, hcψ, hteψ⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ p.y) k
  obtain ⟨er, her, cr, hcr, hter⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (QForm.rigK_val (ϖ := ϖ) D) k
  obtain ⟨tc, htc, hvtc⟩ := exists_cubN D.toPre.cub (1 : TO hϖ hv ⟶ D.toPre.P.A) m (cP D.toPre _ α) k
  let h₀ : (TO hϖ hv).left ⟶ Spec (CommRingCat.of V) := (TO hϖ hv).hom
  let u := LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ e' h₀)
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eψ h₀)))
    (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ er h₀))) tc)
    (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ G₀ k))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ he' _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ heψ _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ her _))) htc) (invGen_isGen _ _ _ _ (powGen_isGen' _ _ _ _ hG₀ k))
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  have hfs : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      (((((∏ i, h (h₀ ≫ φV i) ^ εV i) * (h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1))⁻¹) *
        (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1))⁻¹) *
        ∏ i, h (![(1 * m ^ k * cP D.toPre _ α).left, (1 * m ^ k).left, (1 * cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left, (m * cP D.toPre _ α).left, m.left, (cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left] i) ^ (![1, -1, -1, 1, -k, k, k, -k] : Fin 8 → ℤ) i) *
        (∏ i, h (gtφO hϖ hv m α i) ^ ((k : ℤ) * DegPre.gtε i))⁻¹) = 1 := by
    intro U _ h
    let o : TO hϖ hv ⟶ D.toPre.P.A := 1
    have e := hfe' U (fun q => h (o.left ≫ q))
    have w : o.left ≫ D.toPre.P.A.hom = h₀ := Over.w o
    have q₀ : ∀ i, o.left ≫ D.toPre.P.A.hom ≫ φV i = h₀ ≫ φV i := fun i => by rw [← Category.assoc, w]
    have q₁ : ∀ χ, o.left ≫ (cQ D.toPre D.toPre.P.A χ).left = (cP D.toPre (TO hϖ hv) χ).left := fun χ =>
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre o χ)
    have q₂ : o.left ≫ (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A p.y).left =
        (cP D.toPre (TO hϖ hv) α * cP D.toPre (TO hϖ hv) p.y).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) ((MonObj.comp_mul o _ _).trans
        (congrArg₂ (· * ·) (comp_cP D.toPre o α) (comp_cP D.toPre o p.y)))
    have q₃ : o.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TO hϖ hv ⟶ D.toPre.P.A).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) o)
    simp only [q₀, q₁, q₂, q₃] at e
    rw [e, hmk, _root_.one_mul, _root_.one_mul, mul_comm (cP D.toPre (TO hϖ hv) p.y), mul_comm m]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, gtφO, DegPre.gtε]
    module
  have pψ : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ (D.toPre.c p.y).left) ^ ((k : ℤ) * -1) =
        h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1) := fun U _ h => by
    rw [Fintype.prod_unique]
    rfl
  have pr : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ 𝟙 _ ≫ eSec D.toPre.P.A) ^ ((k : ℤ) * 1) =
        h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1) := fun U _ h => by
    rw [Fintype.prod_unique, Hom.one_def]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val u r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj u hu (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
  obtain ⟨a', ha'⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val (LB.invGen D.toPre.P.L _ _ u) r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu) (fun U _ h => by
      refine (prod_neg _ _ ?_).trans inv_one
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
  let z₀ : Spec (CommRingCat.of F) := default
  choose J₀ hJ₀ using fun χ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => exists_chart hL (χ z₀)
  have hG : Good D.toPre.P.L z₀ J₀ := hJ₀
  have h1 := ht _ (𝟙 _) z₀ J₀ hG
  have h2 := chain_val (𝟙 (TF (R := V) F)) hG p α
  have h3 := val_famMult (𝟙 (TF (R := V) F)) hG k p.y α
  have h4 := hve' F _ (𝟙 _) z₀ J₀ hG
  have h5 := val_genHasVal (hφ := fun _ => QForm.ptK_eq D.toPre p.y) hteψ ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h6 := val_genHasVal (hφ := fun _ => by rw [Category.id_comp]; rfl) hter ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h7 := hvtc (TF (R := V) F) (ιS hϖ hv) z₀ J₀ hG
  have h8 := ha _ (ιS hϖ hv).left z₀ J₀ hG
  have h8' := ha' _ (ιS hϖ hv).left z₀ J₀ hG
  have hι : (ιS hϖ hv).left ≫ (TO hϖ hv).hom = DegPre.jFR (R := V) F := Over.w (ιS hϖ hv)
  have hid : Over.Hom.left (𝟙 (TF (R := V) F)) = 𝟙 (Spec (CommRingCat.of F)) := Over.id_left _
  rw [hid] at h2 h3
  simp only [Category.id_comp] at h1 h2 h3 h4 h5 h6 h8 h8'

  have hu8 : val u (ιS hϖ hv).left z₀ J₀ = val (Z := (TF (R := V) F).left) e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (val (Z := (TF (R := V) F).left) eψ (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      (val (Z := (TF (R := V) F).left) er (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      val tc (ιS hϖ hv).left z₀ J₀ * (val G₀ (ιS hϖ hv).left z₀ J₀ ^ k)⁻¹ := by
    simp only [u, h₀, val_mul hG, val_inv, val_pull hG, val_powGen, hι]
  have h7' : val tc (ιS hϖ hv).left z₀ J₀ = cubN (th D.toPre z₀ J₀) k 1 p.g.b (cP D.toPre (TF (R := V) F) α) := by
    rw [h7, MonObj.comp_one, hm, comp_cP]
  have key := unit_calc h1 (h7' ▸ h2) h3 h4 h5 h6 h8 hu8
  have g1 : gs (𝟙 (TF (R := V) F).left) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) = germConst F z₀ t :=
    gs_id_const z₀ t
  have g2 : ∀ c : FractionRing V, gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 _) c) =
      germConst F z₀ (algebraMap (FractionRing V) F c) := fun c => gs_scal _ z₀ c
  have g3 : ∀ b : Γ((TO hϖ hv).left, ⊤), gs ((ιS hϖ hv).left ≫ 𝟙 _) z₀ ⊤ b = germConst F z₀ (ιr (v := v) b) := fun b => by
    rw [Category.comp_id]; exact gs_specMap _ z₀ b
  have hinj : Function.Injective (germConst F z₀) := (germConst F z₀).injective
  have k1 : algebraMap (FractionRing V) F c₀ * ιr (v := v) a =
      t ^ k * algebraMap (FractionRing V) F cψ * algebraMap (FractionRing V) F cr := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [← g1, ← g2, ← g2, ← g2, ← g3]
    exact key
  have k2 : ιr (v := v) a * ιr (v := v) a' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← g3, ← g3, ← h8, ← h8', val_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have va : v (ιr (v := v) a) = 0 := by
    have e : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by rw [← AddValuation.map_mul, k2, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg e (v_ιr a')) (v_ιr a)
  have k3 := congrArg v k1
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, va, hv _ _ hc₀,
    hv _ _ hcψ, hv _ _ hcr] at k3
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [g1, map_zero, zero_mul] at h1
    exact (val (p.g.s α) (𝟙 _) z₀ J₀).ne_zero h1
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) ht0
  refine ⟨q, hq, ?_⟩
  rw [hq] at k3
  have k4 : (((k : ℤ) * Q p.y + QForm.bOf D.toPre Q p.y α : ℤ) : ℚ) + 0 =
      k • q + (((k : ℤ) * Q p.y : ℤ) : ℚ) + (((k : ℤ) * 0 : ℤ) : ℚ) := by exact_mod_cast k3
  rw [nsmul_eq_mul] at k4
  push_cast at k4
  linarith

theorem main : TWM.VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

end GlobalTheory.RatioVal
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace WeightDvd

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem appLE_dvd {P T : Scheme.{0}} [IsAffine P] (p : P ⟶ T) (W : T.Opens) (e : ⊤ ≤ p ⁻¹ᵁ W) (u v : Γ(T, W))
    (h : ∀ w ∈ W, gs (𝟙 T) w W u ∣ gs (𝟙 T) w W v) : (p.appLE W ⊤ e).hom u ∣ (p.appLE W ⊤ e).hom v := by
  rw [← Ideal.mem_span_singleton, (isAffineOpen_top P).mem_ideal_iff]
  intro z hz
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have k : ∀ c : Γ(T, W), (P.presheaf.germ ⊤ z hz).hom ((p.appLE W ⊤ e).hom c) =
      (p.stalkMap z).hom (gs (𝟙 T) (p z) W c) := fun c =>
    ((gs_eq (𝟙 P) z ⊤ hz _).symm.trans (gs_appLE p W ⊤ e (𝟙 P) z hz c)).trans
      ((by rw [Category.id_comp] : gs (𝟙 P ≫ p) z W c = gs p z W c).trans (gs_stalkMap p z W (e hz) c))
  have := map_dvd (p.stalkMap z).hom (h (p z) (e hz))
  rw [← k, ← k] at this
  exact this

theorem dvd_of_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (s : Finset X) (a : Γ(Y.left, V)) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      gs (snd (splitTorus S X) Y).left w V a ∣
        ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ)) :
    ∀ χ ∈ s, a ∣ h χ := by
  intro χ₀ hχ₀
  have k : ∀ (w : (splitTorus S X ⊗ Y).left) (hw : (snd (splitTorus S X) Y).left w ∈ V) (c : Γ(Y.left, V)),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun w hw c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  have H := appLE_dvd (TorusInj.pt (X := X) hV) _ (TorusInj.pt_le hV) (((snd (splitTorus S X) Y).left.app V).hom a)
    (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) fun w hw => by
      rw [k w hw, gs_fsum (𝟙 _) w _ hw]
      refine (hs w hw).trans (dvd_of_eq (Finset.sum_congr rfl fun χ _ => ?_))
      rw [gs_mul (𝟙 _) w _ hw, k w hw, gs_res (𝟙 _) w _ hw]
  have H' : TorusInj.ev hV (((snd (splitTorus S X) Y).left.app V).hom a) ∣ TorusInj.ev hV
      (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) :=
    map_dvd (Scheme.ΓSpecIso (TorusInj.GA (X := X) (V := V))).hom.hom H

  simp only [map_sum, map_mul, TorusInj.ev_chi, TorusInj.ev_snd, AddMonoidAlgebra.single_mul_single,
  add_zero, _root_.one_mul] at H'
  obtain ⟨g, hg⟩ := H'
  have hc := congrArg (fun f => f.coeff χ₀) hg
  rw [TorusInj.coeff_sum_single X s _ χ₀ hχ₀] at hc
  refine ⟨g.coeff χ₀, hc.trans ?_⟩
  simp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem val_act (β : D.toPre.X) (w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left) {J}
    (hJ : Good D.toPre.P.L w J) :
    (val (tG U e β) (WeightPf.act (U.gt e)).left w J).val =
      gs (𝟙 _) w ⊤ (TorusInj.chiP D.toPre.X (thickObj R I e G) β) *
        (val (tG U e β) (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w J).val := by
  have E := val_corr hJ ((U.gt e).t_weight β) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.toPre.P.L) (K := PEmpty) (Y := (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left)
    PEmpty.elim (𝟙 _)
  exact (congrArg Units.val (gm_rp₁ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ _ _ hm
    (charUnit _ D.toPre.X β))).trans ((gs_unit _ w ⊤ trivial _).symm.trans
      ((gs_pull (𝟙 _) (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ trivial _).trans
        (by rw [Category.id_comp])).symm)

theorem dvd_on_group (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hσ : SecIsMul G.hom r σ τ)
    (hE : U.ExpandsAt e k σ f) (α : D.toPre.X) (y : (thickObj R I e G).left) (J) (hJ : Good D.toPre.P.L y J) :
    cst (pGl U e ≫ D.toPre.P.A.hom) y r ∣ sval (f α) (pGl U e) y J := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  by_cases hα : α ∉ S
  · have := (hS _ (𝟙 _) y J hJ).1 α hα
    rw [Category.id_comp] at this
    rw [this]
    exact dvd_zero _
  push Not at hα
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (pGl U e ≫ D.toPre.famφB β a)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (Oφl U e β a)
  have hy : y ∈ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) :=
    mem_finf S _ _ fun β _ => ⟨hJ.mem (D.toPre.famφB β) (pGl U e), Set.mem_iInter.2 fun a => hJ _⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := ((thickObj R I e G).left.isBasis_affineOpens).exists_subset_of_mem_open hy
    (S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β))).2
  have hVW' : V ≤ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) := hVW
  have hVf : ∀ β ∈ S, V ≤ pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_left)
  have hVt : ∀ β ∈ S, V ≤ LB.wchart D.toPre.P.L (Oφl U e β) (jt β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_right)
  have ex : ∀ β ∈ S, ∃ c : Γ((thickObj R I e G).left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (thickObj R I e G).left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs (ρ ≫ pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ((f β).f (jf β)) *
        (gm ρ z (LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) ((tG U e β).s (jt β))).val := fun β hβ =>
    ⟨((pGl U e).appLE _ V (hVf β hβ)).hom ((f β).f (jf β)) * (res (hVt β hβ) ((tG U e β).s (jt β))).val,
      fun Z ρ z hz => (gs_mul ρ z V hz _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ z hz _)
        ((gs_unit ρ z V hz _).trans (congrArg Units.val (gm_res ρ z _ hz _))))⟩
  choose! c hc using ex
  have hpG := WeightPf.act_left_pG (U.gt e)
  have hb : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := dvd_of_sum D.toPre.X (thickObj R I e G) hV S (constFn (pGl U e ≫ D.toPre.P.A.hom) V r) c (fun w hw => by
    choose d hd using fun ψ : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ =>
      if ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ)) then
        J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ) else d ψ
    have hJ₂ : Good D.toPre.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hd ψ
    have eJ : ∀ φ : (thickObj R I e G).left ⟶ D.toPre.P.A.left,
        φ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w) ∈ D.toPre.P.L.U (J φ) →
        J₂ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ) = J φ := fun φ h => by
      have e₁ : (WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ = φ := by
        rw [← Category.assoc, WeightPf.sec_left_snd, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl I G e ((WeightPf.act (U.gt e)).left w))
    have E := (hS _ (WeightPf.act (U.gt e)).left w J₂ hJ₂).2 jL hL
    have hs : sv U k σ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL =
        cst (((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom) w r *
          sv U k τ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL :=
      secIsMul_gs hσ _ w (fun _ => jL) (Set.mem_iInter.2 fun _ => hL)
    have e₂ : ((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ pGl U e ≫ D.toPre.P.A.hom := by
      rw [Category.assoc, ← hb, ← Category.assoc, hpG, Category.assoc]
    rw [hs, e₂, mul_left_comm] at E
    refine (dvd_of_eq (gs_constFn _ V _ w hw r)).trans ((Dvd.intro _ E).trans
      (dvd_of_eq (Finset.sum_congr rfl fun β hβ => ?_)))
    rw [hc β hβ _ _ w hw, val_act U e β w hJ₂, mul_left_comm, hpG,
      sval_of (f β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (tG U e β) _ w J₂ (jt β) (fun a => eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  obtain ⟨g, hg⟩ := H
  have E := hc α hα _ (𝟙 _) y hyV
  rw [hg, gs_mul (𝟙 _) y V hyV, gs_constFn _ V (𝟙 _) y hyV, Category.id_comp, Category.id_comp] at E
  exact (Units.dvd_mul_right).1 (Dvd.intro _ E)

end WeightDvd

theorem expandsAt_dvd_of_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom r σ τ → U.ExpandsAt e k σ f → ∀ (α : D.toPre.X) (x : (thickObj R I e D.toPre.P.A).left) (J), Geo.Tor.Good D.toPre.P.L x J → Geo.Tor.cst ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) x r ∣ Geo.Tor.sval (f α) (fstG I e D.toPre.P.A).left x J := by
  intro R _ _ I D A G _ _ U e k r σ τ f hσ hE α x J hJ
  have := (U.gt e).q_flat
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x
  choose J' hJ' using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have H := WeightDvd.dvd_on_group U e k r σ τ f hσ hE α y J' hJ'
  have hm := hJ.mem (D.toPre.famφB α) (fstG I e D.toPre.P.A).left
  have e₁ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left (fstG I e D.toPre.P.A).left y _ hm
    ((f α).f fun a => J ((fstG I e D.toPre.P.A).left ≫ D.toPre.famφB α a))
  have e₂ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) y ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₃ := sec_trans (f α) (pGl U e) y hm (Good.mem hJ' (D.toPre.famφB α) (pGl U e))
  refine dvd_descend (U.gt e).q.left y ?_
  exact (dvd_of_eq e₂.symm).trans ((H.mul_left _).trans (dvd_of_eq (e₃.symm.trans e₁)))

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpUniq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by
  intro hB V _ _ _ D A G _ _ U k σ f g hf hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.proper
  have := D.toPre.P.isAb.geomConnected
  let d : ∀ α : D.toPre.X, D.toPre.SecB k α := fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))
  have hd : ∀ α j, (d α).f j = (f α).f j - (g α).f j := fun α j => (sub_eq_add_neg _ _).symm
  have h0 : ∀ e, U.ExpandsAt e k SecOps.secZero d := fun e =>
    GlobalTheory.expandsAt_sub V _ D A G U e k σ σ SecOps.secZero f g d (fun j => (sub_self _).symm) hd (hf e) (hg e)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((hd α j).symm.trans ?_)
  refine hB V D.toPre.P.A _ (linComb_isLB _ D.toPre.P.isLB _ _) (d α) ϖ hϖ (fun i e => ?_) j
  obtain ⟨τ, hτ⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U e k α (d α)).1
    (WeightPf.weightIndep V _ D A G U e k SecOps.secZero d (fun _ => map_zero _) (h0 e) α)
  rw [hτ i]
  change _ ∈ Ideal.span {resTop ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε k)).U i) (scal D.toPre.P.A.hom ϖ)} ^ e
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine Dvd.dvd.mul_right ?_ _
  simp only [scal, pow_succ, map_mul, map_pow]
  exact Dvd.dvd.mul_right (dvd_refl _) _

end GlobalTheory.ExpUniq
end
