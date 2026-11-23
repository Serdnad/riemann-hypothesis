module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.SameLam

section Comp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D₃ : DegData R I}
  {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
  {U₃ : UnifPre I D₃ A₃ G₃} {a : G₁ ⟶ G₂} {a' : G₂ ⟶ G₃}

theorem over_comp {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {b' : D₂.toPre.P.A ⟶ D₃.toPre.P.A} (h : Over₀ U₁ U₂ a b)
    (h' : Over₀ U₂ U₃ a' b') : Over₀ U₁ U₃ (a ≫ a') (b ≫ b') := fun e => by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h' e, ← Category.assoc, h e, Category.assoc]

theorem over_id : Over₀ U₁ U₁ (𝟙 _) (𝟙 _) := fun e => by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem onTorus_comp {h : D₂.toPre.X → D₁.toPre.X} {h' : D₃.toPre.X → D₂.toPre.X} (H : OnTorus U₁ U₂ a h)
    (H' : OnTorus U₂ U₃ a' h') : OnTorus U₁ U₃ (a ≫ a') (h ∘ h') := fun e => by
  obtain ⟨t, ht, et⟩ := H e
  obtain ⟨t', ht', et'⟩ := H' e
  refine ⟨t ≫ t', fun χ => unit_ext fun z _ => ?_, by
    rw [Functor.map_comp, ← Category.assoc, et, Category.assoc, et', Category.assoc]⟩
  have e₁ := congrArg (gm (𝟙 _) z ⊤) (ht (h' χ))
  have e₂ := congrArg (gm (𝟙 _ ≫ t.left) z ⊤) (ht' χ)
  refine Eq.trans ?_ e₁
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) (t ≫ t').left z ⊤ trivial _)).trans
    (Eq.trans ?_ ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)).symm)
  refine Eq.trans ?_ e₂
  refine Eq.trans ?_ ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _ ≫ t.left) t'.left z ⊤ trivial _)).symm
  rw [Over.comp_left, Category.assoc]

theorem onTorus_id : OnTorus U₁ U₁ (𝟙 _) id := fun e =>
  ⟨𝟙 _, fun χ => unit_ext fun z _ => ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans
    (gm_pull (𝟙 _) (𝟙 _) z ⊤ trivial _)).trans (by rw [Category.comp_id]; rfl), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩

end Comp



theorem iso_of_lbIso_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG lin D' A' U' _ o' oA' lin' H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨h, th⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨k, tk⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre (𝟙 G)
  have un' := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D' A' A' G G U'.toUnifPre U'.toUnifPre (𝟙 G)
  have ipB : incB ≫ prB = 𝟙 _ := un'.1 _ _ (by have := over_comp qinc qpr; rwa [Category.comp_id] at this) over_id
  have piB : prB ≫ incB = 𝟙 _ := un.1 _ _ (by have := over_comp qpr qinc; rwa [Category.comp_id] at this) over_id
  have kh : ∀ χ, k (h χ) = χ := congrFun (un'.2 _ _ (by have := onTorus_comp tk th; rwa [Category.comp_id] at this)
    onTorus_id)
  have hk : ∀ χ, h (k χ) = χ := congrFun (un.2 _ _ (by have := onTorus_comp th tk; rwa [Category.comp_id] at this)
    onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  let xe : D'.toPre.X ≃+ D.toPre.X :=
    { toFun := h, invFun := k, left_inv := kh, right_inv := hk, map_add' := h.map_add }

  have ql : ∀ x, Over₀ U.toUnifPre U.toUnifPre (oG.act x) (o.onB.act x) := fun x e => lin.q_lin e x
  have ql' : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (o'.onB.act x) := fun x e => lin'.q_lin e x
  have il : ∀ x, OnTorus U.toUnifPre U.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have il' : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin'.i_lin e x
  have linB : ∀ a, o'.onB.act a ≫ incB = incB ≫ o.onB.act a := fun a =>
    (GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (oG.act a)).1 _ _
      (by have := over_comp (ql' a) qinc; rwa [Category.comp_id] at this)
      (by have := over_comp qinc (ql a); rwa [Category.id_comp] at this)
  have linS : ∀ (b : O) χ, star b • h χ = h (star b • χ) := fun b => congrFun
    ((GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (oG.act b)).2 _ _
      (by have := onTorus_comp (il b) th; rwa [Category.comp_id] at this)
      (by have := onTorus_comp th (il' b); rwa [Category.id_comp] at this))
  have linX : ∀ (a : O) x, h (a • x) = a • h x := fun a x => by
    have := linS (star a) x
    rw [star_star] at this
    exact this.symm

  have L : Lin U.toUnifPre U'.toUnifPre (𝟙 G) prB h := ⟨inferInstance, hprB, qpr, th⟩
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A'.A, IsMonHom c ∧ Gen₀ U.toUnifPre U'.toUnifPre (𝟙 G) c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map (𝟙 G) ≫ U'.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨E, eG, -⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (𝟙 G) (𝟙 A.A) inferInstance inferInstance
    (by simp)
  have eh : ∀ y, E.h y = y := fun y =>
    congrFun (un.2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) onTorus_id) y
  have adj : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) := by
    rw [eG]
    simp only [Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U.LG.isLB _ _)
  have H₂ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) (𝟙 G) E.aG (𝟙 G) c c
    E.aA (𝟙 _) gc gc E.ext (by simp [Gen₀]) (by rw [eG]; simp only [Category.comp_id]; exact H)
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C E E
    adj H₂ Ω K
  have H' : LBIso (abelian₂ G U'.LG.L) ((abelian₂ G U.LG.L).pull (lift (fst G G ≫ 𝟙 G) (snd G G ≫ 𝟙 G) : G2 G ⟶ G2 G).left) := by
    simp only [Category.comp_id, lift_fst_snd, Over.id_left]
    exact LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) H
  have H₃ := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hA D' D A' A G G hG hG U' U (𝟙 G) (𝟙 G) incB incB inferInstance inferInstance hincB hincB
    qinc qinc H'
  have key := GlobalTheory.Mum.Two.Fac.periods_of_factor R D'.toPre D.toPre D.tau_bimult O o 1 1 incB prB h φ hincB hprB
    (by rw [piB, o.onB.map_one]) (fun χ => (C χ).imp fun _ => And.left)
    (by rw [o.onB.map_one, Category.comp_id]; exact H₃) Ω hφ
    (fun y => by rw [hhφ, eh, star_one, one_smul, one_smul, one_smul])
  rw [o.onB.map_one, Category.comp_id] at key
  obtain ⟨cφ, w, hw, ht⟩ := key
  have φh : ∀ x, φ (h x) = x := fun x => hinj ((hhφ (h x)).trans (eh _))
  refine ⟨⟨incB, prB, ipB, piB⟩, xe, hincB, qinc, tk, linB, linX, fun x => ?_, w, hw, fun a b z J J' hJ hJ' => ?_⟩
  · show D'.toPre.c x ≫ incB = D.toPre.c (h x)
    have := cφ (h x)
    rw [φh] at this
    rw [this, Category.assoc, piB, Category.comp_id]
  · have := ht (h a) (h b) z J J' hJ hJ'
    rw [φh, φh, one_smul, one_smul, one_smul] at this
    exact this

end GlobalTheory.Mum.SameLam
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pairing_isPerfect_abelianSchemes_both_kernels_zero : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | exact GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | (intros; apply GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlgMorphisms

variable {R : Type} [CommRing R]

instance isClosedImmersion_thick (I : Ideal R) (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem isPullback_trans {I : Ideal R} (X : Over (Spec (CommRingCat.of R)))
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left)
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (e : ℕ) : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := by
  have hw : β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, ← (hb (e + 1)).w, ← Category.assoc,
      hβ, (hb e).w, Category.assoc, thickTrans_comp]
  refine IsPullback.of_right ?_ hw (hb (e + 1))
  rw [hβ, thickTrans_comp]
  exact hb e

theorem formalAlgebraisation_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    haveI := hI
    exact IsAdicComplete.le_jacobson_bot I

  let fW : pullback X.hom Z.hom ⟶ Spec (CommRingCat.of R) := pullback.fst X.hom Z.hom ≫ X.hom
  haveI : IsSeparated (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback X.hom Z.hom).flip hZs
  haveI : LocallyOfFiniteType (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback X.hom Z.hom).flip hZl
  haveI : QuasiCompact (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback X.hom Z.hom).flip hZq
  have hAlg : Alg fW I := GlobalTheory.T.grothendieck_existence_closedSubschemes_separated R I hI _ fW inferInstance inferInstance inferInstance

  have hcomm : ∀ e, b e ≫ X.hom = f e ≫ Z.hom := fun e => by rw [(hb e).w, hf e]
  let j : ∀ e, (Y e).left ⟶ pullback X.hom Z.hom := fun e => pullback.lift (b e) (f e) (hcomm e)
  have hj₁ : ∀ e, j e ≫ pullback.fst X.hom Z.hom = b e := fun e => pullback.lift_fst _ _ _
  have hj₂ : ∀ e, j e ≫ pullback.snd X.hom Z.hom = f e := fun e => pullback.lift_snd _ _ _
  have hbci : ∀ e, IsClosedImmersion (b e) := fun e =>
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb e).flip inferInstance
  have hjci : ∀ e, IsClosedImmersion (j e) := fun e => by
    haveI : IsClosedImmersion (j e ≫ pullback.fst X.hom Z.hom) := by rw [hj₁]; exact hbci e
    exact IsClosedImmersion.of_comp (j e) (pullback.fst X.hom Z.hom)
  have hjf : ∀ e, j e ≫ fW = (Y e).hom ≫ thick R I e := fun e => by
    simp only [fW]
    rw [← Category.assoc, hj₁, (hb e).w]
  have hjβ : ∀ e, β e ≫ j (e + 1) = j e := fun e => by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hj₁, hβ]
    · rw [Category.assoc, hj₂, hj₂, hfβ]
  have hYp : ∀ e, IsProper (Y e).hom := fun e =>
    MorphismProperty.of_isPullback (P := @IsProper) (hb e) hX
  obtain ⟨T, i, c, hi, hip, hci, hcpb⟩ := GlobalTheory.T.formal_algebraisation_tower R I _ fW hAlg Y β
    (isPullback_trans X Y β b hb hβ) hYp j hjci hjf hjβ

  let φ : T ⟶ X.left := i ≫ pullback.fst X.hom Z.hom
  have hφX : φ ≫ X.hom = i ≫ fW := Category.assoc _ _ _
  haveI : IsProper (φ ≫ X.hom) := by rw [hφX]; exact hip
  haveI : IsProper φ := IsProper.of_comp φ X.hom
  have hcφ : ∀ e, c e ≫ φ = b e := fun e => by
    simp only [φ]
    rw [← Category.assoc, hci, hj₁]
  haveI hφiso : IsIso φ := GlobalTheory.T.isIso_of_proper_isIso_on_reductions R I hIj T X.left φ X.hom inferInstance hX Y c
    (fun e => by rw [hφX]; exact hcpb e) (fun e => by rw [hcφ]; exact hb e)

  let gl : X.left ⟶ Z.left := inv φ ≫ i ≫ pullback.snd X.hom Z.hom
  have hgw : gl ≫ Z.hom = X.hom := by
    simp only [gl, Category.assoc]
    rw [← pullback.condition, ← Category.assoc i, ← Category.assoc (inv φ)]
    exact IsIso.inv_hom_id_assoc φ X.hom
  refine ⟨Over.homMk gl hgw, fun e => ?_, fun g' hg' => ?_⟩
  · show b e ≫ gl = f e
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]
  · refine GlobalTheory.T.morphism_eq_of_eq_on_thickenings R I hIj X Z hX hZs Y b hb g' _ fun e => ?_
    rw [hg' e]
    show f e = b e ≫ gl
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]

end GlobalTheory.FormalAlgMorphisms
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogCanon

theorem restr_top_surj {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (h : O = ⊤)
    (x : H0 p B O) : ∃ g : H0 p B ⊤, H0.restr le_top g = x := by
  subst h
  refine ⟨x, ?_⟩
  show (LB.toMod B).presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op x = x
  rw [show (homOfLE (le_refl (⊤ : Y.Opens))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem dimFlag_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (h : ¬ 1 ≤ Dw.p + Dw.q) : dimFlag Dw = 0 := by
  have : Dw.p + Dw.q = 0 := by omega
  simp [GlobalTheory.FlagTan.dimFlag, this]

theorem logCanon_iff : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω b s hs m
  have hV : IsVariety₀ TF.X Z := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  · have hKS : (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) := fun K _ _ y => GlobalTheory.T.kodaira_spencer_iso_flag_tangent hP hG E H Dw l Xo c K y hpq
    obtain ⟨ω₀⟩ := GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary hP.p5 E H Dw l Xo c TF.Y TF.X Z (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) hKS
    exact (GlobalTheory.T.canonical_modification_ks_iso hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m).trans (GlobalTheory.T.canonical_modification_ks_iso_sec hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ M ω b s hs m)
  · have h0 := dimFlag_eq_zero Dw hpq
    have hU : U₀ TF.X Z = ⊤ := GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero c.F _ (str₀ TF.X Z) (h0 ▸ hV.1) _ (dense_U₀ TF.X Z)
    have hall : ∀ y, y ∈ U₀ TF.X Z := fun y => hU.symm ▸ (Set.mem_univ y : y ∈ ((⊤ : (Y₀ TF.X Z).Opens) : Set _))
    have hoff : M.off = ⊤ := eq_top_iff.2 fun x _ => M.off_eq.ge (hall _)
    refine iff_of_true ?_ (restr_top_surj hoff _)
    obtain ⟨g, hg⟩ := restr_top_surj hU m
    refine ⟨g, fun y hy => (hy (hall y)).elim, hg⟩

end GlobalTheory.LogCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSExists

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} (h : W₁ ≤ W₀) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h), fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

theorem isField_sub {Z : Scheme.{0}} {W₀ : Z.Opens} {d d' : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) (hd' : IsField W₀ d') : IsField W₀ (fun W f => d W f - d' W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · simp only [hd.1 W hW, hd'.1 W hW]; ring
  · simp only [hd.2.1 W hW, hd'.2.1 W hW]; ring
  · simp only [map_sub, hd.2.2 W W' h hW, hd'.2.2 W W' h hW]

theorem lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := GlobalTheory.T.exists_vectorField_lifts_affine_cover_smooth_group

theorem cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := GlobalTheory.T.cechCocycle_verticalFields_eq_coboundary_add_logDerivatives

theorem exists_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t ⊤ U v D Θ := by
  intro E _ _ _ H X t hP hA hK U n v hv hb D
  obtain ⟨J, W, j, d, hWa, hcov, hWj, hd, hlift⟩ := lifts E H X t U D
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => hcov ▸ le_iSup W i
  have hres : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i)
      ((t.G.hom.appLE U.1 (W i) (hWU i)).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i) (homOfLE (inf_le_left : W i ⊓ W i' ≤ W i)).op)
  have hres' : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i')
      ((t.G.hom.appLE U.1 (W i') (hWU i')).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i') (homOfLE (inf_le_right : W i ⊓ W i' ≤ W i')).op)
  have a1 : ∀ i i' (r : Γ(X, U.1)), d i (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres i i' r, (hd i).2.2 _ _ inf_le_left le_rfl, hlift i (hWU i), hres]
  have a2 : ∀ i i' (r : Γ(X, U.1)), d i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres' i i' r, (hd i').2.2 _ _ inf_le_right le_rfl, hlift i' (hWU i'), hres']
  obtain ⟨Θ, h, hh, hhv, hks⟩ := cocycle E H X t hP hA hK U n v hv hb J W j hWa hcov hWj
    (fun i i' O f => d i O f - d i' O f)
    (fun i i' => isField_sub (isField_mono inf_le_left (hd i)) (isField_mono inf_le_right (hd i')))
    (fun i i' hW r => by
      show d i _ _ - d i' _ _ = 0
      rw [a1, a2, sub_self])
    (fun i i' i'' O _ f => sub_add_sub_cancel _ _ _)
  refine ⟨Θ, J, W, j, fun i O f => d i O f - h i O f, by rw [inf_top_eq]; exact hcov, hWj,
    fun i => isField_sub (hd i) (hh i), fun i hW r => ?_, fun i i' O hO f S _ φ g₀ w hg hO' hw => ?_⟩
  · show d i _ _ - h i _ _ = _
    rw [hlift i hW r, hhv i hW r, sub_zero]
  · have e := hks i i' O hO f S φ g₀ w hg hO' hw
    have hv' : ∀ a b : Γ(t.G.left, O), valR g₀ O (a - b) = valR g₀ O a - valR g₀ O b := fun a b => by
      simp only [valR, dif_pos hO', map_sub]
    show valR g₀ O ((d i O f - h i O f) - (d i' O f - h i' O f)) = _
    rw [show (d i O f - h i O f) - (d i' O f - h i' O f) = (d i O f - d i' O f) - (h i O f - h i' O f) by ring,
      hv', e]
    ring

end GlobalTheory.KSExists
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
end
