module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumAgree

theorem subsingleton_thick (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = maximalIdeal R := by
    intro P
    have hp : (P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : maximalIdeal R ^ (e + 1) ≤ P.asIdeal.comap (Ideal.Quotient.mk _) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
      exact P.asIdeal.zero_mem
    have hm : maximalIdeal R ≤ _ := hp.le_of_pow_le hle
    exact ((maximalIdeal.isMaximal R).eq_of_le hp.ne_top hm).symm
  constructor
  intro P Q
  change PrimeSpectrum _ at P Q
  exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((key P).trans (key Q).symm))

theorem eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  intro R _ _ _ _ D A G _ _ hG U e x x' hx hx' W y hy hW
  have hH : IsSemiAbelian (thickObj R (maximalIdeal R) e G) :=
    IsSemiAbelian.pullback (thick R (maximalIdeal R) e) G hG
  have := hH.smooth
  have hflat : Flat (thickObj R (maximalIdeal R) e G).hom := inferInstance
  let V : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
    Over.mk (W.ι ≫ (thickObj R (maximalIdeal R) e G).hom)
  let j : V ⟶ thickObj R (maximalIdeal R) e G := Over.homMk W.ι rfl
  have hsub := subsingleton_thick R e
  have hVs : Surjective V.hom := ⟨fun s => ⟨⟨y, hy⟩, Subsingleton.elim _ _⟩⟩
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hF := GlobalTheory.Mum.FlatMul.main _ _ V j hj hflat
  have hS := GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ V j hj hVs
    (fun K _ t => GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ _ hH K t)
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)).left := Flat.epi_of_flat_of_surjective _
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)) := Over.epi_of_epi_left _
  have hjx : j ≫ x = j ≫ x' := Over.OverMorphism.ext hW
  rw [← cancel_epi ((fst V V ≫ j) * (snd V V ≫ j)), MonObj.mul_comp, MonObj.mul_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, hjx]

end GlobalTheory.MumAgree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.NormLam

theorem lbIso_cubeLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

theorem lbIso_lam_adj_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP
  have hwh := oG.hom w
  have hwh' := oG.hom (star w)
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a
  have hc := fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) =
      fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x) :=
    fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G),
      GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y =
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y) :=
    fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _
      ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))
    rw [hq]
    exact GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have hN := cubeLB_isLB' ![𝟙 G, oG.act w] hM
  have hPL := P.L.isLB
  have cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB := fun x => cubeLB_isLB' x hPL
  have cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB :=
    fun x => cubeLB_isLB' x hN
  have cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB := fun x => cubeLB_isLB' x hM

  have isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L) :=
    fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)
  refine ⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩
  · exact LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _)
      (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)
  · exact LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm
      (lbIso_cubeLB' _ hP).symm)

end GlobalTheory.Mum.NormLam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DDataGens

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) →
    ∃ τ₀ : GlobalTheory.UChart.Gens D, ∀ a b, (τ₀ a b).IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J := by
  intro R _ _ D hB hU
  choose t ht hc using fun y => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D y).1 (hU y)
  have key : ∀ a b, ∃ g : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), g.IsGen ∧
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val g (toUnit (TK R)).left z J = val (t (a + b)) (toUnit (TK R)).left z J *
          (val (t a) (toUnit (TK R)).left z J)⁻¹ * (val (t b) (toUnit (TK R)).left z J)⁻¹ *
          val (t 0) (toUnit (TK R)).left z J := by
    intro a b
    let T := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (t (a + b))
      (LB.invGen D.P.L _ _ (t a))) (LB.invGen D.P.L _ _ (t b))) (t 0)
    have hT : T.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ht _) (DVR.invGen_isGen _ _ _ _ (ht _)))
      (DVR.invGen_isGen _ _ _ _ (ht _))) (ht _)
    obtain ⟨g, hg, hv⟩ := exists_gen D.P.isLB
      (φ' := ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left]) (ε' := ![-1, 1, 1, -1])
      (by
        intro U _ h
        simp [Fintype.prod_sum_type, Fin.prod_univ_four]) T hT
    refine ⟨g, hg, fun z J hJ => ?_⟩
    rw [hv _ _ z J hJ]
    simp only [T, val_mul hJ, val_inv]
  choose τ₀ hτ hv using key
  refine ⟨τ₀, fun a b => ⟨hτ a b, fun z J hJ => ?_⟩⟩
  have hp : ∀ y, val (t y) (toUnit (TK R)).left z J = val (D.psi y) (𝟙 _) z J := fun y => by
    rw [← val_corr hJ (hc y) (𝟙 _), val_pull hJ, Category.id_comp, toUnit_TK_left]
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, toUnit_TK_left]
  rw [hv a b z J hJ, hp, hp, hp, hp, GlobalTheory.PsiZero.val_psi_zero hB hJ]
  simp only [DegPre.tau, val_mul hJ, val_inv, vρ]

end GlobalTheory.DDataGens
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChartNotAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem subsingleton_of_closed_mem_abLocus {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    (P : PELUnif (maximalIdeal R) t) (hc : (closedPoint R : Sp R) ∈ abLocus t.G) : Subsingleton P.D.toPre.X := by
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal R ^ (0 + 1) ≤ (closedPoint R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick R (maximalIdeal R) 0 q ∈ abLocus t.G := by
    rw [← hq] at hc; exact hc
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom

end GlobalTheory.ChartNotAb


open GlobalTheory.ChartNotAb in
theorem GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hT hm hc
  obtain ⟨-, -, -, -, -, ⟨N, s, ε, τ₀, -, hε, -, -⟩, -⟩ := hT
  have hs := subsingleton_of_closed_mem_abLocus C.P hc
  let i : Fin C.m := ⟨0, hm⟩
  apply ε.ne_zero (Sum.inl i)
  apply Subtype.ext
  rw [Submodule.coe_zero, hε i]
  ext x y
  rw [Subsingleton.elim x 0]
  simp
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ z ∈ Z, D.EF x z = 0}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro x y hx hy z hz
    show D.EF (x + y) z = 0
    rw [map_add (f := _), LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  smul_mem' := by
    intro a x hx z hz
    show D.EF (a • x) z = 0
    rw [D.adj]
    exact hx _ (Z.smul_mem _ hz)

def IsIsoSat (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ ∀ (n : ℕ) (x : D.La), n ≠ 0 → n • x ∈ Z → x ∈ Z

def IsLower (D D' : Datum H) (Z : Submodule (𝓞 E) D.La) (f : perp D Z →ₗ[𝓞 E] D'.La) : Prop :=
  Function.Surjective f ∧ (∀ x, f x = 0 ↔ (x : D.La) ∈ Z) ∧ ∀ x y, D'.EF (f x) (f y) = D.EF x y

def lowLevel (l : Level H) : Level H :=
  { l with A := l.M', A_pos := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos }

theorem ka_le (l : Level H) (c : Coeff l) : KA (lowLevel l) ≤ c.F := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact c.zeta_mem

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def lowS (C : UChart.Fam Xo c R) : Sp R ⟶ Sp (KA (lowLevel l)) :=
  spMap (C.b.comp (IntermediateField.inclusion (ka_le l c)).toRingHom)

def toF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : c.F →+* F :=
  (algebraMap (FractionRing R) F).comp ((algebraMap R (FractionRing R)).comp C.b)

def XFLevel (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ((I.ζ l.M' : Fˣ) : F) = toF C F ⟨zeta l.M', c.zeta_mem⟩ ∧
  ∀ (k : ℕ) (a : Dw.La) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
    ((k = l.A ∧ σ = Xo.univ.etaA a) ∨
      (k = l.M ∧ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) ∧ σ = Xo.univ.eta a)) →
    ∀ x : TFK (R := R) F ⟶ C.P.A.A, C.P.ToA F k (I.ev k a) x →
      ∃ g : Sp F ⟶ tK.G.left, g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) ∧
        g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ σ.left

def FiltGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ∀ n, 0 < n → ∀ a, (∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0) ↔
    ∃ b ∈ perp Dw Z, ∃ e, a = b + n • e

abbrev LowTate (C : UChart.Fam Xo c R) (D' : Datum H) (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C))
    (F : Type) [Field F] [Algebra (FractionRing R) F] :=
  TateIso D' F (Over.mk (jFK (R := R) F ≫ jK R) ⟶ o'.t.G) (fun a g => g ≫ o'.t.act.act a)
    (fun n g g' z => Out.WeilIs o'.t.G o'.t.PP.L n g g' (unitOn z))

def LowGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C)) (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) (I' : LowTate C D' o' F) : Prop :=
  (∀ n, I'.ζ n = I.ζ n) ∧
  (∀ w, toUnit _ ≫ o'.etaA w = I'.ev (lowLevel l).A w) ∧
  (∀ w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), toUnit _ ≫ o'.eta w = I'.ev l.M w) ∧
  ∀ n, 0 < n → ∀ a : perp Dw Z, ∃ q : QkPt C.P.D.toPre F n,
    QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0 ∧ q.g.b.left = (I'.ev n (f a)).left ≫ φB

end GlobalTheory.LowDat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorSym

open GlobalTheory.CechPic GlobalTheory.EndRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def genι (G : Over (Sp R)) : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

theorem lam_push (U : UnifPre I D A G) {T : Over (Sp (FractionRing R))} (x y : T ⟶ (Over.pullback (jK R)).obj G) :
    @id (Pic T.left) (lam (T := (Over.map (jK R)).obj T) (cls _ U.LG.isLB) (push (genι G) x) (push (genι G) y)) =
      lam (cls _ A.isLB) (x ≫ U.gen.hom) (y ≫ U.gen.hom) := by
  have := U.gen_hom
  have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
  rw [cls_pull A.isLB, cls_pull U.LG.isLB] at e
  have hm : ∀ x y : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) (x * y) = push (genι G) x * push (genι G) y :=
    fun x y => push_mul (genι G) (𝟙 _) (Category.id_comp _).symm x y
  have h1 : push (genι G) (1 : T ⟶ (Over.pullback (jK R)).obj G) = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hp : ∀ x : T ⟶ (Over.pullback (jK R)).obj G,
      @id (Pic T.left) (pull (push (genι G) x).left (cls _ U.LG.isLB)) =
        pull x.left (pull U.gen.hom.left (cls _ A.isLB)) := fun x => by
    rw [e, ← pull_comp]; rfl
  rw [← lam_pull U.gen.hom, lam, lam, ← hm, ← h1, ← hp, ← hp, ← hp, ← hp]
  rfl

theorem lam_act (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.OAct O}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) {T : Over (Sp (FractionRing R))}
    (x y : (Over.map (jK R)).obj T ⟶ G) :
    lam (cls _ U.LG.isLB) (x ≫ oG.act a) y = lam (cls _ U.LG.isLB) x (y ≫ oG.act (star a)) := by
  have sj : ∀ x : (Over.map (jK R)).obj T ⟶ G, ∃ x' : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) x' = x :=
    fun x => ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨x, rfl⟩ := sj x
  obtain ⟨y, rfl⟩ := sj y
  have e' : ∀ f : G ⟶ G, push (genι G) ((Over.pullback (jK R)).map f) = genι G ≫ f := fun f =>
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  rw [← push_comp _ (e' _), ← push_comp _ (e' _)]
  refine (lam_push U _ _).trans (Eq.trans ?_ (lam_push U _ _).symm)
  obtain ⟨t, ht⟩ := GlobalTheory.RosatiDescent.exists_gen_of_rosatiAdj (oA.rosati a)
  have := cls_of_rosati A.isLB t ht (x ≫ U.gen.hom) (y ≫ U.gen.hom)
  rw [Category.assoc, Category.assoc, h.ext, h.ext, ← Category.assoc, ← Category.assoc, lam, lam, this]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F hF A' G' _ _ _ U' oA oG hlin G _ _ _ inc pr _ _ hip hpi κ₀ hκ
  have hs : oG.act (star F.e * F.f * F.e) = oG.act (star F.e * star F.f * F.e) :=
    congrArg oG.act hF.2.1
  have hi : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  let GK := (Over.pullback (jK R)).obj G
  have hL := U'.LG.isLB
  have sy : ∀ x y : (Over.map (jK R)).obj (G2 GK) ⟶ G,
      lam (cls _ hL) (x ≫ inc) (y ≫ inc ≫ oG.act F.f) = lam (cls _ hL) (y ≫ inc) (x ≫ inc ≫ oG.act F.f) := fun x y => by
    have e₁ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act F.f)
    have e₂ := lam_act U'.toUnifPre hlin F.f (x ≫ inc) (y ≫ inc)
    have e₃ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act (star F.f))
    have e₄ : inc ≫ oG.act F.f ≫ oG.act (star F.e) = inc ≫ oG.act (star F.f) ≫ oG.act (star F.e) := by
      have := congrArg (inc ≫ ·) hs
      simpa only [oG.map_mul, reassoc_of% hi] using this
    simp only [Category.assoc, hi] at e₁ e₂ e₃
    rw [e₁, e₄, ← e₃, ← e₂, lam_comm]
  have hP := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hL)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  refine (gen_iff_sum (pull_isLB hP κ₀) _ _).2 ?_
  rw [cls_pull hP, GlobalTheory.FullSiegel.cls_lam_pull hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← pull_comp]
  let X : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (fst GK GK)
  let Y : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (snd GK GK)
  have k₁ : κ₀ = (lift X Y).left := by
    refine pullback.hom_ext (hκ.1.trans ?_) (hκ.2.trans ?_)
    · exact (congrArg (·.left) (lift_fst X Y)).symm
    · exact (congrArg (·.left) (lift_snd X Y)).symm
  have k₂ : (lift (snd GK GK) (fst GK GK)).left ≫ κ₀ = (lift Y X).left := by
    rw [k₁]; exact lift_push (genι G) _ _
  have p₁ := pull_lam (lift X Y) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  have p₂ := pull_lam (lift Y X) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  rw [lift_fst_assoc, lift_snd_assoc] at p₁ p₂
  rw [← k₁] at p₁
  rw [← k₂] at p₂
  exact add_neg_eq_zero.2 (p₂.trans ((sy Y X).trans p₁.symm))

end GlobalTheory.Mum.FactorSym
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def SecTw {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))} {N : ℕ}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : Prop :=
  ∀ (Z : Scheme.{0}) (p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left),
    p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left →
    p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom →
    ∀ z J, Good A.L z J → sval t' p z J = sval t p' z J
end GlobalTheory.Mum
end
