module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.PureWt

theorem cf_diag {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
    {f : A →+* R} {m : Multiplicative X →* R}
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (σ : R →+ R) (κ : X → A)
    (hσ : ∀ b ψ, σ (f b * m (Multiplicative.ofAdd ψ)) = f (κ ψ) * (f b * m (Multiplicative.ofAdd ψ)))
    (χ : X) (s : R) : WtPart.cf hb χ (σ s) = κ χ * WtPart.cf hb χ s := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, WtPart.cf_zero, mul_zero]
  | add x y hx hy => simp only [map_add (f := _), WtPart.cf_add, mul_add, hx, hy]
  | single ψ b =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, hσ, ← _root_.mul_assoc, ← map_mul, WtPart.cf_mono,
      WtPart.cf_mono]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

theorem exists_char_ne {k X K : Type} [Field k] [Infinite k] [AddCommGroup X] (b : Module.Basis K ℤ X)
    {χ α : X} (h : χ ≠ α) :
    ∃ t : Multiplicative X →* kˣ, t (Multiplicative.ofAdd χ) ≠ t (Multiplicative.ofAdd α) := by
  obtain ⟨i, hi⟩ : ∃ i, b.repr χ i ≠ b.repr α i := by
    by_contra hn
    push Not at hn
    exact h (b.repr.injective (Finsupp.ext hn))
  have hn : (b.repr χ i - b.repr α i).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 hi)
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x ^ (b.repr χ i - b.repr α i).natAbs ≠ 1 := by
    by_contra hc
    push Not at hc
    generalize (b.repr χ i - b.repr α i).natAbs = n at hn hc
    have : NeZero n := ⟨hn⟩
    have : Finite kˣ := Finite.of_surjective (fun x : rootsOfUnity n k => (x : kˣ))
      fun x => ⟨⟨x, (mem_rootsOfUnity n x).2 (hc x)⟩, rfl⟩
    have : Finite k := Finite.of_surjective (fun x : Option kˣ => x.elim (0 : k) Units.val) fun x => by
      by_cases hx : x = 0
      · exact ⟨none, hx.symm⟩
      · exact ⟨some (Units.mk0 x hx), rfl⟩
    exact not_finite k
  refine ⟨(zpowersHom kˣ x).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom), fun e => hx ?_⟩
  have e' : x ^ (b.repr χ i) = x ^ (b.repr α i) := e
  rw [pow_natAbs_eq_one, zpow_sub, e', mul_inv_cancel]

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

theorem translate_mem {Z : Over S} (τ : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (V : E.B.left.Opens) (z : Z.left)
    (hz : g.left z ∈ D.q.left ⁻¹ᵁ V) : ((τ ≫ D.i) * g).left z ∈ D.q.left ⁻¹ᵁ V :=
  haveI := D.q_hom
  GtBaseChange.translate_mem D.q D.i D.isKernel τ g V z hz

theorem gm_points {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd χ)) =
      gm τ.left z ⊤ (charUnit S X χ) := by
  apply Units.ext
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial, splitTorusPointsEquiv_val]
  rfl

theorem hasWt_mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) (c : Γ(E.B.left, V)) (χ : E.X) :
    UFib.HasWt D.i (D.q.left ⁻¹ᵁ V)
      ((D.q.left.app V).hom c * WtPart.mono D j V h (Multiplicative.ofAdd χ)) χ := by
  intro Z τ g z hz
  have hz' := translate_mem D τ g V z hz
  set v := AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom with hv
  let A : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ := (gm ((τ ≫ D.i) * g).left z _).comp v
  let C : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ :=
    (gm (𝟙 Z.left) z ⊤).comp (splitTorusPointsEquiv S E.X Z τ) * (gm g.left z _).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k) := by
      simp [hv]
    refine congrArg Additive.ofMul ?_
    change gm _ z _ (v (Multiplicative.ofAdd (E.basis k))) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))) *
        gm _ z _ (v (Multiplicative.ofAdd (E.basis k)))
    rw [hvk, gm_points, gm_res _ z _ hz, gm_res _ z _ hz']
    exact (GtBaseChange.hasWeight_iff D.i _ _ _ (D.act_le _) _).2 (D.equiv j k) Z τ g z (h hz)
  have e : gm ((τ ≫ D.i) * g).left z _ (v (Multiplicative.ofAdd χ)) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd χ)) *
        gm g.left z _ (v (Multiplicative.ofAdd χ)) :=
    congrArg (fun φ => Additive.toMul (φ χ)) hAC
  have em : WtPart.mono D j V h (Multiplicative.ofAdd χ) = (v (Multiplicative.ofAdd χ)).val := rfl
  rw [em, gs_mul _ z _ hz, gs_mul _ z _ hz', gs_unit _ z _ hz, gs_unit _ z _ hz', e, gm_points,
    gs_pull _ _ z V hz, gs_pull _ _ z V hz', TorusTranslate.translate_comp_q, Units.val_mul]
  ring

theorem translate_appLE (V : E.B.left.Opens) (τ : G ⟶ splitTorus S E.X)
    (hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (χ : E.X) (hs : UFib.HasWt D.i _ s χ) (a : Γ(S, ⊤))
    (ha : τ.left.appTop.hom (charUnit S E.X χ).val = G.hom.appTop.hom a) :
    (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s =
      (D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a) * s := by
  refine fn_ext fun z hz => ?_
  have e := hs G τ (𝟙 G) z hz
  have e₁ : gs (𝟙 G.left) z _ ((((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s) =
      gs ((τ ≫ D.i) * 𝟙 G).left z _ s :=
    (gs_res (𝟙 G.left) z hle hz _).trans ((gs_pull (𝟙 G.left) ((τ ≫ D.i) * 𝟙 G).left z (D.q.left ⁻¹ᵁ V) (hle hz) s).trans (by rw [Category.id_comp]))
  have e₂ : gs (𝟙 G.left) z _ ((D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a)) =
      gs G.hom z ⊤ a := by
    refine (gs_pull (𝟙 G.left) _ z V hz _).trans ((gs_res (𝟙 G.left ≫ D.q.left) z (U := E.B.hom ⁻¹ᵁ ⊤) le_top hz _).trans
      ((gs_pull _ E.B.hom z ⊤ trivial a).trans ?_))
    rw [Category.id_comp, Over.w]
  rw [e₁, e, gs_mul (𝟙 G.left) z (D.q.left ⁻¹ᵁ V) hz, e₂, gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  exact congrArg₂ (· * ·) (congrArg (G.left.presheaf.germ ⊤ z trivial).hom ha) rfl

theorem hasWt_iff_weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  intro k _ _ E G _ D j V hV h f α
  have hb := D.coord j V hV h
  constructor
  · intro hf χ hχ
    obtain ⟨t, ht⟩ := exists_char_ne (k := k) E.basis hχ
    let c : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    let e := splitTorusPointsEquiv (Sp k) E.X G
    let τ := e.symm ((Units.map (G.hom.appTop.hom.comp c).toMonoidHom).comp t)
    have hτ : ∀ ψ, τ.left.appTop.hom (charUnit (Sp k) E.X ψ).val =
        G.hom.appTop.hom (c (t (Multiplicative.ofAdd ψ))) := fun ψ => by
      rw [← splitTorusPointsEquiv_val]
      change (e (e.symm _) _).val = _
      rw [e.apply_symm_apply]
      rfl
    have hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) :=
      fun z hz => translate_mem D τ (𝟙 G) V z hz
    let κ : k →+* Γ(E.B.left, V) := (E.B.hom.appLE ⊤ V le_top).hom.comp c
    have e₁ := cf_diag hb (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom.toAddMonoidHom
      (fun ψ => κ (t (Multiplicative.ofAdd ψ)))
      (fun b ψ => translate_appLE D V τ hle _ ψ (hasWt_mono D j V h b ψ) _ (hτ ψ)) χ f
    have e₂ := cf_diag hb (AddMonoidHom.mulLeft ((D.q.left.app V).hom (κ (t (Multiplicative.ofAdd α)))))
      (fun _ => κ (t (Multiplicative.ofAdd α))) (fun _ _ => rfl) χ f
    have e₃ := e₁.symm.trans ((congrArg (WtPart.cf hb χ) (translate_appLE D V τ hle f α hf _ (hτ α))).trans e₂)
    rw [← sub_eq_zero, ← sub_mul, ← map_sub] at e₃
    exact ((IsUnit.mk0 _ (sub_ne_zero.2 fun e => ht (Units.ext e))).map κ).mul_right_eq_zero.1 e₃
  · intro hf
    have e : f = (D.q.left.app V).hom (WtPart.cf hb α f) * WtPart.mono D j V h (Multiplicative.ofAdd α) := by
      refine WtPart.cf_ext hb fun χ => ?_
      rw [WtPart.cf_mono]
      split_ifs with hχ
      · rw [hχ]
      · exact hf χ fun e => hχ e.symm
    rw [e]
    exact hasWt_mono D j V h _ α

end GlobalTheory.ZH.PureWt
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valF_appLE {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f)
    {U : M.Z.Opens} {V : M'.Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : (V : Set M'.Z).Nonempty) (g : Γ(M.Z, U)) :
    M'.res V hV ((f.appLE U V e).hom g) = φ (valF M.pt U g) := by
  rw [res_apply, ← hf.valF_app ⟨_, e hV.some_mem⟩ g]
  exact (valR_appLE M'.pt f e (M'.top_le_preimage_pt hV) g).trans (valR_comp M'.pt f U g)

theorem crd_mulVec_of_hasVal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  intro o Ω _ _ _ M Ω' _ _ φ N N' a q W H d J _ st σ t u c ha hq hW ht hu htu R _ x w hx
  obtain ⟨k, e, hk, hw⟩ := hx
  have ea : (H.pull a).U k ≤ a ⁻¹ᵁ H.U (k PUnit.unit) := LB.wchart_le H _ k PUnit.unit
  have eq : (H.pull a).U k ≤ q ⁻¹ᵁ W := fun z _ => hW z
  refine ⟨k PUnit.unit, e, le_preimage_comp x a ea hk, fun i => ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hC : (((H.pull a).U k : N'.Z.Opens) : Set N'.Z).Nonempty := ⟨x y, hk (x := y) trivial⟩
  have key : (a.appLE _ _ ea).hom ((st i).f (k PUnit.unit)) =
      ∑ j, (q.appLE _ _ eq).hom (c i j) * (σ j).f k := by
    apply N'.res_injective _ hC

    rw [map_sum, ha.valF_appLE ea hC, ht i _ ⟨_, ea hC.some_mem⟩, htu]
    simp only [map_mul, hq.valF_appLE eq hC, AlgHom.id_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_apply, hu j k hC, mul_div_assoc]

  rw [← valR_appLE x a ea hk, key, valR_eq x _ hk, map_sum, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← valR_eq x _ hk, ← valR_eq x _ hk, valR_appLE x q eq hk, hw j, mul_left_comm]

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valR_mem_image_ringOn {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {N : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {Y : Scheme.{0}} {j : Y ⟶ M.Z} [IsOpenImmersion j]
    {b : N.Z ⟶ Y} (h : M.IsHom N φ (b ≫ j)) {V : Y.Opens} (hV : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V) (g : Γ(Y, V)) :
    valR (N.pt ≫ b) V g ∈ φ '' (M.ringOn (j ''ᵁ V : M.Z.Opens) : Set Ω) := by
  have hne : ((j ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨_, _, hV (x := IsLocalRing.closedPoint Ω') trivial, rfl⟩
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  refine ⟨valF M.pt _ ((j.appIso V).inv.hom g), (mem_ringOn_iff_exists hne).2 ⟨_, rfl⟩, ?_⟩
  refine (valR_spMap_comp φ.toRingHom M.pt _ (M.top_le_preimage_pt hne) _).symm.trans ?_
  rw [← show N.pt ≫ b ≫ j = spMap φ.toRingHom ≫ M.pt from h, ← Category.assoc, ← valR_appLE _ j hle hV,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res _ le_rfl hV g

theorem projChart_of_isPullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  intro o Ω _ _ _ M Ω' _ _ φ N U₀ R _ X p u₀ a b H J s t sq hom imm crd hdiv W hWU hW hne
  obtain ⟨V, rfl⟩ : ∃ V : U₀.toScheme.Opens, U₀.ι ''ᵁ V = W :=
    ⟨U₀.ι ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hWU⟩
  have hV : IsAffineOpen V := U₀.ι.isAffineOpen_iff_of_isOpenImmersion.1 hW
  have hmem : ∀ z : N.Z, (b ≫ U₀.ι) z ∈ U₀.ι ''ᵁ V ↔ b z ∈ V := fun z =>
    Iff.of_eq (congrArg (b z ∈ ·) (U₀.ι.preimage_image_eq V))
  refine ⟨fun z _ => ?_, fun i hi => ?_⟩
  · have hz : a z ∈ ⨆ i ∈ (Set.univ : Set J), nonzeroLocus (s i) := by rw [imm.1]; trivial
    simp only [Set.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (hdiv i z).2 hi⟩
  obtain ⟨hD, r, hr, hgen⟩ := imm.2 i trivial
  have hU : IsAffineOpen (a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V) := by
    have : IsAffine _ := isAffineOpen_top (Sp R)
    have : IsAffine _ := hV
    have : IsAffine _ := hD
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top
      rfl).isoPullback.hom
  have hset : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z) =
      {z' | (b ≫ U₀.ι) z' ∈ U₀.ι ''ᵁ V ∧ N.Div t i z'} :=
    Set.ext fun z => and_comm.trans (and_congr (hmem z).symm (hdiv i z).symm)
  refine ⟨_, hU, hset, le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)⟩
  · have hgp : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀.ι ''ᵁ V := by
      have e := congrArg (fun f => f (IsLocalRing.closedPoint Ω')) (show N.pt ≫ b ≫ U₀.ι = _ from hom)
      rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
      refine (congrArg (· ∈ U₀.ι ''ᵁ V) e).mpr ?_
      exact M.top_le_preimage_pt hne (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    have hUne : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z).Nonempty :=
      ⟨_, hset.ge ⟨hgp, div_genericPoint hi⟩⟩
    have hpt := N.top_le_preimage_pt hUne
    have ha : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s i) := le_preimage_comp _ a inf_le_left hpt
    have hb : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V := le_preimage_comp _ b inf_le_right hpt
    set A := Algebra.adjoin o (φ '' (M.ringOn (U₀.ι ''ᵁ V : M.Z.Opens) : Set Ω) ∪ Set.range fun j => t j / t i)
    have hB : ∀ g, valR (N.pt ≫ b) V g ∈ A := fun g =>
      Algebra.subset_adjoin (Or.inl (hom.valR_mem_image_ringOn hb g))
    have hA : ∀ g, valR (N.pt ≫ a) (nonzeroLocus (s i)) g ∈ A := fun g => by
      have : Subring.closure (Set.range (constFn p (nonzeroLocus (s i))) ∪ Set.range r) ≤
          A.toSubring.comap (valMap _ _ ha).hom := by
        rw [Subring.closure_le]
        rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, valR_constFn _ _ _ ha, Category.assoc, sq.w, ← Category.assoc, ← valR_constFn _ _ _ hb]
          exact hB _
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, eq_div_of_mul_eq hi (CrdCalc.crd_ratio crd (hr j) ha).symm]
          exact Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      rw [valR_eq _ _ ha]
      exact this (hgen.ge (Subring.mem_top g))
    have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top rfl).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hD)
    have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
    have hle : (⊤ : Subring _) ≤ A.toSubring.comap (valMap _ _ hpt).hom := by
      rw [← hcl, Subring.closure_le]
      rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hA g
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hB g
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
    rw [valF_eq_valR, valR_eq _ _ hpt]
    exact hle (Subring.mem_top f)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hom.map_mem_O (mem_ringOn.1 hx _ (hset.le hz).1)
    · exact mem_ringOn.2 fun z hz => (hset.le hz).2.2 j

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem IsHom.apply_genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (h : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  have e : (N.pt ≫ q) (IsLocalRing.closedPoint Ω') =
      (spMap φ.toRingHom ≫ M.pt) (IsLocalRing.closedPoint Ω') := by
    rw [show N.pt ≫ q = _ from h]
  have e' : q (N.pt (IsLocalRing.closedPoint Ω')) = M.pt (spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) := e
  rw [e']
  exact M.top_le_preimage_pt hW (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial

theorem IsHom.comp_id {N Q : RatModel o Ω'} {q : N.Z ⟶ M.Z} {a : Q.Z ⟶ N.Z} (h : M.IsHom N φ q)
    (ha : N.IsHom Q (AlgHom.id o Ω') a) : M.IsHom Q φ (a ≫ q) := by
  simpa only [AlgHom.id_comp] using h.comp ha

theorem exists_isHom_of_projChart {N₁ N₂ : RatModel o Ω'} {q₁ : N₁.Z ⟶ M.Z} {q₂ : N₂.Z ⟶ M.Z}
    (h₁ : M.IsHom N₁ φ q₁) (h₂ : M.IsHom N₂ φ q₂) {J : Type} [Finite J] {t : J → Ω'}
    (h : ∀ z, ∃ (W : M.Z.Opens) (i : J), q₁ z ∈ W ∧ N₁.Div t i z ∧ M.ProjChart N₂ φ q₂ W t) :
    ∃ a, N₂.IsHom N₁ (AlgHom.id o Ω') a := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨W, i, hz, hi, hc⟩ := h z
  obtain ⟨U, hU, hD, hR⟩ := hc.2 i hi.1
  refine ⟨q₁ ⁻¹ᵁ W ⊓ ⟨_, N₁.isOpen_setOf_div t i⟩, U, ⟨hz, hi⟩, hU,
    ⟨genericPoint N₂.Z, hD ▸ ⟨h₂.apply_genericPoint_mem ⟨_, hz⟩, div_genericPoint hi.1⟩⟩,
    fun x hx => mem_ringOn.2 fun w hw => ?_⟩
  rw [hR] at hx
  refine (Algebra.adjoin_le ?_ : _ ≤ N₁.O w) hx
  rintro _ (⟨y, hy, rfl⟩ | ⟨j, rfl⟩)
  · exact h₁.map_mem_O (ringOn_le_O (M := M) (U := W) (z := q₁ w) hw.1 hy)
  · exact hw.2.2 j

theorem exists_isPullback_of_projChart_of_isPullback {N P Q : RatModel o Ω'} {U₀ : M.Z.Opens} {b : N.Z ⟶ U₀.toScheme}
    {f : P.Z ⟶ M.Z} {ι : Q.Z ⟶ P.Z} [IsOpenImmersion ι] {g : Q.Z ⟶ U₀.toScheme} (hι : P.IsHom Q (AlgHom.id o Ω') ι)
    (hpb : IsPullback ι g f U₀.ι) {J : Type} [Finite J] {t : J → Ω'} (hb : M.IsHom N φ (b ≫ U₀.ι))
    (hf : M.IsHom P φ f)
    (h : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty →
      M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) :
    ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  have hU : ∀ {X : Scheme.{0}} (b : X ⟶ U₀.toScheme) (z : X), (b ≫ U₀.ι) z ∈ U₀ := fun b z => by
    rw [Scheme.Hom.comp_apply]
    exact (b z).2
  obtain ⟨a₀, ha₀⟩ : ∃ a, P.IsHom N (AlgHom.id o Ω') a := by
    refine exists_isHom_of_projChart hb hf (t := t) fun z => ?_
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (hU b z)
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h1.1 z hz
    exact ⟨W, i, hz, hi, h2⟩
  have hfι : M.IsHom Q φ (ι ≫ f) := hf.comp_id hι
  obtain ⟨c, hc⟩ : ∃ c, N.IsHom Q (AlgHom.id o Ω') c := by
    refine exists_isHom_of_projChart hfι hb (t := t) fun z => ?_
    have hz0 : (ι ≫ f) z ∈ U₀ := hpb.w ▸ hU g z
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hz0
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h2.1 (ι z) (by rwa [Scheme.Hom.comp_apply] at hz)
    refine ⟨W, i, hz, ⟨hi.1, fun j => ?_⟩, h1⟩
    rw [hι.O_eq z]
    exact hi.2 j
  have hw : a₀ ≫ f = b ≫ U₀.ι := IsHom.unique (φ := φ) (hf.comp_id ha₀) hb
  obtain ⟨a₁, e₁, e₂⟩ : ∃ a₁ : N.Z ⟶ Q.Z, a₁ ≫ ι = a₀ ∧ a₁ ≫ g = b :=
    ⟨hpb.lift a₀ b hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have ha₁ : Q.IsHom N (AlgHom.id o Ω') a₁ := by
    unfold IsHom at hι ha₀ ⊢
    have e : spMap (AlgHom.id o Ω').toRingHom = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp] at hι ha₀ ⊢
    rw [← cancel_mono ι, Category.assoc, e₁, hι, ha₀]
  have h₁ : a₁ ≫ c = 𝟙 N.Z := IsHom.unique (φ := AlgHom.id o Ω') (hc.comp_id ha₁) N.isHom_id
  have h₂ : c ≫ a₁ = 𝟙 Q.Z := IsHom.unique (φ := AlgHom.id o Ω') (ha₁.comp_id hc) Q.isHom_id
  have : IsIso a₁ := ⟨c, h₁, h₂⟩
  refine ⟨a₀, ha₀, ?_⟩
  exact hpb.of_iso (asIso a₁).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← e₁]) (by simp [← e₂]) (by simp) (by simp)

theorem exists_isPullback_of_projChart :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  intro o Ω _ _ _ M Ω' _ _ φ _ N P U₀ b f J _ t hb hf h
  have hbU : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀ := by
    rw [Scheme.Hom.comp_apply]
    exact (b _).2
  have hV : ((f ⁻¹ᵁ U₀ : P.Z.Opens) : Set P.Z).Nonempty := ⟨_, hf.apply_genericPoint_mem ⟨_, hbU⟩⟩
  exact @exists_isPullback_of_projChart_of_isPullback o Ω _ _ _ M Ω' _ _ φ N P (P.openPart _ hV) U₀ b f
    (f ⁻¹ᵁ U₀).ι (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U₀).ι)) (f ∣_ U₀) (P.isHom_openPart _ hV)
    (isPullback_morphismRestrict f U₀).flip J _ t hb hf h

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_complete_dvr_integral_closure_finite : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (Sp K)) [GrpObj A] Q, PotModel W L ((Over.pullback (spMap (algebraMap K L))).obj A) Q → PotModel V K A Q := by
  first | exact @GlobalTheory.SS.exists_complete_dvr_finite_extension | exact GlobalTheory.SS.exists_complete_dvr_finite_extension | (intros; apply GlobalTheory.SS.exists_complete_dvr_finite_extension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.closure_eq_ker_of_meets_torsion_cosets' : ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  first | exact @GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | exact GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | (intros; apply GlobalTheory.closure_eq_ker_of_meets_torsion_cosets <;> assumption)
end
