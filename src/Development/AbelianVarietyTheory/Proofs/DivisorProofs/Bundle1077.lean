module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

theorem _root_.GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  first | exact @GlobalTheory.LBDescent.exists_lb_of_invariant_frames | exact GlobalTheory.LBDescent.exists_lb_of_invariant_frames | (intros; apply GlobalTheory.LBDescent.exists_lb_of_invariant_frames <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open GlobalTheory.AbLaw GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem exists_not_NV_mix (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (d : ℤ) :
    ∃ N : ℕ, ∀ a b : ℕ, N ≤ a + b → (a : ℤ) - b = d → ∀ j : ℕ, ¬ NV A (mix A L a b) (j + 1) := by
  have := hA.proper
  letI := algebraΓOfHom A.hom
  have hLa : IsAmpleLB L := isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hι : IsIso (GrpObj.inv : A ⟶ A) := ⟨⟨GrpObj.inv, by simp, by simp⟩⟩
  have : IsIso (GrpObj.inv : A ⟶ A).left := (Over.forget _).map_isIso GrpObj.inv
  have hinv : IsAmpleLB (L.pull (GrpObj.inv : A ⟶ A).left) := hLa.pull_of_isAffineHom _
  have hM : (mix A L 1 1).IsLB := LB.isLB_linComb hL _ _
  have hMa : IsAmpleLB (mix A L 1 1) := by
    refine hLa.tensor hinv hM ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hM hL) (LB.isLB_pull hL _))).1 ?_)
    unfold mix at hM ⊢
    rw [cls_div (LB.isLB_div hM hL) (LB.isLB_pull hL _), cls_div hM hL, cls_pull hL,
      cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul]
    abel
  have hP : (mix A L d 0).IsLB := LB.isLB_linComb hL _ _
  have hF := Twist.isFiniteQC_twist (F := structureModule A.left) hP
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hMa.eventually_subsingleton_coh_twistZ (f := A.hom) (fun _ => rfl) (twist (structureModule A.left) (mix A L d 0)))
  have hsep : A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
    infer_instance
  refine ⟨(2 * n₀ + d).toNat, fun a b hN hd j ⟨κ, _, _, W, hW, hc, hne⟩ => hne ?_⟩
  have hI : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, W i) := fun s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hW i
  have hQ : (mix A L a b).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv A.hom hQ hc hI (j + 1)
  obtain ⟨e₂⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule A.left) hP
    (Twist.isLB_lbZPow hM b) hQ (by
      rw [cls_lbZPow hM]
      unfold mix at hP hQ hM ⊢
      rw [cls_linComb hL, cls_linComb hL, cls_linComb hL]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul, zero_smul, add_zero]
      have ha : (a : ℤ) = d + b := by omega
      rw [ha, add_smul, smul_add]
      abel)
  haveI := hn₀ b (by omega) (j + 1) j.succ_pos
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  exact (e.trans (cohOn.mapIso K ⊤ (j + 1) e₂).symm).injective.subsingleton

end GlobalTheory.AmpleGen
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.PureLift GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.GrpTangent
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

theorem eq_epsScale_of_isLieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {c : Fin 1 → R}
    {v : Fin 1 → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb c v w) : w = epsScale (c 0) ≫ v 0 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : (List.ofFn u).prod = u 0 := by simp
  rw [h1]
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact hu 0

theorem push_sub_smul_mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : LieExact A)
    {v : Fin 1 → (epsR R ⟶ A)} (hv : IsLieBasis v) (W : A ⟶ A) [IsMonHom W] {s : Fin 1 → R}
    (e : IsLieComb s v (v 0 ≫ W)) (y : HdR A) : push (dp0 R) (𝟙 _) W y - s 0 • y ∈ Fil A := by
  obtain ⟨u, hu⟩ := (hA.1 y).exists
  obtain ⟨c, hc, -⟩ := hv.2 u hu.1
  have hu' : u = epsScale (c 0) ≫ v 0 := eq_epsScale_of_isLieComb hc
  have hW : v 0 ≫ W = epsScale (s 0) ≫ v 0 := eq_epsScale_of_isLieComb e
  have key : u ≫ W = epsScale (s 0) ≫ u := by
    rw [hu', Category.assoc, hW, epsScale_mul_assoc, epsScale_mul_assoc, mul_comm]
  have h1 := hu.push W
  rw [key] at h1
  exact h1.sub_mem (hu.smul (s 0))

theorem exists_isPolForm (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨hall, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨z, hz⟩ : ∃ z, IsChern (dp0 R) (A.hom ≫ 𝟙 (Sp R)) L z :=
    GlobalTheory.Cris.ChernExists.exists_isChern L hL
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hmem : ∀ x, x ∈ prim (dp0 R) (𝟙 (Sp R)) A := fun x => by
    rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hall]
    exact Submodule.mem_top
  refine ⟨_, n, fun k => ⟨a k, hmem _⟩, fun k => ⟨b k, hmem _⟩, ?_, rfl⟩
  have hz' : z = ∑ k, cup _ (a k) (b k) := by

    rw [← e.apply_symm_apply z, ← hab, map_sum]
    exact Finset.sum_congr rfl fun k _ => he _ _
  rw [hz'] at hz
  exact hz

private theorem pGen_pull_refl {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (F : Y ⟶ X) :
    PGen (⟨fun p => (L.pull F).g p.1 p.2⟩ : LB.Iso (L.pull F) (L.pull F)) := by
  intro Z f y j j' k k' h1 h2 h3 h4
  unfold gw
  dsimp only
  have e1 : (f ≫ F) y ∈ L.U j := h1
  have e2 : (f ≫ F) y ∈ L.U j' := h2
  have e3' : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 h3
  have e3 : (f ≫ F) y ∈ L.U (k PUnit.unit) := e3'
  have e4' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 h4
  have e4 : (f ≫ F) y ∈ L.U (k' PUnit.unit) := e4'
  rw [gm_pull_g L F f y (fun _ => j) k (mem_pull.2 h1) h3, gm_pull_g L F f y k k' h3 h4,
    gm_pull_g L F f y (fun _ => j') k' (mem_pull.2 h2) h4]
  have c1 := gm_cocycle hL (f ≫ F) y e1 e2 e4
  have c2 := gm_cocycle hL (f ≫ F) y e1 e4 e3
  have c3 := gm_cocycle hL (f ≫ F) y e3 e4 e3
  have c4 := gm_cocycle hL (f ≫ F) y e3 e3 e3
  have hkk : (gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit))) (L.g (k PUnit.unit) (k PUnit.unit)) = 1 := by
    have h := congrArg (· * ((gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit)))
      (L.g (k PUnit.unit) (k PUnit.unit)))⁻¹) c4
    simpa using h
  have hinv := eq_inv_of_mul_eq_one_right (c3.trans hkk)
  rw [← c2, ← c1, hinv, mul_right_comm]

theorem isPureBC_ell : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω),
    IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  intro hP E _ _ _ H S _ ω C
  unfold IsPureBC
  intro R _ f A _ φ hpb W' _ hW'

  haveI : IsCommMonObj A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb
  have hA : IsAbelianScheme A := by
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hpb.1 C.P.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hpb.1 C.P.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 C.P.isAb.geomConnected⟩
  have hgG : SmoothOfRelativeDimension 1 C.P.A.hom := by
    have h := C.P.smoothDim
    rw [C.dim] at h
    exact h
  have hgA : SmoothOfRelativeDimension 1 A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb.1 hgG
  have hLie : LieExact A := (hP.2.1 R A 1 hA hgA).1

  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange S R f C.P.A A φ hpb
    C.P.isAb.smooth 1 ![C.v] C.basis
  have e : IsLieComb (fun i => f (![ω] i)) v' (v' 0 ≫ W') := by
    apply (GlobalTheory.lieComb_baseChange S R f C.P.A A φ hpb 1 ![C.v]
      (C.v ≫ C.act.act (GlobalTheory.CM.wK H)) ![ω] v' (v' 0 ≫ W') hv'φ C.eig).1
    have hv0 : (v' 0).left ≫ φ = spMap (Chart.dualMapR f) ≫ C.v.left := hv'φ 0
    rw [Over.comp_left, Over.comp_left, Category.assoc, hW', ← Category.assoc, hv0, Category.assoc]
  have hquot : ∀ y : HdR A, push (dp0 R) (𝟙 _) W' y - f ω • y ∈ Fil A :=
    fun y => push_sub_smul_mem_Fil hLie hv' W' e y

  have hL' : (C.P.L.pull φ).IsLB := pull_isLB C.P.isLB φ
  obtain ⟨ψ, hψ⟩ := exists_isPolForm hP.1 hA hgA hL'
  obtain ⟨hiso, hperf⟩ := hP.2.2.2.2 R A 1 hA hgA (C.P.L.pull φ) hL' ψ hψ
  have hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A (C.P.L.pull φ) :=
    kTriv_pull hpb C.P.isLB hL' (pGen_pull_refl C.P.L C.P.isLB φ) C.P.ktriv
  haveI := hperf hK

  obtain ⟨o', ho'⟩ := GlobalTheory.CM.ellPull_exists_oAct hpb C.act
  haveI := o'.hom (GlobalTheory.CM.wK H)
  haveI := o'.hom (1 - GlobalTheory.CM.wK H)
  have hWo : o'.act (GlobalTheory.CM.wK H) = W' := by
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [ho', hW']
    · rw [Over.w, Over.w]

  have hb : ((1 - GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.bar ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) := by
    rw [show ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.w0 from rfl, GlobalTheory.CM.kform_bar_w0]
    push_cast
    rfl
  have HG : LBIso (cubeLB C.P.A ![fst C.P.A C.P.A ≫ C.act.act (GlobalTheory.CM.wK H), snd C.P.A C.P.A] C.P.L)
      (cubeLB C.P.A ![fst C.P.A C.P.A, snd C.P.A C.P.A ≫ C.act.act (1 - GlobalTheory.CM.wK H)] C.P.L) := by
    have h := C.adj (GlobalTheory.CM.wK H) (1 - GlobalTheory.CM.wK H) hb
    unfold GlobalTheory.CM.LamEq at h
    simpa only [Category.comp_id] using h
  have HA := GlobalTheory.PolAdjoint.lbIso_cube hpb C.P.L hW' (ho' (1 - GlobalTheory.CM.wK H)) HG
  have hadj : ∀ x y : HdR A, ψ (push (dp0 R) (𝟙 _) W' x) y =
      ψ x (push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y) :=
    GlobalTheory.PolAdjoint.adjoint_of_lbIso hP.1 hA hgA hL' hψ W' (o'.act (1 - GlobalTheory.CM.wK H)) HA
  have hpushb : ∀ y : HdR A, push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y = y - push (dp0 R) (𝟙 _) W' y := by
    intro y
    have h1 : GlobalTheory.DeRham.act (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H) = 1 - push (dp0 R) (𝟙 _) W' := by
      set_option synthInstance.maxHeartbeats 200000 in
       rw [map_sub, map_one, GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (GlobalTheory.CM.wK H),
        push_congr (dp0 R) (𝟙 _) hWo]
    rw [← GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H), h1]
    rfl

  have hfil : ∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W' x = f (1 - ω) • x := by
    intro x hx
    have hlie : ∀ y : HdR A, ψ x (push (dp0 R) (𝟙 _) W' y) = f ω * ψ x y := by
      intro y
      have h0 := hiso x hx _ (hquot y)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have key : ψ (push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x) = 0 := by
      ext y
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hadj, hpushb, map_sub, hlie, map_sub, map_one,
        smul_eq_mul, LinearMap.zero_apply]
      ring
    have hinj := (LinearMap.IsPerfPair.bijective_left ψ).1
    have h0 : push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x = 0 := hinj (by rw [key, map_zero])
    exact sub_eq_zero.mp h0
  exact ⟨hfil, hquot⟩

end GlobalTheory.PureLift
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace GlobalTheory.EndDivisible

theorem exists_relation_of_cls (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (hf : Smooth f)
    (hp : GlobalTheory.AbLaw.IsProjBy f) (c : Pic X) :
    ∃ n : ℕ, ∀ (B : LB X) (hB : B.IsLB), cls B hB = c → ∀ σ : Fin n → LB.Sec B,
      ∃ a : Fin n → K, a ≠ 0 ∧ ∀ i, ∑ k, GlobalTheory.AbLaw.cst f (B.U i) (a k) * (σ k).f i = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨Q⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy K X f hf hp M hM
  refine ⟨Q.a + 1, fun B hB hc σ => ?_⟩
  obtain ⟨w, hw⟩ := (cls_eq_iff hB hM).1 hc
  let e : LB.Sec B ≃ₗ[Γ(X, ⊤)] LB.Sec M :=
    (GlobalTheory.AbLaw.SecOn.topEquiv B).symm ≪≫ₗ GlobalTheory.AbLaw.SecOn.congr hB hM w hw ⊤ ≪≫ₗ GlobalTheory.AbLaw.SecOn.topEquiv M
  obtain ⟨a, ha, h⟩ := Q.exists_relation (fun k => e (σ k))
  let a' : Fin (Q.a + 1) → Γ(X, ⊤) := fun k =>
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a k))
  have ev : ∀ (N : LB X) (τ : Fin (Q.a + 1) → LB.Sec N) (i : N.ι),
      (∑ k, a' k • τ k).f i = ∑ k, GlobalTheory.AbLaw.cst f (N.U i) (a k) * (τ k).f i := fun N τ i => by
    let F : LB.Sec N →+ Γ(X, N.U i) := AddMonoidHom.mk' (fun s => s.f i) (fun _ _ => rfl)
    exact map_sum F _ _
  have h1 : ∑ k, a' k • e (σ k) = 0 :=
    GlobalTheory.AbLaw.HighTwist.sec_eq_zero _ fun i => (ev M _ i).trans (h i)
  have h2 : ∑ k, a' k • σ k = 0 := by
    apply e.injective

    rw [map_sum, map_zero, ← h1]
    exact Finset.sum_congr rfl fun k _ => e.map_smul _ _
  exact ⟨a, ha, fun i => (ev B σ i).symm.trans (by rw [h2]; rfl)⟩

theorem eff_nsmul_of_pos {X : Scheme.{0}} [IsIntegral X] (c : Pic X) (hc : GlobalTheory.EffBound.Eff c) (N : ℕ)
    (hN : 1 ≤ N) : GlobalTheory.EffBound.Eff (N • c) := by
  induction N, hN using Nat.le_induction with
  | base => rwa [one_nsmul]
  | succ n _ ih => rw [succ_nsmul]; exact GlobalTheory.EffBound.eff_add _ _ ih hc

theorem exists_pull_monomial {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (t : ℕ)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) (a : ℕ) (ha : a ≤ t) :
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => ((N * t : ℕ) : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) := by
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N) (fun _ => f ≫ w) (fun _ => 1)
      (fun _ : Unit => u) (fun _ => ((N * t : ℕ) : ℤ)) := by
    intro U _ h
    rw [hu]
    simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha, zpow_natCast]
    rw [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem constSt : ConstSt := by
  intro K _ _ A _ hA L hL hamp m
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]; infer_instance⟩
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
    exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL d, n, s, hs⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hamp ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := exists_relation_of_cls K A.left A.hom hA.smooth hproj (N • m)
  refine ⟨n, fun t hnt ψ hψ heff => ?_⟩
  obtain ⟨P, hP, hPc, ε, p₀, hε⟩ := eff_nsmul_of_pos _ heff N hN
  have hQ := LB.isLB_linComb hL (K := Unit) (fun _ => ψ.left) (fun _ => ((N * t : ℕ) : ℤ))
  have hT : cls _ (isLB_tens hP hQ) = N • m := by
    rw [cls_tens hP hQ, hPc, cls_linComb hL, Fintype.sum_unique, natCast_zsmul, nsmul_sub, mul_nsmul',
      sub_add_cancel]
  let w := (A.hom ⁻¹ᵁ ⊤).ι
  let f : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨z⟩ : Nonempty A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good L z J := by
    choose I hI using fun χ : A.left ⟶ A.left => exists_chart hL (χ z)
    exact ⟨I, hI⟩
  obtain ⟨p, hp⟩ := exists_chart hP z
  have hεz : gs (𝟙 _) z (P.U p) (ε.f p) ≠ 0 := by
    rw [gs_eq (𝟙 _) z (P.U p) hp]
    exact GlobalTheory.EffBound.germ_sec_ne_zero ε hε p z hp
  let κ := germPull A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    choose σ hσ using fun a : Fin n =>
      exists_pull_monomial L hL w N (s i) (s j) t f ψ.left hf.symm z J hJ a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn _ _ hT (fun a => GlobalTheory.EffBound.tensSec ε (σ a))
    have hm₂ := hJ.mem (K := Unit) (fun _ => ψ.left) (𝟙 _)
    have hm : (𝟙 A.left : A.left ⟶ A.left) z ∈ P.U p ⊓ LB.wchart L (K := Unit) (fun _ => ψ.left)
      (fun _ => J (𝟙 _ ≫ ψ.left)) := ⟨hp, hm₂⟩
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (p, fun _ => J (𝟙 _ ≫ ψ.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (c k) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ t * gs (𝟙 _) z (P.U p) (ε.f p)) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) A.hom z ⊤ _ le_top hm (E.symm (c k)))
        ((gs_mul (𝟙 _) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z inf_le_left hm _)
          ((gs_res (𝟙 _) z inf_le_right hm _).trans (hσ k))))).symm
      have e₁ : (κ.comp E.symm.toRingHom) (c k) = gs (𝟙 _ ≫ A.hom) z ⊤ (E.symm (c k)) := by
        rw [Category.id_comp]
        exact germPull_apply _ _ _ _ _
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) c hc (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero (hy.pow _).ne_zero hεz))
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have h2 : η[A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  apply Over.OverMorphism.ext
  rw [hp, ← h2, Hom.one_def]
  simp

end GlobalTheory.AmpleRigid
end
end
