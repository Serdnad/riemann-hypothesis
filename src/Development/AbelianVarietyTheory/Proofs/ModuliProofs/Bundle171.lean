module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFamily

theorem exists_isSharp_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  intro laws _ cube h g W J a bas hW hbas hunit k o _ b em S _ _ s t₀ hk hd₀
  obtain ⟨t, hd, back⟩ := GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices h g W J a bas k o b em S s t₀ hunit hd₀
  obtain ⟨rmul, radd, rone, rpt⟩ := GlobalTheory.T.dense_fromSet_sharpClass h g W _ _ bas k o b em S s t hd
  obtain ⟨adj, diag⟩ := GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers laws.globalFns cube h g W _ _ bas k o b em S s t hd
  letI := t.ab.comm
  let ρ : Matrix (Fin 8) (Fin 8) ℤ → (t.A ⟶ t.A) := fun m => t.act (Sum.inr m)
  obtain ⟨A, _, pr, hA, hpr, hprod, hρ⟩ := GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action S t.A ρ t.ab (fun m => t.hom _)
    (fun m m' => rmul (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl) (fun m m' => radd (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl)
    (rone (Sum.inr 1) rfl)
  letI := hA.comm
  obtain ⟨P, hP, r₁, r₂, hsym, hbi, hiso⟩ := GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower W S t.A A pr t.L ρ hW hpr hprod t.isLB
    (cube S t.pol t.L t.isLB) hρ (fun m m' e => adj (Sum.inr m) (Sum.inr m') e) (fun m e => diag (Sum.inr m) e)
  let pt : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := fun i => Over.homMk (t.pt i).left (Over.w (t.pt i))
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A) := fun x =>
    (∏ i, pt i ^ bas.symm (Pi.single 0 x) i) ≫ pr 0
  have hadd : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    have := hpr 0
    simp only [lev, Pi.single_add, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib, MonObj.mul_comp]
  have hpt : ∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left := fun i u => by
    have e₁ : ρ (Matrix.single 0 u 1) ≫ pr 0 = pr u := by
      rw [hρ, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.single_apply, eq_comm]
    have e₂ := rpt (Sum.inr (Matrix.single 0 u 1)) i
    have e₃ : (fun u' => ∑ v, (Sum.elim a id (Sum.inr (Matrix.single 0 u 1)) : Matrix (Fin 8) (Fin 8) ℤ) u' v •
        bas (Pi.single i 1) v) = Pi.single 0 (bas (Pi.single i 1) u) := by
      funext u'
      by_cases hu : u' = 0
      · subst hu
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hu, Ne.symm hu]
    rw [e₃, List.prod_ofFn] at e₂
    rw [← e₁, ← Category.assoc, e₂]
    rfl
  obtain ⟨htor, hgeo⟩ := GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme h g _ bas k o b S s t A pr lev hk.pos hpr hprod hadd hpt
  refine ⟨{ A := A, ab := hA, P := P, isLB := hP, rig₁ := r₁, rig₂ := r₂, symm := hsym, lev := lev, lev_add := hadd,
            lev_tors := htor, geom := fun K _ _ p β z hp hz => ⟨(hgeo K p).1, (hgeo K p).2, fun x y => ?_⟩ },
    ⟨GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form W S t.A A pr t.L P hW t.ab hA hpr hprod t.isLB hP hbi hiso t.ample,
      GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower W S t.A A pr t.L P hpr hprod t.isLB hP hsym hbi hiso t.ktriv⟩,
    back _ ⟨pr, hpr, hprod, hiso, fun j u => ?_, hpt⟩⟩
  · have e : unitOn (z ^ (2 * omegaStd x y)) = unitOn z ^ (2 * omegaStd x y) := map_zpow (Units.map _) _ _
    rw [e]
    exact GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form laws.globalFns h k W S t.A A pr t.L P K p (fun x => toUnit _ ≫ lev x) (unitOn z) hW t.ab hA
      hpr hprod t.isLB hP hsym hbi hiso (fun x y => by rw [hadd, MonObj.comp_mul])
      (fun x => by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
      (GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints laws h g W _ bas k o b S s t A pr lev hbas hpr hprod hadd hpt K p β z hp hz) x y
  · rw [rmul (Sum.inr (Sum.elim a id j)) (Sum.inr 1) j (_root_.mul_one _).symm, rone (Sum.inr 1) rfl, Category.id_comp]
    exact hρ _ u

end GlobalTheory.SharpFamily
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PolExtendDVR

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB Y} {M : LB X} {φ : Y ⟶ X} (h : LBIso L (M.pull φ)) (g : Z ⟶ Y) :
    LBIso (L.pull g) (M.pull (g ≫ φ)) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L g g rfl)
    (chartPullSame M (fun _ : PUnit => g ≫ φ) (fun _ => φ) (fun _ => 1) g fun _ => rfl) h

theorem exists_baseChange (hB : PolBaseChangeSt) {V K V' K' : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (a : V →+* V') (ha : Function.Injective a)
    (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left)
    (hφ : IsGrpPullback P.A B (spMap (algebraMap V K)) φ) (hL : LBIso P.L (M.L.L.pull φ)) :
    ∃ (P' : PolAV (Sp K')) (M' : GlobalTheory.UU.CP ((Over.pullback (spMap a)).obj B))
      (φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left),
      IsGrpPullback P'.A ((Over.pullback (spMap a)).obj B) (spMap (algebraMap V' K')) φ' ∧
        LBIso P'.L (M'.L.L.pull φ') ∧ LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := by
  have hi : Function.Injective ((algebraMap V' K').comp a) := (IsFractionRing.injective V' K').comp ha
  let b : K →+* K' := IsFractionRing.lift hi
  have hb : b.comp (algebraMap V K) = (algebraMap V' K').comp a :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hi x
  have hs : spMap b ≫ spMap (algebraMap V K) = spMap (algebraMap V' K') ≫ spMap a := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hB _ _ (spMap b) P
  have gp : IsGrpPullback P'.A P.A (spMap b) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  have hπ := isGrpPullback_pullback B (spMap a)
  have gc := (gp.comp hφ).congr hs rfl
  obtain ⟨M', w, hw⟩ := GlobalTheory.UU.exists_pull M (GlobalTheory.UU.toBase_mul_pullback B (spMap a))
  have hM : LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := ⟨w, hw.gen⟩
  let φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left :=
    pullback.lift (g ≫ φ) (P'.A.hom ≫ spMap (algebraMap V' K')) (gc.1.w.trans (Category.assoc _ _ _).symm)
  have e : φ' ≫ pullback.fst B.hom (spMap a) = g ≫ φ := pullback.lift_fst _ _ _
  refine ⟨P', M', φ', hπ.cancel (gc.congr rfl e.symm) (pullback.lift_snd _ _ _), ?_, hM⟩
  have i₁ : LBIso P'.L (M.L.L.pull (g ≫ φ)) :=
    LBIso.trans P'.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull M.L.isLB _) (LBIso.symm ⟨t, ht⟩) (lbIso_pull_comp hL g)
  have i₂ := lbIso_pull_comp hM φ'
  rw [e] at i₂
  exact LBIso.trans P'.isLB (LB.isLB_pull M.L.isLB _) (LB.isLB_pull M'.L.isLB _) i₁ i₂.symm

end GlobalTheory.PolExtendDVR

namespace GlobalTheory


open PolExtendDVR IsLocalRing in
theorem polarisation_extends_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L ∧ KTriv B M.L.L := by
  intro h h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ hL
  let V' := AdicCompletion (maximalIdeal V) V
  obtain ⟨P', M', φ', hφ', hL', hM⟩ := exists_baseChange (K' := FractionRing V') h.polBaseChange (algebraMap V V')
    (algebraMap_adicCompletion_injective_of_dvr V) P B M φ hφ hL
  have hπ := isGrpPullback_pullback B (spMap (algebraMap V V'))
  have hB' := (pol_pull _ _ B _ _ _ M.L.L M'.L.L M.L.isLB M'.L.isLB hB hπ hM).1
  have hA' := GlobalTheory.T.relAmple_extended_principalPolarisation_dvr h h₂ V' (FractionRing V') P' _ M' φ' hB' hφ' hL' inferInstance
  have : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hA : RelAmple B M.L.L :=
    AmpleDescent.relAmple_of_faithfullyFlat V V' B _ _ M.L.L M'.L.L hB hπ M.L.isLB M'.L.isLB hM hA'
  exact ⟨hA, KTrivSpread.kTriv_of_generic_fibre h V K P B M φ hB hφ hL hA⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleExt

theorem exists_hom {X U : Scheme.{0}} {j : U ⟶ X} {G G' : Over X} [GrpObj G] [GrpObj G'] {G₀ : Over U} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} {φ' : G₀.left ⟶ G'.left} (h : IsGrpPullback G₀ G j φ) (h' : IsGrpPullback G₀ G' j φ')
    (hx : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f) :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback G j)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso h' (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx (e.inv ≫ e'.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  rw [← hφ, Category.assoc, ← ExtUnique.pullback_map_left_fst j F, hFf, ← Category.assoc, ← Over.comp_left,
    e.hom_inv_id_assoc, hφ']

end TripleExt
end GlobalTheory

theorem GlobalTheory.exists_sabMap_id_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ := by
  intro hdvr E _ _ _ H X U j hX hj₁ hj₂ hj₃ hj₄ t₀ t t' a a' hp
  obtain ⟨hgen, -, hdom, -⟩ := densePart_basic X U j hj₁ hj₂ hj₃ hj₄
  have hred : IsReduced X := by
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hX.1 x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  have hnoeth : IsLocallyNoetherian X := by
    obtain ⟨z, hz, -⟩ := hX.2
    exact LocallyOfFiniteType.isLocallyNoetherian z
  have := hdom hred
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart
    (GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart
    (GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have gp : IsGrpPullback t.G t'.G (𝟙 X) F.left :=
    haveI : IsMonHom (asIso F).hom := hF
    isGrpPullback_of_iso (asIso F)
  have hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left := fun x => by
    have : t.act.act x ≫ F = F ≫ t'.act.act x := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
    exact congrArg (fun z => z.left) this
  have hlb : LBIso t.PP.L (t'.PP.L.pull F.left) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff _ _ _).1 a.lin
    obtain ⟨w', hw', -⟩ := (isPullCubical_iff _ _ _).1 a'.lin
    have hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w'' := by
      rw [hφ]; exact ⟨w', hw'⟩
    obtain ⟨w'', hw''⟩ := hw''
    obtain ⟨r, hr, -⟩ := Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw''
      a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst
    obtain ⟨ρ, hρ, -⟩ := Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig
      t'.PP.rigGen t.PP.rigGen
    have sm := t.semi.smooth
    have gc := t.semi.geomConnected
    exact GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX.1 hj₁ hj₂ hj₃ hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G])
      sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (LB.isLB_pull t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩
  obtain ⟨b, hb⟩ := exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left
    ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb
  exact ⟨b, by rw [hb]; exact hφ⟩
end
