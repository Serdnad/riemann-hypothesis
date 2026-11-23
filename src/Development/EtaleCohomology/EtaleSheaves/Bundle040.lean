module

public import Development.EtaleCohomology.EtaleSheaves.Bundle026
public import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.StalkGermPf

abbrev toO {X S : Scheme.{0}} (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback p (S.fromSpecStalk s) ⟶ overO p U :=
  pullback.map p (S.fromSpecStalk s) p U.ι (𝟙 _) (U.fromSpecStalkOfMem s hs) (𝟙 _) (by simp) (by simp)

def StalkCont : Prop := Cont → Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p], IsUnit (q : Γ(S, ⊤)) → ∀ (i n : ℤ) (s : S),
  (∀ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i), pull _ (sch.map (toO p s U hs)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ z : Ht q (sch.obj (pullback p (S.fromSpecStalk s))) n i, ∃ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i),
    pull _ (sch.map (toO p s U hs)) _ _ x = z)

variable {Y X S : Scheme.{0}}

theorem pull_mc {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Ht q (sch.obj C) n i) :
    pull _ (sch.map (a ≫ b)) (tw q i) n x = pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) := by
  rw [Functor.map_comp, pull_comp]

theorem toO_res (p : X ⟶ S) (s : S) {V U : S.Opens} (h : V ≤ U) (hV : s ∈ V) :
    toO p s V hV ≫ resO p h = toO p s U (h hV) := by
  have e : V.fromSpecStalkOfMem s hV ≫ S.homOfLE h = U.fromSpecStalkOfMem s (h hV) := by
    rw [← cancel_mono U.ι]; simp
  simp only [toO, resO]; rw [pullback.map_comp]; congr 1 <;> simp [e]

theorem toO_f (f : Y ⟶ X) (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ toO p s U hs =
      toO (f ≫ p) s U hs ≫ fO f p U := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_f (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_res (p : X ⟶ S) {W V U : S.Opens} (h1 : W ≤ V) (h2 : V ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem StalkGerm_of (hS : StalkCont) : StalkGerm := by
  intro hC hH q Y X S f p _ _ _ _ _ _ hq i s he n
  obtain ⟨ia, sa⟩ := hS hC hH q p hq i n s
  obtain ⟨ib, -⟩ := hS hC hH q (f ≫ p) hq i n s
  have hb := he n
  constructor
  · intro U hs x hx
    apply ia U hs x
    apply hb.1
    rw [map_zero, ← pull_mc, toO_f, pull_mc, hx, map_zero]
  · intro U hs y
    obtain ⟨w, hw⟩ := hb.2 (pull _ (sch.map (toO (f ≫ p) s U hs)) _ _ y)
    obtain ⟨U1, hs1, x1, hx1⟩ := sa w
    have hs2 : s ∈ U ⊓ U1 := ⟨hs, hs1⟩
    have hx2' : pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n
        (pull (ZMod q) (sch.map (resO p (inf_le_right : U ⊓ U1 ≤ U1))) (tw q i) n x1) = w := by
      rw [← pull_mc, toO_res]; exact hx1
    obtain ⟨x2, hx2⟩ : ∃ x2 : H (ZMod q) (sch.obj (overO p (U ⊓ U1))) (tw q i) n,
        pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n x2 = w := ⟨_, hx2'⟩
    have e1 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _ (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) =
        pull _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _)
          (by simp) (by simp))) (tw q i) n (pull _ (sch.map (toO p s (U ⊓ U1) hs2)) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, toO_f]
    have e2 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (toO (f ≫ p) s U hs)) (tw q i) n y := by
      rw [← pull_mc, toO_res]
    have h0 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2 -
          pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) = 0 := by
      rw [map_sub, e1, e2, hx2, hw, sub_self]
    obtain ⟨V, hV, hsV, hd⟩ := ib _ hs2 _ h0
    refine ⟨V, hV.trans inf_le_left, hsV, pull _ (sch.map (resO p hV)) _ _ x2, ?_⟩
    rw [map_sub, sub_eq_zero] at hd
    have g1 : pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p hV)) _ _ x2) =
        pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, res_f]
    have g2 : pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (resO (f ≫ p) (hV.trans inf_le_left))) (tw q i) n y := by
      rw [← pull_mc, res_res]
    rw [g1, hd, g2]

end LateralTheory.E.StalkGermPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
end
end

section

noncomputable section

namespace LateralTheory.E.BaerFlatZModCriterion

open TensorProduct

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_eq_smul_of_baer (hB : Module.Baer R M) {a b : R}
    (hab : ∀ r, b * r = 0 → ∃ s, r = a * s) {m : M} (hm : a • m = 0) : ∃ m' : M, m = b • m' := by
  let f : R →ₗ[R] R := LinearMap.toSpanSingleton R R b
  have hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    intro x hx
    simp only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢
    obtain ⟨s, rfl⟩ := hab x (by rw [mul_comm]; exact hx)
    rw [mul_comm, mul_smul, hm, smul_zero]
  let g : LinearMap.range f →ₗ[R] M :=
    (LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g', hg'⟩ := hB (LinearMap.range f) g
  refine ⟨g' 1, ?_⟩
  have h1 : f 1 = b := by simp [f]
  have hmem : b ∈ LinearMap.range f := ⟨1, h1⟩
  have := hg' b hmem
  have hg : g ⟨b, hmem⟩ = m := by
    have e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩ := Subtype.ext h1.symm
    rw [e]
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hg, ← this, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_baer [IsPrincipalIdealRing R]
    (hA : ∀ a : R, ∃ b, a * b = 0 ∧ ∀ r, b * r = 0 → ∃ s, r = a * s) (hB : Module.Baer R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y n =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      exact Subtype.ext hc.symm
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, by rw [tmul_add]⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := pure x
  simp only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.lsmul_apply] at hx
  obtain ⟨b, hab, hb⟩ := hA a
  obtain ⟨m', rfl⟩ := exists_eq_smul_of_baer hB hb hx
  rw [← smul_tmul]
  have : b • (⟨a, haI⟩ : I) = 0 := Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])
  rw [this, zero_tmul]

end General

section ZModPart

theorem zmod_ann (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, a * b = 0 ∧ ∀ r : ZMod q, b * r = 0 → ∃ s, r = a * s := by
  obtain ⟨n, hn⟩ : ∃ n, n = a.val := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd n q := ⟨_, rfl⟩
  have hq : 0 < q := NeZero.pos q
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := hg ▸ Nat.gcd_dvd_right n q
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_left n q
  have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hg0
  have ha : a = (n : ZMod q) := by rw [hn, ZMod.natCast_zmod_val]
  refine ⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hgn
    rw [ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
  · intro r hr
    have hr' : q ∣ (q / g) * r.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hr
    have hdiv : g ∣ r.val := by
      have h2 : (q / g) * g ∣ (q / g) * r.val := by rw [Nat.div_mul_cancel hgq]; exact hr'
      exact Nat.dvd_of_mul_dvd_mul_left hqg h2
    obtain ⟨t, ht⟩ := hdiv
    have hz := Nat.gcd_eq_gcd_ab n q
    have hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) hz
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, add_zero, ← hg] at this
      rw [this, ha]
    refine ⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]

end ZModPart

end LateralTheory.E.BaerFlatZModCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion LateralTheory.E.BaerFlatZModCriterion in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of : LeafInjFlatZMod := by
  intro q _ M _ _ hinj
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  refine flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)
  obtain ⟨b, hab, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext hab, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext hs⟩
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContAffPf

lemma isoSpec_inv_nat {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

lemma pp {R : Type} [CommRing R] {A B C E : Spc} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E) (h : a ≫ b = c ≫ d)
    (F : Shv R) (n : ℤ) (x : H R E F n) : pull R a F n (pull R b F n x) = pull R c F n (pull R d F n x) := by
  rw [← pull_comp, h, pull_comp]

theorem aff_case (hB1 : B1) (q : ℕ) {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) (ha : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)) (hcs : ∀ j, CompactSpace (D.obj j))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (hu : ∀ j, IsUnit (q : Γ(D.obj j, ⊤)))
    (hA : ∀ j, IsAffine (D.obj j)) (hP : IsAffine c.pt) (n i : ℤ) :
    (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
    ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0 := by
  obtain ⟨hE⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j) := fun _ => hP
  have B := hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := I)
  have huP : IsUnit (q : Γ(c.pt, ⊤)) := by
    have := (hu j0).map (c.π.app j0).appTop.hom
    simpa using this
  constructor
  · intro x
    obtain ⟨j, y, hy⟩ := B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP
    refine ⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩
    have key := pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom)
      (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n y
    refine key.trans ?_
    have hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y =
      pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x := hy
    rw [hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, pull_id]
  · intro j y hy
    obtain ⟨k, f, hk⟩ := B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by
      have key2 := pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv)
        (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y
      exact key2.trans (by rw [hy]; exact map_zero _))
    refine ⟨k.unop, f.unop, ?_⟩
    have e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
    rw [e1]
    have key3 := pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom)
      (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)
    refine key3.trans ?_
    have hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0 := hk
    rw [hk', map_zero]

theorem ContAff_of : ContAff := by
  intro h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : IsAffine (D.obj j0) := IsAffine.of_isIso e.hom
  have hc' : IsLimit (c.whisker (Over.forget j0)) := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc
  have hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k) := fun k => by
    have i1 := ha k.hom
    have i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right)) := ‹IsAffine (D.obj j0)›
    exact @isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2
  have hP : IsAffine c.pt := by
    have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f) := ha
    have := hcs; have := hqs
    have := isAffineHom_π_app D c hc j0
    exact isAffine_of_isAffineHom (c.π.app j0)
  have R := aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _)
    (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨k, y, hy⟩ := R.1 x
    exact ⟨k.left, y, hy⟩
  · obtain ⟨k, g, h0, -⟩ := IsCofilteredOrEmpty.cone_objs j j0
    obtain ⟨l, f, hf⟩ := R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by
      show pull _ (sch.map (c.π.app k)) _ _ _ = 0
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]
      exact hy)
    refine ⟨l.left, f.left ≫ g, ?_⟩
    rw [D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]
    exact hf

end LateralTheory.E.ContAffPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

def ClosedAt {X T : Scheme.{0}} (c : X ⟶ T) (W : T.Opens) : Prop :=
  ∀ b : Γ(X, c ⁻¹ᵁ W), (c.app W).hom.IsIntegralElem b → ∃ a, c.app W a = b

def NormClosed : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ V : g.normalization.Opens, IsAffineOpen V → ∀ b : Γ(Z, g.toNormalization ⁻¹ᵁ V),
    (g.toNormalization.app V).hom.IsIntegralElem b → ∃ a, g.toNormalization.app V a = b

theorem RelNorm_of_closed (hN : NormClosed) : LateralTheory.E.SteinPf.RelNorm := by
  intro Z S g _ _ hZ
  haveI : IsIntegral Z := hZ.1
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance, inferInstance, inferInstance,
    g.toNormalization_fromNormalization, fun V hV hne => ⟨?_, ?_, hN g hZ.1 V hV⟩⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := g.toNormalization.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨z, hz⟩
  · haveI : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
    exact g.toNormalization.app_injective V

end LateralTheory.E.RelNormPf
end
end
