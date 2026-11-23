module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle195
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNsmulOfDvd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPts

theorem exists_geomPt (S : Scheme.{0}) (p : S) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S), Set.range x = {p} := by
  refine ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p))))
      ≫ S.fromSpecResidueField p, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨IsLocalRing.closedPoint _, ?_⟩, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

theorem eq_comp_section {S X : Scheme.{0}} (g : X ⟶ S) [IsSeparated g] (τ : S ⟶ X) (w : τ ≫ g = 𝟙 S) {k : Type}
    [Field k] (x : Sp k ⟶ S) (z : Sp k ⟶ X) (hz : z ≫ g = x)
    (h : z (IsLocalRing.closedPoint k) ∈ Set.range τ) : x ≫ τ = z := by
  have : IsClosedImmersion (τ ≫ g) := by rw [w]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ g
  have : Surjective (pullback.fst z τ) := ⟨fun q => by
    rw [← Set.mem_range, Scheme.Pullback.range_fst, Subsingleton.elim q (IsLocalRing.closedPoint k)]
    exact h⟩
  have : IsIso (pullback.fst z τ) := isIso_of_isClosedImmersion_of_surjective _
  have e : (inv (pullback.fst z τ) ≫ pullback.snd z τ) ≫ τ = z := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← hz, ← e]
  simp only [Category.assoc, reassoc_of% w]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {J : Type}
    (σ : J → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (σ j).left) ↔ ∃ j, toUnit (Over.mk x) ≫ σ j = z := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨IsLocalRing.closedPoint k, rfl⟩)
    exact ⟨j, Over.OverMorphism.ext (eq_comp_section G.hom (σ j).left (Over.w _) x z.left (Over.w z) hj)⟩
  · rintro ⟨j, rfl⟩ _ ⟨q, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, _, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {P : Ideal (𝓞 E)} {p i : ℕ}

theorem heckeSet_eq {S : Scheme.{0}} {t : SAB H S} {K K' : Set t.G.left} (hp : p ≠ 0) (h : HeckeSet D t P p i K)
    (h' : HeckeSet D t P p i K') (hle : K ⊆ K') : K = K' := by
  refine hle.antisymm fun g hg => ?_
  obtain ⟨k, _, _, z, hz⟩ := exists_geomPt _ g
  obtain ⟨C, hC, hk⟩ := h k (z ≫ t.G.hom)
  obtain ⟨C', hC', hk'⟩ := h' k (z ≫ t.G.hom)
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [hk'.2.2.2.2.1]; exact pow_ne_zero _ hp)
  have e : C = C' := Subgroup.eq_of_le_of_card_ge (fun u hu => (hC' u).2 (((hC u).1 hu).trans hle))
    (by rw [hk.2.2.2.2.1, hk'.2.2.2.2.1])
  have m : (Over.homMk z rfl : Over.mk (z ≫ t.G.hom) ⟶ t.G) ∈ C := by
    rw [e, hC']
    exact hz.subset.trans (Set.singleton_subset_iff.2 hg)
  exact (hC _).1 m (hz.symm.subset rfl)

theorem pow_eq_one {S : Scheme.{0}} {t : SAB H S} {T : Over S} {C : Subgroup (T ⟶ t.G)} (hp : (p : 𝓞 E) ∈ P)
    (h : t.HeckeKer T D P p i C) {x : T ⟶ t.G} (hx : x ∈ C) : x ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span t x (p ^ 2)).1 fun a ha => h.2.2.1 hx a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp
  rwa [map_natCast] at this

theorem exists_set (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp (KA l)} (o : Ob D l s)
    (C : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G)) (h : o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C) :
    ∃ K : Set o.t.G.left, EtSet o.t.G K ∧ HeckeSet D o.t P p i K ∧ (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧
      ∀ K', (∀ z ∈ C, Set.range z.left ⊆ K') → K ⊆ K' := by
  have := o.proper
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [h.2.2.2.2.1]; exact pow_ne_zero _ hA.2.2.1.ne_zero)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let σ : Fin n → (𝟙_ (Over (Sp k)) ⟶ o.t.G) := fun j => (e.symm j).1
  have tu : ∀ j, toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j = (e.symm j).1 := fun j => by
    apply Over.OverMorphism.ext
    simp [σ]
  have hσ : ∀ j, σ j ^ p ^ 2 = 1 := fun j => pow_eq_one (T := 𝟙_ (Over (Sp k))) hA.2.2.2.1 h (e.symm j).2
  have hC : (C : Set _) = Set.range (fun j => toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j) := by
    ext z
    refine ⟨fun hz => ⟨e ⟨z, hz⟩, by simp only [tu, Equiv.symm_apply_apply]⟩, ?_⟩
    rintro ⟨j, rfl⟩
    simp only [tu]
    exact (e.symm j).2
  obtain ⟨V, -, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n _ s o σ hA hσ
  have h1 : Set.range (𝟙 (Sp k) :) ⊆ V := (hV k _).2 ⟨fun a b hab => e.symm.injective (Subtype.ext
    (Over.OverMorphism.ext (by simpa [σ] using hab))), C, hC, h⟩
  have h2 := fun (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) =>
    (hV k' x).1 fun q _ => h1 ⟨q, rfl⟩
  refine ⟨⋃ j, Set.range (σ j).left, ?_, fun k' _ _ x => ?_, fun z => ?_, fun K' hK' => ?_⟩
  · obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_id o.t
    refine GlobalTheory.HkFam.etSet_of_lists _ _ (𝟙 _) o.t.G o.t.G m.φ (p ^ 2) n σ _
      ⟨o.t.semi.comm, o.t.semi.smooth, inferInstance, o.t.semi.geomConnected⟩ m.cart ?_ inferInstance inferInstance
      inferInstance ⟨hσ, by rw [hm]; rfl, fun k' _ _ x => (h2 k' x).1⟩
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  · obtain ⟨C', hC', hk⟩ := (h2 k' x).2
    refine ⟨C', fun z => ?_, hk⟩
    rw [range_subset_iff, ← SetLike.mem_coe, hC']
    rfl
  · rw [range_subset_iff, ← SetLike.mem_coe, hC]
    rfl
  · exact Set.iUnion_subset fun j => hK' _ (e.symm j).2

theorem existsUnique_carries {Xo : Moduli D l} (Z : KerScheme Xo P p i) (hA : admitted l P p) (k : Type) [Field k]
    [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (h : Xo.univ.t.HeckeKer (Over.mk y) D P p i C) : ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y rfl rfl
    (by simp [spMap]) Xo.univ
  have key : ∀ y' : Sp k ⟶ Xo.X, 𝟙 _ ≫ y = y' → ∀ C : Subgroup (Over.mk y' ⟶ Xo.univ.t.G),
      Xo.univ.t.HeckeKer (Over.mk y') D P p i C → ∃ C' : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C' ∧
      ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk y' ⟶ Xo.univ.t.G), v.left = u.left ≫ m.toSABMap.φ →
        (u ∈ C' ↔ v ∈ C) := by
    rintro _ rfl C h
    obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk (𝟙 (Sp k)))
    have hh : ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk (𝟙 _ ≫ y) ⟶ Xo.univ.t.G),
        v.left = u.left ≫ m.toSABMap.φ → (u ∈ Subgroup.comap ρ.toMonoidHom C ↔ v ∈ C) := fun u v e => by
      rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
      rfl
    exact ⟨_, (GlobalTheory.HkSetPull.heckeKer_iff D P p i m.toSABMap (Over.mk (𝟙 (Sp k))) _ C hh).2 h, hh⟩
  obtain ⟨C', h', hCC⟩ := key y (Category.id_comp _) C h
  obtain ⟨K, het, hK, hmem, hmin⟩ := exists_set hA o C' h'
  obtain ⟨z, ⟨hz, n, hn⟩, huniq⟩ := Z.rep _ (y ≫ Xo.s) inferInstance o K het hK
  have cc := fun z : Sp k ⟶ Z.Hk => (GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₁ o).2
    Z.π₁ z Z.m₁
  have pre : ∀ {z : Sp k ⟶ Z.Hk} (n : ObjMap o Z.o₁ z) (w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      Set.range (w.left ≫ n.toSABMap.φ) ⊆ Z.K ↔ Set.range w.left ⊆ n.toSABMap.φ ⁻¹' Z.K := fun n w => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_subset_iff]
  refine ⟨z, ?_, fun z' hz' => huniq z' ?_⟩
  · obtain ⟨m', hm'⟩ := (cc z).1 n
    have e : z ≫ Z.π₁ = y := (Xo.rep _ (y ≫ Xo.s) inferInstance o).unique
      ⟨(Category.assoc _ _ _).trans hz, ⟨m'⟩⟩ ⟨rfl, ⟨m⟩⟩
    have rigid : ∀ (y' : Sp k ⟶ Xo.X) (m' : ObjMap o Xo.univ y'), y = y' → m'.toSABMap.φ = m.toSABMap.φ := by
      rintro _ m' rfl
      exact GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o y (.inl inferInstance) _ _
        fun a => ⟨_, m'.eta a, m.eta a⟩
    refine ⟨e, fun u v huv => ?_⟩
    let w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G := Over.homMk (n.cart.1.lift u.left (𝟙 _) (by simpa using Over.w u))
      (n.cart.1.lift_snd _ _ _)
    have hw : w.left ≫ n.toSABMap.φ = u.left := n.cart.1.lift_fst _ _ _
    rw [← hCC w v (by rw [huv, ← hw, Category.assoc, ← hm', rigid _ m' e.symm]), hmem, hn, ← pre, hw]
  · obtain ⟨rfl, hc⟩ := hz'
    obtain ⟨n', hn'⟩ := (cc z').2 m
    refine ⟨(Category.assoc _ _ _).symm, n', heckeSet_eq hA.2.2.1.ne_zero hK
      (GlobalTheory.HkSetPull.heckeSet_pull D P p i n'.toSABMap _ Z.hecke) (hmin _ fun w hw => ?_)⟩
    have ww : w.left ≫ o.t.G.hom = 𝟙 _ := Over.w w
    let u : Over.mk z' ⟶ Z.o₁.t.G := Over.homMk (w.left ≫ n'.toSABMap.φ) (by
      rw [Category.assoc, n'.cart.1.w, reassoc_of% ww]; rfl)
    let v : Over.mk (z' ≫ Z.π₁) ⟶ Xo.univ.t.G := Over.homMk (w.left ≫ m.toSABMap.φ) (by
      rw [Category.assoc, m.cart.1.w, reassoc_of% ww]; rfl)
    exact (pre n' w).1 ((hc u v ((congrArg (w.left ≫ ·) hn').trans (Category.assoc _ _ _).symm)).2 ((hCC w v rfl).1 hw))

end GlobalTheory.HkPts

theorem GlobalTheory.kerScheme_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  intro E _ _ _ H D l Xo P p i Z hA
  refine ⟨GlobalTheory.HkPts.existsUnique_carries Z hA, fun hi => ⟨fun q => ?_⟩⟩
  obtain ⟨k, _, _, y, hy⟩ := GlobalTheory.HkPts.exists_geomPt _ q
  obtain ⟨C, hC⟩ := GlobalTheory.exists_heckeKer E H D l Xo P p i hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hi k y
  obtain ⟨z, ⟨rfl, -⟩, -⟩ := GlobalTheory.HkPts.existsUnique_carries Z hA k y C hC
  obtain ⟨a, ha⟩ := hy.symm.subset rfl
  exact ⟨z a, (Scheme.Hom.comp_apply _ _ _).symm.trans ha⟩
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  first | exact @GlobalTheory.HkFam.exists_quotient_triple_family | exact GlobalTheory.HkFam.exists_quotient_triple_family | (intros; apply GlobalTheory.HkFam.exists_quotient_triple_family <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  first | exact @GlobalTheory.kerScheme_points | exact GlobalTheory.kerScheme_points | (intros; apply GlobalTheory.kerScheme_points <;> assumption)

end
end
