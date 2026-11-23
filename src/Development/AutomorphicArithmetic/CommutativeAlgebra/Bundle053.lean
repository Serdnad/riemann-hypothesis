module

public import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsogenyWithKernelSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsoOfPIsogenyKernelEq
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyKernelPointsIffOfIsPIsog
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.QO.PullIsog

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem comp_eq_one_iff {S S' : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {C C' : Over S'}
    [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left}
    (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have hleftu : (pushHom hu T x).left = x.left ≫ u := rfl
  have hinj : Function.Injective (pushHom hv T) := by
    intro y z hyz
    apply Over.OverMorphism.ext
    apply hv.1.hom_ext
    · exact congrArg Over.Hom.left hyz
    · rw [Over.w y, Over.w z]
  have hpush : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := by
    apply Over.OverMorphism.ext
    show (x ≫ g').left ≫ v = (pushHom hu T x).left ≫ g.left
    rw [hleftu, Over.comp_left, Category.assoc, hg, Category.assoc]
  constructor
  · intro h1
    rw [← hpush, h1, map_one]
  · intro h1
    apply hinj
    rw [hpush, h1, map_one]

theorem exists_isPIsog_pull {c : ℕ} {T Y : Scheme.{0}} {s₁ : T ⟶ Sp R} {s : Y ⟶ Sp R} {t : T ⟶ Y}
    {o₁ o₁' : Obj b N s₁} {o o' : Obj b N s} (m : ObjMap o₁ o t) (m' : ObjMap o₁' o' t) {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) :
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ ∧ IsPIsog c o₁ o₁' ψ₁ := by
  obtain ⟨ψ', hq⟩ := h.exists_quasiInv
  obtain ⟨B₁, _, _, θ, ψ₁, ψ₁', _, hpb, hq₁, h1, h2⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback T Y t o.A o'.A c ψ ψ' o₁.A m.φ o'.ab hq m.cart
  obtain ⟨e, he, heθ⟩ := grpPullback_iso hpb m'.cart
  have hψ : m.φ ≫ ψ.left = (ψ₁ ≫ e.hom).left ≫ m'.φ := by
    rw [h1, ← heθ, Over.comp_left, Category.assoc]
  have hψ' : ∀ {W : Scheme} (k : o'.A.left ⟶ W), ψ₁.left ≫ e.hom.left ≫ m'.φ ≫ k = m.φ ≫ ψ.left ≫ k := by
    intro W k
    rw [← Category.assoc m.φ, hψ, Over.comp_left]
    simp only [Category.assoc]
  have hψ0 : ψ₁.left ≫ e.hom.left ≫ m'.φ = m.φ ≫ ψ.left := by
    rw [hψ, Over.comp_left, Category.assoc]
  have ext' : ∀ {Z : Over T} (f g : Z ⟶ o₁'.A), f.left ≫ m'.φ = g.left ≫ m'.φ → f = g :=
    fun f g hfg => Over.OverMorphism.ext (m'.cart.1.hom_ext hfg (by rw [Over.w f, Over.w g]))
  haveI := hq₁.1
  haveI := hq₁.2.1
  haveI := he
  refine ⟨ψ₁ ≫ e.hom, hψ, h.1, inferInstance, ?_, ?_, ?_, e.inv ≫ ψ₁', inferInstance, ?_, ?_⟩
  · intro c'
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.act c', hψ', ← Category.assoc (o₁.act.act c').left m.φ, m.act c', Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.1 c')
    simpa only [Over.comp_left, Category.assoc] using this
  · intro y
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.eta y, ← Category.assoc (o₁.eta y).left m.φ, m.eta y, Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.2.1 y)
    simpa only [Over.comp_left] using this
  · have hpow₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpull₁ : (o₁'.P.pull (sq2 (ψ₁ ≫ e.hom))).IsLB := pull_isLB o₁'.isLB _
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o.isLB m.φ₂ (pull_isLB o.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m.pol
    have e2 : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB m'.φ₂ (pull_isLB o'.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m'.pol
    obtain ⟨hpolψ⟩ := h.2.2.2.2.1
    have e3 : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = c • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
        ← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact ((GlobalTheory.CechPic.cls_eq_iff _ _).mpr hpolψ).symm
    have key : sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply pullback.hom_ext
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left
        rw [Category.assoc, m'.sq.1, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.1]
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left
        rw [Category.assoc, m'.sq.2, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.2]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hpow₁ hpull₁).mp ?_⟩
    rw [GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c hpow₁, GlobalTheory.CechPic.cls_pull o₁'.isLB _ hpull₁, e1, e2,
      ← GlobalTheory.CechPic.pull_comp, key, GlobalTheory.CechPic.pull_comp, e3, map_nsmul]
  · rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hq₁.2.2.1
  · rw [Category.assoc, ← Category.assoc ψ₁', hq₁.2.2.2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, Iso.inv_hom_id]

end UpperTheory.QO.PullIsog

open UpperTheory.QO.PullIsog in
theorem UpperTheory.exists_isPIsog_isTj_of_section_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (σ : S ⟶ Rd.Y.left), σ ≫ Rd.Y.hom = 𝟙 S → ∃ (o'' : Obj b N s) (ψ'' : o.A ⟶ o''.A), IsPIsog c o o'' ψ'' ∧ IsTj r w j o o'' ψ'' ∧ ∀ (T : Over S) (a : T ⟶ o.A), ∃ a₀ : Over.mk (T.hom ≫ σ) ⟶ Rd.o₀.A, a₀.left ≫ Rd.m₀.φ = a.left ∧ (a ≫ ψ'' = 1 ↔ a₀ ≫ Rd.ψ = 1) ∧ ∀ v : Ideal (𝓞 D.F), KilledBy o v a ↔ KilledBy Rd.o₀ v a₀ := by
  intro p _ D R _ b N hN hNp r w j c S s o Rd σ hσ
  let idm : ObjMap o o (𝟙 S) :=
    { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
      act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }
  obtain ⟨m', hm'⟩ := IsogRep.exists_factor hN hNp hσ Rd.m₀ idm
  have hs : σ ≫ Rd.Y.hom ≫ s = s := by rw [← Category.assoc, hσ, Category.id_comp]
  obtain ⟨o'', ⟨m''⟩⟩ := IsogRep.exists_pull σ Rd.o' hs
  obtain ⟨ψ'', hsq, hiso⟩ := exists_isPIsog_pull m' m'' Rd.isog
  refine ⟨o'', ψ'', hiso, ?_, fun T a => ?_⟩
  · exact (tjAt_id_iff r w j o o'' ψ'').1
      ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o Rd.o₀ m' o''.A Rd.o'.A m''.φ ψ'' Rd.ψ r w j m''.cart hsq).1
        fun k _ _ _ x _ => Rd.tj k x)
  · refine ⟨pushHom m'.cart T a, ?_, comp_eq_one_iff m'.cart m''.cart hsq.symm a, fun v => ?_⟩
    · change (a.left ≫ m'.φ) ≫ Rd.m₀.φ = a.left
      rw [Category.assoc, hm']
      exact Category.comp_id _
    · unfold GlobalTheory.UPel.HT.ES.KilledBy
      exact forall₂_congr fun x _ => comp_eq_one_iff m'.cart m'.cart (m'.act _) a
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.SectionEquivalence

variable {T U : Scheme.{0}} {G' : Over T} [GrpObj G'] {G : Over U} [GrpObj G] {f : T ⟶ U} {φ : G'.left ⟶ G.left}

private theorem mul_left (hp : IsGrpPullback G' G f φ) (h h' : 𝟙_ (Over T) ⟶ G') {g : T ⟶ U} (hg : 𝟙 T ≫ f = g)
    (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = h.left ≫ φ) (hy : y₀.left = h'.left ≫ φ) :
    (x₀ * y₀).left = (h * h').left ≫ φ := by
  subst hg
  exact hp.2 _ h h' x₀ y₀ hx hy

private def secEquiv (hp : IsGrpPullback G' G f φ) : (𝟙_ (Over T) ⟶ G') ≃* (Over.mk f ⟶ G) where
  toFun h := Over.homMk (h.left ≫ φ) (by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    show (h.left ≫ φ) ≫ G.hom = f
    rw [Category.assoc, hp.1.w, ← Category.assoc, e]
    exact Category.id_comp f)
  invFun a := (Over.homMk (hp.1.lift a.left (𝟙 T) ((Over.w a).trans (Category.id_comp f).symm))
    (hp.1.lift_snd _ _ _) : Over.mk (𝟙 T) ⟶ G')
  left_inv h := by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_)
    · exact hp.1.lift_fst _ _ _
    · exact (hp.1.lift_snd _ _ _).trans e.symm
  right_inv a := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  map_mul' h h' := Over.OverMorphism.ext
    (mul_left hp h h' (Category.id_comp f) _ _ rfl rfl).symm

private theorem secEquiv_left (hp : IsGrpPullback G' G f φ) (h : 𝟙_ (Over T) ⟶ G') :
    (secEquiv hp h).left = h.left ≫ φ := rfl

private theorem secEquiv_comp {H' : Over T} [GrpObj H'] {H : Over U} [GrpObj H] {φ₁ : H'.left ⟶ H.left}
    (hp : IsGrpPullback G' G f φ) (hp₁ : IsGrpPullback H' H f φ₁) (α : G' ⟶ H') (β : G ⟶ H)
    (e : α.left ≫ φ₁ = φ ≫ β.left) (h : 𝟙_ (Over T) ⟶ G') :
    secEquiv hp₁ (h ≫ α) = secEquiv hp h ≫ β := by
  refine Over.OverMorphism.ext ?_
  rw [secEquiv_left, Over.comp_left, Over.comp_left, secEquiv_left, Category.assoc, Category.assoc, e]

end UpperTheory.SectionEquivalence

open UpperTheory.SectionEquivalence

theorem UpperTheory.repData_geometric_points_of_subData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Rd.Y.left, y ≫ Rd.Y.hom = x ∧ KerGeo Rd Sd y := by
  intro p _ D R _ _ b N hN hNp hpu hm r w j c hw hr hj hc S _ s o Rd Sd k _ _ x
  obtain ⟨ox, ⟨m⟩⟩ := IsogRep.exists_pull x o (s' := x ≫ s) rfl
  have hp' : IsGrpPullback ox.A o.A x m.φ := m.cart
  letI := Sd.grp
  haveI := Sd.hom
  let Ksub : Subgroup (Over.mk x ⟶ o.A) := (IsMonHom.monoidHom Sd.i (Over.mk x)).range
  let H₀ : Subgroup (𝟙_ (Over (Sp k)) ⟶ ox.A) := Ksub.comap (secEquiv hp').toMonoidHom
  have memH : ∀ h, h ∈ H₀ ↔ InSub Sd.i (secEquiv hp' h) := fun h => Iff.rfl
  have hstab : ∀ (a : D.O), ∀ h ∈ H₀, h ≫ ox.act.act a ∈ H₀ := by
    intro a h hh
    rw [memH] at hh ⊢
    obtain ⟨z, hz⟩ := hh
    obtain ⟨g, hg⟩ := Sd.stable a
    refine ⟨z ≫ g, ?_⟩
    rw [secEquiv_comp hp' hp' _ _ (m.act a) h, Category.assoc, hg, ← Category.assoc, hz]
  have hkill : ∀ h ∈ H₀, ES.KilledBy ox w h := by
    intro h hh c hc
    have hk := Sd.killed _ _ ((memH h).1 hh) c hc
    rw [← secEquiv_comp hp' hp' _ _ (m.act _) h, ← map_one (secEquiv hp')] at hk
    exact (secEquiv hp').injective hk
  have hcard : Nat.card H₀ = Ideal.absNorm w ^ j := by
    haveI := Sd.mono
    haveI := Sd.fin
    haveI := Sd.et
    have hmem : ∀ z : Over.mk x ⟶ Sd.K, (secEquiv hp').symm (z ≫ Sd.i) ∈ H₀ := fun z => by
      rw [memH, MulEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    have e1 : H₀ ≃ (Over.mk x ⟶ Sd.K) := by
      refine (Equiv.ofBijective (fun z : Over.mk x ⟶ Sd.K => (⟨_, hmem z⟩ : H₀)) ⟨?_, ?_⟩).symm
      · intro z z' hzz
        have hz := congrArg (fun u : H₀ => secEquiv hp' u.1) hzz
        simp only [MulEquiv.apply_symm_apply] at hz
        exact (cancel_mono Sd.i).1 hz
      · rintro ⟨h, hh⟩
        obtain ⟨z, hz⟩ := (memH h).1 hh
        refine ⟨z, Subtype.ext ?_⟩
        simp only [hz, MulEquiv.symm_apply_apply]
    have e2 : (Over.mk x ⟶ Sd.K) ≃ {t : Spec (CommRingCat.of k) ⟶ Sd.K.left // t ≫ Sd.K.hom = x} :=
      { toFun := fun z => ⟨z.left, by simpa using Over.w z⟩
        invFun := fun t => Over.homMk t.1 t.2
        left_inv := fun z => Over.OverMorphism.ext rfl
        right_inv := fun t => Subtype.ext rfl }
    let pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank Sd.K.hom x pt
    rw [Nat.card_congr (e1.trans e2), hc]
    have hK : (toUnit Sd.K).left = Sd.K.hom := by simpa using Over.w (toUnit Sd.K)
    have hr := Sd.deg.rank (x pt)
    rw [hK] at hr
    exact hr
  obtain ⟨o', ψ, hiso, htj, hker⟩ :=
    UpperTheory.exists_isogeny_with_kernel_subgroup p D R b N hN hNp hpu hm r w j c hw hr hc k (x ≫ s) ox H₀ hstab hkill hcard
  obtain ⟨y, ⟨hy, m₀', m₁, hsq⟩, -⟩ := Rd.univ (Sp k) x ox o' m ψ hiso htj
  subst hy
  refine ⟨y, rfl, ?_⟩
  intro a₀ a ha
  have hp₀ := m₀'.cart
  have hp₁ := m₁.cart
  obtain ⟨mm, hmm⟩ := IsogRep.exists_comp m₀' Rd.m₀
  have hφ : m.φ = m₀'.φ ≫ Rd.m₀.φ := by
    rw [← hmm]
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ o ox _ _ m mm rfl
  obtain ⟨h, rfl⟩ : ∃ h, secEquiv hp₀ h = a₀ := ⟨(secEquiv hp₀).symm a₀, MulEquiv.apply_symm_apply _ _⟩
  have haa : a = secEquiv hp' h := by
    apply Over.OverMorphism.ext
    rw [secEquiv_left, hφ, ← Category.assoc, ← secEquiv_left hp₀, ha]
  have hψ1 : secEquiv hp₀ h ≫ Rd.ψ = secEquiv hp₁ (h ≫ ψ) :=
    (secEquiv_comp hp₀ hp₁ ψ Rd.ψ hsq.symm h).symm
  have hkb : ∀ I : Ideal (𝓞 D.F), ES.KilledBy Rd.o₀ I (secEquiv hp₀ h) ↔ ES.KilledBy ox I h := by
    intro I
    refine forall₂_congr fun c _ => ?_
    rw [← secEquiv_comp hp₀ hp₀ _ _ (m₀'.act _) h, ← map_one (secEquiv hp₀),
      (secEquiv hp₀).injective.eq_iff]
  rw [haa, ← memH, ← hker, hψ1, ← map_one (secEquiv hp₁), (secEquiv hp₁).injective.eq_iff]
  simp only [hkb]

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.KernelTorsionPullback

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_equiv_points_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  let Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G) :=
    { toFun := fun x => Over.homMk (x.left ≫ φ) (by
        show _ = T.hom ≫ f
        rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
      invFun := fun y => Over.homMk (hp.1.lift y.left T.hom (Over.w y)) (by simp)
      left_inv := fun x => by
        apply Over.OverMorphism.ext
        apply hp.1.hom_ext
        · simp
        · simp
      right_inv := fun y => by
        apply Over.OverMorphism.ext
        simp }
  have hl : ∀ x, (Φ x).left = x.left ≫ φ := fun x => rfl
  have h1 : Φ 1 = 1 := by
    have hm := hp.2 T 1 1 (Φ 1) (Φ 1) (hl 1) (hl 1)
    have hsq : Φ 1 * Φ 1 = Φ 1 := by
      apply Over.OverMorphism.ext
      rw [hm, _root_.mul_one]
      rfl
    exact mul_left_cancel (a := Φ 1) (by rw [hsq, _root_.mul_one])
  refine ⟨Φ, hl, fun x => ⟨fun hx => Φ.injective (by rw [hx, h1]), fun hx => by rw [hx, h1]⟩⟩

private theorem isTj_of_pull {Y S : Scheme.{0}} {σ : Y ⟶ Sp R} {σ₁ : S ⟶ Sp R} {f : S ⟶ Y} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j : ℕ} {o o' : Obj b N σ} {o₁ o₁' : Obj b N σ₁}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) {ψ : o.A ⟶ o'.A} {ψ₁ : o₁.A ⟶ o₁'.A}
    (e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (h : IsTj r w j o o' ψ) : IsTj r w j o₁ o₁' ψ₁ := by
  intro k _ _ _ x
  obtain ⟨h1, h2⟩ := h k (x ≫ f)
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_of_isGrpPullback m.cart (Over.mk x)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_of_isGrpPullback m'.cart (Over.mk x)
  have hψ : ∀ g, Φ' (g ≫ ψ₁) = Φ g ≫ ψ := by
    intro g
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, e]
  have hk1 : ∀ g, g ≫ ψ₁ = 1 ↔ Φ g ≫ ψ = 1 := by
    intro g
    rw [← hψ, hΦ'1]
  have hkill : ∀ v g, KilledBy o₁ v g ↔ KilledBy o v (Φ g) := by
    intro v g
    apply forall₂_congr
    intro a _
    have hc : Φ (g ≫ o₁.act.act ((algebraMap (𝓞 D.F) D.O) a))
        = Φ g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) a) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act]
    rw [← hc, hΦ1]
  constructor
  · intro g hg hex
    rw [hkill]
    obtain ⟨e0, he⟩ := hex
    exact h1 (Φ g) ((hk1 g).mp hg) ⟨e0, (hkill _ g).mp he⟩
  · rw [← h2]
    exact Nat.card_congr (Φ.subtypeEquiv (fun g => by rw [hk1, hkill]))

private theorem exists_equiv_points_mk_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk g ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  subst hg
  exact exists_equiv_points_of_isGrpPullback hp T

private theorem ker_iff {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s}
    (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {k : Type} [Field k] (y : Sp k ⟶ Rd.Y.left) {x : Sp k ⟶ S}
    (e : y ≫ Rd.Y.hom = x) {t : Sp k ⟶ Sp R} {ox o₁ : Obj b N t} (m : ObjMap ox o x) (my : ObjMap ox Rd.o₀ y)
    (hm : my.φ ≫ Rd.m₀.φ = m.φ) (n : ObjMap o₁ Rd.o' y) (ψ₁ : ox.A ⟶ o₁.A)
    (hψ : my.φ ≫ Rd.ψ.left = ψ₁.left ≫ n.φ) (hK : KerGeo Rd Sd y) (h : Over.mk (𝟙 (Sp k)) ⟶ ox.A)
    (a : Over.mk x ⟶ o.A) (ha : a.left = h.left ≫ m.φ) :
    (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy ox (uIdeal D r ^ e) h) ↔ InSub Sd.i a := by
  subst e
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_mk_of_isGrpPullback my.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_mk_of_isGrpPullback n.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  have key := hK (Φ h) a (by rw [hΦl, Category.assoc, hm, ha])
  rw [← key]
  have hψ' : Φ' (h ≫ ψ₁) = Φ h ≫ Rd.ψ := by
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, hψ]
  have hk : ∀ v, KilledBy ox v h ↔ KilledBy Rd.o₀ v (Φ h) := by
    intro v
    apply forall₂_congr
    intro c _
    have hc : Φ (h ≫ ox.act.act ((algebraMap (𝓞 D.F) D.O) c))
        = Φ h ≫ Rd.o₀.act.act ((algebraMap (𝓞 D.F) D.O) c) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, my.act]
    rw [← hc, hΦ1]
  rw [← hψ', hΦ'1]
  exact and_congr Iff.rfl (exists_congr fun _ => hk _)

end UpperTheory.KernelTorsionPullback

private theorem exists_objMap_same_phi_of_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f f' : S' ⟶ S}
    (hf : f = f') (n : ObjMap o' o f) : ∃ n' : ObjMap o' o f', n'.φ = n.φ := by
  subst hf
  exact ⟨n, rfl⟩

open UpperTheory.KernelTorsionPullback in
theorem UpperTheory.subData_points_correspond_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left), y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → KerGeo Rd Sd y₁ → KerGeo Rd Sd y₂ → y₁ = y₂ := by
  intro p _ D R _ _ b N hN hcop hp hm1 r w j c hw hu hc S _ s o Rd Sd k _ _ y₁ y₂ hy hK₁ hK₂
  obtain ⟨x, hx⟩ : ∃ x, y₁ ≫ Rd.Y.hom = x := ⟨_, rfl⟩
  have hx2 : y₂ ≫ Rd.Y.hom = x := hy ▸ hx
  obtain ⟨ox, ⟨my₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o₀ (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨o₁, ⟨n₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o' (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨ψ₁, hiso₁, hsq₁⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₁ Rd.o₀ Rd.o' ox o₁ my₁ n₁ Rd.ψ Rd.isog
  have htj₁ : IsTj r w j ox o₁ ψ₁ := isTj_of_pull my₁ n₁ hsq₁ Rd.tj
  obtain ⟨mc, hmc⟩ := IsogRep.exists_comp my₁ Rd.m₀
  obtain ⟨m, hmφ⟩ := exists_objMap_same_phi_of_eq hx mc
  obtain ⟨my₂, hmy₂⟩ := IsogRep.exists_factor hN hcop hx2 Rd.m₀ m
  obtain ⟨o₂, ⟨n'⟩⟩ := IsogRep.exists_pull y₂ Rd.o' (s' := x ≫ s) (by rw [← hx2, Category.assoc])
  obtain ⟨ψ₂, hiso₂, hsq₂⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₂ Rd.o₀ Rd.o' ox o₂ my₂ n' Rd.ψ Rd.isog
  have hker : ∀ h : 𝟙_ (Over (Sp k)) ⟶ ox.A,
      (h ≫ ψ₁ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) ↔
        (h ≫ ψ₂ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) := by
    intro h
    let a : Over.mk x ⟶ o.A := Over.homMk (h.left ≫ m.φ) (by
      show _ = x
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w h]
      exact Category.id_comp x)
    rw [ker_iff Rd Sd y₁ hx m my₁ (by rw [hmφ, hmc]) n₁ ψ₁ hsq₁ hK₁ h a rfl,
      ker_iff Rd Sd y₂ hx2 m my₂ hmy₂ n' ψ₂ hsq₂ hK₂ h a rfl]
  have hgeo := isogeny_kernel_points_iff_of_isPIsog p D R b N hp r w c hw hu k (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hker
  obtain ⟨mm, hmm⟩ := exists_iso_of_pIsogeny_kernel_eq p D R b N hN hcop hp c (Sp k) (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hgeo
  obtain ⟨nc, hnc⟩ := IsogRep.exists_comp mm n'
  obtain ⟨n₂, hn₂⟩ := exists_objMap_same_phi_of_eq (Category.id_comp y₂) nc
  exact (Rd.univ (Sp k) x ox o₁ m ψ₁ hiso₁ htj₁).unique ⟨hx, my₁, n₁, hsq₁⟩
    ⟨hx2, my₂, n₂, by rw [hn₂, hnc, ← Category.assoc, hmm, hsq₂]⟩
end
