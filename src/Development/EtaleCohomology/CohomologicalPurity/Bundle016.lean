module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
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
import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def Good {d : ℕ} (P : SP d) (V : P.X.affineOpens) : Prop :=
  (P.ι.ker.ideal V).FG ∧ Chart d Γ(P.X, V.1) (P.ι.ker.ideal V)

structure Sys {d : ℕ} (P : SP d) where
  J : Type
  [ord : Preorder J]
  V : J → P.X.affineOpens
  mono : ∀ {j k}, j ≤ k → V j ≤ V k
  good : ∀ j, Good P (V j)
  cov : ∀ x : P.X, ∃ j, x ∈ (V j).1
  dir : ∀ (x : P.X) j k, x ∈ (V j).1 → x ∈ (V k).1 → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ (V l).1

attribute [instance] Sys.ord

def Sys.all (hC : LeafChart) {d : ℕ} (P : SP d) : Sys P where
  J := {V : P.X.affineOpens // Good P V}
  V j := j.1
  mono h := h
  good j := j.2
  cov x := by
    obtain ⟨V, h, -, g⟩ := hC d P x ⊤ trivial
    exact ⟨⟨V, g⟩, h⟩
  dir x j k hj hk := by
    obtain ⟨V, h, l, g⟩ := hC d P x (j.1.1 ⊓ k.1.1) ⟨hj, hk⟩
    exact ⟨⟨V, g⟩, l.trans inf_le_left, l.trans inf_le_right, h⟩

variable {d : ℕ}

abbrev eta (H : Hens) (P : SP d) (V : P.X.affineOpens) : Γ(P.X, V.1) →+* H.obj Γ(P.X, V.1) (P.ι.ker.ideal V) := H.η _ _

abbrev hensTo (H : Hens) (P : SP d) (V : P.X.affineOpens) : Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ⟶ P.X :=
  Spec.map (CommRingCat.ofHom (eta H P V)) ≫ V.2.fromSpec

def Sys.aff {P : SP d} (S : Sys P) : S.J ⥤ Scheme.{0} where
  obj j := Spec Γ(P.X, (S.V j).1)
  map f := Spec.map (P.X.presheaf.map (homOfLE (S.mono f.le)).op)
  map_id j := by rw [← Spec.map_id, ← P.X.presheaf.map_id]; rfl
  map_comp f g := by rw [← Spec.map_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.hen {P : SP d} (S : Sys P) (H : Hens) : S.J ⥤ Scheme.{0} where
  obj j := Spec (H.obj Γ(P.X, (S.V j).1) (P.ι.ker.ideal (S.V j)))
  map f := Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal (S.mono f.le))))
  map_id j := by
    have e : (P.X.presheaf.map (homOfLE (le_refl (S.V j).1)).op).hom = RingHom.id Γ(P.X, (S.V j).1) :=
      (congrArg CommRingCat.Hom.hom (P.X.presheaf.map_id (op (S.V j).1))).trans (CommRingCat.hom_id)
    have k : ∀ φ h, φ = RingHom.id _ → H.map (I := P.ι.ker.ideal (S.V j)) (J := P.ι.ker.ideal (S.V j)) φ h = RingHom.id _ := by
      rintro _ h rfl; exact H.map_id _ _ h
    exact (congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (k _ _ e)).trans (Spec.map_id _)
  map_comp {i j k} f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← H.map_comp _ _ _ _ (fun x hx =>
      P.ι.ker.ideal_le_comap_ideal (S.mono f.le) (P.ι.ker.ideal_le_comap_ideal (S.mono g.le) hx))]
    congr 3
    rw [← CommRingCat.hom_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.toAff {P : SP d} (S : Sys P) (H : Hens) : S.hen H ⟶ S.aff where
  app j := Spec.map (CommRingCat.ofHom (eta H P (S.V j)))
  naturality j k f := by
    dsimp only [Sys.hen, Sys.aff]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, H.map_η]; rfl

theorem Sys.cocAff {P : SP d} (S : Sys P) : Coc (S.aff ⋙ yoneda) fun j => yoneda.map (S.V j).2.fromSpec := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))

theorem Sys.cocHen {P : SP d} (S : Sys P) (H : Hens) :
    Coc (S.hen H ⋙ yoneda) fun j => yoneda.map (hensTo H P (S.V j)) := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (by
    have h := (S.toAff H).naturality f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (S.V k).2.fromSpec) h).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))))))

abbrev Sys.E {P : SP d} (S : Sys P) (H : Hens) : Spc := hoc (S.hen H ⋙ yoneda)

abbrev Sys.π {P : SP d} (S : Sys P) (H : Hens) : S.E H ⟶ sch.obj P.X := aug _ (S.cocHen H)

def LeafQuot : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), IndNbhd φ I →
  Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)

def LeafZ : Prop := ∀ (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (B : Type) [CommRing B]
  (φ : Γ(X, V.1) →+* B),
  (∃ z, IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) z
    (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ι) ∧
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
    off B ((ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U

def LeafAbv : Prop := ∀ (Y X : Scheme.{0}) (w : Y ⟶ X) (U' : Y.Opens) (U : X.Opens) (h : U' = w ⁻¹ᵁ U),
  ∃ e : opn U' ≅ abv U (sch.map w), e.hom.right = 𝟙 (sch.obj Y) ∧ e.hom ≫ abvMap U (sch.map w) = opnMap w U' U h.le

def LeafLocFst : Prop := E1 → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) → ∀ i,
  Eqv _ (pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι)) (tw q i)

def LeafLocIso : Prop := ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) h,
  IsIso (pbRel (sch.map P.ι) (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafLocHen : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) →
  (P.ι.ker.ideal V).FG → ∀ h, Exc q (abvRel P.U (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafPrdAff : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η → HenselianRing C K →
  ∀ (_ : Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I) hy (n i : ℤ),
  Function.Bijective fun a : Ht q (sp C) n i =>
    Hs.act q (P := opn (off C K)) a (thom d q C K (fun j => η (ψ (MvPolynomial.X j))) hy)

def LeafPrdRing : Prop := Hyp → ∀ (H : Hens) (d q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), IsUnit (q : A) → I.FG →
  Chart d A I → ∀ c : Hs q (opn (off A I)) (2 * d) d,
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (x : Fin d → B) hx h, φ.Etale →
    Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h) _ _ c = thom d q B (I.map φ) x hx) →
  ∀ h (n i : ℤ), Function.Bijective fun a : Ht q (sp (H.obj A I)) n i =>
    Hs.act q (P := opn (off (H.obj A I) (I.map (H.η A I)))) a
      (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (H.η A I))) (off _ (I.map (H.η A I))) (off A I) h) _ _ c)

def LeafLocPrd : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ) [NeZero q],
  IsUnit (q : Γ(P.X, ⊤)) → Good P V → Prd q P.U (sch.map (hensTo H P V)) (fcl d q P)

def LeafRefine : Prop := ∀ (hC : LeafChart) (H : Hens) (d : ℕ) (P' P : SP d) (φ : P'.Hom P),
  ∃ (S' : Sys P') (a : S'.E H ⟶ (Sys.all hC P').E H) (b : S'.E H ⟶ (Sys.all hC P).E H),
    a ≫ (Sys.all hC P').π H = S'.π H ∧ b ≫ (Sys.all hC P).π H = S'.π H ≫ sch.map φ.f

theorem hs_pull_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  have e : dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
    exact (pushout.map_comp φ.left ψ.left _ _ _ _ (Arrow.w φ).symm (Arrow.w φ).symm (Arrow.w ψ).symm (Arrow.w ψ).symm).symm
  apply Subtype.ext
  change pull _ (dbl.map (φ ≫ ψ)) _ _ x.1 = pull _ (dbl.map φ) _ _ (pull _ (dbl.map ψ) _ _ x.1)
  rw [e, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} {φ : P'' ⟶ P'} {ψ : P' ⟶ P} (h : Exc q φ) (h' : Exc q ψ) : Exc q (φ ≫ ψ) :=
  fun n i => by
    have e : ⇑(Hs.pull q (φ ≫ ψ) n i) = Hs.pull q φ n i ∘ Hs.pull q ψ n i := funext (hs_pull_comp q φ ψ n i)
    rw [e]; exact (h n i).comp (h' n i)

theorem eqv_comp {R : Type} [CommRing R] {E'' E' E : Spc} {f : E'' ⟶ E'} {g : E' ⟶ E} {F : Shv R} (h : Eqv R f F)
    (h' : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]; exact (h n).comp (h' n)

theorem eqv_iso {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem abvRel_abvMap {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abvRel U a π' π h ≫ abvMap U π = abvMap U π' :=
  Arrow.hom_ext _ _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) h

theorem goal_of (hH : LeafHens) (hC : LeafChart) (fst : LeafFstHoc) (rel : LeafRelHoc) (exc : LeafExcHoc) (prd : LeafPrdHoc)
    (loc : LeafLoc) (locExc : LeafLocExc) (lf : LeafLocFst) (li : LeafLocIso) (lh : LeafLocHen) (lp : LeafLocPrd)
    (ref : LeafRefine) : LeafTube := by
  intro hyp d
  obtain ⟨H⟩ := hH
  have hyp' := hyp
  obtain ⟨a1, -, a3, -, -, -, -, -, -, -, -, e1⟩ := hyp'
  have ok : ∀ (P : SP d) (S : Sys P) (q : ℕ) [NeZero q], IsUnit (q : Γ(P.X, ⊤)) →
      (∀ i, Eqv _ (pullback.fst (S.π H) (sch.map P.ι)) (tw q i)) ∧ (∀ i, Eqv _ (pullback.snd (S.π H) (sch.map P.ι)) (tw q i)) ∧
      Exc q (abvMap P.U (S.π H)) ∧ Prd q P.U (S.π H) (fcl d q P) := by
    intro P S q _ hq
    have L : Loc (aug _ S.cocAff) := loc S.J S.aff P.X (fun j => (S.V j).2.fromSpec) (fun j => (S.V j).2.isOpenImmersion_fromSpec)
      (fun x => by
        obtain ⟨j, h⟩ := S.cov x
        exact ⟨j, (S.V j).2.range_fromSpec.ge h⟩)
      (fun x j k hj hk => by
        obtain ⟨l, h, h', h''⟩ := S.dir x j k ((S.V j).2.range_fromSpec.le hj) ((S.V k).2.range_fromSpec.le hk)
        exact ⟨l, h, h', (S.V l).2.range_fromSpec.ge h''⟩) S.cocAff
    have hj : ∀ j, (Functor.whiskerRight (S.toAff H) yoneda).app j ≫ yoneda.map (S.V j).2.fromSpec =
        yoneda.map (hensTo H P (S.V j)) := fun j => (yoneda.map_comp _ _).symm
    have hj' := fun j => (disc.map_comp _ _).symm.trans (congrArg disc.map (hj j))
    have hg := map_aug _ _ _ (S.cocHen H) S.cocAff hj
    refine ⟨fun i => fst a3 _ _ _ _ _ _ (yoneda.map P.ι) _ (S.cocHen H) fun j => lf e1 H d P (S.V j) q hq i, fun i => ?_, ?_,
      prd hyp q _ _ _ P.U _ (S.cocHen H) _ _ _ fun j => lp hyp H d P (S.V j) q hq (S.good j)⟩
    · have e : pullback.snd (S.π H) (sch.map P.ι) =
          pbRel (sch.map P.ι) _ _ _ hg ≫ pullback.snd (aug _ S.cocAff) (sch.map P.ι) :=
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
      rw [e]
      refine eqv_comp (rel a3 _ _ _ _ _ _ _ _ (yoneda.map P.ι) _ _ (S.cocHen H) S.cocAff hj' hg fun j => ?_) fun n => ?_
      · exact @eqv_iso _ _ _ _ _ (li H d P (S.V j) (hj' j)) _
      · exact @a1 _ _ _ _ _ (L _ _ P.ι) _ n
    · rw [← abvRel_abvMap P.U _ _ _ hg]
      exact exc_comp q (exc a3 q _ _ _ _ _ P.U _ _ (S.cocHen H) S.cocAff hj' hg
        fun j => lh hyp H d P (S.V j) q hq (S.good j).1 (hj' j)) (locExc a1 q _ _ _ _ L)
  refine ⟨fun P => ⟨_, (Sys.all hC P).π H, ok P _⟩, fun P' P φ => ?_⟩
  obtain ⟨S', a, b, ha, hb⟩ := ref hC H d P' P φ
  exact ⟨⟨_, S'.π H, ok P' S'⟩, a, b, ha, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dbl_map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) :
    dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    simp

theorem LeafActNat_of : LeafActNat := by
  intro hA q _ P' P φ n m i j a b
  apply Subtype.ext
  have hc := (hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1
  change pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 -
      pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) =
    cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) -
      pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)))
  have e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) =
      pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a) := by
    rw [← pull_comp, ← pull_comp, dbl_map_fold]
  have hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) =
      cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) := by
    rw [hc, e1]
  rw [map_sub, hcc]
  congr 1
  rw [← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right,
    ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDblSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (dbl (abv U (E := disc.obj c.pt) (disc.map π)))
    fun a => dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))))

def LeafDiscSumH : Prop := ∀ (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

theorem leafDiscSumH : LeafDiscSumH := fun A E c hc =>
  ⟨isColimitCofanMkObjOfIsColimit disc E (fun a => c.inj a)
    (hc.some.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ => by simp)))⟩

def LeafPbSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
    fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left))

theorem dbl_inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_inl_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inl P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inl P ≫ h := by
  rw [← Category.assoc, dbl_inl_map, Category.assoc]

theorem dbl_inr_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inr P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inr P ≫ h := by
  rw [← Category.assoc, dbl.inr_map, Category.assoc]

def dbl_cofan {A : Type} {P : Arrow Spc} (Q : A → Arrow Spc) (φ : ∀ a, Q a ⟶ P)
    (hl : IsColimit (Cofan.mk P.left fun a => (φ a).left)) (hr : IsColimit (Cofan.mk P.right fun a => (φ a).right)) :
    IsColimit (Cofan.mk (dbl P) fun a => dbl.map (φ a)) := by
  refine Cofan.IsColimit.mk _ (fun s => pushout.desc (Cofan.IsColimit.desc hr fun a => dbl.inl (Q a) ≫ s.inj a)
      (Cofan.IsColimit.desc hr fun a => dbl.inr (Q a) ≫ s.inj a) ?_) ?_ ?_
  · refine Cofan.IsColimit.hom_ext hl _ _ fun a => ?_
    have w := Arrow.w (φ a)
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    change ((φ a).left ≫ P.hom) ≫ _ = ((φ a).left ≫ P.hom) ≫ _
    rw [w, Category.assoc, Category.assoc, f1, f2, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ s.inj a) (pushout.condition (f := (Q a).hom) (g := (Q a).hom))
  · intro s a
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
    apply pushout.hom_ext (f := (Q a).hom) (g := (Q a).hom)
    · exact (dbl_inl_map_assoc (φ a) _).trans ((congrArg _ (pushout.inl_desc _ _ _)).trans f1)
    · exact (dbl_inr_map_assoc (φ a) _).trans ((congrArg _ (pushout.inr_desc _ _ _)).trans f2)
  · intro s m hm
    apply pushout.hom_ext
    · refine Eq.trans ?_ (pushout.inl_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f1.symm
      exact (dbl_inl_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))
    · refine Eq.trans ?_ (pushout.inr_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f2.symm
      exact (dbl_inr_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))

theorem leafDblSum_of (hP : LeafPbSum) : LeafDblSum := fun X U A E c hc π π' h =>
  ⟨dbl_cofan _ _ (hP X U A E c hc π π' h).some (leafDiscSumH A E c hc).some⟩

theorem LeafHsSum_of_dbl (hS : LeafSum) (hD : LeafDblSum) (hd : LeafDiscSumH) : LeafHsSum := by
  intro q X U A E c hc π π' h n i
  have S1 := hS (ZMod q) (tw q i) A _ _ (hD X U A E c hc π π' h) n
  have S2 := hS (ZMod q) (tw q i) A _ _ (hd A E c hc) n
  constructor
  · intro x y e
    apply Subtype.ext
    apply S1.1
    funext a
    exact congrArg Subtype.val (congrFun e a)
  · intro y
    obtain ⟨x, hx⟩ := S1.2 (fun a => (y a).1)
    have hx' : ∀ a, pull _ (dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))) (tw q i) n x
        = (y a).1 := fun a => congrFun hx a
    have m : x ∈ Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i := by
      refine AddMonoidHom.mem_ker.mpr ?_
      apply S2.1
      funext a
      have e := dbl.inr_map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))
      have y0 : pull _ (dbl.inr _) (tw q i) n (y a).1 = 0 := (y a).2
      have e2 : disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π)) =
          dbl.inr _ ≫ dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) := e.symm
      have key : pull _ (disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π))) (tw q i) n x = 0 := by
        exact (congrArg (fun f => pull (ZMod q) f (tw q i) n x) e2).trans ((pull_comp _ _ _ _ _ _).trans
          ((congrArg (pull (ZMod q) (dbl.inr _) (tw q i) n) (hx' a)).trans y0))
      exact ((pull_comp _ _ _ _ _ _).symm.trans key).trans (map_zero _).symm
    exact ⟨⟨x, m⟩, funext fun a => Subtype.ext (hx' a)⟩

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.LeafLevelPf
open LateralTheory.CohomologicalPurity.TubeCut

variable {J : Type} [SmallCategory J]

theorem elt_eqToHom {F : J ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by subst h; rfl

theorem chn_eq (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (x : ((hoc D).obj n).obj U) :
    (inj D n (chn x ⋙ Functor.Elements.π _)).app U (chn x |>.obj 0).val = x := by
  change mkChn (F := D.flip.obj U) _ _ _ = chn x
  fapply CategoryTheory.Functor.ext
  · intro i
    let f := (chn x).map (homOfLE (Fin.zero_le i))
    refine Functor.Elements.ext _ _ (by rfl) ?_
    change (D.flip.obj U).map (𝟙 ((chn x).obj i).obj)
      ((D.flip.obj U).map f.hom ((chn x).obj 0).val) = ((chn x).obj i).val
    rw [(D.flip.obj U).map_id]
    exact f.map_val
  · intro i k g
    apply Functor.Elements.hom_ext
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom]
    erw [elt_eqToHom, elt_eqToHom]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem bij (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective (Cofan.mk (((hoc D).obj n).obj U) (fun σ => ((evaluation _ _).obj U).map (inj D n σ)) :
      Cofan fun σ : Fin (n.unop.len + 1) ⥤ J => ((evaluation _ _).obj U).obj (D.obj (σ.obj 0))).cofanTypes.fromSigma := by
  constructor
  · rintro ⟨σ, a⟩ ⟨σ', a'⟩ h
    change (inj D n σ).app U a = (inj D n σ').app U a' at h
    have e : σ = σ' := congrArg (fun F => F ⋙ Functor.Elements.π (D.flip.obj U)) h
    subst e
    have h2 := congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h
    have h3 : (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a =
        (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' := by
      change (D.flip.obj U).elementsMk (σ.obj 0) _ = (D.flip.obj U).elementsMk (σ.obj 0) _ at h2
      injection h2
    have hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b := by
      intro b
      have : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := rfl
      rw [this, σ.map_id, D.map_id]; rfl
    rw [hid, hid] at h3
    subst h3; rfl
  · intro x
    exact ⟨⟨chn x ⋙ Functor.Elements.π _, (chn x |>.obj 0).val⟩, chn_eq D n U x⟩

theorem LeafLevel_of : LeafLevel := by
  intro J _ D n
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_
  exact Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))

end LateralTheory.CohomologicalPurity.LeafLevelPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleLocBase : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (Y : Scheme.{0}) (g : Y ⟶ X),
  ∃ (D' : J ⥤ Scheme.{0}) (c' : ∀ j, D'.obj j ⟶ Y), (∀ j, IsOpenImmersion (c' j)) ∧
    (∀ y : Y, ∃ j, y ∈ Set.range (c' j)) ∧
    (∀ (y : Y) j k, y ∈ Set.range (c' j) → y ∈ Set.range (c' k) → ∃ l, l ≤ j ∧ l ≤ k ∧ y ∈ Set.range (c' l)) ∧
    ∃ hc' : Coc (D' ⋙ yoneda) (fun j => yoneda.map (c' j)),
      Nonempty (Arrow.mk (pullback.snd (aug _ hc) (sch.map g)) ≅ Arrow.mk (aug _ hc'))

def EtaleLocAug : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R], QuasiIso ((chains R).map (aug _ hc))

theorem LeafLocCut.goal_of (hb : EtaleLocBase) (ha : EtaleLocAug) : LeafLoc := by
  intro J _ D X c ho hcov hdir hc R _ Y g
  obtain ⟨D', c', ho', hcov', hdir', hc', ⟨e⟩⟩ := hb J D X c ho hcov hdir hc Y g
  have h := ha J D' Y c' ho' hcov' hdir' hc' R
  exact (quasiIso_iff_of_arrow_mk_iso _ _ ((chains R).mapArrow.mapIso e.symm)).1 h

end LateralTheory.CohomologicalPurity.TubeCut
end
end
