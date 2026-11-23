module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.EtaleCohomology.EtaleSheaves.AdjoinRootExtension.AdjoinRootOfInjective
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Development.EtaleCohomology.EtaleSheaves.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
import Development.EtaleCohomology.EtaleSheaves.Bundle009

@[expose] public section

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.GlueRelPfNat
variable (R : Type) [CommRing R]

theorem map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff φ₁ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.map, mappingCone.inl_desc,
      Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inl_fst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      mappingCone.inl_fst]
    simp
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp [mappingCone.map]

end LateralTheory.E.GlueRelPfNat
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex.HomComplex

namespace LateralTheory.E.GlueRelPf

def obs (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) : Ht q U m i →+ Hrel (ZMod q) u (tw q i) (m + 1) :=
  HK.pre (ZMod q) (CochainComplex.mappingCone.fst ((chains (ZMod q)).map u)) (tw q i) m (m + 1) (add_comm 1 m)

def ConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ),
  Function.Exact (HK.pull R φ F m) (HK.pre R (CochainComplex.mappingCone.fst φ) F m (m + 1) (add_comm 1 m))

end LateralTheory.E.GlueRelPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf
end
end

section

noncomputable section
open CategoryTheory Polynomial

namespace LateralTheory.E.AICExtPf

def towerObj (C : CommRingCat.{0}) : ℕ → CommRingCat.{0}
  | 0 => C
  | n + 1 => CommRingCat.of (StepRing (towerObj C n))

def towerMap (C : CommRingCat.{0}) (n : ℕ) : towerObj C n ⟶ towerObj C (n + 1) :=
  CommRingCat.ofHom (stepHom (towerObj C n))

abbrev towerF (C : CommRingCat.{0}) : ℕ ⥤ CommRingCat.{0} := Functor.ofSequence (towerMap C)

def fm (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : towerObj C i →+* towerObj C j :=
  ((towerF C).map (homOfLE h)).hom

instance (C : CommRingCat.{0}) :
    DirectedSystem (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h) where
  map_self i x := by
    have h1 : (towerF C).map (homOfLE (le_refl i)) = 𝟙 _ :=
      (congrArg (towerF C).map (Subsingleton.elim _ _)).trans ((towerF C).map_id i)
    exact congrArg (fun φ : (towerF C).obj i ⟶ (towerF C).obj i => φ.hom x) h1
  map_map k j i hij hjk x := by
    show ((towerF C).map (homOfLE hij) ≫ (towerF C).map (homOfLE hjk)).hom x = _
    rw [← Functor.map_comp, homOfLE_comp]; rfl

lemma fm_succ (C : CommRingCat.{0}) (n : ℕ) (h : n ≤ n + 1) : fm C n (n + 1) h = stepHom (towerObj C n) := by
  have := Functor.ofSequence_map_homOfLE_succ (towerMap C) n
  simp only [fm]
  rw [this]; rfl

lemma fm_comp_succ (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) (h' : i ≤ j + 1) :
    fm C i (j + 1) h' = (stepHom (towerObj C j)).comp (fm C i j h) := by
  rw [← fm_succ C j (Nat.le_succ j)]
  show ((towerF C).map (homOfLE h')).hom =
    ((towerF C).map (homOfLE h) ≫ (towerF C).map (homOfLE (Nat.le_succ j))).hom
  rw [← Functor.map_comp, homOfLE_comp]

lemma fm_injective (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : Function.Injective (fm C i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro x y hxy; simpa [DirectedSystem.map_self (f := fun i j h => fm C i j h)] using hxy
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact (stepHom_injective _).comp ih

lemma fm_isIntegral (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : (fm C i j h).IsIntegral := by
  induction j, h using Nat.le_induction with
  | base =>
    intro x
    have e : ∀ y, fm C i i le_rfl y = y := fun y => DirectedSystem.map_self (f := fun i j h => fm C i j h) y
    exact ⟨X - Polynomial.C x, monic_X_sub_C x, by simp [eval₂_sub, e]⟩
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact RingHom.IsIntegral.trans _ _ ih (stepHom_isIntegral _)

abbrev Lim (C : CommRingCat.{0}) : Type :=
  Ring.DirectLimit (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h)

lemma of_comp (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) :
    (Ring.DirectLimit.of _ (fun i j h => fm C i j h) j).comp (fm C i j h) =
      Ring.DirectLimit.of _ (fun i j h => fm C i j h) i := by
  ext x
  exact Ring.DirectLimit.of_f (G := fun i => (towerObj C i : Type)) (f := fun i j h => fm C i j h) h x

theorem lim_aic (C : CommRingCat.{0}) : GlobalTheory.EtC.AIC (Lim C) := by
  intro p hp hd
  obtain ⟨n, q, hq⟩ := Ring.DirectLimit.Polynomial.exists_of p
  have hinj := Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) n
  have hqm : q.Monic := by
    apply hinj
    rw [← leadingCoeff_map_of_injective hinj, hq, hp.leadingCoeff, map_one]
  have hqd : 0 < q.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hq]; exact hd
  obtain ⟨a, ha'⟩ : ∃ a : towerObj C (n + 1), (q.map (fm C n (n + 1) (Nat.le_succ n))).eval a = 0 := by
    rw [fm_succ]; exact step_has_root (towerObj C n) q hqm hqd
  refine ⟨Ring.DirectLimit.of _ (fun i j h => fm C i j h) (n + 1) a, ?_⟩
  rw [← hq, ← of_comp C n (n + 1) (Nat.le_succ n), ← Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, ha', map_zero]

theorem AICExt_of : LateralTheory.E.t_E3Cut.AICExt := by
  intro C
  refine ⟨CommRingCat.of (Lim C), CommRingCat.ofHom (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0),
    ?_, ?_, lim_aic C⟩
  · intro x
    obtain ⟨n, y, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨p, hp, hy⟩ := fm_isIntegral C 0 n (Nat.zero_le n) y
    refine ⟨p, hp, ?_⟩
    change eval₂ (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0) _ p = 0
    rw [← of_comp C 0 n (Nat.zero_le n), ← hom_eval₂, hy, map_zero]
  · exact Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) 0

end LateralTheory.E.AICExtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StandardPushout

variable {S : Type} [CommRing S] (f g : S)

def descR {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) : Localization.Away (f * g) →+* T :=
  IsLocalization.Away.lift (f * g) (g := a.comp (algebraMap S _)) (by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit f).map a
    · rw [h]; exact (IsLocalization.Away.algebraMap_isUnit g).map b)

theorem descR_alg {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) (s : S) :
    descR f g a b h (algebraMap S _ s) = a (algebraMap S _ s) :=
  IsLocalization.lift_eq _ _

theorem rL_alg (s : S) : LateralTheory.E.t_E1Cut.rL f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayRight_eq f g s

theorem rR_alg (s : S) : LateralTheory.E.t_E1Cut.rR f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayLeft_eq g f s

theorem isPushout_away :
    IsPushout (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
      (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)) (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g)) := by
  have hw : CommRingCat.ofHom (algebraMap S (Localization.Away f)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)
      = CommRingCat.ofHom (algebraMap S (Localization.Away g)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g) := by
    ext x
    simp [rL_alg, rR_alg]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  have hc : ∀ s : PushoutCocone (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g))),
      s.inl.hom.comp (algebraMap S _) = s.inr.hom.comp (algebraMap S _) := fun s => by
    have := congrArg CommRingCat.Hom.hom s.condition
    simpa using this
  refine PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (descR f g s.inl.hom s.inr.hom (hc s)))
    ?_ ?_ ?_
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp [rL_alg, descR_alg]
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext x
    have := congrArg (fun φ => φ x) (hc s)
    simp only [RingHom.comp_apply] at this
    simp [rR_alg, descR_alg, this]
  · intro s m h1 _
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (algebraMap S (Localization.Away f) x)) h1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, rL_alg] at this
    simp [descR_alg, this]

instance constPreserves (J : Type) [SmallCategory J] :
    PreservesLimitsOfShape J (SimplicialObject.const PSh) := by
  apply preservesLimitsOfShape_of_evaluation
  intro k
  exact preservesLimitsOfShape_of_natIso
    (NatIso.ofComponents (fun X => Iso.refl X) (by intros; rfl) :
      𝟭 PSh ≅ SimplicialObject.const PSh ⋙ (evaluation _ _).obj k)

instance schPreserves (J : Type) [SmallCategory J] : PreservesLimitsOfShape J sch := by
  unfold sch
  infer_instance

theorem isPullback_sp :
    IsPullback (spMap (LateralTheory.E.t_E1Cut.rL f g)) (spMap (LateralTheory.E.t_E1Cut.rR f g))
      (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away f g)).map sch

end LateralTheory.E.StandardPushout

open LateralTheory.E.StandardPushout in
theorem LateralTheory.E.MVPf.StdPB_of : LateralTheory.E.MVPf.StdPB := by
  intro S _ f g
  have h := isPullback_sp f g
  exact ⟨h.isoPullback.hom, inferInstance, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PiecesPf

lemma sq1 {T S C' C : Type} [CommRing T] [CommRing S] [CommRing C'] [CommRing C]
    (a : T →+* C') (π : T →+* S) (ρ : C' →+* C) (b : S →+* C) (hρ : Function.Surjective ρ) (hπ : Function.Surjective π)
    (hcomm : ρ.comp a = b.comp π) (hker : RingHom.ker ρ = (RingHom.ker π).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom π) (CommRingCat.ofHom ρ) (CommRingCat.ofHom b) := by
  have w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b := by
    ext x; exact congrArg (fun f : T →+* C => f x) hcomm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)
  · intro s
    refine CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)
    rw [hker, Ideal.map_le_iff_le_comap]
    intro t ht
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    simp only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢
    rw [h1, ht, map_zero]
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact RingHom.liftOfSurjective_comp_apply ρ hρ _ x
  · intro s
    ext x
    obtain ⟨t, rfl⟩ := hπ x
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢
    rw [← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]
    exact h1
  · intro s m hm _
    ext x
    obtain ⟨y, rfl⟩ := hρ x
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.liftOfSurjective_comp_apply]
    have := congrArg (fun f => f.hom y) hm
    simpa using this

theorem Pieces_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) :
    LateralTheory.E.FinEtSectionPf.Pieces := by
  intro _ _ S C _ _ _ _ hQA
  obtain ⟨T, _, _, π, hAIC, hπ⟩ := hQA
  obtain ⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩ := hL T S C π hπ
  have := hEt
  obtain ⟨n, e', he', hoi⟩ := hA T C' hAIC
  refine ⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩
  let fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j)) :=
    IsLocalization.Away.map _ _ ρ (e' j)
  have : IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j))) := by
    rw [Submonoid.map_powers]; infer_instance
  have H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ := IsLocalization.map_comp _
  have sq2 := CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))
  have sq := (sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ sq
  have hj := hoi j
  rw [CommRingCat.ofHom_comp] at hj
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj
  rw [CommRingCat.ofHom_comp]
  exact this

end LateralTheory.E.PiecesPf
end
end

section

namespace LateralTheory.E.LJacPf

theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := by simpa only [Ideal.jacobson_bot] using hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.Deg0Pf

theorem exists_prim (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hA : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  obtain ⟨z, hz⟩ : ∃ z : S, (Polynomial.cyclotomic q S).eval z = 0 := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact hA _ (Polynomial.cyclotomic.monic q S) (by
        rw [Polynomial.natDegree_cyclotomic]
        exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (ζ : Prim q A) : (ζ.map f).map g = ζ.map (g.comp f) := rfl

theorem rL_comp {S : Type} [CommRing S] (f g : S) :
    (rL f g).comp (algebraMap S (Localization.Away f)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_comp {S : Type} [CommRing S] (f g : S) :
    (rR f g).comp (algebraMap S (Localization.Away g)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem Deg0_of : LateralTheory.E.AcycQAPf.Deg0 := by
  intro hQ hH hL h9 q _ i S _ hS hq f g hfg c
  obtain ⟨e, he⟩ := hH h9 q i
  obtain ⟨ζ⟩ := exists_prim q S (hQ S hS).1 hq
  obtain ⟨a, b, hab⟩ := hL q S hS f g hfg ((e _ (ζ.map (algebraMap S (Localization.Away (f * g))))).symm c)
  refine ⟨e _ (ζ.map (algebraMap S (Localization.Away f))) a, e _ (ζ.map (algebraMap S (Localization.Away g))) b, ?_⟩
  rw [he, he, prim_map_comp, prim_map_comp, rL_comp, rR_comp, ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.Deg0Pf
end
end
