module

public import Development.EtaleCohomology.TateTwists.Bundle005
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Development.EtaleCohomology.TateTwists.Bundle006
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    exact this.symm

theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dite_eq_left (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.pp_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x ∧ ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev (R := R) α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev (R := R) α p s h U x)

def LateralTheory.EtaleFoundations.pp_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def LateralTheory.EtaleFoundations.pp_ev_delta : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i)

namespace LateralTheory.EtaleFoundations.OpPf
variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}

theorem img_ex (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) : ∃ β, ρ.IsImage α β := by
  obtain ⟨β, hβ⟩ := hM R (E := E) (I := J) (n := n) (fun p s h U x => ρ.app U s (ev (R := S) α p s h U x)) (by
    intro p s h V U g x
    rw [ρ.nat, (hB S).2.1])
  exact ⟨β, fun p s h U x => hβ p s h U x⟩

theorem img_unique (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    {α : Cochain ((chains S).obj E) I n} {β β' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) (h' : ρ.IsImage α β') : β = β' :=
  (hB R).2.2.1 β β' (fun p s hh U x => by rw [h, h'])

theorem img_delta (hD : LateralTheory.EtaleFoundations.pp_ev_delta) (ρ : SemiMap I J) {E : Spc} {n m : ℤ} (hm : n + 1 = m)
    {α : Cochain ((chains S).obj E) I n} {β : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) : ρ.IsImage (δ n m α) (δ n m β) := by
  intro p t ht U x
  cases p with
  | zero =>
    obtain rfl : t = m := by omega
    rw [(hD R hm β U).1 x, (hD S hm α U).1 x, h, ρ.comm]
  | succ p =>
    rw [(hD R hm β U).2 p _ t rfl ht x, (hD S hm α U).2 p _ t rfl ht x]
    rw [map_add (f := _), ← ρ.comm, ← h]
    congr 1

    rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← h]

theorem img_cocycle (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) :
    ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1 := by
  obtain ⟨β, hβ⟩ := img_ex hB hM ρ α.1
  refine ⟨Cocycle.mk β (n + 1) rfl ?_, hβ⟩
  have h1 := img_delta hD ρ rfl hβ
  rw [Cocycle.δ_eq_zero] at h1
  have h0 : ρ.IsImage (0 : Cochain ((chains S).obj E) I (n + 1)) (0 : Cochain ((chains R).obj E) J (n + 1)) := by
    intro p s h U x
    rw [((hB R).1 0 0 p s h U x).2.2.1, ((hB S).1 0 0 p s h U x).2.2.1, map_zero]
  exact img_unique hB ρ h1 h0

noncomputable def img (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  (img_cocycle hB hM hD ρ α).choose

theorem img_spec (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (img hB hM hD ρ α).1 :=
  (img_cocycle hB hM hD ρ α).choose_spec

theorem img_eq (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n)
    (h : ρ.IsImage α.1 β.1) : img hB hM hD ρ α = β :=
  Cocycle.ext (img_unique hB ρ (img_spec hB hM hD ρ α) h)

noncomputable def zmap (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) (E : Spc) (n : ℤ) : Cocycle ((chains S).obj E) I n →+ CohomologyClass ((chains R).obj E) J n :=
  AddMonoidHom.mk' (fun α => CohomologyClass.mk (img hB hM hD ρ α)) (fun a b => by
    rw [← CohomologyClass.mk_add]
    congr 1
    apply img_eq
    intro p s h U x
    have ha := img_spec hB hM hD ρ a p s h U x
    have hb := img_spec hB hM hD ρ b p s h U x
    change ev (R := R) ((img hB hM hD ρ a).1 + (img hB hM hD ρ b).1) p s h U x = ρ.app U s (ev (R := S) (a.1 + b.1) p s h U x)
    rw [((hB R).1 _ _ p s h U x).1, ((hB S).1 _ _ p s h U x).1, map_add (f := _), ha, hb])

noncomputable def theOp (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom (zmap hB hM hD ρ E n) (by
    intro α hα
    obtain ⟨γ, hγ⟩ := (mem_coboundaries_iff α (n - 1) (by omega)).1 hα
    obtain ⟨γ', hγ'⟩ := img_ex hB hM ρ γ
    have h1 := img_delta hD ρ (by omega : n - 1 + 1 = n) hγ'
    rw [hγ] at h1
    have h2 := img_eq hB hM hD ρ α (Cocycle.mk (δ (n - 1) n γ') (n + 1) rfl (δ_δ _ _ _ _)) h1
    change CohomologyClass.mk (img hB hM hD ρ α) = 0
    rw [h2, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ', rfl⟩)
  nat := by
    intro E E' f n x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    change CohomologyClass.mk (zcomp _ (img hB hM hD ρ α) (zero_add n)) =
      CohomologyClass.mk (img hB hM hD ρ (zcomp _ α (zero_add n)))
    congr 1
    symm
    apply img_eq
    intro p s h U y
    change ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp (img hB hM hD ρ α).1 (zero_add n)) p s h U y =
      ρ.app U s (ev (R := S) ((Cochain.ofHom ((chains S).map f)).comp α.1 (zero_add n)) p s h U y)
    rw [(hB R).2.2.2.1, (hB S).2.2.2.1, img_spec hB hM hD ρ α]

end LateralTheory.EtaleFoundations.OpPf

open LateralTheory.EtaleFoundations.OpPf in
theorem LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk)
    (hD : LateralTheory.EtaleFoundations.pp_ev_delta) : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  intro S R _ _ I J ρ
  refine ⟨fun E n α => img_cocycle hB hM hD ρ α, fun E n α β h => ?_⟩
  have hc : ∃ c : NatOp I J, ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) β.1 p s h U x = ρ.app U s (ev (R := S) α.1 p s h U x)) →
      c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
    refine ⟨theOp hB hM hD ρ, fun E n α β h => ?_⟩
    change CohomologyClass.mk (img hB hM hD ρ α) = CohomologyClass.mk β
    rw [img_eq hB hM hD ρ α β h]
  exact pick_spec hc E n α β h
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_sheaf_section_locally_iff_of_presheaf_facts : EtaleLocalIffAffineEtaleCoverPointwise := by
  intro U P hP
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS
    obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
    let 𝒱 := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := 𝒱.covers y
    refine ⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩
    · have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    · simp only [Scheme.Hom.comp_apply, hz, hy]
    · exact hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hA hE hx hPg using h
    refine ⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩
    · refine (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩
      rintro W k ⟨x⟩
      exact hPg x
    · intro W k hk
      exact hk

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem sec_glue_forget_isSheaf (R : Type) [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have : PreservesLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    preservesLimitsOfSize_shrink.{1, 0, 0, 1} _
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology.{0} F.obj
      (forget (ModuleCat.{1} (ULift.{1} R))) F.property)

theorem etale_sheaf_sections_glue_of_forget_isSheaf : EtaleSheafSectionsSeparatedAndGlue := by
  intro R _ F U
  have hT := sec_glue_forget_isSheaf R F
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨S, hS, h⟩ := hab
    exact (hT S hS).isSeparatedFor.ext (fun V g hg => h V g hg)
  · intro S hS s hs
    let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
      fun V g hg => s V g hg
    have hc : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨t, ht, -⟩ := hT S hS x hc
    exact ⟨t, fun V g hg => ht g hg⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

def tensPure {R : Type} [CommRing R] {I J : Cx R} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
    (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)

def EtaleSheafTensorComplexExists : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R)
    (φ : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
      Sec.res g (φ U w x) = φ V w (Tens.res g w x)) ∧
    (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (K.d w (w + 1)) (φ U w (tensPure s t w h a b)) =
        φ U (w + 1) (tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b) +
        s.negOnePow • φ U (w + 1) (tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b))) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, φ V w x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), φ U w x = 0 → Loc U fun _ g => Tens.res g w x = 0)

theorem etale_tensor_complex_exists_of_sheaf_tensor_complex (hS : EtaleSheafTensorComplexExists) : EtaleComplexTensorPairingExists := by
  intro R _ I J
  obtain ⟨K, φ, hnat, hd, hsurj, hinj⟩ := hS R I J
  let μ : Pair I J K :=
    { mul := fun U s t w h => (TensorProduct.mk (ULift.{1} R) _ _).compr₂
          ((φ U w).comp (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
            (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩))
      nat := by
        intro V U g s t w h a b
        have := hnat g w (tensPure s t w h a b)
        simpa [tensPure, Tens.res, DirectSum.lmap_lof] using this
      leibniz := by
        intro U s t w h a b
        simpa [tensPure] using hd U s t w h a b }
  have hlift : ∀ U w, μ.lift U w = φ U w := by
    intro U w
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp [Pair.lift, μ]
  refine ⟨K, μ, ?_, ?_⟩
  · intro U w y
    simpa [hlift] using hsurj U w y
  · intro U w x hx
    exact hinj U w x (by simpa [hlift] using hx)

end LateralTheory.EtaleFoundations
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResSecPf

variable (R : Type) [CommRing R]

noncomputable abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

lemma exact_pos (F : Shv R) (m n k : ℤ) (hn : 0 < n) (hm : m + 1 = n) (hk : n + 1 = k) :
    (ShortComplex.mk ((res R F).d m n) ((res R F).d n k) (by simp)).Exact := by
  have h1 : (res R F).ExactAt n := by
    unfold res
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1

lemma subsing (F : Shv R) (U : Scheme.{0}) (n : ℤ) (hn : n < 0) :
    Subsingleton (Sec ((res R F).X n) U) := by
  have hz : IsZero ((res R F).X n) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have := (hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  constructor
  intro a b
  have e : ∀ x : Sec ((res R F).X n) U, x = 0 := by
    intro x
    have := congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)
    simpa [Sec.map] using this
  rw [e a, e b]

lemma resι_e (F : Shv R) :
    resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom = (injectiveResolution F).ι.f 0 := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

lemma d01' (F : Shv R) : ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
    (injectiveResolution F).cocomplex.d 0 1 = (injectiveResolution F).cochainComplex.d 0 1 ≫
      ((injectiveResolution F).cochainComplexXIso 1 1 rfl).hom := by
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  simp

lemma etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  unfold resι res
  refine (Category.assoc _ _ _).trans ?_
  erw [h]
  simp

noncomputable abbrev S0 (F : Shv R) : ShortComplex (Shv R) := ShortComplex.mk _ _ (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)

lemma etaleSheaf_injectiveResolution_initial_shortComplex_exact (F : Shv R) : (S0 R F).Exact := by
  let I := injectiveResolution F
  have hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork
  refine (ShortComplex.exact_iff_of_iso ?_).2 hN
  refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_
  · exact (Category.id_comp _).trans (resι_e R F).symm
  · exact d01' R F

lemma mono_resι_var (F : Shv R) : Mono (resι R F) := by
  have : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h := resι_e R F
  have : Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom) := by
    rw [h]; assumption
  exact mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom

def exact_loc : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact →
  ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

lemma part1 (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U) :
    Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z := by
  constructor
  · intro hz
    have hE : ((S0 R F).map (secF R U)).Exact :=
      (etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance
    rw [ShortComplex.moduleCat_exact_iff] at hE
    exact hE z hz
  · rintro ⟨a, rfl⟩
    have := congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)
    simpa [Sec.map] using this

lemma part2 (F : Shv R) (U : Scheme.{0}) : Function.Injective (Sec.map (resι R F) (U := U)) := by
  have := mono_resι_var R F
  have : Mono ((secF R U).map (resι R F)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

end LateralTheory.EtaleFoundations.ResSecPf

open LateralTheory.EtaleFoundations.ResSecPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_sections_exact_of_local_exactness (hL : exact_loc) : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact := by
  intro R _ F U
  refine ⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩
  intro m n k hn hm z hk hz
  exact hL R _ (exact_pos R F m n k hn hm hk) U z hz
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ShfLocPf

theorem etale_sheaf_sections_eq_of_locally_eq : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    intro V g hg
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, ht⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]
  · intro F φ
    refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩
    · exact toSheafify_sheafifyLift Scheme.etaleTopology φ F.property
    · intro ψ hψ
      ext1
      exact sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ

end LateralTheory.EtaleFoundations.ShfLocPf
end
