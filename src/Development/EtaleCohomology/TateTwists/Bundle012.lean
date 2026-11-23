module

public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvB
variable {R : Type} [CommRing R]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev]

noncomputable def evHom {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (fun α β => ev_add α β p s h U x)

theorem ev_compHom {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp [ev, Cochain.comp_v _ _ (add_zero n) _ s s h (add_zero s)]

theorem isZero_pos {E : Spc} (a : ℤ) (ha : 0 < a) : IsZero (((chains R).obj E).X a) := by
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  change -(j : ℤ) = a at hj
  omega

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (hφ : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := hφ U.unop x
  simp only [freeGen] at this
  exact this

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) x :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom f y)
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) U x :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) y)
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainsXIso_nat {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp [chainsXIso, chains, chainsN, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f p = -(p:ℤ) from rfl)]


theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have := sec_nat ((chainsXIso R E p).inv ≫ α.v _ _ h) g (freeGen R _ U x)
  rw [freeGen_res] at this
  exact this

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hαβ : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  apply Cochain.ext
  intro a b hab
  by_cases ha : 0 < a
  · exact (isZero_pos a ha).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k : ℤ) := ⟨(-a).toNat, by omega⟩
  rw [← cancel_epi (chainsXIso R E k).inv]
  exact free_ext _ _ (fun U x => hαβ k b hab U x)

theorem ev_pull {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  have e1 : ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v (-(p:ℤ)) s h =
      ((chains R).map f).f (-(p:ℤ)) ≫ α.v (-(p:ℤ)) s h := by
    rw [Cochain.comp_v _ _ (zero_add n) (-(p:ℤ)) (-(p:ℤ)) s (add_zero _) h, Cochain.ofHom_v]
  unfold ev
  rw [e1, ← Category.assoc, chainsXIso_nat, Category.assoc]
  have := freeGen_map (R := R) (f.app (op (SimplexCategory.mk p))) U x
  simp only [Sec.map] at this
  simp [this, Sx.map]

end LateralTheory.EtaleFoundations.EvB

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ?_, fun α p s h V U g x => LateralTheory.EtaleFoundations.EvB.ev_res α p s h V U g x,
    fun α β hαβ => LateralTheory.EtaleFoundations.EvB.ev_ext α β hαβ, fun f α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_pull f α p s h U x,
    fun m α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_compHom m α p s h U x⟩
  have H := LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) (E := E) p s h U x
  exact ⟨map_add (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β, map_sub (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β,
    map_zero (LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) p s h U x), fun c => map_zsmul (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) c α⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.FlipPf
open GlobalTheory.EtC

variable {R : Type} [CommRing R]

lemma negOnePow_smul_smul {M : Type*} [AddCommGroup M] (n : ℤ) (x : M) :
    ((n.negOnePow : ℤ) • ((n.negOnePow : ℤ) • x)) = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

lemma coef1 (s t : ℤ) : ((t * s).negOnePow : ℤ) * (t.negOnePow : ℤ) = ((t * (s + 1)).negOnePow : ℤ) := by
  rw [mul_add, mul_one, Int.negOnePow_add, Units.val_mul]

lemma coef2 (s t : ℤ) : (s.negOnePow : ℤ) * (((t + 1) * s).negOnePow : ℤ) = ((t * s).negOnePow : ℤ) := by
  rw [add_mul, one_mul, Int.negOnePow_add, Units.val_mul, mul_left_comm, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U s t w h := ((t * s).negOnePow : ℤ) • (μ.mul U t s w (by omega)).flip
  nat := by
    intro V U g s t w h b a
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul, μ.nat]
  leibniz := by
    intro U s t w h b a
    have hl := μ.leibniz U t s w (by omega) a b
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    dsimp only [Sec.map] at hl ⊢
    rw [hl, smul_add]
    simp only [Units.smul_def, smul_smul, coef1, coef2]
    exact add_comm _ _

def swIx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w :=
  DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) •
      ((DirectSum.lof (ULift.{1} R) _
        (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p)) ∘ₗ
        (TensorProduct.comm (ULift.{1} R) _ _).toLinearMap)

lemma sw_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    sw I J U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    ((p.1.1 * p.1.2).negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p) (b ⊗ₜ a) := by
  unfold sw
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_sw {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (flipPair μ).lift U w (sw I J U w x) = μ.lift U w x := by
  have key : (flipPair μ).lift U w ∘ₗ sw I J U w = μ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul, lift_lof]
    erw [lift_lof (flipPair μ) U w (swIx p) b a]
    simp only [flipPair, LinearMap.smul_apply, LinearMap.flip_apply]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma sw_sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    sw J I U w (sw I J U w x) = x := by
  have key : sw J I U w ∘ₗ sw I J U w = LinearMap.id := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [sw_lof, map_zsmul]
    erw [sw_lof J I U w (swIx p) b a]
    show ((p.1.1 * p.1.2).negOnePow : ℤ) • ((p.1.2 * p.1.1).negOnePow : ℤ) • _ = _
    rw [mul_comm p.1.2 p.1.1]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma res_sw (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res g w (sw I J U w x) = sw I J V w (Tens.res g w x) := by
  have key : Tens.res g w ∘ₗ sw I J U w = sw I J V w ∘ₗ Tens.res g w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul]
    unfold Tens.res
    erw [DirectSum.lmap_lof, DirectSum.lmap_lof, TensorProduct.map_tmul, TensorProduct.map_tmul, sw_lof]
    rfl
  exact LinearMap.congr_fun key x

lemma lift_sw' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens J I U w) :
    μ.lift U w (sw J I U w x) = (flipPair μ).lift U w x := by
  conv_rhs => rw [← sw_sw J I U w x]
  rw [lift_sw]

lemma isTensor_flip {I J K : Cx R} (μ : Pair I J K) (hμ : μ.IsTensor) : (flipPair μ).IsTensor := by
  obtain ⟨hs, hi⟩ := hμ
  constructor
  · intro U w y
    obtain ⟨S, hS, hP⟩ := hs U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨sw I J V w x, by rw [lift_sw, hx]⟩
  · intro U w x hx
    have h0 : μ.lift U w (sw J I U w x) = 0 := by rw [lift_sw', hx]
    obtain ⟨S, hS, hP⟩ := hi U w _ h0
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h1 : Tens.res g w (sw J I U w x) = 0 := hP V g hg
    show Tens.res g w x = 0
    rw [← sw_sw J I U w x, res_sw, h1, map_zero]

end LateralTheory.EtaleFoundations.FlipPf

theorem LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  intro R _ I J K μ
  refine ⟨LateralTheory.EtaleFoundations.FlipPf.flipPair μ, ?_, ?_, LateralTheory.EtaleFoundations.FlipPf.isTensor_flip μ⟩
  · intro U s t w h a b
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
  · intro U s t w h b a
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
    rw [mul_comm s t]
    exact (LateralTheory.EtaleFoundations.FlipPf.negOnePow_smul_smul _ _).symm
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCupCompatAlexanderWhitneyCocycleSpec : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

theorem etale_cochain_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (add_zero n) (-(p : ℤ)) s s h (add_zero s), Cochain.ofHom_v]
  rfl

theorem etale_cocycle_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (zcomp α (Cocycle.ofHom m) (add_zero n)).1 p s h U x =
      Sec.map (m.f s) (ev α.1 p s h U x) :=
  etale_cochain_comp_hom_evaluation_eq_map m α.1 p s h U x

theorem etale_cup_compatible_with_coefficient_maps_of_spec (hspec : EtaleCupCompatAlexanderWhitneyCocycleSpec) : EtaleCupProductNaturalInCoefficients := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, hγ⟩ := (hspec R μ hk).1 α β
  rw [(hspec R μ hk).2 α β γ hγ, cpost_mk, cpost_mk, cpost_mk]
  symm
  apply (hspec R ν hk).2
  intro N w h U x
  rw [etale_cocycle_comp_hom_evaluation_eq_map, hγ N w h U x]
  simp only [Sec.map]

  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, etale_cocycle_comp_hom_evaluation_eq_map, etale_cocycle_comp_hom_evaluation_eq_map]
  congr 1
  exact hc U _ _ w _ _ _

end LateralTheory.EtaleFoundations
end
