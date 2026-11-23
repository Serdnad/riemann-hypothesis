module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle017
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

def kap (ξ : Spec (CommRingCat.of (FractionRing V))) :
    FractionRing V →+* (Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

omit [IsDiscreteValuationRing V] in
theorem gs_scal (ξ : Spec (CommRingCat.of (FractionRing V))) (c : FractionRing V) :
    gs (𝟙 _) ξ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) = kap ξ c := by
  rw [gs_eq _ ξ ⊤ trivial]
  rfl

def SV (ϖ : V) (ξ : Spec (CommRingCat.of (FractionRing V)))
    (s : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ)ˣ) (n : ℤ) : Prop :=
  ∃ c, HasVal ϖ c n ∧ s.val = kap ξ c

theorem SV.mul (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s t} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ t m) : SV ϖ ξ (s * t) (n + m) := by
  obtain ⟨c, ⟨u, hu⟩, hc⟩ := hs
  obtain ⟨d, ⟨v, hv⟩, hd⟩ := ht
  refine ⟨c * d, ⟨u * v, ?_⟩, by rw [Units.val_mul, hc, hd, map_mul]⟩
  rw [hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      hϖ.ne_zero), Units.val_mul, map_mul]; ring

theorem SV.prod (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {T : Type} (S : Finset T)
    {s : T → _} {n : T → ℤ} (hs : ∀ i, SV ϖ ξ (s i) (n i)) : SV ϖ ξ (∏ i ∈ S, s i) (∑ i ∈ S, n i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, ⟨1, by simp⟩, by simp⟩
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]; exact (hs a).mul hϖ ih

theorem SV.unique (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ s m) : n = m := by
  obtain ⟨c, hc, e⟩ := hs
  obtain ⟨d, hd, e'⟩ := ht
  have : c = d := (kap ξ).injective (e.symm.trans e')
  exact hasVal_unique hϖ hc (this ▸ hd)

theorem sv_unit (ξ : Spec (CommRingCat.of (FractionRing V))) (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (closedPoint V : Spec (CommRingCat.of V)) ∈ U) (a : Γ(Spec (CommRingCat.of V), U)ˣ) :
    SV ϖ ξ (gm (jK V) ξ U a) 0 := by
  obtain rfl := eq_top_of_closedPoint_mem U hU
  refine ⟨algebraMap V _ ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a : Vˣ) : V),
    ⟨_, by rw [zpow_zero, _root_.one_mul]⟩, ?_⟩
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  refine congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom
    (Eq.trans ?_ hnat.symm)
  rw [Iso.hom_inv_id_apply]
  rfl

theorem sv_unit' (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} (p : Spec (CommRingCat.of V) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint V) ∈ U) (a : Γ(X, U)ˣ) :
    SV ϖ ξ (gm (jK V ≫ p) ξ U a) 0 := by
  have h : p (jK V ξ) ∈ U := by
    have := eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK V ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK V) p ξ U h]
  exact sv_unit ξ _ hU _

theorem sv_gen (hϖ : Irreducible ϖ) (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X}
    {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) {J} (hJ : Good L ξ J)
    (hc : ∀ k, φ k (closedPoint V) ∈ L.U (J (jK V ≫ φ k))) : SV ϖ ξ (val t (𝟙 _) ξ J) n := by
  obtain ⟨e, c, -, hcv, H⟩ := SectionScalarValuation.exists_val_genHasVal hn
  have H1 := H _ (𝟙 _) ξ J hJ
  rw [gs_scal, Category.id_comp] at H1
  obtain ⟨d, ⟨u, hu⟩, hd⟩ : SV ϖ ξ (val e (jK V) ξ J) 0 :=
    sv_unit ξ _ (Set.mem_iInter.2 hc) _
  refine ⟨c * d, ?_, by rw [H1, hd, map_mul]⟩
  rw [hu, zpow_zero, _root_.one_mul]
  exact hasVal_mul_unit hcv u

theorem exists_goodV (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of V) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint V) ∈ L.U (J (jK V ≫ p)) := by
  haveI : IsDominant (jK V) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of V) ⟶ X => exists_chart hL (p (closedPoint V))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of V) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK V ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK V) h))
    (fun p => by
      have := eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK V ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

section Box

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem mapsAt_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n)))
    (H : GeneratorPullback.MapsAt M M' pr w p n a b) (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    val b (𝟙 _) y J = bw w p y (fun i => J (p ≫ pr i)) (J' p) ^ n * val a (𝟙 _) y J' := by
  have hm' : p y ∈ LB.wchart M pr (fun i => J (p ≫ pr i)) ⊓ M'.U (J' p) :=
    ⟨Set.mem_iInter.2 fun i => hJ (p ≫ pr i), hJ' p⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J (p ≫ pr i), J' p) := hm'
  have E := congrArg (gm (𝟙 Y) y _) (H (fun i => J (p ≫ pr i)) (J' p))
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])]
  refine (gm_res _ y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))))
  exact gm_pull (𝟙 Y) p y _ hm' _

theorem val_finProdGen {K I : Type} [Fintype K] [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good M z J) :
    val (GeneratorPullback.finProdGen M φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Box

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → QForm.IsQ D'.toPre ϖ (fun x => ∑ i, Q (pD.xe x i)) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ x
  obtain ⟨m, hm⟩ := QForm.exists_QVal hϖ D' x
  suffices h : m = ∑ i, Q (pD.xe x i) by rw [h] at hm; exact hm
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_goodV ξ D.toPre.P.isLB D.toPre.P.A.hom
  obtain ⟨J', hJ', hJc'⟩ := exists_goodV ξ D'.toPre.P.isLB D'.toPre.P.A.hom
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi x
  have e1 := mapsAt_val pD.w _ _ _ b hb ξ hJ hJ'
  have e2 := (val_corr hJ hcorr (𝟙 _)).trans (val_finProdGen _ _ _ _ _ hJ)
  have s1 : SV ϖ ξ (val (D'.toPre.psi x) (𝟙 _) ξ J') m :=
    sv_gen hϖ ξ hm hJ' fun _ => hJc' _ (Over.w _)
  have s2 := SV.prod hϖ Finset.univ fun i : Fin j =>
    sv_gen hϖ ξ (hQ (pD.xe x i)) hJ fun _ => hJc _ (Over.w _)
  have hx : D'.toPre.xK x = jK V ≫ (D'.toPre.c x).left := QForm.ptK_eq _ x
  have s3 : SV ϖ ξ (bw pD.w (D'.toPre.xK x) ξ (fun i => J (D'.toPre.xK x ≫ (pD.pw.pr i).left))
      (J' (D'.toPre.xK x))) 0 := by
    rw [hx]
    refine sv_unit' ξ _ _ ?_ _
    refine ⟨Set.mem_iInter.2 fun i => ?_, hJc' _ (Over.w _)⟩
    exact hJc ((D'.toPre.c x).left ≫ (pD.pw.pr i).left) (QForm.over_sec _ _)
  have s4 := s3.mul hϖ s2
  rw [← e2, zero_add] at s4
  have e3 := e1
  rw [zpow_neg_one, eq_inv_mul_iff_mul_eq] at e3
  exact s1.unique hϖ (e3 ▸ s4)

end GlobalTheory.QBox
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxSpan

theorem span_eq_top_of_card {C M : Type} [CommRing C] (hC : IsField C) [AddCommGroup M] [Module C M]
    {I I' : Type} [Fintype I] [Fintype I'] (b : I → M) (hli : LinearIndependent C b)
    (hsp : Submodule.span C (Set.range b) = ⊤) (v : I' → M) (hv : LinearIndependent C v)
    (hc : Fintype.card I' = Fintype.card I) : Submodule.span C (Set.range v) = ⊤ := by
  let _ : Field C := hC.toField
  have hb : Module.finrank C M = Fintype.card I :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
  have _ : Module.Finite C M := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  exact hv.span_eq_top_of_card_eq_finrank' (hc.trans hb.symm)

theorem exists_basis (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [CommRing F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) :
    ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (Over.mk q), LinearIndependent Γ((Over.mk q).left, ⊤) b ∧
      Submodule.span Γ((Over.mk q).left, ⊤) (Set.range b) = ⊤ := by
  obtain ⟨V, hpV, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn default
  have hbo : (baseOver (Spec (CommRingCat.of K))).hom = 𝟙 _ := rfl
  have hr : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : q x = default := Subsingleton.elim _ _
    rw [this]
    exact hpV
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ V.toScheme, t ≫ V.ι ≫ (baseOver (Spec (CommRingCat.of K))).hom = q := by
    refine ⟨IsOpenImmersion.lift V.ι q hr, ?_⟩
    rw [hbo]
    erw [Category.comp_id]
    exact IsOpenImmersion.lift_fac _ _ _
  unfold LPow at b
  choose b' hb' using fun i => GlobalTheory.IndivisibleSection.exists_pull_chart (b i) (homAt (V := V) t ▷ P.A).left
    (fun _ => (snd (baseAt (V := V) t) P.A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨hli, hsp⟩ := hb F t b' (fun i j => hb' i j _)
  exact ⟨fun i => SecM.ofSec P.A (b' i), hli, hsp⟩

theorem comb_apply {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) (T : Over S) {I : Type}
    [Fintype I] (c : I → Γ(T.left, ⊤)) (v : I → SecM A L a T) (jj) :
    (∑ l, c l • v l).1 jj = ∑ l, liftFun A _ (c l) * (v l).1 jj := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

private theorem ΓSpecIso_inv_hom_apply (F : Type) [CommRing F] (x : Γ(Spec (CommRingCat.of F), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end BoxSpan


open BoxSpan in
theorem boxProduct_span : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ s : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), ∃ (n : ℕ) (c : Fin n → F) (t : Fin n → Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' : Fin n → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ l, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' l) r z J' = ∏ i, Geo.Tor.sval (t l i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) ∧ ∀ jj, s.f jj = ∑ l, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t' l).f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk s
  obtain ⟨b, hbi, -⟩ := exists_basis hL.secBaseChange A k hk F (TFK (R := R) F).hom
  obtain ⟨b', hbi', hbs'⟩ := exists_basis hL.secBaseChange A' k hk F (TFK (R := R) F).hom
  let σ : Fin (k ^ A.g) → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left)
      (fun _ => (k : ℤ))) := fun l => ⟨(b l).1, fun i i' => (b l).2 i i'⟩
  have hb : ∀ c : Fin (k ^ A.g) → F, (∀ jj, ∑ l, liftFun A.A _
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (σ l).f jj = 0) → c = 0 := by
    intro c hc
    have h0 := Fintype.linearIndependent_iff.mp hbi
      (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) (by
        apply Subtype.ext
        funext jj
        exact (comb_apply A.A A.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) _ b jj).trans (hc jj))
    funext l
    have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (h0 l)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h1
    exact h1
  choose t' ht' using fun a : Fin j → Fin (k ^ A.g) =>
    exists_boxSec_pow_ext R j A A' pA F k (fun i => σ (a i))
  have hind := boxProduct_linearIndependent R j A A' pA F k (k ^ A.g) σ hb t' ht'
  have hli : LinearIndependent Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
      (fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hc := hind (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g a)) (by
      intro jj
      have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
      have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
        (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h2
      exact congrArg (fun x => liftFun (T := TFK (R := R) F) A'.A _ x * (t' a).f jj) (ΓSpecIso_inv_hom_apply F (g a)))
    have h2 := congrFun hc a
    rw [Pi.zero_apply] at h2
    rw [← ΓSpecIso_inv_hom_apply F (g a), h2, map_zero]
  have hfield : IsField Γ((Over.mk (TFK (R := R) F).hom).left, ⊤) :=
    MulEquiv.isField (Field.toIsField F)
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv
  have hcard : Fintype.card (Fin j → Fin (k ^ A.g)) = Fintype.card (Fin (k ^ A'.g)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, polAV_g_of_isPowPolAV _ j A A' pA, ← pow_mul,
      mul_comm]
    exact (Fintype.card_fin _).symm
  have hspan := span_eq_top_of_card hfield b' hbi' hbs' _ hli hcard
  have hmem : (SecM.ofSec A'.A s : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom)) ∈
      Submodule.span Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
        (Set.range fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hmem
  let e := Fintype.equivFin (Fin j → Fin (k ^ A.g))
  refine ⟨Fintype.card (Fin j → Fin (k ^ A.g)), fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g (e.symm l)),
    fun l i => σ (e.symm l i), fun l => t' (e.symm l), fun l => ht' (e.symm l), ?_⟩
  intro jj
  have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
  have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
    (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
  refine h2.symm.trans ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  congr 1
  exact (ΓSpecIso_inv_hom_apply F _).symm

end GlobalTheory
end
