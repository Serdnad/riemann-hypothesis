module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.Bundle030
public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle022
public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle043
import Development.EtaleCohomology.TateTwists.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.EtaleCohomology.EtaleSheaves.Bundle037

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfB
open LateralTheory.E.LeafTw0LocGenPfA

theorem geo {q : ℕ} [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W h => ∃ a : (ZMod q)ˣ, h.appTop ξ.1 = (h.appTop ζ.1) ^ (a : ZMod q).val := by
  classical
  have key : ∀ x : V, ∃ (Wx : V.Opens) (_ : x ∈ Wx) (a : (ZMod q)ˣ),
      V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op ξ.1 =
        V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op (ζ.1 ^ (a : ZMod q).val) := by
    intro x
    have hq : IsUnit ((q : V.presheaf.stalk x)) := by
      simpa using ζ.2.1.map (V.presheaf.germ ⊤ x trivial).hom
    have hr : ∀ z : Γ(V, ⊤), Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
        Polynomial.aeval ((V.presheaf.germ ⊤ x trivial).hom z) (Polynomial.cyclotomic q ℤ) = 0 := by
      intro z hz
      have h := Polynomial.aeval_algHom_apply (V.presheaf.germ ⊤ x trivial).hom.toIntAlgHom z (Polynomial.cyclotomic q ℤ)
      rw [hz, map_zero] at h
      exact h
    obtain ⟨a, ha⟩ := local_pow hq (hr _ ζ.2.2) (hr _ ξ.2.2)
    have h2 : (V.presheaf.germ ⊤ x trivial).hom ξ.1 = (V.presheaf.germ ⊤ x trivial).hom (ζ.1 ^ (a : ZMod q).val) := by
      rw [map_pow]; exact ha
    obtain ⟨Wx, hx, i1, i2, he⟩ := TopCat.Presheaf.germ_eq V.presheaf (U := ⊤) (V := ⊤) x trivial trivial _ _ h2
    refine ⟨Wx, hx, a, ?_⟩
    have e1 : i1 = homOfLE le_top := Subsingleton.elim _ _
    have e2 : i2 = homOfLE le_top := Subsingleton.elim _ _
    subst e1 e2
    exact he
  choose Wx hx a ha using key
  have fin : ∀ (x : V) {W : Scheme.{0}} (g' : W ⟶ (Wx x).toScheme),
      (g' ≫ (Wx x).ι).appTop ξ.1 = ((g' ≫ (Wx x).ι).appTop ζ.1) ^ (a x : ZMod q).val := by
    intro x W g'
    have hle : (Wx x).ι ''ᵁ ⊤ ≤ Wx x := by simp
    have hW : ∀ z : Γ(V, ⊤), (Wx x).ι.appTop z =
        V.presheaf.map (homOfLE hle).op (V.presheaf.map (homOfLE le_top : Wx x ⟶ ⊤).op z) := by
      intro z
      rw [Scheme.Opens.ι_appTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hW, hW, ha x]
    simp only [map_pow]
    exact map_pow (ConcreteCategory.hom (Scheme.Hom.appTop g')) _ _
  let 𝒰 : V.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers V (fun x => (Wx x).toScheme) (fun x => (Wx x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨_, Scheme.Cover.mem_grothendieckTopology 𝒰, fun W h hh => ?_⟩
  obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨a x, fin x g⟩

end LateralTheory.E.LeafTw0LocGenPfB
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

end LateralTheory.E.TruncationKernel
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf Opposite

namespace LateralTheory.E.TruncCokPf

def sq {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') :
    Arrow.mk (yoneda.map (Spec.map u)) ⟶ Arrow.mk (yoneda.map (Spec.map e)) :=
  Arrow.homMk (yoneda.map (Spec.map φ'')) (yoneda.map (Spec.map φ')) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h])

def LevelLow (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') : Prop :=
  ∀ (p : ℕ) (m : ℤ), m < n →
    (∀ k : ℤ, k + 1 = m → Function.Surjective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F k)) ∧
    Function.Injective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F m)

def Levels : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''), Et e → SpS e → P E (d ≫ e) →
    LevelLow (ZMod q) (tw q i) n e φ' u φ'' hpo.w

end LateralTheory.E.TruncCokPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceDegeneracyIdentities

theorem pull_pull {E : Spc} {U : Scheme.{0}} {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (x : Sx E c U) :
    (E.map f.op).app (op U) ((E.map g.op).app (op U) x) = (E.map (f ≫ g).op).app (op U) x := by
  rw [op_comp, E.map_comp]; rfl

theorem pull_congr {E : Spc} {U : Scheme.{0}} {a b : ℕ} {f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b}
    (h : f = g) (x : Sx E b U) : (E.map f.op).app (op U) x = (E.map g.op).app (op U) x := by rw [h]

theorem f0s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 0 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem L_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (y : Sx E n U) : (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map f.op).app (op U) y) =
      ((ofCat (glCat 1)).map f.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) y) := by
  have h := L.naturality f.op
  have h2 := NatTrans.congr_app h (op U)
  first
  | exact (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h2 y)
  | exact (by simpa only [NatTrans.comp_app, types_comp_apply] using congr_fun h2 y)

theorem line_mul {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 2 U) :
    lineUnit L (y.face 1) = lineUnit L (y.sub 0 1 (by omega)) * lineUnit L (y.sub 1 1 (by omega)) := by
  unfold lineUnit Sx.face Sx.sub SimplicialObject.δ
  rw [L_nat, L_nat, L_nat]
  generalize (L.app (op (SimplexCategory.mk 2))).app (op U) y = z
  let z' : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := z
  change Matrix.GeneralLinearGroup.det (z'.map' 0 2) = Matrix.GeneralLinearGroup.det (z'.map' 0 1) * Matrix.GeneralLinearGroup.det (z'.map' 1 2)
  rw [z'.map'_comp 0 1 2, SingleObj.comp_as_mul, map_mul, mul_comm]

theorem f0s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 0 1 (by omega) = (x.face 3).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 1 1 (by omega) = (x.face 0).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 1 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem local_zero (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hC : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α) {V : Scheme.{0}}
    (x : Sx E 3 V) (a b c : (Γ(V, ⊤))ˣ) (ha : a ^ q = lineUnit L (x.sub 0 1 (by omega)))
    (hb : b ^ q = lineUnit L (x.sub 1 1 (by omega))) (hc : c ^ q = lineUnit L (x.sub 2 1 (by omega))) :
    ev (δ 2 3 α) 3 0 (by simp) V x = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
    2 (-1) 0 (by norm_num) (by norm_num) x
  refine hd.trans ?_
  have h0 : ev α 3 (-1) (by norm_num) V x = 0 :=
    LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q (-1) (by norm_num)) V _ _
  have v0 := hC.2.2 V (x.face 0) b c (by rw [f0s0]; exact hb) (by rw [f0s1]; exact hc)
  have v1 := hC.2.2 V (x.face 1) (a * b) c (by rw [f1s0, line_mul, f3s0, f3s1, mul_pow, ha, hb]) (by rw [f1s1]; exact hc)
  have v2 := hC.2.2 V (x.face 2) a (b * c) (by rw [f2s0]; exact ha) (by rw [f2s1, line_mul, f0s0, f0s1, mul_pow, hb, hc])
  have v3 := hC.2.2 V (x.face 3) a b (by rw [f3s0]; exact ha) (by rw [f3s1]; exact hb)
  rw [Fin.sum_univ_four]
  erw [h0, v0, v1, v2, v3]
  rw [mul_assoc]
  simp only [Sec.map, map_zero, zero_add]
  convert smul_zero (Int.negOnePow 3) using 2
  simp
  abel


open LateralTheory.EtaleFoundations.FirstChernUniqueness in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra := by
  intro q _ E L hi α hC U x
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine loc_imp (loc_and (root_line hr q L hi U (x.sub 0 1 (by omega)))
    (loc_and (root_line hr q L hi U (x.sub 1 1 (by omega))) (root_line hr q L hi U (x.sub 2 1 (by omega)))))
    fun V g hv => ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hv
  rw [← sub_res] at ha hb hc
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, local_zero q L α hC (x.res g) a b c ha hb hc]
  simp [Sec.res]

end LateralTheory.E.ChernCocycleFaceDegeneracyIdentities
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceFormulas

lemma δ0_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma δ2_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma face0 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ0_eq]

lemma face2 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ2_eq]

lemma glMat_face1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (y.face 1) = glMat (y.sub 1 1 (by omega)) * glMat (y.sub 0 1 (by omega)) := by
  let z : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := y
  have h1 : glMat (y.face 1) = z.map' 0 2 := rfl
  have h2 : glMat (y.sub 1 1 (by omega)) = z.map' 1 2 := rfl
  have h3 : glMat (y.sub 0 1 (by omega)) = z.map' 0 1 := rfl
  rw [h1, h2, h3, ← SingleObj.comp_as_mul, ← z.map'_comp 0 1 2]

lemma L_map {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx E n U) :
    (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map θ.op).app (op U) x) =
      ((ofCat (glCat 1)).map θ.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) x) :=
  congrArg (fun φ => φ.app (op U) x) (L.naturality θ.op)

lemma lineUnit_face1 {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.sub 0 1 (by omega)) * lineUnit L (x.sub 1 1 (by omega)) := by
  have key := glMat_face1 ((L.app (op (SimplexCategory.mk 2))).app (op U) x)
  unfold lineUnit
  unfold Sx.face Sx.sub SimplicialObject.δ at *
  rw [L_map, L_map, L_map, key, map_mul, mul_comm]

open LateralTheory.E.ChernClassRootLocalization in
lemma etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hα : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α)
    (V : Scheme.{0}) (y : Sx E 2 V) (v w : (Γ(V, ⊤))ˣ) (hv : v ^ q = lineUnit L (y.sub 0 1 (by omega)))
    (hw : w ^ q = lineUnit L (y.sub 1 1 (by omega))) : ev (δ 2 3 α) 2 1 (by simp) V y = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α V).2 1 0 1
    (by norm_num) (by norm_num) y
  have e0 : ev α 1 1 (by omega) V (y.face 0) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w) :=
    hα.2.1 V _ w (by rw [face0]; exact hw)
  have e2 : ev α 1 1 (by omega) V (y.face 2) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v) :=
    hα.2.1 V _ v (by rw [face2]; exact hv)
  have e1 : ev α 1 1 (by omega) V (y.face 1) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V (v * w)) :=
    hα.2.1 V _ (v * w) (by rw [lineUnit_face1, mul_pow, hv, hw])
  have e3 := hα.2.2 V y v w hv hw
  refine hd.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  have e3' : ev α (1 + 1) 0 (by omega) V y = kumT q V v + kumT q V w - kumT q V (v * w) := e3
  have hn : (3 : ℤ).negOnePow = -1 := by rw [Int.negOnePow_odd]; decide
  rw [e3', e0, e1, e2, hn]
  simp only [Sec.map, map_add (f := _), map_sub]
  simp
  abel

open LateralTheory.E.ChernClassRootLocalization in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles := by
  intro q _ E L hi α hα U x
  apply sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 0 1 (by omega)))
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 1 1 (by omega)))) fun V g hvw => ?_
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hvw
  rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
  rw [← ev_res]
  exact (etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots q L α hα V _ v w hv hw).trans (map_zero ((_ : Sec _ U →ₗ[_] Sec _ V))).symm

end LateralTheory.E.ChernCocycleFaceFormulas
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleEdgeCoboundary


open LateralTheory.E.ChernClassRootLocalization in
theorem sec_dd (q : ℕ) {V : Scheme.{0}} (y : Sec ((res _ (tw q 1)).X 0) V) :
    Sec.map ((res _ (tw q 1)).d 1 2) (Sec.map ((res _ (tw q 1)).d 0 1) y) = 0 := by
  have h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0 := HomologicalComplex.d_comp_d _ _ _ _
  change ((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0
  rw [h]
  rfl

theorem etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges := by
  intro q _ E L hi α hα U x
  have key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' =
      Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x') := by
    intro V x'
    have := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
      0 1 2 (by simp) (by simp) x'
    rw [this]
    simp [hα.1]
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]
  exact (map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm

end LateralTheory.E.ChernCocycleEdgeCoboundary
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafIrredPf

lemma mem_range {C0 D0 S T : Scheme.{0}} {v0 : C0 ⟶ D0} {c0 : C0 ⟶ T} {q : D0 ⟶ S} {t : T ⟶ S}
    (h : IsPullback v0 c0 q t) (x : D0) (y : T) (hxy : q x = t y) : x ∈ Set.range v0 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t) x y hxy
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← hz, ← h.isoPullback_inv_fst]
  rfl

lemma spec_gen {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (y : Sp Ω) (p : Sp R) :
    toR R y ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) ((toR R) y) p).mp
  intro a ha
  have hA : (toR R).base y = PrimeSpectrum.comap (algebraMap R Ω) y := by
    rw [Spec.map_base]; rfl
  change a ∈ ((toR R).base y).asIdeal at ha
  rw [hA] at ha
  let y' : PrimeSpectrum Ω := y
  have ha' : algebraMap R Ω a ∈ y'.asIdeal := ha
  rw [Ideal.eq_bot_of_prime y'.asIdeal, Ideal.mem_bot] at ha'
  have ha := ha'
  have : a = 0 := Subtype.ext (by simpa using ha)
  rw [this]; exact p.asIdeal.zero_mem

theorem LeafIrred_of : LeafIrred := by
  intro k _ Ω _ _ R _ C0 D0 c0 q v0 hc hq h
  obtain ⟨hint, -, -⟩ := hc
  have := hint
  have := hq
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : IrreducibleSpace C0 := irreducibleSpace_of_isIntegral C0
  have hirr : IsIrreducible (Set.range v0) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C0).image v0 v0.continuous.continuousOn
  have hdense : Dense (Set.range v0) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨c⟩ := (inferInstance : Nonempty C0)
    have hopen : IsOpen (q '' U) := q.isOpenMap U hU
    have hmem : toR R (c0 c) ∈ q '' U := (spec_gen R (c0 c) (q x)).mem_open hopen ⟨x, hx, rfl⟩
    obtain ⟨x', hx'U, hx'⟩ := hmem
    exact ⟨x', hx'U, mem_range h x' (c0 c) hx'⟩
  have : IsIrreducible (Set.univ : Set D0) := by
    rw [← hdense.closure_eq]; exact hirr.closure
  exact { isPreirreducible_univ := this.2, toNonempty := ⟨this.1.some⟩ }

end LateralTheory.E.LeafIrredPf
end
end
