module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.ConeLoc

open CochainComplex.mappingCone

private theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W t => P' W (t ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => k V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun V g hg => hT V g hg)
  · rintro W t ⟨V, e, g, hg, he, rfl⟩
    exact hT' V g hg W e he

private theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => k V g (hP V g hg)⟩

section
variable {R : Type} [CommRing R]

private theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

private theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ + ψ) a = Sec.map φ a + Sec.map ψ a := rfl

private theorem sm_sub {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ - ψ) a = Sec.map φ a - Sec.map ψ a := rfl

private theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (-φ) a = - Sec.map φ a := rfl

private theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have hn := φ.hom.naturality g.op
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hn]

private theorem ms_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem ms_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

private theorem ms_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b :=
  map_sub (φ.hom.app (op U)).hom a b

private theorem ms_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a :=
  map_neg (φ.hom.app (op U)).hom a

private theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ a b

private theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (h ≫ g) a = Sec.res h (Sec.res g a) := by
  simp [Sec.res]

end

variable {K M : Cx ℤ} (φ : K ⟶ M)

private theorem fst_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((fst φ).1.v j k hjk) (Sec.map ((mappingCone φ).d i j) s) =
      - Sec.map (K.d j k) (Sec.map ((fst φ).1.v i j hij) s) := by
  rw [← sm_comp, d_fst_v φ i j k hij hjk, sm_neg, sm_comp]

private theorem snd_d (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((snd φ).v j j (add_zero _)) (Sec.map ((mappingCone φ).d i j) s) =
      Sec.map (φ.f j) (Sec.map ((fst φ).1.v i j hij) s) + Sec.map (M.d i j) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  rw [← sm_comp, d_snd_v φ i j hij, sm_add, sm_comp, sm_comp]

private theorem decomp (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    s = Sec.map ((inl φ).v j i (by omega)) (Sec.map ((fst φ).1.v i j hij) s) +
      Sec.map ((inr φ).f i) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  have hid := id_X φ i j hij
  calc s = Sec.map (𝟙 _) s := rfl
    _ = _ := by rw [← hid]; rfl

private theorem d_inl (n : ℤ) {T : Scheme.{0}} (a : Sec (K.X n) T) (ha : Sec.map (K.d n (n + 1)) a = 0) :
    Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) := by
  rw [← sm_comp, inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, ha, ms_zero, sub_zero]

private theorem d_inr (i j : ℤ) {T : Scheme.{0}} (c : Sec (M.X i) T) :
    Sec.map ((mappingCone φ).d i j) (Sec.map ((inr φ).f i) c) = Sec.map ((inr φ).f j) (Sec.map (M.d i j) c) := by
  rw [← sm_comp, inr_f_d, sm_comp]

private theorem core (Q : Scheme.{0} → Prop) (hQ : ∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V)
    (H1 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (M.X n) T), Sec.map (M.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (K.X n) V) (c : Sec (M.X (n - 1)) V), Sec.map (K.d n (n + 1)) a = 0 ∧
        Sec.map (φ.f n) a = Sec.res g b + Sec.map (M.d (n - 1) n) c)
    (H2 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (K.X n) T), Sec.map (K.d n (n + 1)) a = 0 →
      (∃ c : Sec (M.X (n - 1)) T, Sec.map (φ.f n) a = Sec.map (M.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) a' = Sec.res g a)
    (U : Scheme.{0}) (hU : Q U) (n : ℤ) (b : Sec ((mappingCone φ).X n) U)
    (hb : Sec.map ((mappingCone φ).d n (n + 1)) b = 0) :
    Loc U fun V g => ∃ c : Sec ((mappingCone φ).X (n - 1)) V,
      Sec.map ((mappingCone φ).d (n - 1) n) c = Sec.res g b := by
  have hdec := decomp φ n (n + 1) rfl b
  have hfd := fst_d φ n (n + 1) (n + 1 + 1) rfl rfl b
  have hsd := snd_d φ n (n + 1) rfl b
  set x := Sec.map ((fst φ).1.v n (n + 1) rfl) b with hx
  set y := Sec.map ((snd φ).v n n (add_zero n)) b with hy
  have hxd : Sec.map (K.d (n + 1) (n + 1 + 1)) x = 0 := by
    rw [hb, ms_zero] at hfd
    exact neg_eq_zero.mp hfd.symm
  have hxy : Sec.map (φ.f (n + 1)) x + Sec.map (M.d n (n + 1)) y = 0 := by
    rw [hb, ms_zero] at hsd
    exact hsd.symm
  have hyx : Sec.map (M.d n (n + 1)) y + Sec.map (φ.f (n + 1)) x = 0 := (add_comm _ _).trans hxy
  have hcob : ∃ c : Sec (M.X (n + 1 - 1)) U,
      Sec.map (φ.f (n + 1)) x = Sec.map (M.d (n + 1 - 1) (n + 1)) c := by
    refine ⟨Sec.map (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (-y), ?_⟩
    rw [← sm_comp (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (M.d (n + 1 - 1) (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ms_neg]
    exact eq_neg_of_add_eq_zero_left hxy
  apply loc_bind (H2 U hU (n + 1) x hxd hcob)
  rintro V g ⟨a', ha'⟩
  set a := Sec.map (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom a' with ha
  have had : Sec.map (K.d n (n + 1)) a = Sec.res g x := by
    rw [ha, ← sm_comp (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom (K.d n (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ha']
  set y' := Sec.res g y + Sec.map (φ.f n) a with hy'
  have hy'd : Sec.map (M.d n (n + 1)) y' = 0 := by
    rw [hy', ms_add, ← sm_res, ← sm_comp (φ.f n) (M.d n (n + 1)), φ.comm n (n + 1), sm_comp, had,
      ← sm_res, ← res_add, hyx, res_zero]
  have hdc1 : Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) - Sec.map ((inl φ).v (n + 1) n (by omega)) (Sec.res g x) := by
    rw [← sm_comp ((inl φ).v n (n - 1) (by omega)) ((mappingCone φ).d (n - 1) n),
      inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, had]
  apply loc_mono (H1 V (hQ g hU) n y' hy'd)
  rintro W t ⟨a₂, c₂, ha₂, hφ⟩
  refine ⟨Sec.map ((inl φ).v n (n - 1) (by omega)) a₂ - Sec.map ((inr φ).f (n - 1)) c₂ -
    Sec.res t (Sec.map ((inl φ).v n (n - 1) (by omega)) a), ?_⟩
  rw [res_comp, hdec, ms_sub, ms_sub, d_inl φ n a₂ ha₂, d_inr, ← sm_res, hdc1, hφ, hy']
  simp only [sm_res, map_sub, map_add (f := _)]
  abel

end UpperTheory.ConeLoc

theorem UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
            ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec ((mappingCone ρ.toZ).X n) U), Sec.map ((mappingCone ρ.toZ).d n (n + 1)) b = 0 →
          Loc U fun V g => ∃ c : Sec ((mappingCone ρ.toZ).X (n - 1)) V, Sec.map ((mappingCone ρ.toZ).d (n - 1) n) c = Sec.res g b := by
  intro R _ L B ρ Q hQ H1 H2 U hU n b hb
  exact UpperTheory.ConeLoc.core ρ.toZ Q hQ (fun T hT m c hc => H1 T hT m c hc)
    (fun T hT m a ha hc => H2 T hT m a ha hc) U hU n b hb
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem comp_gamma {T : Scheme.{0}} (φ : Polynomial ℤ →+* Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
      (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  erw [Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc _ _

theorem UpperTheory.affineLine_hom_existsUnique_of_globalSection :
    ∀ (T : Scheme.{0}) (a : Γ(T, ⊤)), ∃! s : T ⟶ A1, s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X) = a := by
  intro T a
  have key : ∀ s : T ⟶ A1, s = T.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop) := by
    intro s
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let φ : Polynomial ℤ →+* Γ(T, ⊤) := Polynomial.eval₂RingHom (Int.castRingHom _) a
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · have h : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
        (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom Polynomial.X = a := by
      rw [comp_gamma]
      simp [φ]
    rw [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h
  · intro s hs
    suffices e : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop =
        CommRingCat.ofHom φ by
      rw [key s, e]
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rw [CommRingCat.hom_comp, RingHom.comp_apply, hs]
      simp [φ]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.GqPt

private theorem hom_ext (q : ℕ) {R : Type} [CommRing R] {f g : LqR q →+* R}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g :=
  _root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) :
    sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private theorem val_map_tq (q : ℕ) {T : Scheme.{0}} (s : T ⟶ Gq q) :
    ((Units.map s.appTop.hom.toMonoidHom (tq q) : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) =
      (sec s).hom (LaurentPolynomial.T 1) := rfl

end UpperTheory.GqPt

open UpperTheory.GqPt in
theorem UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit ((q : ℕ) : Γ(T, ⊤)) → ∀ t : (Γ(T, ⊤))ˣ, ∃! s : T ⟶ Gq q, Units.map s.appTop.hom.toMonoidHom (tq q) = t := by
  intro q _ T hq t
  let lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)
  let φ : LqR q →+* Γ(T, ⊤) := LaurentPolynomial.eval₂ lam t
  have hφ : φ (LaurentPolynomial.T 1) = t := by
    simp only [φ, LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · refine Units.ext ?_
    rw [val_map_tq, sec_to]
    exact hφ
  · intro s hs
    refine sec_inj ?_
    rw [sec_to]
    refine CommRingCat.hom_ext (hom_ext q ?_)
    have h1 := val_map_tq q s
    rw [hs] at h1
    exact h1.symm.trans hφ.symm
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

private theorem conn_neg (a9 : A9) {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) :
    Conn R f F (-1) := by
  have hs := (a9 R F).1
  refine ⟨fun j hj => ?_, ?_⟩
  · haveI := hs E j (by omega)
    haveI := hs E' j (by omega)
    exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · haveI := hs E' (-1) (by omega)
    exact Function.injective_of_subsingleton _

private theorem conn_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (n : ℤ) :
    Conn R (disc.map f) F n ↔ Conn R (disc.map g) F n := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact conn_sq R w (eqv_iso R _ F) (eqv_iso R _ F) n

private theorem eqv_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (h : Eqv R (disc.map g) F) : Eqv R (disc.map f) F := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact fun n => ((sq R w (eqv_iso R _ F) (eqv_iso R _ F) n).1).2 (h n)

private theorem conn_all (a1 : A1) (a9 : A9) (b1 : B1) (b2 : B2) (b4 : B4) (hC : Cover) (hE : EqvQA)
    (hD : DescStep) (hL : CechLevels) (q : ℕ) [NeZero q] (i : ℤ) (m : ℕ) :
    ∀ (B : Type) [CommRing B] (J : Ideal B), IsUnit (q : B) →
      (∀ (C : Type) [CommRing C] (χ : B →+* C), χ.IsIntegral → Good C (J.map χ)) →
      Conn (ZMod q) (spMap (Ideal.Quotient.mk J)) (tw q i) ((m : ℤ) - 1) := by
  induction m with
  | zero =>
    intro B _ J _ _
    rw [Nat.cast_zero, zero_sub]
    exact conn_neg a9 _ _
  | succ m ih =>
    intro B _ J hq hG
    obtain ⟨A', _, φ, hφ, hsurj, hQA⟩ := hC B
    obtain ⟨⟨h1, h2, h3, h4⟩, ψ, hψ, hlev, h0⟩ := hL B A' φ J hφ hsurj
    have hψc : Conn (ZMod q) ψ (tw q i) ((m : ℤ) - 1 + 1) := by
      apply hD a1 (ZMod q) (tw q i) ψ ((m : ℤ) - 1)
      · intro p
        obtain ⟨C, _, χ, hχ, ⟨e⟩⟩ := hlev p
        rw [conn_level e]
        apply ih C (J.map χ) (by simpa using hq.map χ)
        intro C' _ χ' hχ'
        rw [Ideal.map_map]
        exact hG C' (χ'.comp χ) (RingHom.IsIntegral.trans _ _ hχ hχ')
      · obtain ⟨e⟩ := h0
        apply eqv_level e
        exact hE a1 a9 b1 b2 q A' (J.map φ) hQA (hG A' φ hφ) (by simpa using hq.map φ) i
    have hmm : ((m : ℤ) - 1 + 1) = ((m + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [hmm] at hψc
    have hqJ : IsUnit ((q : ℕ) : B ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
    have ea := @b4 q _ _ (Spec.map (CommRingCat.ofHom φ)) h1 h2 (unit_spec (A := B) hq) i
    have eb := @b4 q _ _ _ h3 h4 (unit_spec (A := B ⧸ J) hqJ) i
    exact (conn_sq (ZMod q) hψ eb ea _).1 hψc

theorem UpperTheory.etaleCohomology_descent_of_cech_cover :
    A1 → A9 → B1 → B2 → B4 → Cover → HensIdem → EqvQA → DescStep → CechLevels → E1 := by
  intro a1 a9 b1 b2 b4 hC hH hE hD hL q A _ I _ hq i
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : A) = 1 := isUnit_zero_iff.mp (by simpa using hq)
    haveI : Subsingleton A := subsingleton_of_zero_eq_one h01
    have hb : Function.Bijective (Ideal.Quotient.mk I) :=
      ⟨fun x y _ => Subsingleton.elim x y, Ideal.Quotient.mk_surjective⟩
    haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
      (RingEquiv.ofBijective (Ideal.Quotient.mk I) hb).toCommRingCatIso.isIso_hom
    exact eqv_iso _ _ _
  · haveI : NeZero q := ⟨hq0⟩
    intro n
    have hc := conn_all a1 a9 b1 b2 b4 hC hE hD hL q i (n.toNat + 2) A I hq
      (fun C _ χ hχ => hH A I C χ hχ)
    exact hc.1 n (by push_cast; omega)

end
end
