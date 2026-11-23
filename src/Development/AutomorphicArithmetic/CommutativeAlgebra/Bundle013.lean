module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Mathlib.Tactic.TypeStar
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem unit_on (T : Scheme.{0}) (f : Γ(T, ⊤)) (W : T.Opens) (h : W ≤ T.basicOpen f) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact (T.mem_basicOpen f x trivial).1 (h hx)

private theorem unit_cover (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤))
    (hv : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ i, x ∈ T.basicOpen (v i) := by
  have hx : x ∈ (⨆ g ∈ Set.range v, T.basicOpen g) := by
    rw [iSup_basicOpen_of_span_eq_top (X := T) ⊤ _ hv]
    trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem UpperTheory.locally_exists_isUnit_of_span_range_eq_top :
    ∀ (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤)), Ideal.span (Set.range v) = ⊤ →
        Loc T fun V g => ∃ i, IsUnit (g.appTop.hom (v i)) := by
  intro T M v hv
  let S : Sieve T :=
    { arrows := fun V g => ∃ i, IsUnit (g.appTop.hom (v i))
      downward_closed := by
        rintro Y Z g ⟨i, hi⟩ k
        refine ⟨i, ?_⟩
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact hi.map _ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Fin M => T.basicOpen (v i)) :=
    eq_top_iff.2 (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (unit_cover T v hv x))
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (T.openCoverOfIsOpenCover _ hcov))
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  apply S.downward_closed
  have hu := unit_on T (v i) ((T.basicOpen (v i)).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])
  exact ⟨i, hu⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isIso_of_bijective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Bijective (fun x : Sx S k T => x.map f)) → IsIso f := by
  intro S S' f h
  haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by
    intro n
    haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by
      intro T
      obtain ⟨⟨k⟩⟩ := n
      obtain ⟨T⟩ := T
      rw [isIso_iff_bijective]
      exact h k T
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isPullback_of_unique_simplices_pullback :
    ∀ {P A B C : Spc} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (u : B ⟶ C), t ≫ r = l ≫ u →
        (∀ (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u → ∃! z : Sx P k T, z.map t = x ∧ z.map l = y) →
        IsPullback t l r u := by
  intro P A B C t l r u hw h
  refine IsPullback.of_forall_isPullback_app (fun n => ?_)
  refine IsPullback.of_forall_isPullback_app (fun T => ?_)
  obtain ⟨⟨k⟩⟩ := n
  obtain ⟨T⟩ := T
  have hw' : ∀ x : Sx P k T, Sx.map r (Sx.map t x) = Sx.map u (Sx.map l x) := by
    intro x
    have := congrArg (fun f : P ⟶ C => (f.app (op ⟨k⟩)).app (op T) x) hw
    simpa [Sx.map] using this
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hw' x
  · rintro x y ⟨h1, h2⟩
    obtain ⟨z, -, hz⟩ := h k T (Sx.map t (x : Sx P k T)) (Sx.map l (x : Sx P k T)) (hw' x)
    have hx := hz x ⟨rfl, rfl⟩
    have hy := hz y ⟨h1.symm, h2.symm⟩
    exact hx.trans hy.symm
  · intro a b hab
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := h k T a b hab
    exact ⟨z, h1, h2⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.mono_of_injective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Injective (fun x : Sx S k T => x.map f)) → Mono f := by
  intro S S' f hf
  have hm : ∀ n : SimplexCategoryᵒᵖ, Mono (f.app n) := by
    intro n
    have hm' : ∀ T : Schemeᵒᵖ, Mono ((f.app n).app T) := by
      intro T
      rw [mono_iff_injective]
      exact hf n.unop.len T.unop
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app f
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem sx_face_face {E : Spc} {p : ℕ} {U : Scheme} (y : Sx E (p+2) U) {a b : Fin (p+2)}
    (h : a ≤ b) : (y.face b.succ).face a = (y.face a.castSucc).face b := by
  unfold Sx.face
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app,
    SimplicialObject.δ_comp_δ E h]

private theorem sum_neg_one_pow_face_face_eq_zero {A : Type*} [AddCommGroup A] {E : Spc} {p : ℕ} {U : Scheme}
    (f : Sx E p U → A) (y : Sx E (p+2) U) :
    ∑ j : Fin (p+3), ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i) = 0 := by
  have ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b :=
    fun h => sx_face_face y h
  rw [← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]
  let g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2) := fun ji =>
    if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega))
    else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))
  have gg : ∀ ji, g (g ji) = ji := by
    rintro ⟨j, i⟩
    by_cases h : (j : ℕ) ≤ i
    · have h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2)) := by simp; omega
      simp only [g, dif_pos h, dif_neg h1]
      ext <;> simp
    · have h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2)) := by simp; omega
      simp only [g, dif_neg h, dif_pos h1]
      ext <;> simp
  refine Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)
  · rintro ⟨j, i⟩ _
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h]
      have hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc := by ext; simp
      have hle : j.castLT (by omega) ≤ i := by rw [Fin.le_def]; simpa using h
      rw [ff hle, ← hj]
      simp only [Fin.val_succ, Fin.coe_castLT]
      rw [← add_smul]
      convert zero_smul ℤ _
      rw [show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring
    · simp only [g, dif_neg h]
      have hj0 : j ≠ 0 := by intro h0; simp [h0] at h
      have hle : i ≤ j.pred hj0 := by rw [Fin.le_def]; simp; omega
      have key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0) := by
        have := ff hle
        rwa [Fin.succ_pred] at this
      rw [key]
      simp only [Fin.coe_castSucc, Fin.coe_pred]
      rw [← add_smul]
      convert zero_smul ℤ _
      have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      rw [this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring
  · rintro ⟨j, i⟩ _ _ heq
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega
    · simp only [g, dif_neg h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega

theorem UpperTheory.supportDoubleComplex_isAdmissible :
    ∀ (R : Type) [CommRing R] (E : Spc) (Z : Sub E) (K : Cx R) (m : ℤ), (famDC Z K m).Ok := by
  intro R _ E Z K m
  unfold famDC
  constructor
  · intro p s t u x
    apply Subtype.ext
    funext U y
    change Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0
    rw [HomologicalComplex.d_comp_d]
    rfl
  · intro p s x
    apply Subtype.ext
    funext U y
    simp [Fam.δ]
    have hz := sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y
    have hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) =
        m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) := by
      intro j
      rw [smul_comm, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, pow_add]
    simp_rw [hj, ← Finset.smul_sum]
    rw [hz, smul_zero, smul_zero]
  · intro p s t x
    apply Subtype.ext
    funext U y
    simp [Fam.map, Fam.δ]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_us {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (e : ℤˣ) (x : G) :
    f (e • x) = e • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem D_zero (C : DC) (n : ℤ) (x : C.Tot) (s t : ℤ) (h : s + 1 = t) :
    C.D n x 0 t = C.d 0 s t (x 0 s) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem D_succ (C : DC) (n : ℤ) (x : C.Tot) (p : ℕ) (s t : ℤ) (h : s + 1 = t) :
    C.D n x (p + 1) t = C.d (p + 1) s t (x (p + 1) s) + (n + 1).negOnePow • C.δ p t (x p t) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem col {C C' : DC} {Φ : C.Hom C'} {p : ℕ} (h : Φ.ColEx p) (r s t u : ℤ) (e1 : r + 1 = s)
    (e2 : s + 1 = t) (e3 : t + 1 = u) (a : C.A p t) (y : C'.A p s) (ha : C.d p t u a = 0)
    (hy : Φ p t a = C'.d p s t y) :
    ∃ (a' : C.A p s) (y' : C'.A p r), C.d p s t a' = a ∧ y = Φ p s a' + C'.d p r s y' := by
  subst e2
  subst e3
  obtain rfl : r = s - 1 := by omega
  exact h s a y ha hy

private structure Cl {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s) : Prop where
  sb : ∀ s, (p : ℤ) + s ≠ n + 1 → b s = 0
  sz : ∀ s, (p : ℤ) + s ≠ n → z s = 0
  db : ∀ s t, s + 1 = t → C.d p s t (b s) = 0
  pz : ∀ s t, s + 1 = t → Φ p t (b t) = C'.d p s t (z s)

private structure Sv {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s)
    (u : ∀ s, C.A p s) (v : ∀ s, C'.A p s) : Prop where
  su : ∀ s, (p : ℤ) + s ≠ n → u s = 0
  sv : ∀ s, (p : ℤ) + s ≠ n - 1 → v s = 0
  du : ∀ s t, s + 1 = t → C.d p s t (u s) = b t
  yv : ∀ r s, r + 1 = s → z s = Φ p s (u s) + C'.d p r s (v r)

private theorem solve {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {p : ℕ} (hcol : Φ.ColEx p)
    {b : ∀ s, C.A p s} {z : ∀ s, C'.A p s} (h : Cl Φ n p b z) : ∃ u v, Sv Φ n p b z u v := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = n - p := ⟨_, rfl⟩
  obtain ⟨a', y', ha', hy'⟩ := col hcol (s0 - 1) s0 (s0 + 1) (s0 + 1 + 1) (by ring) rfl rfl
    (b (s0 + 1)) (z s0) (h.db _ _ rfl) (h.pz _ _ rfl)
  refine ⟨Function.update (fun _ => 0) s0 a', Function.update (fun _ => 0) (s0 - 1) y',
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s t hst
    by_cases hs : s = s0
    · subst hst
      subst hs
      rw [Function.update_self, ha']
    · simp [Function.update_of_ne hs, h.sb t (by omega)]
  · intro r s hrs
    by_cases hs : s = s0
    · have hr : r = s - 1 := by omega
      subst hr
      subst hs
      rw [Function.update_self, Function.update_self, hy']
    · have hr : r ≠ s0 - 1 := by omega
      simp [Function.update_of_ne hs, Function.update_of_ne hr, h.sz s (by omega)]

private structure St {C C' : DC} (Φ : C.Hom C') (n : ℤ) (a : C.Tot) (y : C'.Tot) (p : ℕ) where
  b : ∀ s, C.A p s
  z : ∀ s, C'.A p s
  u : ∀ s, C.A p s
  v : ∀ s, C'.A p s
  cl : Cl Φ n p b z
  sv : Sv Φ n p b z u v
  hb : ∀ s, C.δ p s (a p s) = C.δ p s (b s)
  hz : ∀ s, C'.δ p s (y p s) = C'.δ p s (z s)

private theorem cl_zero {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot}
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y) :
    Cl Φ n 0 (a 0) (y 0) := by
  refine ⟨fun s hs => ha 0 s hs, fun s hs => hy 0 s hs, ?_, ?_⟩
  · intro s t e
    have h1 := congrFun (congrFun hD 0) t
    rw [D_zero C (n + 1) a s t e] at h1
    exact h1
  · intro s t e
    have h1 := congrFun (congrFun hP 0) t
    rw [D_zero C' n y s t e] at h1
    exact h1

private theorem cl_next {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot} {p : ℕ}
    (hC : C.Ok) (hC' : C'.Ok) (hΦ : Φ.Ok)
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y)
    (x : St Φ n a y p) :
    Cl Φ n (p + 1) (fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s))
      (fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [ha (p + 1) s hs, x.sv.su s (by omega), map_zero, smul_zero, sub_zero]
  · intro s hs
    simp only [hy (p + 1) s hs, x.sv.sv s (by omega), map_zero, smul_zero, add_zero]
  · intro s t e
    have h1 := congrFun (congrFun hD (p + 1)) t
    rw [D_succ C (n + 1) a p s t e, Int.negOnePow_succ, Units.neg_smul, x.hb t] at h1
    simp only [Pi.zero_apply] at h1
    have h2 : C.d (p + 1) s t (C.δ p s (x.u s)) = C.δ p t (x.b t) := by
      rw [hC.comm, x.sv.du s t e]
    simp only [map_sub, map_us, h2]
    rwa [← sub_eq_add_neg] at h1
  · intro s t e
    have h1 := congrFun (congrFun hP (p + 1)) t
    rw [D_succ C' n y p s t e] at h1
    change Φ (p + 1) t (a (p + 1) t) = _ at h1
    have h3 : C'.δ p t (y p t) =
        C'.δ p t (Φ p t (x.u t)) + C'.d (p + 1) s t (C'.δ p s (x.v s)) := by
      rw [x.hz t, x.sv.yv s t e, map_add (f := _), hC'.comm]
    have h4 : Φ (p + 1) t (C.δ p t (x.u t)) = C'.δ p t (Φ p t (x.u t)) := hΦ.2 p t (x.u t)
    simp only [map_sub, map_add (f := _), map_us, h4]
    rw [h1, h3, smul_add]
    abel

theorem UpperTheory.totalExact_of_columnExact :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → (∀ p, Φ.ColEx p) → Φ.TotEx := by
  intro C C' Φ hC hC' hΦ hcol n a y ha hy hD hP
  have hcl0 := cl_zero (Φ := Φ) ha hy hD hP
  have hs0 := solve (hcol 0) hcl0
  let S0 : St Φ n a y 0 := ⟨a 0, y 0, hs0.choose, hs0.choose_spec.choose, hcl0,
    hs0.choose_spec.choose_spec, fun _ => rfl, fun _ => rfl⟩
  let step : ∀ p, St Φ n a y p → St Φ n a y (p + 1) := fun p x =>
    { b := fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s)
      z := fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)
      u := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose
      v := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose
      cl := cl_next hC hC' hΦ ha hy hD hP x
      sv := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose_spec
      hb := fun s => by simp only [map_sub, map_us, hC.δδ, smul_zero, sub_zero]
      hz := fun s => by simp only [map_add (f := _), map_us, hC'.δδ, smul_zero, add_zero] }
  let S : ∀ p, St Φ n a y p := fun p => Nat.rec (motive := fun p => St Φ n a y p) S0 step p
  refine ⟨fun p s => (S p).u s, fun p s => (S p).v s, ?_, ?_, ?_, ?_⟩
  · intro p s hps
    exact (S p).sv.su s hps
  · intro p s hps
    exact (S p).sv.sv s hps
  · funext p t
    rcases p with _ | p
    · rw [D_zero C n _ (t - 1) t (by ring)]
      exact (S 0).sv.du (t - 1) t (by ring)
    · rw [D_succ C n _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.du (t - 1) t (by ring)
      change C.d (p + 1) (t - 1) t ((S (p + 1)).u (t - 1)) =
        a (p + 1) t - (n + 1).negOnePow • C.δ p t ((S p).u t) at h1
      beta_reduce
      rw [h1, sub_add_cancel]
  · funext p t
    rcases p with _ | p
    · show y 0 t = Φ 0 t ((S 0).u t) + C'.D (n - 1) (fun p s => (S p).v s) 0 t
      rw [D_zero C' (n - 1) _ (t - 1) t (by ring)]
      exact (S 0).sv.yv (t - 1) t (by ring)
    · show y (p + 1) t = Φ (p + 1) t ((S (p + 1)).u t) +
        C'.D (n - 1) (fun p s => (S p).v s) (p + 1) t
      rw [D_succ C' (n - 1) _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.yv (t - 1) t (by ring)
      change y (p + 1) t + (n + 1).negOnePow • C'.δ p t ((S p).v t) =
        Φ (p + 1) t ((S (p + 1)).u t) + C'.d (p + 1) (t - 1) t ((S (p + 1)).v (t - 1)) at h1
      have e : (n - 1 + 1).negOnePow = -(n + 1).negOnePow := by
        rw [sub_add_cancel, Int.negOnePow_succ, neg_neg]
      beta_reduce
      rw [e, Units.neg_smul, eq_sub_of_add_eq h1]
      abel
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private noncomputable abbrev evF (p : ℕ) (W : Scheme.{0}) : Spc ⥤ Type :=
  ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p))) ⋙
    ((evaluation Scheme.{0}ᵒᵖ Type).obj (op W))

theorem UpperTheory.mem_pullbackImage_iff_factors_through_open :
    ∀ {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (p : ℕ) (W : Scheme.{0}) (z : Sx E p W), ((Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z ↔ ∃ w : W ⟶ U.toScheme, w ≫ U.ι = under π z) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ W), under π (z.res g) = g ≫ under π z) ∧ ∀ (r : ℕ) (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk p), under π (z.along θ) = under π z := by
  intro X U E π p W z
  have hpb : IsPullback ((evF p W).map (pullback.fst π (sch.map U.ι)))
      ((evF p W).map (pullback.snd π (sch.map U.ι))) ((evF p W).map π)
      ((evF p W).map (sch.map U.ι)) := (IsPullback.of_hasPullback π (sch.map U.ι)).map (evF p W)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(evF p W).map (pullback.snd π (sch.map U.ι)) y, ?_⟩
    exact (ConcreteCategory.congr_hom hpb.w y).symm
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy, -⟩ := Types.exists_of_isPullback hpb z (show Sx (sch.obj U.toScheme) p W from w) hw.symm
    exact ⟨y, hy⟩
  · intro V g
    exact ConcreteCategory.congr_hom ((π.app (op (SimplexCategory.mk p))).naturality g.op) z
  · intro r θ
    exact congrFun (congrArg (fun t => t.app (op W)) (π.naturality θ.op)) z
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.surjective_of_isPullback_spec_field_ext :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → Surjective u := by
  intro k L _ _ _ C X c u x hpb
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [surjective_iff]
    intro p
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine ⟨q, ?_⟩
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hs
end
