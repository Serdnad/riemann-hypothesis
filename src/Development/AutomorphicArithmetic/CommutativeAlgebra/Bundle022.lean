module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle014
public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
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
import Mathlib.Tactic.TypeStar
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ConstantCochains

variable {R : Type} [CommRing R] {E : Spc} {K : Cx R}

private theorem map_id' {p : ℕ} {U : Scheme.{0}} (z : Sx E p U) : Sx.map (𝟙 E) z = z := rfl

private def cst {U : Scheme.{0}} {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) : Sec (K.X b) U := e ▸ v

private theorem res_cst {V U : Scheme.{0}} (g : V ⟶ U) {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) :
    Sec.res g (cst e v) = cst e (Sec.res g v) := by
  subst e; rfl

private theorem cst_fam (x : (famDC (Sub.bot E) K 0).Tot) (p : ℕ) (U : Scheme.{0}) (z : Sx E p U)
    {s t : ℤ} (e : t = s) (e' : t + 0 = s + 0) :
    (show Fam (Sub.bot E) p (K.X (s + 0)) from x p s).1 U z =
      cst e' ((show Fam (Sub.bot E) p (K.X (t + 0)) from x p t).1 U z) := by
  subst e; rfl

private theorem exists_cochain (n : ℤ) (x : (famDC (Sub.bot E) K 0).Tot) :
    ∃ γ : Cochain ((chains R).obj E) K n, Comp (𝟙 E) γ x := by
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (K.X s) U :=
    fun p s _ U z => cst (add_zero s) ((x p s).1 U z)
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (z : Sx E p U),
      Sec.res g (a p s h U z) = a p s h V (z.res g) := by
    intro p s h V U g z
    exact (res_cst g _ _).trans (congrArg (cst (add_zero s)) ((x p s).2.1 V U g z))
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U z) = a p j (hp ▸ hij) U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  let γ : Cochain ((chains R).obj E) K n := Cochain.mk φ
  have hγ : ∀ p s h U z, ev γ p s h U z = a p s h U z := by
    intro p s h U z
    have he := hφ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, ?_⟩
  intro p s h U z
  rw [map_id', hγ]
  exact cst_fam x p U z (add_zero s) (add_zero (s + 0))

private theorem eq_zero_of_comp {N : ℤ} (γ : Cochain ((chains R).obj E) K N)
    (h : Comp (𝟙 E) γ (0 : (famDC (Sub.bot E) K 0).Tot)) : γ = 0 := by
  have hext : ∀ α β : Cochain ((chains R).obj E) K N,
      (∀ p s h U z, ev α p s h U z = ev β p s h U z) → α = β := by
    intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U z => H k s hs U z)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  apply hext
  intro p s hs U z
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 0 := ⟨s, (add_zero s).symm⟩
  have h1 := h p t hs U z
  rw [map_id'] at h1
  rw [← h1]
  simp [ev]
  rfl

private theorem eq_of_comp {N : ℤ} (γ γ' : Cochain ((chains R).obj E) K N)
    (x : (famDC (Sub.bot E) K 0).Tot) (h : Comp (𝟙 E) γ x) (h' : Comp (𝟙 E) γ' x) : γ = γ' := by
  have h2 := (UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 N N (add_zero N)).2.2.2.1 γ γ' x x h h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (eq_zero_of_comp _ h2)

end UpperTheory.ConstantCochains

open UpperTheory.ConstantCochains in
theorem UpperTheory.supportDoubleComplex_bot_totalModel :
    ∀ (R : Type) [CommRing R] (E : Spc) (K : Cx R) (n : ℤ), TModel (famDC (Sub.bot E) K 0) n (HRel (E := E) (K := K) (n := n)) := by
  intro R _ E K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have Ik := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 k k (add_zero k)
  have I1 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1) (k + 1) (add_zero _)
  have I2 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1 + 1) (k + 1 + 1) (add_zero _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ⟩ := exists_cochain (k + 1) x
    have h1 := I1.2.2.1 γ x hγ
    rw [hD] at h1
    have h0 := eq_zero_of_comp _ h1
    exact ⟨CohomologyClass.mk (Cocycle.mk γ _ rfl h0), Cocycle.mk γ _ rfl h0, rfl, hγ⟩
  · intro c
    obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨x, hx, hc⟩ := I1.1 γ (fun _ _ _ _ _ hm => False.elim hm)
    refine ⟨x, hx, ?_, γ, rfl, hc⟩
    have h1 := I1.2.2.1 γ x hc
    rw [Cocycle.δ_eq_zero] at h1
    have c00 : Comp (𝟙 E) (0 : Cochain ((chains R).obj E) K (k + 1 + 1))
        (0 : (famDC (Sub.bot E) K 0).Tot) := by
      intro p s h U z
      simp [ev]
      rfl
    exact I2.2.1 0 _ 0 (I1.2.2.2.2 x hx) (fun _ _ _ => rfl) h1 c00
  · rintro x c x' c' ⟨γ, rfl, hγ⟩ ⟨γ', rfl, hγ'⟩
    exact ⟨γ - γ', CohomologyClass.mk_sub _ _, I1.2.2.2.1 _ _ _ _ hγ hγ'⟩
  · rintro x c hx ⟨γ, rfl, hγ⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ k rfl, add_sub_cancel_right]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨y, hy, hyβ⟩ := Ik.1 β (fun _ _ _ _ _ hm => False.elim hm)
      refine ⟨y, hy, ?_⟩
      have h1 := Ik.2.2.1 β y hyβ
      rw [hβ] at h1
      exact I1.2.1 _ _ _ (Ik.2.2.2.2 y hy) hx h1 hγ
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ⟩ := exists_cochain k y
      exact ⟨β, eq_of_comp _ _ _ (Ik.2.2.1 β y hβ) hγ⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem units_map_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (η : ℤˣ) (x : A) :
    f (η • x) = η • f x := by
  simp [Units.smul_def]

private theorem colEx_transfer {C C' D D' : DC} (Φ : C.Hom C') (Ψ : D.Hom D') (p : ℕ) (η : ℤˣ)
    (e : ∀ s, C.A p s ≃+ D.A 0 s) (e' : ∀ s, C'.A p s ≃+ D'.A 0 s)
    (hd : ∀ s t x, e t (C.d p s t x) = D.d 0 s t (e s x))
    (hd' : ∀ s t x, e' t (C'.d p s t x) = D'.d 0 s t (e' s x))
    (hΦ : ∀ s x, e' s (Φ p s x) = η • Ψ 0 s (e s x)) (h : Ψ.ColEx 0) : Φ.ColEx p := by
  have hηη : ∀ {A : Type 1} [AddCommGroup A] (x : A), η • η • x = x := fun x => by
    rw [smul_smul, Int.units_mul_self, one_smul]
  intro s a y ha hy
  have hΨ : ∀ s x, Ψ 0 s (e s x) = η • e' s (Φ p s x) := fun s x => by rw [hΦ, hηη]
  obtain ⟨a', y', h1, h2⟩ := h s (e _ a) (η • e' s y)
    (by rw [← hd, ha, map_zero])
    (by rw [hΨ, hy, hd', units_map_smul])
  refine ⟨(e s).symm a', η • (e' _).symm y', ?_, ?_⟩
  · apply (e _).injective
    rw [hd, AddEquiv.apply_symm_apply, h1]
  · apply (e' _).injective
    have h3 : e' s y = η • (Ψ 0 s a' + D'.d 0 (s - 1) s y') := by rw [← h2, hηη]
    have h4 : e' (s - 1) (η • (e' (s - 1)).symm y') = η • y' := by
      have := units_map_smul (e' (s - 1)).toAddMonoidHom η ((e' (s - 1)).symm y')
      simpa using this
    rw [h3, map_add (f := _), hΦ, hd', AddEquiv.apply_symm_apply, h4, units_map_smul, smul_add]

private def lvl {R : Type} [CommRing R] {E : Spc} {p : ℕ} (Z : Sub E)
    (Z' : Sub (disc.obj (E.obj (op (SimplexCategory.mk p)))))
    (h : ∀ (W : Scheme.{0}) (z : Sx E p W), Z'.mem 0 W z ↔ Z.mem p W z) (M : Shv R) :
    Fam Z p M ≃+ Fam Z' 0 M where
  toFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).1 hx)⟩
  invFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem disc_δ {R : Type} [CommRing R] {F : PSh} (Z : Sub (disc.obj F)) (L : Cx R) (m s : ℤ)
    (x : (famDC Z L m).A 0 s) : (famDC Z L m).δ 0 s x = 0 := by
  apply Subtype.ext
  funext U z
  have hf : ∀ i, Sx.face (E := disc.obj F) z i = z := fun _ => rfl
  change m.negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Fam Z 0 (L.X (s + m)) from x).1 U (Sx.face (E := disc.obj F) z i) = 0
  simp [Fin.sum_univ_two, hf]

private theorem fam_smul {R : Type} [CommRing R] {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) (a : Fam Z p M)
    (W : Scheme.{0}) (z : Sx E p W) : (η • a).1 W z = η • a.1 W z := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> simp

theorem UpperTheory.relativeCupProduct_levelwise_compat :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X) (p : ℕ)
    (Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m))
    (Ψ : (famDC (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))) I 0).Hom (famDC (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))) K m)),
    IsProd μ π β Φ → IsProd μ (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) β Ψ → Ψ.TotEx → Φ.ColEx p := by
  intro R _ I J K μ X U E π m β p Φ Ψ hΦ hΨ hT
  have h0 : Ψ.ColEx 0 := UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero _ _ Ψ (disc_δ _ _ _) (disc_δ _ _ _) hT
  have hbot : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))).mem 0 W z ↔ (Sub.bot E).mem p W z :=
    fun _ _ => Iff.rfl
  have himg : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))).mem 0 W z ↔
        (Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z := fun W z =>
    ((UpperTheory.mem_pullbackImage_iff_factors_through_open U (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) 0 W z).1).trans
      ((UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1).symm
  refine colEx_transfer Φ Ψ p (m * (p : ℤ)).negOnePow (fun s => lvl _ _ hbot _) (fun s => lvl _ _ himg _)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ h0
  intro s x
  apply Subtype.ext
  funext W z
  have h1 := hΦ p s x W z
  have h2 := hΨ 0 s (lvl _ _ hbot _ x) W z
  refine Eq.trans h1 (Eq.trans ?_ (fam_smul _ _ _ (m * (p : ℤ)).negOnePow (Ψ 0 s (lvl _ _ hbot _ x)) W z).symm)
  refine congrArg _ (Eq.trans ?_ h2.symm)
  have h0' : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
  rw [h0', one_smul]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem inl_fold' (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _

private theorem inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

private theorem aw_last {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m) {W : Scheme.{0}} {p : ℕ}
    (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (r k : ℕ) (hr : r = p) (hk : k = 0) (s t w : ℤ) (h : s + t = w)
    (hs : -(r : ℤ) + n = s) (ht : -(k : ℤ) + m = t) (h0 : 0 + r ≤ p) (h1 : r + k ≤ p)
    (s' : ℤ) (hs' : -(p : ℤ) + n = s') (h' : s' + m = w) :
    μ.mul W s t w h (ev α r s hs W (x.sub 0 r h0)) (ev β k t ht W (x.sub r k h1)) =
      μ.mul W s' m w h' (ev α p s' hs' W x) b := by
  subst hr hk
  have ht' : m = t := by simpa using ht
  subst ht'
  subst hs
  subst hs'
  rw [(GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.1, hb]

private theorem aw_eval {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m)
    (γ : Cochain ((chains R).obj D) K (n + m)) (hγ : μ.IsAW rfl α β γ)
    (hβ : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx D k W), ev β k s h W y = 0)
    {W : Scheme.{0}} {p : ℕ} (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (w : ℤ) (h : -(p : ℤ) + (n + m) = w)
    (s : ℤ) (hs : -(p : ℤ) + n = s) (h' : s + m = w) :
    ev γ p w h W x = (m * (p : ℕ)).negOnePow • μ.mul W s m w h' (ev α p s hs W x) b := by
  rw [hγ p w h W x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · exact congrArg _ (aw_last μ α β x b hp hb _ _ rfl (Nat.sub_self p) _ _ _ _ _ _ _ _ s hs h')
  · intro r _
    have hk : 0 < p - ((Fin.castSucc r : Fin (p + 1)) : ℕ) := by
      have := r.2
      simp only [Fin.val_castSucc]
      omega
    rw [hβ _ hk, map_zero, smul_zero]

private theorem last_vertex {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}}
    (z : Sx E p W) (h : p + 0 ≤ p) (ι' : E ⟶ dbl (abv U π)) (ι : sch.obj X ⟶ dbl (opn U))
    (hι : ι' ≫ dbl.map (abvMap U π) = π ≫ ι) :
    ((z.map ι').sub p 0 h).map (dbl.map (abvMap U π)) = Sx.map (E := sch.obj X) (p := 0) ι (under π z) := by
  rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.1 ι']
  have h1 : ((z.sub p 0 h).map ι').map (dbl.map (abvMap U π)) = (z.sub p 0 h).map (ι' ≫ dbl.map (abvMap U π)) := rfl
  rw [h1, hι]
  have h2 : (z.sub p 0 h).map (π ≫ ι) = Sx.map (E := sch.obj X) (p := 0) ι (under π (z.sub p 0 h)) := rfl
  rw [h2, ((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.2, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.2 0 _]

theorem UpperTheory.relativeCupProduct_realizes_product_of_representative :
    LeafAW → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m j i n : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X), IsRep U β c.1 →
    ∀ Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m), IsProd (twPair q i j) π β Φ →
    ∀ (x : (famDC (Sub.bot E) (res _ (tw q i)) 0).Tot) (a : Ht q E n i), HRel x a → SRel (P := abv U π) (N := n + m) (Φ.tot x) (Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)).1 := by
  intro hAW q _ X U E π m j i n c β hrep Φ hΦ x a hx
  obtain ⟨-, -, γ₀, hγ₀, h0l, h0r, h0p⟩ := hrep
  obtain ⟨α, hα, hαx⟩ := hx
  let α' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q i)) n :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.fold (abv U π)))) α (zero_add n)
  let β' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q j)) m :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.map (abvMap U π)))) γ₀ (zero_add m)
  obtain ⟨γ, hγ, hcup⟩ := (hAW q i j).2 (dbl (abv U π)) n m α' β'
  have evα : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev α'.1 p s h W y = ev α.1 p s h W (y.map (dbl.fold (abv U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.fold (abv U π)) α.1 p s h W y
  have evβ : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev β'.1 p s h W y = ev γ₀.1 p s h W (y.map (dbl.map (abvMap U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.map (abvMap U π)) γ₀.1 p s h W y
  have hvan : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) k W), ev β'.1 k s h W y = 0 := by
    intro k hk s h W y
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [evβ]
    exact h0p k s _ W _
  have hinr : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (abv U π).right p W),
      ev γ.1 p s h W (z.map (dbl.inr (abv U π))) = 0 := by
    intro p s h W z
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inr (abv U π))).sub p 0 (by omega)) = 0 := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inr (abv U π)) (dbl.inr (opn U)) (dbl.inr_map (abvMap U π)))).trans ?_
      exact h0r W _
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ 0 (by omega) hb s h (-(p : ℤ) + n) rfl (by omega), map_zero, smul_zero]
  refine ⟨γ, ?_, ?_, hinr⟩
  · have hC : cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 = CohomologyClass.mk γ := by
      rw [← hcup, ← hα]
      change cup q _ (pull _ (dbl.map (abvMap U π)) _ m c.1) = _
      rw [← hγ₀]
      rfl
    have hz : pull _ (dbl.inr (abv U π)) (tw q (i + j)) (n + m) (CohomologyClass.mk γ) = 0 := by
      have h0 : zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m)) = 0 := by
        have hc : (zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m))).1 = 0 := by
          refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.1 _ _ fun p s h W z => ?_
          rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).1 0 0 p s h W z).2.2.1]
          exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.inr (abv U π)) γ.1 p s h W z).trans (hinr p s h W z)
        exact Cocycle.ext hc
      exact (congrArg CohomologyClass.mk h0).trans (CohomologyClass.mk_zero _ _ _)
    change CohomologyClass.mk γ = cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 -
      pull _ (dbl.fold (abv U π)) _ _ (pull _ (dbl.inr (abv U π)) _ _
        (cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1))
    rw [hC, hz, map_zero, sub_zero]
  · intro p s h W z
    have hs : -(p : ℤ) + n = s + 0 := by omega
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inl (abv U π))).sub p 0 (by omega)) = Sec.res (under π z) β := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inl (abv U π)) (dbl.inl (opn U)) (inl_map' (abvMap U π)))).trans ?_
      exact h0l W _
    have e := hΦ p s (x p s) W z
    rw [hαx p s hs W z] at e
    refine e.trans ?_
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ _ (by omega) hb (s + m) h (s + 0) hs (by omega), evα]
    have hf : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (𝟙 E) := by
      have h1 : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (dbl.inl (abv U π) ≫ dbl.fold (abv U π)) := rfl
      rw [h1, inl_fold']
      rfl
    rw [hf]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.exists_closed_locus_of_torsion_abelianScheme :
    ∀ {S T : Scheme.{0}} (x : T ⟶ S) (A G : Over S) [GrpObj A] (inc : G ⟶ A) (k : ℕ), (∀ (T' : Over S) (a : T' ⟶ G), (a ≫ inc) ^ k = 1) → IsUnit (k : Γ(T, ⊤)) → ∀ (A₁ : Over T) [GrpObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → ∃ V : (Over.mk x ⊗ G).left.Opens, IsClosed (V : Set (Over.mk x ⊗ G).left) ∧ ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G) (g : Over.mk t.left ⟶ A₁), g.left ≫ φ₁ = a.left ≫ inc.left → (g ≫ f = 1 ↔ Set.range (lift t a).left ⊆ V) := by
  intro S T x A G _ inc k hk hu A₁ _ φ₁ B₁ _ f hP hB hf
  have hfe := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B₁ (hG := hB) hu
  obtain ⟨hfin, het⟩ := hfe.2
  let pr : (Over.mk x ⊗ G).left ⟶ T := (fst (Over.mk x) G).left
  have hpr : pr ≫ x = (Over.mk x ⊗ G).hom := Over.w (fst (Over.mk x) G)
  obtain ⟨τ, hτ, -⟩ := UpperTheory.SubRep.pull_existsUnique hP (Over.mk x ⊗ G) pr hpr (snd (Over.mk x) G ≫ inc)
  have hτk : τ ^ k = 1 := by
    apply UpperTheory.SubRep.pull_ext hP
    rw [UpperTheory.SubRep.pull_pow hP _ pr hpr hτ k, hk _ (snd (Over.mk x) G), UpperTheory.SubRep.pull_one hP _ pr hpr]
  have hpow : ∀ n : ℕ, (τ ≫ f) ^ n = (τ ^ n) ≫ f := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hwk : (τ ≫ f) ^ k = 1 := by
    rw [hpow, hτk, MonObj.one_comp]
  obtain ⟨c, hc, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (τ ≫ f) hwk
  obtain ⟨c₀, hc₀, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk pr ⟶ B₁) (one_pow k)
  obtain ⟨V, hV, H⟩ := GlobalTheory.LevCover.clopenCond_eq c c₀
  refine ⟨V, hV, fun T' t a g hg => ?_⟩
  have hl : (lift t a).left ≫ pr = t.left := by
    change ((lift t a) ≫ fst (Over.mk x) G).left = t.left
    rw [lift_fst]
  let h : Over.mk t.left ⟶ Over.mk pr := Over.homMk (lift t a).left hl
  have hhτ : h ≫ τ = g := by
    apply UpperTheory.SubRep.pull_ext hP
    have e : (lift t a).left ≫ (snd (Over.mk x) G ≫ inc).left = a.left ≫ inc.left := by
      change (lift t a ≫ snd (Over.mk x) G ≫ inc).left = _
      rw [lift_snd_assoc]; rfl
    change (lift t a).left ≫ τ.left ≫ φ₁ = _
    rw [hτ, e, hg]
  have hgf : g ≫ f = h ≫ τ ≫ f := by rw [← hhτ, Category.assoc]
  have key : g ≫ f = 1 ↔ h ≫ c = h ≫ c₀ := by
    constructor
    · intro e
      have h1 : (h ≫ c) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc, ← hgf, e]
      have h2 : (h ≫ c₀) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc₀, MonObj.comp_one]
      exact (GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk t.left ⟶ B₁) (one_pow k)).unique h1 h2
    · intro e
      rw [hgf, ← hc, ← Category.assoc, e, Category.assoc, hc₀, MonObj.comp_one]
  exact key.trans (H _ h)
end
