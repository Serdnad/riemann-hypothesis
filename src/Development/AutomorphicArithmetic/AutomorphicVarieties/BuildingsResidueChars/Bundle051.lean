module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_realPart_invariant :
    UpperTheory.V.Af.BA.ReInv := by
  intro L _ _ N σ hσ
  refine ⟨fun x => ?_, fun h hh => ⟨fun y => ?_, fun g hg => ?_⟩⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have e : embO w (σ (σ x)) = embO w x := by rw [hσ, hσ]; simp
    apply RingOfIntegers.coe_injective
    exact w.embedding.injective (by simpa [embO] using e)
  · have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have him : ((mat h w) i j).im = 0 := hh w i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, him]
    ring
  · have hfix : ∀ i j, σ ((↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        = (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j => by
      have := congrArg (fun u : Gm L N => (u : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        (mem_Fix.mp (inv_mem hg))
      exact this
    intro w i j
    have hs : g • h = pull (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) h := rfl
    show ((mat (g • h) w) i j).im = 0
    rw [hs, mat_pull]
    set B := (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hBdef
    have hB : B.map (starRingEnd ℂ) = B := by
      ext a b
      simp only [hBdef, Matrix.map_apply]
      rw [← hσ w, hfix]
    have hM : (mat h w).map (starRingEnd ℂ) = mat h w := by
      ext a b
      simp only [Matrix.map_apply]
      exact Complex.conj_eq_iff_im.mpr (hh w a b)
    have hBt : Bᴴ.map (starRingEnd ℂ) = Bᴴ := by
      ext a b
      have := congrFun (congrFun hB b) a
      simp only [Matrix.map_apply, Matrix.conjTranspose_apply] at this ⊢
      simp only [Complex.star_def, Complex.conj_conj]
      exact this.symm
    have hP : (Bᴴ * mat h w * B).map (starRingEnd ℂ) = Bᴴ * mat h w * B := by
      rw [Matrix.map_mul, Matrix.map_mul, hBt, hM, hB]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply] at this
    exact Complex.conj_eq_iff_im.mp this
end

section

open CategoryTheory

namespace UpperTheory.V.Af.BA.ResolutionExactness

variable {Γ : Type} [Group Γ]

private theorem comp_zero_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C}
    (h : Function.Exact f.hom g.hom) : f ≫ g = 0 := by
  ext x
  exact h.apply_apply_eq_zero x

private theorem exact_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (h : Function.Exact f.hom g.hom) : (ShortComplex.mk f g w).Exact := by
  exact (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => (h x).1 hx)

set_option backward.isDefEq.respectTransparency false in
private theorem main : UpperTheory.V.Af.BA.ResOf := by
  intro Γ _ X d ε hX hε h0 hd
  have hdd : ∀ p, d (p + 1) ≫ d p = 0 := fun p => comp_zero_of (hd p)
  let K : ChainComplex (Rep ℂ Γ) ℕ := ChainComplex.of X d hdd
  have hK : ∀ j, K.d (j + 1) j = d j := fun j => by simp [K]
  have hK0 : K.d 1 0 ≫ ε = 0 := by
    rw [hK 0]
    exact comp_zero_of h0
  let π : K ⟶ (ChainComplex.single₀ (Rep ℂ Γ)).obj (Rep.trivial ℂ Γ ℂ) :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hK0⟩
  have hπ0 : π.f 0 = ε := by simp [π]
  let P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ) :=
    { complex := K
      projective := hX
      π := π
      quasiIso := ⟨fun n => by
        cases n with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · refine ⟨exact_of _ ?_, ?_⟩
            · show Function.Exact (K.d 1 0).hom (π.f 0).hom
              rw [hπ0, hK 0]
              exact h0
            · show Epi (π.f 0)
              rw [hπ0, Rep.epi_iff_surjective]
              exact hε
          all_goals rfl
        | succ m =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
            refine exact_of _ ?_
            show Function.Exact (K.d (m + 2) (m + 1)).hom (K.d (m + 1) m).hom
            rw [hK, hK]
            exact hd m
          · apply ChainComplex.exactAt_succ_single_obj⟩ }
  refine ⟨P, fun p => ⟨Iso.refl _⟩, fun e he0 he => ?_⟩
  refine ⟨ChainComplex.ofHom (X := K) (Y := K) e (fun i => by rw [hK]; exact he i), ?_, fun p hp => hp⟩
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  ext1
  simp [P, hπ0, he0]

end UpperTheory.V.Af.BA.ResolutionExactness

theorem UpperTheory.repResolution_exists :
    UpperTheory.V.Af.BA.ResOf :=
  UpperTheory.V.Af.BA.ResolutionExactness.main
end

section

open CategoryTheory UpperTheory.V UpperTheory.V.Af.BA

private theorem hom_sum_apply {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, c i • f i).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom, Rep.smul_hom]
    simp [ih]

private theorem d_coeff {Γ I : Type} [Group Γ] [MulAction Γ I] (K : Cx Γ I) (p : ℕ)
    (x : K.Tup (p + 1)) (y : K.Tup p) :
    ((K.d p).hom.toLinearMap (Finsupp.single x 1) : K.Tup p →₀ ℂ) y =
      ((KH.faceD (fun (i : Fin (p + 2)) => K.re i.succAbove) (Finsupp.single x 1) y : ℤ) : ℂ) := by
  classical
  show (Rep.Hom.hom (K.d p)) (Finsupp.single x 1) y = _
  simp only [Cx.d]
  rw [hom_sum_apply]
  simp [KH.faceD_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Cx.reC_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem UpperTheory.exactCOf_of_exactBase :
    UpperTheory.V.Af.BA.ExactBase → UpperTheory.V.Af.BA.ExactCOf := by
  intro hB Γ I _ _ K hZ
  classical
  obtain ⟨hs, he0, -⟩ := hZ 0
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs 1
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    obtain ⟨t, -⟩ := Finsupp.support_nonempty_iff.2 hv0
    intro c
    exact ⟨Finsupp.single t c, by rw [augC_single]⟩
  · have key := hB (K.Tup 1) (K.Tup 0) Unit _
      ((Finsupp.lsingle ()) ∘ₗ KH.aug (K.Tup 0)) _
      ((Finsupp.lsingle ()) ∘ₗ (Rep.Hom.hom (augC Γ (K.Tup 0))).toLinearMap) (d_coeff K 0) ?_ ?_
    · intro y
      have hy := key y
      simpa [Finsupp.single_eq_zero] using hy
    · intro y z
      simp [KH.aug_single]
      exact augC_single y 1
    · intro y
      have hy := he0 y
      simpa [Finsupp.single_eq_zero] using hy
  · intro p
    exact hB _ _ _ _ _ _ _ (d_coeff K (p + 1)) (d_coeff K p) ((hZ (p + 1)).2.2 p (Nat.lt_succ_self p))
end

section

private theorem cycle_range_conjugate_succAbove {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      (j.succAbove k) = i.succAbove (τ k) := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_succAbove,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

private theorem cycle_range_conjugate_pivot {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      j = i := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_self,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem UpperTheory.perm_split_fin_succ :
    UpperTheory.V.Af.BA.PermSplit := by
  intro n j
  classical
  let F : Fin (n + 1) × Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) := fun p =>
    (Fin.cycleRange p.1)⁻¹ * Equiv.Perm.decomposeFin.symm (0, p.2) * Fin.cycleRange j
  have hinj : Function.Injective F := by
    rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have hi : i = i' := by
      have h1 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j) h
      simp only [F] at h1
      rw [cycle_range_conjugate_pivot, cycle_range_conjugate_pivot] at h1
      exact h1
    subst hi
    simp only [F] at h
    have h2 := Equiv.injective _ (mul_left_cancel (mul_right_cancel h))
    rw [Prod.mk.injEq] at h2
    rw [h2.2]
  have hsurj : Function.Surjective F := by
    intro σ
    have hρ : (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹) 0 = 0 := by
      simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_zero, Fin.cycleRange_self]
    obtain ⟨⟨p, τ⟩, hp⟩ := Equiv.Perm.decomposeFin.symm.surjective
      (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹)
    have hp0 : p = 0 := by
      have h0 := congrArg (fun s : Equiv.Perm (Fin (n + 1)) => s 0) hp
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hρ]
    subst hp0
    refine ⟨(σ j, τ), ?_⟩
    simp only [F]
    rw [hp]
    group
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro i τ
  refine ⟨?_, fun k => cycle_range_conjugate_succAbove i j τ k⟩
  show ((Equiv.Perm.sign (F (i, τ)) : ℤ) : _) = _
  simp only [F, map_mul, map_inv, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, inv_pow, Int.units_inv_eq_self]
  push_cast
  ring
end

section

open CategoryTheory UpperTheory.V.Af.BA in
private def repHomEvalLinearMap {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} (x : A) : (A ⟶ B) →ₗ[ℂ] B where
  toFun φ := φ.hom x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.rep_hom_alternating_sum_eq_zero :
    UpperTheory.V.Af.BA.AltZero := by
  intro Γ I _ _ K
  have key : ∀ (p : ℕ) (t : K.Tup p), (K.alt p).hom (Finsupp.single t 1) =
      ((p + 1).factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin (p + 1)),
        ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) := by
    intro p t
    show repHomEvalLinearMap (B := PC Γ (K.Tup p)) (Finsupp.single t (1 : ℂ)) (K.alt p) = _

    simp only [Cx.alt, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro π _
    congr 1
    exact Cx.reC_single K _ t 1
  refine ⟨?_, ?_⟩
  · apply PC_ext
    intro x
    rw [key 0 x]
    have hre : K.re (id : Fin 1 → Fin 1) x = x := Subtype.ext rfl
    simp [Fintype.sum_unique, hre]
  · intro p hp
    apply PC_ext
    intro t
    rw [key p t]
    have hnt := hp t
    simp only [Function.Injective, not_forall] at hnt
    obtain ⟨a, b, htab, hab⟩ := hnt
    have ht : ∀ y, Subtype.val t (Equiv.swap a b y) = Subtype.val t y := by
      intro y
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, htab]
      · rw [h2, htab]
      · rfl
    set S := ∑ π : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))]
      rw [hSdef, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro π _
      have hre : K.re (⇑((Equiv.mulLeft (Equiv.swap a b)) π)) t = K.re π t :=
        Subtype.ext (funext fun k => by simp [Cx.re, Equiv.Perm.mul_apply, ht])
      rw [hre, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      push_cast
      rw [neg_one_mul, neg_smul]
    have hS0 : S = 0 := self_eq_neg.1 hS
    rw [hS0, smul_zero]
    rfl
end

section

theorem UpperTheory.building_fixed_points_equiv :
    UpperTheory.V.Af.BA.FixEquiv := by
  intro A B _ _ i σ N hi hσ
  have hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n := Fin N) i g ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by
    intro g
    change Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) =
      Matrix.GeneralLinearGroup.map (n := Fin N) i g
    ext a b
    exact (hσ _).2 ⟨g a b, rfl⟩
  have hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y := by
    intro X Y h
    ext a b
    exact hi (congrFun (congrFun h a) b)
  have hpre : ∀ g : GL (Fin N) B,
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) →
      ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin N) σ g = g := hg
    have h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b := by
      intro a b
      refine (hσ _).1 ?_
      have := congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'
      exact this
    choose X hX using h1
    exact ⟨Matrix.of X, by ext a b; exact hX a b⟩
  refine ⟨(MulEquiv.ofBijective
    ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩
  · intro g k h
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin N) i g =
      Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h
    apply Units.ext
    apply hM
    exact congrArg Units.val h1
  · rintro ⟨g, hg⟩
    obtain ⟨X, hX⟩ := hpre g hg
    obtain ⟨Y, hY⟩ := hpre g⁻¹ (inv_mem hg)
    refine ⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.mul_inv
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.inv_mul
    · apply Subtype.ext
      apply Units.ext
      exact hX
end

section

open NumberField in
theorem UpperTheory.exists_CM_integral_of_exists_CM :
    UpperTheory.V.Af.BA.ExCM → UpperTheory.V.Af.BA.ExCMInt := by
  intro h F _ _ _
  obtain ⟨L, i1, i2, i3, i, s, hs, hfix⟩ := h F
  refine ⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩
  · intro w x
    exact hs w.embedding (x : L)
  · intro x y hxy
    have h1 : i (x : F) = i (y : F) := congrArg (fun z : 𝓞 L => (z : L)) hxy
    exact RingOfIntegers.ext (i.injective h1)
  · intro x
    constructor
    · intro hx
      have h1 : s (x : L) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hx
      obtain ⟨y, hy⟩ := (hfix _).1 h1
      have hi : IsIntegral ℤ y := by
        have h2 : IsIntegral ℤ (i.toIntAlgHom y) := by
          have : i.toIntAlgHom y = (x : L) := hy
          rw [this]
          exact x.isIntegral_coe
        exact (isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2
      exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩
    · rintro ⟨y, hy⟩
      have h1 : i (y : F) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hy
      exact RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)
end

section

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
end

section

open CategoryTheory in
theorem UpperTheory.rankCohHom_of_rankHomology :
    UpperTheory.V.Af.CohB.RankHomology → UpperTheory.V.Af.BA.RankCohHom := by
  intro hR Γ _ P q X hX A
  obtain ⟨i⟩ := hX
  rw [(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]
  refine (hR _ q).trans ?_
  rw [ChainComplex.linearYonedaObj_X]
  exact (Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le
end

section

open CategoryTheory in
theorem UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.BA.CoindRetract → UpperTheory.V.Af.BA.BddOver := by
  intro hSum hRet
  unfold UpperTheory.V.Af.BA.BddOver
  intro G _ S hS hB
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, fun A => ?_⟩
  obtain ⟨π, ι, hπι⟩ := hRet G S hS A
  have hq : ∀ q, Module.rank ℂ ↑(groupCohomology A q) ≤
      Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q) := by
    intro q
    have h1 := hSum G Unit A (fun _ => Rep.coind S.subtype (Rep.res S.subtype A))
      (fun _ => π) (fun _ => ι) (by rw [Fintype.sum_unique]; exact hπι) q
    rw [Fintype.sum_unique,
      ((groupCohomology.coindIso (Rep.res S.subtype A) q).toLinearEquiv).rank_eq] at h1
    exact h1
  calc UpperTheory.V.Af.CohB.totCoh A
      = Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology A q)) := rfl
    _ ≤ Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q)) :=
      Cardinal.sum_le_sum _ _ hq
    _ = UpperTheory.V.Af.CohB.totCoh (Rep.res S.subtype A) := rfl
    _ ≤ c * Module.rank ℂ ↑(Rep.res S.subtype A) := hc _
    _ = c * Module.rank ℂ ↑A := rfl
end
