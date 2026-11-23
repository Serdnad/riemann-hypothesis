module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Aesop.BuiltinRules
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle658
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial

namespace GlobalTheory

theorem weightedHomogeneousComponent_one_int {σ A : Type*} [CommRing A] (F : MvPolynomial σ A)
    (m : ℤ) : weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) m F =
      if 0 ≤ m then homogeneousComponent m.toNat F else 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent, weight_one_int]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, coeff_homogeneousComponent]
    by_cases h : (a.degree : ℤ) = m
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hm, if_neg (by omega)]
    simp

theorem isHomogeneous_polyGrading_of_component {ι A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A))
    (hJ : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) :
    (J : Submodule (MvPolynomial ι A) (MvPolynomial ι A)).IsHomogeneous (polyGrading ι A) := by
  intro m F hF
  have e : (decompose (polyGrading ι A) F m : MvPolynomial ι A) =
      weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) m F :=
    weightedDecomposition.decompose'_apply A _ F m
  rw [e, weightedHomogeneousComponent_one_int]
  split_ifs
  · exact hJ F hF _
  · exact zero_mem _

universe u

private theorem grAug_bijective_iff_local (ι : Type) {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M)
    [PolyGradedSMul ι ℳ] [LinearOrder ι] (n : ℤ) :
    Function.Bijective (grAug (ι := ι) (ℳ := ℳ) n) ↔
      (cubeComplex (grCube ι ℳ n)).ExactAt 0 ∧
        (cubeComplex (grCube ι ℳ n)).ExactAt 1 := by
  rw [← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]
  exact Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom
    (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv (ι := ι) ℳ n).bijective

private theorem cechHomologyZeroIso_grAug_local (ι : Type) {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M)
    [PolyGradedSMul ι ℳ] [LinearOrder ι] (n : ℤ) (m : ℳ n)
    (s : {s : Finset ι // s.card = 1}) :
    ((cechHomologyZeroIso (grCube ι ℳ n)).hom.hom
      (grAug (ι := ι) (ℳ := ℳ) n m)).1 s = toHomLoc ℳ s.1 n m := by
  exact (congrFun congr(($(cechAugHomology_comp (grCube ι ℳ n))).hom
    (toHomLoc ℳ ∅ n m)) s).trans (homLocRes_toHomLoc ℳ _ n m)

theorem sum_cubeSign_pair {ι : Type} [LinearOrder ι] {t : Finset ι} (ht : t.card = 2) :
    ∑ i ∈ t, cubeSign t i = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hab]
  have h := cubeSign_mul_erase (t := {a, b}) (by simp) (by simp) hab
  rw [Finset.erase_insert (by simpa using hab), Finset.pair_comm,
    Finset.erase_insert (by simpa using hab.symm), cubeSign_singleton, cubeSign_singleton,
    mul_one, mul_one, Finset.pair_comm] at h
  rw [h]; ring

theorem exists_form_of_compatible_fractions : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous d ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) A) ^ L * (F i - X i ^ N * G) ∈ J := by
  intro A _ _ n J hJ
  letI : Decomposition (grQuot (polyGrading (Fin (n + 1)) A) J) :=
    grQuotDecomposition _ (isHomogeneous_polyGrading_of_component J hJ)
  obtain ⟨n₀, hn₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A (MvPolynomial (Fin (n + 1)) A ⧸ J)
    (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hc => ?_⟩
  have hd' : n₀ ≤ (d : ℤ) := by omega
  have hb := (grAug_bijective_iff_local (ι := Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J)
    (d : ℤ)).2 ⟨hn₀ d hd' 0, hn₀ d hd' 1⟩
  have hmem : ∀ i, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) {i}) N
      (Submodule.Quotient.mk (F i)) ∈ homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) {i} d :=
    fun i => awayFrac_mem_homLoc (ℳ := grQuot (polyGrading (Fin (n + 1)) A) J) (d := ((d + N : ℕ) : ℤ))
      ⟨F i, mem_polyGrading_natCast.2 (hF i), rfl⟩ (by simp)
  let y : ∀ i, (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d).obj {i} :=
    fun i => ⟨_, hmem i⟩
  let x := Cube.termOneEquiv (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) y

  have hres : ∀ (s : {s : Finset (Fin (n + 1)) // s.card = 1}) (T : Finset (Fin (n + 1)))
      (h : s.1 ⊆ T), ∃ j ∈ s.1, (show homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) T d from
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) h (x s)).1 =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) T) N
          (xProd (R := A) (T.erase j) ^ N • Submodule.Quotient.mk (F j)) := by
    rintro ⟨s, hs⟩ T h
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
    refine ⟨j, Finset.mem_singleton_self j, ?_⟩
    have hj : j ∈ T := h (Finset.mem_singleton_self j)
    have e : x ⟨{j}, hs⟩ = y j := Cube.termOneEquiv_apply _ y j
    simp only [e, res_grCube]
    erw [coe_homLocRes]
    exact locRes_awayFrac X h (by rw [Finset.prod_singleton, Finset.prod_erase_mul _ _ hj]) N _

  have hx : Cube.d (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) 1 x = 0 := by
    funext t
    obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 t.2
    have hv : ∀ j ∈ t.1, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) t.1) N
        (xProd (R := A) (t.1.erase j) ^ N • Submodule.Quotient.mk (F j)) =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) t.1) N
        (xProd (R := A) (t.1.erase a) ^ N • Submodule.Quotient.mk (F a)) := by
      intro j hj
      rw [hab'] at hj ⊢
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rfl
      · rw [Finset.mem_singleton] at hj
        subst hj
        have e1 : ({a, j} : Finset (Fin (n + 1))).erase j = {a} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        have e2 : ({a, j} : Finset (Fin (n + 1))).erase a = {j} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        rw [e1, e2]
        simp only [xProd, Finset.prod_singleton, Finset.prod_pair hab]
        rw [awayFrac_eq_iff]
        obtain ⟨L, hL⟩ := hc a j
        refine ⟨L, ?_⟩
        rw [smul_smul, smul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq]
        have := J.mul_mem_left (-((X a * X j) ^ N)) hL
        convert this using 1
        simp only [Finset.prod_pair hab, smul_eq_mul]
        ring
    rw [Cube.d_apply]
    have hbt : b ∈ t.1 := by rw [hab']; simp
    have key : ∀ i : t.1, Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) =
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset b t.1) (x (Cube.eraseIdx t ⟨b, hbt⟩)) := by
      intro i
      obtain ⟨j, hj, e⟩ := hres (Cube.eraseIdx t i) t.1 (Finset.erase_subset i.1 t.1)
      obtain ⟨j', hj', e'⟩ := hres (Cube.eraseIdx t ⟨b, hbt⟩) t.1 (Finset.erase_subset b t.1)
      exact Subtype.ext (e.trans (((hv j (Finset.mem_of_mem_erase hj)).trans
        (hv j' (Finset.mem_of_mem_erase hj')).symm).trans e'.symm))
    rw [Finset.sum_congr rfl fun i _ => by rw [key i], ← Finset.sum_smul,
      Finset.sum_coe_sort t.1 (cubeSign t.1), sum_cubeSign_pair t.2, zero_smul]
    rfl

  obtain ⟨m, hm⟩ := hb.2 ((cechHomologyZeroIso
    (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩)
  obtain ⟨G, hG, hGm⟩ := m.2
  refine ⟨G, mem_polyGrading_natCast.1 hG, fun i => ?_⟩
  have e := cechHomologyZeroIso_grAug_local (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) (d : ℤ) m
    ⟨{i}, Finset.card_singleton i⟩
  have e2 : (cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).hom.hom
      ((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩) =
      ⟨x, hx⟩ :=
    congr(($((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv_hom_id)).hom ⟨x, hx⟩)
  rw [hm, e2] at e
  have e3 : x ⟨{i}, Finset.card_singleton i⟩ = y i := Cube.termOneEquiv_apply _ y i
  have e4 := congrArg Subtype.val (e3.symm.trans e)
  erw [coe_toHomLoc] at e4
  rw [← hGm, awayFrac_eq_iff] at e4
  obtain ⟨l, hl⟩ := e4
  refine ⟨l, ?_⟩
  simp only [xProd, Finset.prod_singleton, LinearMap.coe_restrictScalars, Submodule.mkQ_apply] at hl
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul (p := J) (X i ^ (l + N)),
    Submodule.Quotient.eq] at hl
  convert hl using 1
  simp only [smul_eq_mul]
  ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjSpace

theorem surjective_appLE_of_eq {X Z : Scheme.{0}} {f : Z ⟶ X} {A A' : X.Opens} {B B' : Z.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ f ⁻¹ᵁ A) (h' : B' ≤ f ⁻¹ᵁ A') :
    Function.Surjective (f.appLE A B h).hom → Function.Surjective (f.appLE A' B' h').hom := by
  subst hA hB
  exact id

theorem exists_affineOpen_fraction_pullRatio : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  intro R _ N Y φ hφ y V i hyV hyi
  obtain ⟨U', hU', hU⟩ := φ.isEmbedding.isInducing.isOpen_iff.1 V.isOpen
  let O : (PSpace R N).Opens := ⟨U', hU'⟩ ⊓ φ.coborderRange
  have hyO : φ y ∈ O := ⟨show φ y ∈ U' by rw [← Set.mem_preimage, hU]; exact hyV, subset_coborder ⟨y, rfl⟩⟩
  obtain ⟨h, hhO, hyh⟩ := (isAffineOpen_chart R N i).exists_basicOpen_le (V := O) ⟨φ y, hyO⟩ hyi
  have hD : IsAffineOpen ((PSpace R N).basicOpen h) := (isAffineOpen_chart R N i).basicOpen h
  have hDc : (PSpace R N).basicOpen h ≤ chart R N i := (PSpace R N).basicOpen_le h
  have hle : (PSpace R N).basicOpen h ≤ φ.coborderRange := fun z hz => (hhO hz).2
  haveI : IsAffine ((PSpace R N).basicOpen h) := hD
  have hp : IsPullback (φ ∣_ (PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h).ι
      ((PSpace R N).homOfLE hle) φ.liftCoborder := by
    refine IsPullback.of_bot (h₃₁ := φ) (v₂₁ := 𝟙 _) (v₂₂ := φ.coborderRange.ι) ?_ ?_ ?_
    · rw [Category.comp_id, Scheme.homOfLE_ι]
      exact isPullback_morphismRestrict φ _
    · rw [← cancel_mono φ.coborderRange.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Hom.liftCoborder_ι, morphismRestrict_ι]
    · exact IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Scheme.Hom.liftCoborder_ι]⟩
  haveI : IsClosedImmersion (φ ∣_ (PSpace R N).basicOpen h) := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨hWa, hsurj0⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (φ ∣_ (PSpace R N).basicOpen h)
  have hsurj : Function.Surjective
      (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom := by
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at hsurj0
    exact surjective_appLE_of_eq (by simp) (by simp) _ _ hsurj0
  have hWc : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ φ ⁻¹ᵁ chart R N i := φ.preimage_mono hDc
  refine ⟨φ ⁻¹ᵁ (PSpace R N).basicOpen h, hWc, hyh, ?_, hWa, ?_⟩
  · intro z hz
    have : φ z ∈ U' := (hhO hz).1
    rw [← Set.mem_preimage, hU] at this
    exact this
  · intro g
    obtain ⟨a, rfl⟩ := hsurj g
    have hloc := (isAffineOpen_chart R N i).isLocalization_basicOpen h
    have key : ∀ p : MvPolynomial (Fin (N + 1)) R,
        (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom
          (algebraMap Γ(PSpace R N, chart R N i) Γ(PSpace R N, (PSpace R N).basicOpen h)
            (MvPolynomial.aeval (R := R) (ratio R N i) p)) =
        MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) _).hom
          (pullRatio φ _ i hWc) p := by
      intro p
      have e1 := appLE_resG φ hDc (le_rfl : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ _) (MvPolynomial.aeval (R := R) (ratio R N i) p)
      have e2 := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ (PSpace R N).basicOpen h) (i := i) (hi := hWc))
      exact e1.trans e2
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a
    obtain ⟨m, hm⟩ := s.2
    obtain ⟨P, rfl⟩ := aeval_ratio_surjective R N i b
    obtain ⟨h₀, hh₀⟩ := aeval_ratio_surjective R N i h
    have hQ : MvPolynomial.aeval (R := R) (ratio R N i) (h₀ ^ m) = (s : Γ(PSpace R N, chart R N i)) := by
      rw [map_pow, hh₀, ← hm]
    refine ⟨P, h₀ ^ m, ?_, ?_⟩
    · rw [← key, hQ]
      exact (IsLocalization.map_units _ s).map _
    · rw [← key, ← key, hQ, ← map_mul]
      exact congrArg _ hs

end GlobalTheory.ProjSpace
end

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

def zR (P Q R S : ℕ) : Fin R × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inl w.1)

def yS (P Q R S : ℕ) : Fin S × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inr w.1)

def kap (P Q k k' : ℕ) : Fin (P + Q) → ℂ := fun i => if (i : ℕ) < P then (k : ℂ) else -(k' : ℂ)

theorem zR_inj (P Q R S : ℕ) : Function.Injective (zR P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [zR, Prod.mk.injEq, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem yS_inj (P Q R S : ℕ) : Function.Injective (yS P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [yS, Prod.mk.injEq, Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem zR_ne_yS (P Q R S : ℕ) (u w) : zR P Q R S u ≠ yS P Q R S w := by
  simp [zR, yS]

theorem zR_or_yS (P Q R S : ℕ) (s : Ln P Q R S) :
    (∃ u, zR P Q R S u = s) ∨ ∃ w, yS P Q R S w = s := by
  obtain ⟨a, c | d⟩ := s
  · exact Or.inl ⟨(c, finSumFinEquiv a), by simp [zR]⟩
  · exact Or.inr ⟨(d, finSumFinEquiv a), by simp [yS]⟩

theorem fockF_rowOp {σ I J : Type} [DecidableEq σ] [Fintype J] (z : I × J → σ) (c d : I)
    (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (GlobalTheory.Capelli.rowOp ℂ z c d f) g = Formalism.REAL.fockF f (GlobalTheory.Capelli.rowOp ℂ z d c g) := by
  rw [GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply, Formalism.REAL.fischerInner_sum_left, Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.REAL.fischerInner_X_mul_left, Formalism.REAL.fischerInner_pderiv_left]

theorem eab_isKC_inl {R S : ℕ} (c d : Fin R) : IsKC (Eab (.inl c) (.inl d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

theorem eab_isKC_inr {R S : ℕ} (c d : Fin S) : IsKC (Eab (.inr c) (.inr d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

end GlobalTheory.LowIrr

end
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitaryCellSumLeviReduction_of_steps : GlobalTheory.SatakeWeyl.RankOne → GlobalTheory.SatakeWeyl.EmbExists → GlobalTheory.SatakeWeyl.EmbMem → GlobalTheory.SatakeWeyl.EmbTorus → GlobalTheory.SatakeWeyl.LeviRad → GlobalTheory.SatakeWeyl.UnipSplit → GlobalTheory.SatakeWeyl.Contract → GlobalTheory.SatakeWeyl.TorusConj → GlobalTheory.SatakeWeyl.LeviStep := by
  first | exact @GlobalTheory.SatakeWeyl.leviStep_of_steps | exact GlobalTheory.SatakeWeyl.leviStep_of_steps | (intros; apply GlobalTheory.SatakeWeyl.leviStep_of_steps <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets : GlobalTheory.SatakeWeyl.CartanFour := by
  first | exact @GlobalTheory.SatakeWeyl.Four.cartanFour | exact GlobalTheory.SatakeWeyl.Four.cartanFour | (intros; apply GlobalTheory.SatakeWeyl.Four.cartanFour <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.IndexFour := by
  first | exact @GlobalTheory.SatakeWeyl.IdxFour.indexFour | exact GlobalTheory.SatakeWeyl.IdxFour.indexFour | (intros; apply GlobalTheory.SatakeWeyl.IdxFour.indexFour <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.cell_sum_left_right_invariance_normaliser : GlobalTheory.SatakeWeyl.CellInv := by
  first | exact @GlobalTheory.SatakeWeyl.cellInv_holds | exact GlobalTheory.SatakeWeyl.cellInv_holds | (intros; apply GlobalTheory.SatakeWeyl.cellInv_holds <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps : GlobalTheory.SatakeWeyl.Descent → GlobalTheory.SatakeWeyl.CellInv → GlobalTheory.SatakeWeyl.ChainSum → GlobalTheory.SatakeWeyl.RankOne := by
  first | exact @GlobalTheory.SatakeWeyl.rankOne_of_steps | exact GlobalTheory.SatakeWeyl.rankOne_of_steps | (intros; apply GlobalTheory.SatakeWeyl.rankOne_of_steps <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity : GlobalTheory.SatakeWeyl.Unimod → GlobalTheory.SatakeWeyl.ChainIndex → GlobalTheory.SatakeWeyl.ChainSum := by
  first | exact @GlobalTheory.SatakeWeyl.chainSum_of_unimod | exact GlobalTheory.SatakeWeyl.chainSum_of_unimod | (intros; apply GlobalTheory.SatakeWeyl.chainSum_of_unimod <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex := by
  first | exact @GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | exact GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | (intros; apply GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts : GlobalTheory.SatakeWeyl.Contract := by
  first | exact @GlobalTheory.SatakeWeyl.ContractProof.contract | exact GlobalTheory.SatakeWeyl.ContractProof.contract | (intros; apply GlobalTheory.SatakeWeyl.ContractProof.contract <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  first | exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | exact GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | (intros; apply GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex <;> assumption)
end
