module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := open MvPolynomial GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac in by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := O)
  have pre : pt b v hv ⁻¹ᵁ chart O N r = spOpen (v r) := by
    change ProjPoint.ofHom (grading O N) (eval₂Hom b v) (map_irrelevant_eval₂Hom b hv) ⁻¹ᵁ
      Proj.basicOpen (grading O N) (MvPolynomial.X r) = _
    rw [ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (isHomogeneous_X O r), eval₂Hom_X']
    rfl
  have from_chart : (isAffineOpen_chart O N r).fromSpec =
      Spec.map (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos := by
    rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (Proj.basicOpenIsoSpec (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).hom_inv_id.symm
  have away_ratio (q : Fin (N + 1)) :
      (Proj.awayToSection (grading O N) (MvPolynomial.X r)).hom (ratioAway O N r q) = ratio O N r q := by
    rw [ratioAway, awayToSection_mk]
    exact frac_eq (by ring)
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pre] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  have ratio_mul (q : Fin (N + 1)) :
      pullRatio (pt b v hv) ⊤ r h2 q * fnOn ⊤ (v r) = fnOn ⊤ (v q) := by
    have hu' : IsUnit (eval₂Hom b v (MvPolynomial.X r)) := by rw [eval₂Hom_X']; exact IsUnit.mk0 _ hr
    have h4 := ProjPoint.awayLift_mk_mul (grading O N) (eval₂Hom b v) hu' (X_mem O N r) 1 (MvPolynomial.X q) (X_mem O N q)
    have he : pt b v hv = spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem O N r) hu'
    have : IsIso (Proj.awayToSection (grading O N) (MvPolynomial.X r)) :=
      (Proj.basicOpenIsoAway (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).isIso_hom
    have he2 : spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos =
        ofChartHom r (inv (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
          CommRingCat.ofHom (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
          (Scheme.ΓSpecIso (.of k)).inv) := by
      rw [ofChartHom, from_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
    rw [pullRatio_of_eq he h2 (he ▸ h2), pullRatio_of_eq he2 _ (ofChartHom_preimage _ _),
      pullRatio, ofChartHom_appLE, ← away_ratio, ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc,
      ]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu' (ratioAway O N r q)) * _ = _
    rw [← resG_self (X := Sp k) le_top ((Scheme.ΓSpecIso (.of k)).inv.hom _)]
    change fnOn ⊤ _ * fnOn ⊤ _ = fnOn ⊤ _
    rw [← map_mul]
    exact congrArg _ (by simpa only [ratioAway, eval₂Hom_X', pow_one] using h4)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩

  rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    ratio_mul]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := GlobalTheory.ProjSpace.exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dite_eq_right (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dite_eq_left hk, dite_eq_left hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dite_eq_right hk, dite_eq_right hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dite_eq_right]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dite_eq_left h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CauchyBinet

theorem lform_plk (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h1 : ∑ q, lform D ρ q * plk u e q =
      ∑ f : Fin k → Fin (M + 1), (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det :=
    Equiv.sum_comp (plE M k)
      (fun f : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det)
  rw [h1]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

variable {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {M : ℕ} {D c : Let m → Fin (M + 1) → S}

theorem pair_cellVec (w : Pm m) (x : CellVar m → S) (y z : Let m) :
    ∑ r, D y r * cellVec c w x z r = ∑ i, cell x z.1 i z.2 * ∑ r, D y r * c ⟨z.1, w z.1 i⟩ r := by
  simp only [cellVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem pair_same (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (a b : Fin (m τ)) :
    ∑ r, D (wLet w ⟨τ, a⟩) r * cellVec c w x ⟨τ, b⟩ r = cell x τ a b := by
  rw [pair_cellVec, Finset.sum_eq_single a]
  · rw [h]
    simp [wLet]
  · intro i _ hi
    rw [h, if_neg, mul_zero]
    intro he
    simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
    exact hi ((w τ).injective he).symm
  · simp

theorem pair_ne (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y.1 ≠ z.1) :
    ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  rw [pair_cellVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h, if_neg, mul_zero]
  intro he
  have h2 := congrArg Sigma.fst he
  exact hne h2

theorem pair_self (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (z : Let m) :
    ∑ r, D (wLet w z) r * cellVec c w x z r = 1 := by
  obtain ⟨τ, a⟩ := z
  rw [pair_same h]
  simp [cell]

theorem pair_zero (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y ≠ z)
    (hle : (y.2 : ℕ) ≤ z.2) : ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  by_cases h1 : y.1 = z.1
  · obtain ⟨τ, a⟩ := y
    obtain ⟨τ', b⟩ := z
    dsimp only at h1 hle
    subst h1
    rw [pair_same h]
    have hab : a ≠ b := fun e => hne (by rw [e])
    have hlt : ¬ b < a := not_lt.2 hle
    simp [cell, hab, hlt]
  · exact pair_ne h w x y z h1

theorem det_eq_one_of_unitri {k : ℕ} (N : Matrix (Fin k) (Fin k) S) (b : Fin k → ℕ) (h1 : ∀ l, N l l = 1)
    (h0 : ∀ l l', l ≠ l' → b l' ≤ b l → N l l' = 0) : N.det = 1 := by
  have hb : N.BlockTriangular b := fun l l' hl =>
    h0 l l' (fun e => by subst e; exact lt_irrefl _ hl) hl.le
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : N.toSquareBlock b a = 1 := by
    ext ⟨l, hl⟩ ⟨l', hl'⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    split_ifs with he
    · obtain rfl : l = l' := congrArg Subtype.val he
      exact h1 l
    · exact h0 l l' (fun e => he (Subtype.ext e)) (by rw [hl, hl'])
  rw [this, Matrix.det_one]

theorem lform_plk_down (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (k : ℕ) (e : Fin k → Let m)
    (he : Down e) : ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1 := by
  rw [lform_plk]
  refine det_eq_one_of_unitri _ (fun l => ((e l).2 : ℕ)) (fun l => pair_self h w x (e l)) fun l l' hl hb => ?_
  exact pair_zero h w x (e l') (e l) (fun e' => hl (he.1 e').symm) hb

theorem lform_plk_coord (hD : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) (h : j < i) :
    ∑ q, lform D (fun l : Fin (j + 1) =>
        wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q *
      plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  rw [lform_plk]
  simp only [std, pair_same hD]
  rw [Matrix.det_of_upperTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · have : Fin.castLE (Nat.succ_le_of_lt j.2) (Fin.last j) = j := Fin.ext rfl
      simp only [Matrix.of_apply, Fin.val_last, if_true, this, cell, dif_pos h]
    · intro l _
      have hl : ((l.castSucc : Fin (j + 1)) : ℕ) ≠ j := ne_of_lt l.2
      simp only [Matrix.of_apply, if_neg hl, cell, lt_irrefl, dif_neg, if_true, not_false_eq_true]
  · intro l l' hl
    have hl2 : (l' : ℕ) < l := hl
    have hl' : (l' : ℕ) ≠ j := by have := l.2; omega
    have hn : ¬ Fin.castLE (Nat.succ_le_of_lt j.2) l < Fin.castLE (Nat.succ_le_of_lt j.2) l' :=
      not_lt.2 (le_of_lt hl2)
    have hne : Fin.castLE (Nat.succ_le_of_lt j.2) l' ≠ Fin.castLE (Nat.succ_le_of_lt j.2) l :=
      ne_of_lt hl2
    simp only [Matrix.of_apply, if_neg hl', cell, dif_neg hn, if_neg hne]

theorem main : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ :=
  ⟨lform_plk, fun _ _ _ _ _ _ _ w x h =>
    ⟨lform_plk_down h w x, lform_plk_coord h w x⟩⟩

end GlobalTheory.FlagEmb.CauchyBinet
end
